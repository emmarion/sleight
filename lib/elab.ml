open Term
open Reader
open Env
module V = Value
module Sp = Special

type entry = Term.entry = { name : string option; subterm : bool; mult : mult; sg : sg }
type res = { term : term; ty : term; erasure : mult }

let type_term = Prelude.type_term
let single loc = function [ r ] -> r | rs -> error loc "expected one value, got %d" (List.length rs)
let pos_of expect = if List.for_all (( = ) Erased) expect then Erased else Many
let atom = function Atom (_, n) -> Some n | List _ -> None
let atom_or loc raw what = match atom raw with Some n -> n | None -> error loc "expected %s, got %s" what (Reader.show raw)
let name_or_anon n = if n = "_" then None else Some n

(* A special form's head: a Const, non-erased entry of type (Special) holding one of its variants (section 4). *)
let special_of env raw =
  Option.bind (Option.bind (atom raw) (lookup env)) (fun x ->
      match entry env x with
      | { state = Const (V.VCtor (c, [])); mult = Many; _ } when equal (type_of env x) Prelude.special_term -> List.assoc_opt c.cid Prelude.specials
      | _ -> None)

let is_special env raw s = special_of env raw = Some s
let mult_of env raw = match special_of env raw with Some Sp.Erased -> Some Erased | Some Sp.Many -> Some Many | _ -> None
let mult_or env loc raw = match mult_of env raw with Some m -> m | None -> error loc "expected a multiplicity, got %s" (Reader.show raw)
let is_statement env = function List (_, h :: _) -> List.exists (is_special env h) Sp.statements | _ -> false
let at loc f = try f () with Error (0, msg) -> error loc "%s" msg
let var env loc n =
  match Literal.classify n with
  | `Name -> (match lookup env n with Some x -> x | None -> error loc "unbound name %s" n)
  | `Lit lit -> (match List.assoc_opt (Literal.key lit) env.literals with Some (x, _) -> x | None -> error loc "literal %s outside a top-level form" n)
  | `Bad msg -> error loc "%s" msg

let resolve env x = match canon env (Var x) with Var y -> y | _ -> x

(* Elaborate in the prelude's scope, so user shadowing cannot reach a generated form; the level context
   stays the caller's. *)
let in_prelude env f =
  let frame, r = f { env with scope = env.prelude } in
  ({ frame with scope = env.scope }, r)

(* The entry holding the [Nat] a numeral or character literal stands for: a character's is its code's. *)
let numeral_entry env loc raw =
  let name = atom_or loc raw "a numeral or character literal" in
  let z =
    match Literal.classify name with
    | `Lit (Literal.Numeral z) -> z
    | `Lit (Literal.Char c) -> Z.of_int c
    | _ -> error loc "%s is not a numeral or character literal" name
  in
  match List.assoc_opt (Z.to_string z) env.literals with
  | Some (x, _) -> (z, x)
  | None -> error loc "literal %s is not in scope" (Z.to_string z)

(* An atom naming an entry, read through any alias rule the fact table holds for it (section 9). *)
let named env loc what raw =
  match canon env (Var (var env loc (atom_or loc raw what))) with Var x -> x | t -> error loc "%s is not %s" (show env t) what

let tyname env loc = named env loc "a type constructor"

(* Identity after canonicalization (section 5), solving any metas either side holds (Env.unify). *)
let solve what env loc actual expected =
  try unify env actual expected with Contradiction _ -> error loc "%s mismatch: expected %s, got %s" what (show env expected) (show env actual)

let check what env loc actual expected = ignore (solve what env loc actual expected)
let check_type = check "type" and check_equal = check "value"
let solve_sg env loc sg r = match sg with Ty ty -> solve "type" env loc r.ty ty | Is t -> solve "value" env loc r.term t
let check_sg env loc sg r = ignore (solve_sg env loc sg r)
let under pos m = if pos = Erased then Erased else m
let wild = function Atom (_, "_") -> true | _ -> false

let rec infer env loc t =
  match t with
  | Var x -> type_of env x
  | App (h, args) -> (
      match canon env (infer env loc h) with
      | TyCtor _ -> type_term
      | ValCtor (_, r) -> instantiate (List.rev args) r
      | ty -> error loc "%s has type %s and cannot be applied" (show env h) (show env ty))
  | Fn _ | TyCtor _ | ValCtor _ | Matchable _ | Newtype _ -> type_term
  | Bound _ -> error loc "internal: dangling binder"

let res_of env x = { term = Var x; ty = type_of env x; erasure = (entry env x).mult }
let non_erased env ids = List.filter (fun x -> (entry env x).mult = Many) ids
let term_res env loc t = { term = t; ty = infer env loc t; erasure = Erased }

(* A Matchable's value, where its entry is Const (section 34); a Dyn one is read when the code runs. *)
let adt_of env x = match (entry env x).state with Const (V.VMatchable adt) -> Some adt | _ -> None

let matchables env tid =
  List.filter_map
    (fun x -> match type_of env x with Matchable (d, Var t, cs) when t = tid -> Some (resolve env x, d, cs) | _ -> None)
    env.scope

(* Consistent Matchables for one type are interchangeable (section 19), so the pick prefers one whose ADT the
   elaborator can see, then a non-erased one, over one a non-erased match would have to read and cannot. *)
let find_matchable env loc tid =
  let rank (x, _, _) = if adt_of env x <> None then 0 else if (entry env x).mult = Many then 1 else 2 in
  match List.stable_sort (fun a b -> compare (rank a) (rank b)) (matchables env tid) with
  | [] -> error loc "%s has no Matchable in scope" (name_of env tid)
  | (x, d, cs) :: rest ->
      if List.exists (fun (y, _, _) -> not (equal (type_of env x) (type_of env y))) rest then
        error loc "ambiguous Matchables for %s" (name_of env tid);
      (x, d, cs)

let type_head env ty = match canon env ty with App (Var t, _) -> Some t | _ -> None

let check_empty env loc ty =
  let empty = match type_head env ty with Some t when matchables env t <> [] -> (let _, _, cs = find_matchable env loc t in cs = []) | _ -> false in
  if not empty then error loc "%s is not an empty type" (show env ty)

let ctor_type env loc c =
  match canon env (type_of env c) with ValCtor (tele, ret) -> (tele, ret) | _ -> error loc "%s is not a value constructor" (name_of env c)

let tid_of env loc c = Option.get (type_head env (snd (ctor_type env loc c)))
let marker env loc tid ctors c =
  match List.find_opt (fun (_, c') -> c' = Var c) ctors with
  | Some (m, _) -> m
  | None -> error loc "%s is not a constructor of %s" (name_of env c) (name_of env tid)

let phantom env loc c = let tid = tid_of env loc c in let _, _, ctors = find_matchable env loc tid in marker env loc tid ctors c = Erased

(* A Matchable's constructors, each with its phantom marker and its number of many fields (section 38). *)
let shapes env loc ctors =
  List.map (fun (m, c) -> match c with Var c -> (m, c, List.length (List.filter (fun e -> e.mult = Many) (fst (ctor_type env loc c)))) | _ -> assert false) ctors

let non_phantom shapes = List.filter_map (fun (m, c, n) -> if m = Many then Some (c, n) else None) shapes

(* A phantom constructor heads no runtime value (section 20 rule 2), so discriminants number the others only. *)
let discriminant shapes c = find_index (fun (c', _) -> c' = c) (non_phantom shapes)

let tagged disc shapes = disc = Enum && List.length (non_phantom shapes) > 1

let wrapper disc shapes =
  match List.filter (fun (m, _, n) -> m = Many && n = 1) shapes with
  | [ (_, w, _) ] when (not (tagged disc shapes)) && List.for_all (fun (m, c, n) -> m = Erased || c = w || n = 0) shapes -> Some w
  | _ -> None

let newtype_of env c = List.find_opt (fun x -> match type_of env x with Newtype (Var c') -> c' = c | _ -> false) env.scope
let ctor_of env loc c = match (entry env c).state with Const (V.VCtorFn ct) -> ct | _ -> error loc "%s is not a run-position constructor" (name_of env c)
let const env v = if env.run_pos then Const v else Dyn
let ctor_var env loc = named env loc "a constructor"
let proof_type ctor args = App (Var ctor, args)

let expect_proof env loc ctor p =
  match canon env (infer env loc p) with
  | App (Var c, args) when c = ctor -> args
  | ty -> error loc "expected a %s proof, got %s : %s" (name_of env ctor) (show env p) (show env ty)

let rec is_strict_subterm a b =
  match b with App (_, args) -> List.exists (fun x -> equal a x || is_strict_subterm a x) args | _ -> false

type src_entry = { s_loc : loc; s_subterm : bool; s_mult : mult option; s_sg : [ `Ty of raw | `Is of raw ] option; s_name : string }

let parse_entry env raw =
  match raw with
  | List (l, items) -> (
      let s_subterm, items = match items with t :: rest when is_special env t Sp.Subterm -> (true, rest) | _ -> (false, items) in
      let s_mult, items = match items with t :: rest when mult_of env t <> None -> (mult_of env t, rest) | _ -> (None, items) in
      let mk s_sg s_name = { s_loc = l; s_subterm; s_mult; s_sg; s_name } in
      match items with
      | [ e; i; Atom (_, n) ] when is_special env i Sp.Is -> [ mk (Some (`Is e)) n ]
      | [ Atom (_, n) ] -> [ mk None n ]
      | ty :: names when names <> [] && List.for_all (fun n -> atom n <> None) names ->
          List.map (fun n -> mk (Some (`Ty ty)) (Option.get (atom n))) names
      | _ -> error l "malformed telescope entry %s" (Reader.show raw))
  | Atom (l, _) -> error l "expected a telescope entry, got %s" (Reader.show raw)

let split_arrow env loc items =
  let rec go acc = function
    | [] -> error loc "missing ->"
    | t :: rest when is_special env t Sp.Arrow -> (List.rev acc, rest)
    | t :: rest -> go (t :: acc) rest
  in
  go [] items

let split_returns env items =
  let rec go acc = function
    | List (_, m :: _) as r :: rest when mult_of env m <> None -> go (r :: acc) rest
    | rest -> (List.rev acc, rest)
  in
  go [] items

let no_mults loc = fun _ -> function None -> Some Erased | Some _ -> error loc "these entries carry no multiplicity"

(* Leading annotation tokens drawn from [allowed], in any order. *)
let marks env allowed items =
  let rec go acc = function
    | t :: rest when List.exists (is_special env t) allowed -> go (List.find (is_special env t) allowed :: acc) rest
    | rest -> (acc, rest)
  in
  go [] items

let fact_of env loc = function Ty t -> (t, None) | Is t -> (infer env loc t, Some t)

let anon tele = List.map (fun _ -> None) tele

(* [ids]: terms of the binders already in force, innermost first. Binds one fresh entry per item and returns their ids in order. *)
let open_tele env ?names ?mults ?states ?(ids = []) ?meta tele =
  let nth l i default = match l with Some l -> List.nth l i | None -> default in
  let _, env, _, fresh =
    List.fold_left
      (fun (i, env, ids, fresh) e ->
        let ty, rule = fact_of env 0 (map_sg (instantiate ids) e.sg) in
        let x, env = bind env ?meta (nth names i e.name) (nth mults i e.mult) (nth states i Dyn) ty ?rule in
        (i + 1, env, Var x :: ids, x :: fresh))
      (0, env, ids, []) tele
  in
  (env, List.rev fresh)

let spread mults values =
  snd (List.fold_left_map (fun vs m -> match (m, vs) with Many, v :: rest -> (rest, v) | _ -> (vs, V.VToken)) values mults)

let witness env ?(mult = Erased) ?(value = V.VToken) ty = bind env None mult (const env value) ty

let matchable_code env pos x =
  if pos = Erased then V.CErased else match adt_of env x with Some adt -> V.CConst (V.VMatchable adt) | None -> V.CVar x

(* A match on an ADT the elaborator can see reads no Matchable at runtime (section 17). *)
let match_shape env x tagged = match adt_of env x with Some adt -> V.Known adt | None -> V.Held (V.CVar x, tagged)
let mint_level env name = bind env ~minted_level:true name Erased (const env V.VToken) Prelude.level_term

let rec elab_term ?expect env raw =
  match raw with
  | Atom (l, n) -> Var (var env l n)
  | List (l, []) -> error l "empty form"
  | List (l, head :: args) -> (
      match special_of env head with
      | Some sp -> elab_type_form env l sp args
      | None -> (
          let h = Var (var env l (atom_or l head "a constructor")) in
          match canon env (infer env l h) with
          | TyCtor tele | ValCtor (tele, _) -> App (h, List.rev (elab_term_args env l ?expect tele h args))
          | ty -> error l "%s has type %s and cannot be applied in a type" (show env h) (show env ty)))

and elab_type_form env l sp args =
  match (sp, args) with
  | Sp.Fn, lv :: rest ->
      let lv = elab_term env lv in
      check_type env l (infer env l lv) Prelude.level_term;
      let ps, rs = split_arrow env l rest in
      elab_fn_type env lv ps rs
  | Sp.TyCtor, _ -> let ps, ret = split_arrow env l args in elab_tyctor env l ps ret
  | Sp.ValCtor, _ -> let _, _, _, t = elab_valctor env l args in t
  | Sp.Matchable, d :: t :: cs ->
      let ctor = function
        | List (l, [ m; c ]) -> (mult_or env l m, Var (ctor_var env l c))
        | r -> error (loc r) "expected (multiplicity Constructor)"
      in
      Matchable (disc_of env l d, Var (tyname env l t), List.map ctor cs)
  | Sp.Newtype, [ c ] -> let c = ctor_var env l c in ignore (ctor_type env l c); Newtype (Var c)
  | (Sp.Fn | Sp.Matchable | Sp.Newtype), _ -> error l "malformed %s" (Sp.name sp)
  | _ -> error l "%s cannot appear in a type" (Sp.name sp)

and elab_fn_type env lv ps rs =
  let env, ids, params = elab_tele env ~subterm:true ps in
  let _, _, rets = elab_tele env ~ids:(List.rev ids) rs in
  Fn (lv, params, rets)

and elab_tyctor env l ps ret =
  let env', _, tele = elab_tele env ~mults:(no_mults l) ps in
  (match ret with [ r ] -> check_equal env' l (elab_term env' r) type_term | _ -> error l "TyCtor returns Type");
  TyCtor tele

and elab_valctor env l items =
  let ps, ret = split_arrow env l items in
  let env', ids, tele = elab_tele env ps in
  let ret = match ret with [ r ] -> elab_type env' r | _ -> error l "a constructor returns one type" in
  (match canon env' ret with
  | App (Var t, _) when (not (List.mem t ids)) && (match type_of env' t with TyCtor _ -> true | _ -> false) -> ()
  | _ -> error l "a constructor returns an application of a type constructor in scope, not %s" (show env' ret));
  (env', tele, ret, ValCtor (tele, abstract (List.rev ids) ret))

and disc_of env l d = match special_of env d with Some Sp.Enum -> Enum | Some Sp.Union -> Union | _ -> error l "expected enum or union"

and elab_type env raw =
  let t = elab_term env raw in
  check_type env (loc raw) (infer env (loc raw) t) type_term;
  t

and elab_sg env = function `Ty t -> Ty (elab_type env t) | `Is t -> Is (elab_term env t)

and level_var env l raw =
  match canon env (elab_term env raw) with Var x when equal (type_of env x) Prelude.level_term -> x | t -> error l "%s is not a level" (show env t)

(* Elaborates source entries into a closed telescope, binding each name for the entries after it.
   [ids]: binders already in force, innermost first; [mults] maps an entry's index and declared multiplicity to its actual one. *)
and elab_tele env ?(subterm = false) ?(ids = []) ?(mults = fun _ m -> m) entries =
  let entries = List.concat_map (parse_entry env) entries in
  let _, env, ids, tele =
    List.fold_left
      (fun (i, env, ids, tele) e ->
        if e.s_subterm && not subterm then error e.s_loc "subterm is not allowed here";
        let mult = match mults i e.s_mult with Some m -> m | None -> error e.s_loc "entry %s needs a multiplicity" e.s_name in
        let sg = match e.s_sg with Some s -> elab_sg env s | None -> error e.s_loc "entry %s needs a type or an is clause" e.s_name in
        let ty, rule = fact_of env e.s_loc sg in
        let name = name_or_anon e.s_name in
        let x, env = bind env name mult Dyn ty ?rule in
        (i + 1, env, x :: ids, { name; subterm = e.s_subterm; mult; sg = map_sg (abstract ids) sg } :: tele))
      (0, env, ids, []) entries
  in
  (env, List.rev ids, List.rev tele)

(* Checks [args] against [tele] with [elab env mult arg expect]; returns the argument terms innermost first,
   and their code. A meta stands for each parameter (SUGAR.md 6): an argument written `_` is left to it, and
   is an error unless erased where it stands; any other argument is checked against its parameter and bound
   to its meta. [result] is the application's result telescope over the parameters' metas, unified with
   [expect] eagerly, where a `_` is present, before any argument is read, and again, reporting the mismatch,
   when a `_` would otherwise stay unsolved at the closing paren; every `_` is solved by then or refused. *)
and check_args env loc ?expect ?(result = fun _ -> []) ?(pos = Erased) tele args elab =
  if List.length tele <> List.length args then error loc "expected %d arguments, got %d" (List.length tele) (List.length args);
  let env, metas = open_tele env ~meta:true ~names:(anon tele) ~mults:(List.map (fun _ -> Erased) tele) tele in
  let mvars = List.rev_map (fun x -> Var x) metas in
  let wilds = List.exists wild args in
  let against ~strict env = match expect with Some tele when wilds -> solve_tele ~strict env loc tele (result mvars) | _ -> env in
  let env = against ~strict:false env in
  let env, acc, codes =
    List.fold_left2
      (fun (env, acc, codes) (i, e, m) arg ->
        let sg = map_sg (instantiate acc) e.sg in
        if wild arg then (
          if under pos e.mult = Many then error (Reader.loc arg) "_ stands for an erased argument, and argument %d here is not erased" (i + 1);
          (env, Var m :: acc, codes))
        else
          let env, r, code = elab env e.mult arg (Some [ { e with sg } ]) in
          let env = solve_sg env (Reader.loc arg) sg r in
          (solve "value" env (Reader.loc arg) r.term (Var m), r.term :: acc, if e.mult = Many then code :: codes else codes))
      (env, [], []) (List.mapi (fun i (e, m) -> (i, e, m)) (List.combine tele metas)) args
  in
  let env = if List.exists (has_meta env) acc then against ~strict:true env else env in
  List.iteri (fun i t -> if has_meta env t then error loc "argument %d is _ and cannot be inferred" (i + 1)) (List.rev acc);
  (env, List.map (metaless env) acc, List.rev codes)

(* [result] entrywise against [expect]: terms where both are `is` entries, types always. Not [strict]: a
   failure leaves the environment as it was. *)
and solve_tele ~strict env loc expect result =
  let attempt () =
    if List.length expect <> List.length result then error loc "expected %d values, got %d" (List.length expect) (List.length result);
    List.fold_left2
      (fun env e r ->
        let env = match (e.sg, r.sg) with Is a, Is b -> solve "value" env loc b a | _ -> env in
        let ty = function Ty t -> Some t | Is t -> if has_dangling t then None else Some (infer env loc t) in
        match (ty r.sg, ty e.sg) with Some a, Some b -> solve "type" env loc a b | _ -> env)
      env expect result
  in
  if strict then attempt () else try attempt () with Error _ -> env

and elab_term_args env loc ?expect tele ret args =
  let result mvars = [ { name = None; subterm = false; mult = Erased; sg = Is (App (ret, List.rev mvars)) } ] in
  let _, acc, _ = check_args env loc ?expect ~result tele args (fun env _ a expect -> (env, term_res env (Reader.loc a) (elab_term ?expect env a), V.CErased)) in
  acc

(* [ids] as in [open_tele]. *)
let check_results env loc ?(ids = []) tele ress =
  if List.length tele <> List.length ress then error loc "expected %d values, got %d" (List.length tele) (List.length ress);
  ignore (List.fold_left2 (fun acc e r -> check_sg env loc (map_sg (instantiate acc) e.sg) r; r.term :: acc) ids tele ress)

let mint env ty =
  let x, env = bind env None Erased Dyn ty in
  (env, res_of env x)

let prove_subterm env l a b =
  if not (is_strict_subterm (canon env a) (canon env b)) then error l "%s is not a strict subterm of %s" (show env a) (show env b);
  mint env (proof_type Prelude.subterm [ infer env l a; a; infer env l b; b ])

let prove_predates env l x lvl =
  if not (entry env lvl).minted_level then error l "%s is not a level minted by def-lvl" (name_of env lvl);
  let x = match canon env (Var x) with Var y when x >= lvl -> y | _ -> x in
  if x >= lvl then error l "%s was not in scope when level %s was minted" (name_of env x) (name_of env lvl);
  mint env (proof_type Prelude.predates [ type_of env x; Var x; Var lvl ])

let rec elab_expr ?(cc = V.Plain) ?tele env expect raw : Env.t * res list * V.code =
  let l = loc raw in
  let env, ress, code = elab_form cc tele env expect raw in
  if List.length ress <> List.length expect then error l "expected %d values, got %d" (List.length expect) (List.length ress);
  List.iter2 (fun m r -> if m = Many && r.erasure = Erased then error l "erased value %s : %s used in a non-erased position" (show env r.term) (show env r.ty)) expect ress;
  (env, ress, code)

and elab_expr1 ?cc ?tele env mult raw =
  let env, ress, code = elab_expr ?cc ?tele env [ mult ] raw in
  (env, List.hd ress, code)

and elab_erased env raw =
  let env, r, _ = elab_expr1 env Erased raw in
  (env, r.term)

and elab_form cc expect_tele env expect raw =
  let pos = pos_of expect in
  let arg env m a tele = elab_expr1 ?tele env (under pos m) a in
  match raw with
  | Atom (l, n) ->
      let x = var env l n in
      (env, [ res_of env x ], if pos = Many then V.CVar x else V.CErased)
  | List (l, []) -> error l "empty form"
  | List (l, head :: args) -> (
      match special_of env head with
      | Some sp -> elab_special expect_tele env expect l sp args
      | None -> (
          let env, h, hcode =
            match head with
            | Atom (_, n) -> let x = var env l n in (env, res_of env x, V.CVar x)
            | List _ -> elab_expr1 env pos head
          in
          match canon env h.ty with
          | TyCtor tele ->
              if pos = Many then error l "type constructor application in a non-erased position";
              (env, [ { term = App (h.term, List.rev (elab_term_args env l ?expect:expect_tele tele h.term args)); ty = type_term; erasure = Erased } ], V.CErased)
          | ValCtor (tele, ret) ->
              if pos = Many && h.erasure = Erased then error l "erased constructor %s in a non-erased position" (show env h.term);
              let result mvars = [ { name = None; subterm = false; mult = Erased; sg = Is (App (h.term, List.rev mvars)) } ] in
              let env, acc, codes = check_args env l ?expect:expect_tele ~result ~pos tele args arg in
              let code = if pos = Erased then V.CErased else V.CApp (hcode, codes, V.Ctor) in
              (env, [ { term = App (h.term, List.rev acc); ty = instantiate acc ret; erasure = pos } ], code)
          | Fn (lv, params, rets) -> elab_call cc env ?tele:expect_tele expect l h hcode lv params rets args arg
          | ty -> error l "%s : %s is not applicable" (show env h.term) (show env ty)))

and elab_call cc env ?tele expect l callee hcode lv params rets args arg =
  let pos = pos_of expect in
  if pos = Many && callee.erasure = Erased then error l "erased function %s called in a non-erased position" (show env callee.term);
  let annotation, args =
    let rec go i acc = function
      | List (_, [ k; p ]) :: rest when is_special env k Sp.Predates && i = 0 -> (Some (`Predates p), List.rev_append acc rest)
      | List (_, [ k; p ]) :: rest when is_special env k Sp.Subterm -> (Some (`Subterm (i, p)), List.rev_append acc rest)
      | a :: rest -> go (i + 1) (a :: acc) rest
      | [] -> (None, List.rev acc)
    in
    go 0 [] args
  in
  let env, acc, codes = check_args env l ?expect:tele ~result:(fun mvars -> instantiate_tele mvars rets) ~pos params args arg in
  let arg_terms = List.rev acc in
  let subterm_params = List.filter_map (fun (i, e) -> if e.subterm then Some i else None) (List.mapi (fun i e -> (i, e)) params) in
  let counterpart k = match List.nth_opt env.subterms k with Some x -> x | None -> error l "the enclosing function has no subterm parameter at position %d" k in
  let proof env prove = function Atom (_, "_") -> let env, p = prove env in (env, p.term) | p -> elab_erased env p in
  let same cur = equal (canon env lv) (canon env (Var cur)) in
  let annotation =
    let wild = Atom (l, "_") in
    let differs j pi = match List.nth_opt env.subterms j with Some x -> not (equal (canon env (List.nth arg_terms pi)) (canon env (Var x))) | None -> false in
    match (env.level, annotation) with
    | At cur, None when same cur -> (
        match List.find_opt (fun (j, pi) -> differs j pi) (List.mapi (fun j pi -> (j, pi)) subterm_params) with
        | Some (_, i) -> Some (`Subterm (i, wild))
        | None -> error l "same-level call to %s decreases no subterm argument" (show env callee.term))
    | At _, None -> Some (`Predates wild)
    | _ -> annotation
  in
  let env =
    match (env.level, annotation) with
    | Top, None -> env
    | Top, Some _ -> error l "the top level calls without proofs; drop the decrease annotation (section 24)"
    | At cur, Some (`Subterm (i, p)) when same cur -> (
        let k = match find_index (( = ) i) subterm_params with Some k -> k | None -> error l "argument %d is not a subterm parameter" i in
        List.iteri (fun j pi -> if j < k then check_equal env l (List.nth arg_terms pi) (Var (counterpart j))) subterm_params;
        let env, p = proof env (fun env -> prove_subterm env l (List.nth arg_terms i) (Var (counterpart k))) p in
        match expect_proof env l Prelude.subterm p with
        | [ _; a; _; b ] -> check_equal env l a (List.nth arg_terms i); check_equal env l b (Var (counterpart k)); env
        | _ -> assert false)
    | At cur, Some (`Predates p) when not (same cur) -> (
        let callee_level env = match canon env lv with Var m -> m | t -> error l "%s is not a variable" (show env t) in
        let env, p = proof env (fun env -> prove_predates env l (callee_level env) cur) p in
        match expect_proof env l Prelude.predates p with
        | [ _; x; l2 ] ->
            check_equal env l l2 (Var cur);
            if not (equal (canon env x) (canon env lv)) then
              error l "%s : %s does not relate the callee's level %s" (show env p) (show env (infer env l p)) (show env lv);
            env
        | _ -> assert false)
    | At cur, _ ->
        let kind, ann, other = if same cur then ("same", "subterm", "predates") else ("lower", "predates", "subterm") in
        error l "%s-level call to %s takes a (%s p) annotation, not (%s p)" kind (show env callee.term) ann other
  in
  let env, ids = open_tele env ~names:(anon rets) ~mults:(List.map (fun e -> under pos e.mult) rets) ~ids:acc rets in
  let code =
    let call = V.CApp (hcode, codes, cc) in
    if pos = Erased then V.CErased
    else if List.length expect <> List.length rets || List.for_all2 (fun m e -> m = Many || e.mult = Erased) expect rets then call
    else
      let kept = List.filter_map (fun (m, e) -> if e.mult = Many then Some (fresh (), m) else None) (List.combine expect rets) in
      V.CLet (List.map fst kept, call, V.CValues (List.filter_map (fun (t, m) -> if m = Many then Some (V.CVar t) else None) kept))
  in
  (env, List.map (res_of env) ids, code)

and elab_special tele env expect l sp args =
  let pos = pos_of expect in
  let m =
    if List.mem sp (Sp.Values :: Sp.Match :: Sp.Tail :: Sp.Delegate :: Sp.statements) then pos
    else match expect with [ m ] -> m | _ -> error l "%s produces one value" (Sp.name sp)
  in
  let proof env ctor raw =
    let env, p = elab_erased env raw in
    (env, expect_proof env l ctor p)
  in
  let erased (env, r) = (env, [ r ], V.CErased) in
  let mint env ty = erased (mint env ty) in
  let fetch what x found = match found with Some y -> erased (env, res_of env y) | None -> error l "%s has no %s in scope" (name_of env x) what in
  let compose (c1, p) (c2, q) k =
    let env, p = proof env c1 p in
    let env, q = proof env c2 q in
    let (a, b), (ctor, args) = k (p, q) in
    check_equal env l a b;
    mint env (proof_type ctor args)
  in
  match (sp, args) with
  | (Sp.Fn | Sp.TyCtor | Sp.ValCtor | Sp.Matchable | Sp.Newtype), _ ->
      if pos = Many then error l "a type in a non-erased position";
      erased (env, term_res env l (elab_type_form env l sp args))
  | Sp.Values, _ ->
      if List.length args <> List.length expect then error l "expected %d values, got %d" (List.length expect) (List.length args);
      let entry i = Option.map (fun t -> List.nth t i) tele in
      let env, ress, codes =
        List.fold_left2
          (fun (env, ress, codes) (i, m) a ->
            let tele = Option.map (fun e -> [ { e with sg = map_sg (instantiate (List.map (fun r -> r.term) ress)) e.sg } ]) (entry i) in
            let env, r, code = elab_expr1 ?tele env m a in
            (env, r :: ress, if m = Many then code :: codes else codes))
          (env, [], []) (List.mapi (fun i m -> (i, m)) expect) args
      in
      (env, List.rev ress, if pos = Erased then V.CErased else V.CValues (List.rev codes))
  | Sp.Match, _ -> elab_match tele env expect l args
  | (Sp.Tail | Sp.Delegate), [ (List _ as call) ] ->
      if pos = Erased then error l "%s in an erased position" (Sp.name sp);
      let cc = if sp = Sp.Tail then V.Tail else V.Delegate in
      let env, ress, code = elab_expr ~cc ?tele env expect call in
      (match code with
      | V.CApp (_, _, cc') | V.CLet (_, V.CApp (_, _, cc'), _) when cc' = cc -> ()
      | _ -> error l "%s marks a function call, not %s" (Sp.name sp) (Reader.show call));
      (env, ress, code)
  | Sp.MatchableOf, [ t ] ->
      let x, _, _ = find_matchable env l (tyname env l t) in
      (env, [ res_of env x ], matchable_code env m x)
  | Sp.NewtypeOf, [ c ] -> let c = ctor_var env l c in fetch "Newtype" c (newtype_of env c)
  | Sp.NumeralOf, [ e ] -> (
      let name = atom_or l e "a literal" in
      match Literal.classify name with
      | `Bad msg -> error l "%s" msg
      | `Name -> error l "numeral-of takes a literal, not %s" name
      | `Lit lit -> (
          match List.assoc_opt (Literal.key lit) env.literals with
          | Some (_, Some p) -> erased (env, res_of env p)
          | Some (_, None) -> error l "%s is a string literal, which carries no Numeral proof" name
          | None -> error l "literal %s is not in scope" name))
  | Sp.Distinct, [ a; b ] -> elab_distinct env l a b
  | Sp.LevelOf, [ f ] -> (
      let f = elab_term env f in
      match canon env (infer env l f) with
      | Fn (lv, _, _) -> erased (env, { term = lv; ty = Prelude.level_term; erasure = Erased })
      | ty -> error l "level-of: %s : %s is not a function" (show env f) (show env ty))
  | Sp.ProveSubterm, [ a; b ] -> erased (prove_subterm env l (elab_term env a) (elab_term env b))
  | Sp.ProvePredates, [ x; lv ] -> erased (prove_predates env l (var env l (atom_or l x "a variable")) (level_var env l lv))
  | Sp.PredatesTrans, [ p; q ] ->
      compose (Prelude.predates, p) (Prelude.predates, q)
        (function [ a; x; l1 ], [ _; l1'; l2 ] -> ((l1', l1), (Prelude.predates, [ a; x; l2 ])) | _ -> assert false)
  | (Sp.SubtermTrans | Sp.CoercibleTrans), [ p; q ] ->
      let c = if sp = Sp.SubtermTrans then Prelude.subterm else Prelude.coercible in
      compose (c, p) (c, q) (function [ a; x; _; y ], [ _; y'; b; z ] -> ((y', y), (c, [ a; x; b; z ])) | _ -> assert false)
  | Sp.PredatesSubterm, [ p; q ] ->
      compose (Prelude.predates, p) (Prelude.subterm, q)
        (function [ _; x; lv ], [ b; y; _; x' ] -> ((x', x), (Prelude.predates, [ b; y; lv ])) | _ -> assert false)
  | Sp.Coerce, [ a; p ] -> (
      let env, a, code = elab_expr1 env m a in
      let env, p = proof env Prelude.coercible p in
      match p with
      | [ _; a'; b_ty; b ] ->
          check_equal env l a.term a';
          let x, env = bind env None m Dyn b_ty ~rule:b in
          (env, [ res_of env x ], code)
      | _ -> assert false)
  | Sp.CoercibleRefl, [ e ] ->
      let e = elab_term env e in
      mint env (proof_type Prelude.coercible [ infer env l e; e; infer env l e; e ])
  | Sp.CoercibleSym, [ p ] -> (
      let env, p = proof env Prelude.coercible p in
      match p with
      | [ a; x; b; y ] -> mint env (proof_type Prelude.coercible [ b; y; a; x ])
      | _ -> assert false)
  | Sp.CoercibleWrap, c :: args -> (
      let c = ctor_var env l c in
      let tele, ret = ctor_type env l c in
      if newtype_of env c = None then error l "%s has no Newtype in scope: only a marked newtype's wrapping constructor has one" (name_of env c);
      if List.length (List.filter (fun e -> e.mult = Many) tele) <> 1 then error l "%s is not the wrapping constructor" (name_of env c);
      let acc = elab_term_args env l tele (Var c) args in
      let f = List.nth (List.rev acc) (Option.get (find_index (fun e -> e.mult = Many) tele)) in
      mint env (proof_type Prelude.coercible [ infer env l f; f; instantiate acc ret; App (Var c, List.rev acc) ]))
  | Sp.CoercibleCtor, c :: args ->
      let c = ctor_var env l c in
      let tele, ret = ctor_type env l c in
      if phantom env l c then error l "%s is phantom" (name_of env c);
      let check env side e ty t = check_sg env l (map_sg (instantiate side) e.sg) { term = t; ty; erasure = Erased } in
      let rec go env src tgt tele args =
        match (tele, args) with
        | [], [] -> (env, src, tgt)
        | ({ mult = Erased; _ } as e) :: tele, s :: t :: args ->
            let s = elab_term env s and t = elab_term env t in
            check env src e (infer env l s) s;
            check env tgt e (infer env l t) t;
            go env (s :: src) (t :: tgt) tele args
        | ({ mult = Many; _ } as e) :: tele, p :: args -> (
            match proof env Prelude.coercible p with
            | env, [ sty; s; tty; t ] ->
                check env src e sty s;
                check env tgt e tty t;
                go env (s :: src) (t :: tgt) tele args
            | _ -> assert false)
        | _ -> error l "coercible-ctor: wrong number of arguments for %s" (name_of env c)
      in
      let env, src, tgt = go env [] [] tele args in
      mint env (proof_type Prelude.coercible [ instantiate src ret; App (Var c, List.rev src); instantiate tgt ret; App (Var c, List.rev tgt) ])
  | Sp.CoercibleOf, [ g ] ->
      let g = named env l "a function name" g in
      let about x = (entry env x).name = None && (match type_of env x with App (Var c, [ _; Var g'; _; _ ]) -> c = Prelude.coercible && g' = g | _ -> false) in
      fetch "delegate proof" g (List.find_opt about env.scope)
  | sp, _ when List.mem sp Sp.statements -> error l "%s is a statement, not an expression" (Sp.name sp)
  | sp, _ -> error l "malformed %s form" (Sp.name sp)

and elab_match tele env expect l args =
  match args with
  | m :: scrut :: ann :: branches ->
      let pos = pos_of expect in
      let smult = under pos (mult_or env l m) in
      let env, sres, scode = elab_expr1 env smult scrut in
      let tid = match type_head env sres.ty with Some t -> t | None -> error l "cannot match on %s : %s" (show env sres.term) (show env sres.ty) in
      let mid, disc, ctors = find_matchable env l tid in
      let shapes = shapes env l ctors in
      let tagged = tagged disc shapes in
      if pos = Many && smult = Many && (entry env mid).mult = Erased then
        error l "the Matchable for %s is erased, so a non-erased match cannot take a value of it apart" (name_of env tid);
      let env, ann_tele =
        match (ann, tele) with
        | Atom (_, "_"), Some tele ->
            if List.exists (fun e -> has_meta env (sg_term e.sg)) tele then error l "the telescope _ would reuse still has a _ to infer";
            (env, tele)
        | Atom (_, "_"), None -> error l "no telescope to reuse for _"
        | List (_, ann), _ ->
            let mults i = function
              | Some _ -> error l "a match annotation carries no multiplicities"
              | None -> (match List.nth_opt expect i with Some m -> Some m | None -> error l "match annotation has more than the %d entries the position needs" (List.length expect))
            in
            let env', _, ann_tele = elab_tele env ~mults ann in
            ({ env' with scope = env.scope }, ann_tele)
        | _ -> error l "malformed match annotation"
      in
      if List.length ann_tele <> List.length expect then error l "match annotation has %d entries, position needs %d" (List.length ann_tele) (List.length expect);
      let branch raw =
        let kind, pat, body =
          match raw with
          | List (_, [ a; (Atom _ as c) ]) when is_special env a Sp.Absurd -> (`Auto, c, [])
          | List (_, a :: pat :: body) when is_special env a Sp.Absurd -> (`Proof, pat, body)
          | List (_, pat :: body) -> (`Present, pat, body)
          | _ -> error (loc raw) "malformed branch"
        in
        let bl = loc pat in
        let c, field_names =
          match pat with
          | Atom _ -> (pat, [])
          | List (_, c :: fs) -> (c, List.map (fun f -> atom_or (loc f) f "a field name") fs)
          | _ -> error bl "malformed pattern"
        in
        let c = ctor_var env bl c in
        let phantom = marker env bl tid ctors c = Erased in
        let tele, ret = ctor_type env bl c in
        if kind <> `Auto && List.length field_names <> List.length tele then error bl "%s has %d fields" (name_of env c) (List.length tele);
        let names = if kind = `Auto then anon tele else List.map name_or_anon field_names in
        let unreachable = phantom && smult = Many in
        let mults = List.map (fun e -> if phantom then Erased else under smult e.mult) tele in
        let envb, fids = open_tele { env with run_pos = false } ~names ~mults tele in
        let forced = try Some (at bl (fun () -> refine envb sres c fids ret)) with Contradiction _ -> None in
        let result =
          match (kind, forced) with
          | `Auto, None -> `Absurd
          | `Auto, Some _ -> error bl "branch %s is not refuted" (name_of env c)
          | _, None -> error bl "branch %s is refuted; write (absurd %s)" (name_of env c) (name_of env c)
          | `Present, Some envb ->
              let envb, ress, code = elab_body ~tele:ann_tele envb (if unreachable then List.map (fun _ -> Erased) expect else expect) bl body in
              check_results envb bl ann_tele ress;
              `Present code
          | `Proof, Some envb -> ignore (elab_absurd envb bl body); `Absurd
        in
        (c, non_erased envb fids, unreachable, result)
      in
      let elses, branches = List.partition (function List (_, a :: _) when is_special env a Sp.Else -> true | _ -> false) branches in
      let branches = List.map branch branches in
      List.iter
        (fun (_, c) ->
          match List.length (List.filter (fun (c', _, _, _) -> Var c' = c) branches) with
          | 0 | 1 -> ()
          | n -> error l "constructor %s has %d branches" (show env c) n)
        ctors;
      let covered =
        List.filter_map
          (fun (m, c) ->
            let c = match c with Var c -> c | _ -> assert false in
            if List.exists (fun (c', _, _, _) -> c' = c) branches then None
            else
              let tele, ret = ctor_type env l c in
              let mults = List.map (fun e -> if m = Erased then Erased else under smult e.mult) tele in
              let envb, fids = open_tele { env with run_pos = false } ~names:(anon tele) ~mults tele in
              match at l (fun () -> refine envb sres c fids ret) with
              | _ -> Some (c, m = Erased && smult = Many)
              | exception Contradiction _ -> None)
          ctors
      in
      let reachable = List.filter_map (fun (c, unreachable) -> if unreachable then None else Some c) covered in
      let else_ =
        match elses with
        | [] ->
            (match covered with [] -> () | (c, _) :: _ -> error l "constructor %s has 0 branches" (name_of env c));
            None
        | [ List (el, _ :: body) ] ->
            if covered = [] then error el "else covers no constructor";
            let envb = { env with run_pos = false } in
            let envb, ress, code = elab_body ~tele:ann_tele envb (if reachable = [] then List.map (fun _ -> Erased) expect else expect) el body in
            check_results envb el ann_tele ress;
            if reachable = [] then None else Some code
        | _ -> error l "a match has at most one else branch"
      in
      let real =
        List.filter_map (fun (c, fids, unreachable, r) -> match r with `Present code when not unreachable -> Some (c, fids, code) | _ -> None) branches
      in
      if pos = Many && ((not tagged) || smult = Erased) && List.length real + List.length (Option.to_list else_) > 1 then
        error l "a match without a runtime discriminant can have only one real branch";
      let code =
        match (real, else_) with
        | _ when pos = Erased -> V.CErased
        | [], None -> V.CAbsurd
        | [], Some body when smult = Erased || not tagged -> body
        | [ (_, _, body) ], None when smult = Erased -> body
        | _ ->
            let branch (c, fids, body) = (Option.get (discriminant shapes c), fids, body) in
            V.CMatch { scrut = scode; shape = match_shape env mid tagged; branches = List.map branch real; default = else_ }
      in
      let env, result_ids = open_tele env ~names:(anon ann_tele) ann_tele in
      (env, List.map (res_of env) result_ids, code)
  | _ -> error l "malformed match"

and elab_body ?tele env expect l items =
  match items with
  | [] -> error l "a body needs a final expression"
  | [ final ] -> elab_expr ?tele env expect final
  | stmt :: rest ->
      let env, wrap = elab_stmt env stmt in
      let env, ress, code = elab_body ?tele env expect l rest in
      (env, ress, wrap code)

and elab_absurd env l body =
  let env, ress, _ = elab_body env [ Erased ] l body in
  check_empty env l (single l ress).ty;
  env

and refine env scrut c fids ret =
  let fvars = List.rev_map (fun x -> Var x) fids in
  unify ~force:true (unify ~force:true env scrut.term (App (Var c, List.rev fvars))) scrut.ty (instantiate fvars ret)

and elab_stmt env raw : Env.t * (V.code -> V.code) =
  match raw with
  | List (l, head :: args) -> (
      match (special_of env head, args) with
      | Some Sp.Let, _ -> elab_let env l args
      | Some Sp.DefLvl, [ n ] ->
          let _, env = mint_level env (name_or_anon (atom_or l n "a name")) in
          (env, Fun.id)
      | Some Sp.DefFns, _ -> elab_def_fns env l args
      | Some Sp.DefAdts, _ -> elab_def_adts env args
      | Some Sp.ComptimeMatch, _ -> elab_comptime_match env l args
      | Some Sp.LetMatch, _ -> elab_let_match env l args
      | Some Sp.Unary, _ -> elab_unary env l args
      | _ -> error l "%s is not a statement" (Reader.show raw))
  | _ -> error (loc raw) "%s is not a statement" (Reader.show raw)

and run_code env code = Eval.eval env.values code

and elab_let env l args =
  let binders, rhs = split_returns env args in
  let binders = List.concat_map (parse_entry env) binders in
  let expect = List.map (fun b -> match b.s_mult with Some m -> m | None -> error b.s_loc "let binder needs a multiplicity") binders in
  let inner, ress, code = elab_body env expect l rhs in
  let values = if env.run_pos && pos_of expect = Many then run_code inner code else [] in
  let bind_one (env, ids) ((b, r), v) =
    Option.iter (fun s -> check_sg env b.s_loc (elab_sg env s) r) b.s_sg;
    let state = if env.run_pos then Const v else match r.term with Var y -> (entry env y).state | _ -> Dyn in
    let x, env = bind env (name_or_anon b.s_name) (Option.get b.s_mult) state r.ty ~rule:r.term in
    (env, x :: ids)
  in
  let env', ids = List.fold_left bind_one ({ inner with scope = env.scope }, []) (List.combine (List.combine binders ress) (spread expect values)) in
  let ids = non_erased env' (List.rev ids) in
  (env', if env.run_pos || ids = [] then Fun.id else fun rest -> V.CLet (ids, code, rest))

(* A match on a one-constructor type chooses nothing, so what it learns holds wherever the scrutinee does
   and its fields bind outward (section 16's reason for comptime-match, without a discriminant to verify). *)
(* Runs a literal's statements (Literal.source) in the prelude's scope, once per program. *)
and hoist env lit =
  let key = Literal.key lit in
  if List.mem_assoc key env.literals then env
  else
    let parts = match lit with Literal.Char c -> [ Literal.Numeral (Z.of_int c) ] | Literal.Str s -> Literal.chars s | Literal.Numeral _ -> [] in
    let env = List.fold_left hoist env parts in
    let frame = List.fold_left (fun env item -> fst (elab_stmt env item)) { env with scope = env.prelude } (Reader.parse (Literal.source lit)) in
    let entry =
      match (lit, frame.scope) with
      | Literal.Numeral _, proof :: value :: _ -> (value, Some proof)
      | Literal.Char c, char :: _ -> (char, snd (List.assoc (Z.to_string (Z.of_int c)) env.literals))
      | Literal.Str _, str :: _ -> (str, None)
      | _ -> assert false
    in
    { frame with scope = env.scope; literals = (key, entry) :: frame.literals }

(* [unary] and [distinct] elaborate to calls on the prelude's Numeral lemmas, in the prelude's scope so
   user shadowing cannot reach them; the level context, and so [predates _], stays the caller's. *)
and elab_unary env l args =
  let za, _ = numeral_entry env l (List.hd args) in
  let lo =
    match args with
    | [ _ ] -> Z.zero
    | [ _; b ] ->
        let zb, _ = numeral_entry env l b in
        if Z.geq zb za then error l "unary: %s does not exceed %s" (Z.to_string za) (Z.to_string zb);
        zb
    | _ -> error l "unary takes one or two literals"
  in
  let k = Z.sub za lo in
  if Z.gt k (Z.of_int 4096) then error l "unary: %s successors is beyond the limit" (Z.to_string k);
  let rec upto z acc = if Z.geq z za then List.rev acc else upto (Z.succ z) (z :: acc) in
  let env = List.fold_left (fun env z -> hoist env (Literal.Numeral z)) env (za :: upto lo []) in
  (* Fold the one-step proofs into a single Eq relating the literal to [floor] under k successors, so one
     let-match mints one rule and the literals walked over stay opaque. *)
  let floor, acc =
    if List.length args = 1 then ("(Zero)", "(numeral-zero 0 (numeral-of 0))")
    else (Z.to_string lo, Printf.sprintf "(Refl (Nat) %s)" (Z.to_string lo))
  in
  let step acc z =
    let n = Z.succ z in
    let below = Literal.succs (Z.to_int (Z.sub z lo)) floor in
    let stp =
      Printf.sprintf "(numeral-succ %s %s %s %s %s (numeral-of %s) (numeral-of %s))" (Literal.bin z)
        (Literal.bin n) (Z.to_string z) (Z.to_string n) (Literal.bin_succ z) (Z.to_string z) (Z.to_string n)
    in
    let congd = Printf.sprintf "(eq-cong-succ %s %s %s)" (Z.to_string z) below acc in
    Printf.sprintf "(eq-trans (Nat) %s (Succ %s) (Succ %s) %s %s)" (Z.to_string n) (Z.to_string z) below stp congd
  in
  let src = Printf.sprintf "(let-match erased %s (Refl _ _))" (List.fold_left step acc (upto lo [])) in
  in_prelude env (fun env -> elab_stmt env (List.hd (Reader.parse src)))

and elab_distinct env l a b =
  let za, xa = numeral_entry env l a and zb, xb = numeral_entry env l b in
  if Z.equal za zb then error l "distinct: %s is the same literal twice" (Z.to_string za);
  if not (equal (canon env (Var xa)) (canon env (Var xb))) then
    error l "distinct: %s and %s do not canonicalize equally here" (Z.to_string za) (Z.to_string zb);
  let src =
    Printf.sprintf "(match erased (numeral-inj %s %s %s (numeral-of %s) (numeral-of %s)) (((False) f)) (absurd Refl))"
      (Literal.bin za) (Literal.bin zb) (Z.to_string za) (Z.to_string za) (Z.to_string zb)
  in
  let raw = match Reader.parse src with [ r ] -> r | _ -> assert false in
  let env, (ress, code) =
    in_prelude env (fun env ->
        let env, ress, code = elab_expr env [ Erased ] raw in
        (env, (ress, code)))
  in
  (env, ress, code)

and elab_let_match env l args =
  match args with
  | [ m; scrut; List (pl, c :: fields) ] ->
      let smult = mult_or env l m in
      let env, sres, scode = elab_expr1 env smult scrut in
      let tid = match type_head env sres.ty with Some t -> t | None -> error l "cannot match on %s : %s" (show env sres.term) (show env sres.ty) in
      let mid, disc, ctors = find_matchable env l tid in
      if List.length ctors <> 1 then
        error l "%s has %d constructors, so it needs an ordinary match" (name_of env tid) (List.length ctors);
      let c = ctor_var env pl c in
      if marker env pl tid ctors c = Erased then error pl "%s is phantom" (name_of env c);
      let tele, ret = ctor_type env pl c in
      if List.length fields <> List.length tele then error pl "%s has %d fields" (name_of env c) (List.length tele);
      let names = List.map (fun f -> name_or_anon (atom_or (loc f) f "a field name")) fields in
      let mults = List.map (fun e -> under smult e.mult) tele in
      let shapes = shapes env l ctors in
      let run = env.run_pos && smult = Many in
      let states =
        if not run then None
        else
          let ct = ctor_of env pl c in
          let _, vs = V.destruct ct (List.hd (run_code env scode)) in
          Some (List.map (fun v -> Const v) (spread mults vs))
      in
      let env, fids = open_tele env ~names ~mults ?states tele in
      let env = at l (fun () -> try refine env sres c fids ret with Contradiction msg -> error l "the scrutinee contradicts the facts in force (%s)" msg) in
      ( env,
        if smult = Erased || run then Fun.id
        else fun rest ->
          V.CMatch
            { scrut = scode; shape = match_shape env mid (tagged disc shapes);
              branches = [ (Option.get (discriminant shapes c), non_erased env fids, rest) ]; default = None } )
  | _ -> error l "malformed let-match: expected (let-match <multiplicity> x (C field ...))"

and elab_comptime_match env l args =
  match args with
  | [ x; List (pl, c :: fields) ] ->
      if not env.run_pos then error l "comptime-match is a run-position statement (section 15)";
      let x = var env l (atom_or l x "a variable") in
      let value = match entry env x with { state = Const v; mult = Many; _ } -> v | _ -> error l "comptime-match needs a Const, non-erased scrutinee" in
      let c = ctor_var env pl c in
      let tele, ret = ctor_type env pl c in
      let tid = match type_head env (type_of env x) with Some t -> t | None -> error l "scrutinee is not a datatype value" in
      let _, disc, ctors = find_matchable env l tid in
      if disc = Union then error l "comptime-match needs a non-erased discriminant";
      if marker env pl tid ctors c = Erased then error pl "comptime-match: %s is phantom, so no non-erased value is headed by it" (name_of env c);
      let many_values =
        let ct = ctor_of env pl c in
        let i, vs = V.destruct ct value in
        if i <> ct.index then error l "comptime-match: expected %s, got %s" (name_of env c) (V.show value);
        vs
      in
      if List.length fields <> List.length tele then error pl "%s has %d fields" (name_of env c) (List.length tele);
      let names = List.map (fun f -> name_or_anon (atom_or (loc f) f "a field name")) fields in
      let states = List.map (fun v -> Const v) (spread (List.map (fun e -> e.mult) tele) many_values) in
      let env, fids = open_tele env ~names ~states tele in
      let env = at l (fun () -> try refine env (res_of env x) c fids ret with Contradiction msg -> error l "internal: the verified value contradicts the facts in force (%s)" msg) in
      (env, Fun.id)
  | _ -> error l "malformed comptime-match: expected (comptime-match x (C field ...))"

and elab_def_fns env l args =
  match args with
  | [] -> error l "def-fns needs a level"
  | lv :: fns ->
      let env, lvl =
        match lv with
        | Atom (_, "_") -> let x, env = mint_level env None in (env, x)
        | _ -> (env, level_var env l lv)
      in
      let header raw =
        match raw with
        | List (fl, m :: rest) -> (
            let mult = mult_or env fl m in
            let marks, rest = marks env [ Sp.Absurd; Sp.Extern ] rest in
            match rest with
            | n :: colon :: sg when is_special env colon Sp.Colon ->
                let ps, rest = split_arrow env fl sg in
                let rs, body = split_returns env rest in
                let name = atom_or fl n "a function name" in
                let impl = if List.mem Sp.Extern marks then Some (Ffi.claim Ffi.fns fl name) else None in
                (fl, name, mult, List.mem Sp.Absurd marks, impl, elab_fn_type env (Var lvl) ps rs, body)
            | _ -> error fl "malformed function header")
        | _ -> error (loc raw) "malformed function definition"
      in
      let headers = List.map header fns in
      let env, fids = List.fold_left_map (fun env (_, name, mult, _, _, ty, _) -> let x, env = bind env (Some name) mult Dyn ty in (env, x)) env headers in
      let define x (fl, name, mult, absurd, impl, ty, body) =
        let params, rets = match ty with Fn (_, ps, rs) -> (ps, rs) | _ -> assert false in
        let envb, pids = open_tele env params in
        let subterms = List.filter_map (fun (e, x) -> if e.subterm then Some x else None) (List.combine params pids) in
        let envb = { envb with level = At lvl; subterms; run_pos = false } in
        let envb, code =
          if absurd then (elab_absurd envb fl body, V.CAbsurd)
          else
            let pvars = List.rev_map (fun x -> Var x) pids in
            let tele = instantiate_tele pvars rets in
            let envb, ress, code = elab_body ~tele envb (List.map (fun e -> under mult e.mult) rets) fl body in
            check_results envb fl ~ids:pvars rets ress;
            (envb, if mult = Erased then V.CErased else code)
        in
        let code, delegated = check_marks envb fl pids code in
        ((x, { V.fname = name; params = non_erased envb pids; body = code; impl }), Option.map (fun callee -> (x, ty, callee)) delegated)
      in
      let fns, proofs = List.split (List.map2 define fids headers) in
      let env =
        List.fold_left
          (fun env -> function
            | Some (g, gty, callee) -> snd (witness env (proof_type Prelude.coercible [ gty; Var g; infer env l callee; callee ]))
            | None -> env)
          env proofs
      in
      if env.run_pos then
        let values = Eval.close env.values fns in
        trace := Fns fns :: !trace;
        (List.fold_left (fun env (x, _) -> set_state env x (Const (IntMap.find x values))) env fns, Fun.id)
      else
        let fns = List.filter (fun (x, _) -> (entry env x).mult = Many) fns in
        (env, if fns = [] then Fun.id else fun rest -> V.CLetRec (fns, rest))

(* Validates the tail/delegate marks in a body (section 9), returning the delegated callee if any. Lets that only
   rename (all a coerce leaves), return exactly what they bind, or bind constants nothing mentions (a nested
   def-adts the body never reads) are first folded away, so a marked call stands in tail position in the code
   that runs. *)
and check_marks env l pids code =
  let non_erased = non_erased env in
  let rec resolve sub x = match List.assoc_opt x sub with Some y -> resolve sub y | None -> x in
  let vars_of cs = List.map (function V.CVar x -> x | _ -> -1) cs in
  let returns ids = function V.CValues cs -> vars_of cs = ids | V.CVar x -> ids = [ x ] | _ -> false in
  let constant = function V.CValues cs -> List.for_all (function V.CConst _ -> true | _ -> false) cs | _ -> false in
  let rec mentions x c =
    (match c with V.CVar y -> y = x | V.CLetRec (fns, _) -> List.exists (fun (_, f) -> mentions x f.V.body) fns | _ -> false)
    || List.exists (mentions x) (V.subcodes c)
  in
  let rec norm sub = function
    | V.CVar x -> V.CVar (resolve sub x)
    | V.CLet (ids, rhs, rest) -> (
        match norm sub rhs with
        | V.CVar y when List.length ids = 1 -> norm ((List.hd ids, y) :: sub) rest
        | V.CValues cs when List.length cs = List.length ids && not (List.mem (-1) (vars_of cs)) ->
            norm (List.combine ids (vars_of cs) @ sub) rest
        | rhs ->
            let rest = norm sub rest in
            if returns ids rest then rhs
            else if constant rhs && not (List.exists (fun x -> mentions x rest) ids) then rest
            else V.CLet (ids, rhs, rest))
    | V.CLetRec (fns, rest) ->
        V.CLetRec (List.map (fun (x, f) -> (x, { f with V.body = norm sub f.V.body })) fns, norm sub rest)
    | c -> V.map_code (norm sub) c
  in
  let code = norm [] code in
  let rec marked acc c = List.fold_left marked (match c with V.CApp (_, _, (V.Tail | V.Delegate)) -> c :: acc | _ -> acc) (V.subcodes c)
  in
  let rec tails ~direct = function
    | V.CApp (_, _, (V.Tail | V.Delegate)) as c -> [ c ]
    | V.CLet (_, _, rest) | V.CLetRec (_, rest) -> if direct then [] else tails ~direct rest
    | V.CMatch m -> if direct then [] else List.concat_map (tails ~direct) (List.map (fun (_, _, c) -> c) m.V.branches @ Option.to_list m.V.default)
    | _ -> []
  in
  ( code,
    match marked [] code with
    | [] -> None
    | marks ->
        let delegate = List.exists (function V.CApp (_, _, V.Delegate) -> true | _ -> false) marks in
        let ok = tails ~direct:delegate code in
        List.iter (fun c -> if not (List.memq c ok) then error l "a %s-marked call is not in tail position" (if delegate then "delegate" else "tail")) marks;
        if not delegate then None
        else
          match ok with
          | [ V.CApp (V.CVar f, args, _) ] ->
              if vars_of args <> non_erased pids then error l "a delegate call must pass the function's non-erased parameters straight through";
              Some (Var f)
          | _ -> error l "delegate needs exactly one call to a named function" )

and elab_def_adts env adts =
  let header raw =
    match raw with
    | List (al, n :: colon :: rest) when is_special env colon Sp.Colon -> (
        let ps, rest = split_arrow env al rest in
        match rest with
        | ty :: d :: rest -> let ms, ctors = marks env [ Sp.NewtypeMark; Sp.Extern ] rest in (al, atom_or al n "a type constructor name", ps, ty, disc_of env al d, ms, ctors)
        | _ -> error al "malformed def-adts entry")
    | _ -> error (loc raw) "malformed def-adts entry"
  in
  let headers = List.map header adts in
  let env, tids =
    List.fold_left_map
      (fun env (al, name, ps, ty, _, _, _) ->
        let x, env = bind env (Some name) Erased (const env V.VToken) (elab_tyctor env al ps [ ty ]) in
        (env, x))
      env headers
  in
  let define (env, cids) tid (al, name, _, _, disc, ms, ctors) =
    let ctor env raw =
      match raw with
      | List (cl, m :: n :: colon :: rest) when is_special env colon Sp.Colon ->
          let mult = mult_or env cl m and name = atom_or cl n "a constructor name" in
          let env', tele, ret, ty = elab_valctor env cl rest in
          (match canon env' ret with App (Var t, _) when t = tid -> () | _ -> error cl "%s must return an application of %s" name (name_of env tid));
          if mult = Erased && List.exists (fun e -> e.mult = Many) tele then Printf.eprintf "warning (line %d): phantom constructor %s has a many field\n" cl name;
          let c, env = bind env (Some name) mult (if mult = Erased then const env V.VToken else Dyn) ty in
          (env, (mult, c))
      | _ -> error (loc raw) "malformed constructor"
    in
    let env, ctors = List.fold_left_map ctor env ctors in
    let ctors = List.map (fun (m, c) -> (m, Var c)) ctors in
    let shapes = shapes env al ctors in
    let adt = { V.tname = name; tagged = tagged disc shapes; ctors = []; ext = None } in
    if List.mem Sp.Extern ms then adt.ext <- Some (Ffi.claim Ffi.types al name adt);
    adt.ctors <- List.mapi (fun index (c, arity) -> { V.cname = name_of env c; cid = c; index; arity; adt }) (non_phantom shapes);
    let values = List.map (fun ct -> (ct.V.cid, V.VCtorFn ct)) adt.ctors in
    let env = if env.run_pos then List.fold_left (fun env (c, v) -> set_state env c (Const v)) env values else env in
    let mid, env = witness env ~mult:Many ~value:(V.VMatchable adt) (Matchable (disc, Var tid, ctors)) in
    let env =
      if not (List.mem Sp.NewtypeMark ms) then env
      else match wrapper disc shapes with Some w -> snd (witness env (Newtype (Var w))) | None -> error al "%s is not of newtype shape (section 38)" name
    in
    (env, cids @ values @ [ (mid, V.VMatchable adt) ])
  in
  let env, cids = List.fold_left2 define (env, []) tids headers in
  (env, if env.run_pos || cids = [] then Fun.id else fun rest -> V.CLet (List.map fst cids, V.CValues (List.map (fun (_, v) -> V.CConst v) cids), rest))

let rec literals = function
  | Atom (l, s) -> (match Literal.classify s with `Lit x -> [ x ] | `Bad msg -> error l "%s" msg | `Name -> [])
  | List (_, items) -> List.concat_map literals items

let run_toplevel ?(consume = fun _ _ v -> print_endline (V.show v)) ?(path = "-") env items =
  let rec go env = function
    | [] -> env
    | item :: rest -> (
        let env = List.fold_left hoist env (literals item) in
        at (loc item) (fun () ->
            if rest = [] && not (is_statement env item) then (
              let env, ress, code = elab_expr env [ Many ] item in
              let ty = (single (loc item) ress).ty and v = List.hd (run_code env code) in
              trace := Final (v, ty, path) :: !trace;
              consume env ty v;
              env)
            else (
              if not (is_statement env item) then error (loc item) "only the last top-level form may be an expression";
              go (fst (elab_stmt env item)) rest)))
  in
  go env items
