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
let find_index p l = let rec go i = function [] -> None | x :: xs -> if p x then Some i else go (i + 1) xs in go 0 l

let special_of env raw =
  match raw with
  | Atom (_, n) -> (
      match Option.map (fun x -> entry env x) (lookup env n) with
      | Some { state = Const (V.VCtor (c, [])); mult = Many; _ } -> Hashtbl.find_opt Sp.table c.cid
      | _ -> None)
  | List _ -> None

let is_special env raw s = special_of env raw = Some s
let mult_of env raw = match special_of env raw with Some Sp.Erased -> Some Erased | Some Sp.Many -> Some Many | _ -> None
let is_statement env = function List (_, h :: _) -> List.exists (is_special env h) Sp.statements | _ -> false
let var env loc n = match lookup env n with Some x -> x | None -> error loc "unbound name %s" n

let check_type env loc actual expected =
  if not (equal (canon env actual) (canon env expected)) then
    error loc "type mismatch: expected %s, got %s" (show env expected) (show env actual)

let check_equal env loc actual expected =
  if not (equal (canon env actual) (canon env expected)) then
    error loc "value mismatch: expected %s, got %s" (show env expected) (show env actual)

let check_sg env loc sg r = match sg with Ty ty -> check_type env loc r.ty ty | Is t -> check_equal env loc r.term t

let rec infer env loc t =
  match t with
  | Var x -> type_of env x
  | App (h, args) -> (
      match canon env (infer env loc h) with
      | TyCtor _ -> type_term
      | ValCtor (_, r) -> instantiate (List.rev args) r
      | ty -> error loc "%s has type %s and cannot be applied" (show env h) (show env ty))
  | Fn _ | TyCtor _ | ValCtor _ | Matchable _ -> type_term
  | Bound _ -> error loc "internal: dangling binder"

let res_of env x = { term = Var x; ty = type_of env x; erasure = (entry env x).mult }
let non_erased env ids = List.filter (fun x -> (entry env x).mult = Many) ids
let term_res env loc t = { term = t; ty = infer env loc t; erasure = Erased }

let matchables env tid =
  List.filter_map
    (fun x -> match type_of env x with Matchable (d, Var t, cs) when t = tid -> Some (x, d, cs) | _ -> None)
    env.scope

let find_matchable env loc tid =
  match matchables env tid with
  | [] -> error loc "%s has no Matchable in scope" (name_of env tid)
  | (x, d, cs) :: rest ->
      if List.exists (fun (y, _, _) -> not (equal (type_of env x) (type_of env y))) rest then
        error loc "ambiguous Matchables for %s" (name_of env tid);
      (x, d, cs)

let check_empty env loc ty =
  match canon env ty with
  | App (Var t, _) when (match matchables env t with [ (_, _, []) ] -> true | _ -> false) -> ()
  | _ -> error loc "%s is not an empty type" (show env ty)

let ctor_type env loc c =
  match canon env (type_of env c) with ValCtor (tele, ret) -> (tele, ret) | _ -> error loc "%s is not a value constructor" (name_of env c)

let tid_of env loc c = match canon env (snd (ctor_type env loc c)) with App (Var t, _) -> t | _ -> assert false
let marker ctors c = Option.map fst (List.find_opt (fun (_, c') -> c' = Var c) ctors)
let phantom env loc c = let _, _, ctors = find_matchable env loc (tid_of env loc c) in marker ctors c = Some Erased

(* Each constructor of a Matchable with its phantom marker and its number of many fields; the representation follows (section 38). *)
let shapes env loc ctors =
  List.map (fun (m, c) -> match c with Var c -> (m, c, List.length (List.filter (fun e -> e.mult = Many) (fst (ctor_type env loc c)))) | _ -> assert false) ctors

let tagged disc shapes = disc = Enum && List.length (List.filter (fun (m, _, _) -> m = Many) shapes) > 1

let wrapper disc shapes =
  match List.filter (fun (m, _, n) -> m = Many && n = 1) shapes with
  | [ (_, w, _) ] when (not (tagged disc shapes)) && List.for_all (fun (m, c, n) -> m = Erased || c = w || n = 0) shapes -> Some w
  | _ -> None

let const env v = if env.run_pos then Const v else Dyn
let proof_type ctor args = App (Var ctor, args)

let expect_proof env loc ctor arity p =
  match canon env (infer env loc p) with
  | App (Var c, args) when c = ctor && List.length args = arity -> args
  | ty -> error loc "expected a %s proof, got %s : %s" (name_of env ctor) (show env p) (show env ty)

let rec is_strict_subterm a b =
  match b with App (_, args) -> List.exists (fun x -> equal a x || is_strict_subterm a x) args | _ -> false

type src_entry = { s_loc : loc; s_subterm : bool; s_mult : mult option; s_ty : raw option; s_is : raw option; s_name : string }

let parse_entry env raw =
  match raw with
  | List (l, items) -> (
      let s_subterm, items = match items with t :: rest when is_special env t Sp.Subterm -> (true, rest) | _ -> (false, items) in
      let s_mult, items = match items with t :: rest when mult_of env t <> None -> (mult_of env t, rest) | _ -> (None, items) in
      let mk s_ty s_is s_name = { s_loc = l; s_subterm; s_mult; s_ty; s_is; s_name } in
      match items with
      | [ e; i; Atom (_, n) ] when is_special env i Sp.Is -> [ mk None (Some e) n ]
      | [ Atom (_, n) ] -> [ mk None None n ]
      | ty :: names when names <> [] && List.for_all (fun n -> atom n <> None) names ->
          List.map (fun n -> mk (Some ty) None (Option.get (atom n))) names
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

(* [ids]: terms of the binders already in force, innermost first. Binds one fresh entry per item and returns their ids in order. *)
let open_tele env ?(named = true) ?names ?mults ?(state = Dyn) ?(ids = []) tele =
  let nth l i = Option.map (fun l -> List.nth l i) l in
  let _, env, _, fresh =
    List.fold_left
      (fun (i, env, ids, fresh) e ->
        let sg = map_sg (instantiate ids) e.sg in
        let ty, rule = match sg with Ty t -> (t, None) | Is t -> (infer env 0 t, Some t) in
        let name = match nth names i with Some n -> n | None -> if named then e.name else None in
        let mult = match nth mults i with Some m -> m | None -> e.mult in
        let x, env = bind env name mult state ty ~rule in
        (i + 1, env, Var x :: ids, x :: fresh))
      (0, env, ids, []) tele
  in
  (env, List.rev fresh)

let rec elab_term env raw =
  match raw with
  | Atom (l, n) -> Var (var env l n)
  | List (l, []) -> error l "empty form"
  | List (l, head :: args) -> (
      match special_of env head with
      | Some Sp.Fn -> elab_fn_type env l args
      | Some Sp.TyCtor ->
          let ps, ret = split_arrow env l args in
          let env', _, tele = elab_tele env ~mults:(no_mults l) ps in
          (match ret with [ r ] -> check_equal env' l (elab_term env' r) type_term | _ -> error l "TyCtor returns Type");
          TyCtor tele
      | Some Sp.ValCtor ->
          let ps, ret = split_arrow env l args in
          let env', ids, tele = elab_tele env ps in
          let ret = match ret with [ r ] -> elab_type env' r | _ -> error l "ValCtor returns one type" in
          ValCtor (tele, abstract (List.rev ids) ret)
      | Some Sp.Matchable -> (
          match args with
          | d :: t :: cs ->
              let ctor = function
                | List (l, [ m; c ]) -> (Option.get (mult_of env m), Var (var env l (atom_or l c "a constructor name")))
                | r -> error (loc r) "expected (multiplicity Constructor)"
              in
              Matchable (disc_of env l d, Var (var env l (atom_or l t "a type constructor name")), List.map ctor cs)
          | _ -> error l "malformed Matchable")
      | Some sp -> error l "%s cannot appear in a type" (Sp.name sp)
      | None -> (
          let h = Var (var env l (atom_or l head "a constructor")) in
          match canon env (infer env l h) with
          | TyCtor tele | ValCtor (tele, _) -> App (h, List.rev (elab_term_args env l tele args))
          | ty -> error l "%s has type %s and cannot be applied in a type" (show env h) (show env ty)))

and disc_of env l d = match special_of env d with Some Sp.Enum -> Enum | Some Sp.Union -> Union | _ -> error l "expected enum or union"

and elab_type env raw =
  let t = elab_term env raw in
  check_type env (loc raw) (infer env (loc raw) t) type_term;
  t

and elab_fn_type env l args =
  match args with
  | lv :: rest ->
      let lv = elab_term env lv in
      check_type env l (infer env l lv) Prelude.level_term;
      let ps, rs = split_arrow env l rest in
      let env, ids, params = elab_tele env ~subterm:true ps in
      let _, _, rets = elab_tele env ~ids:(List.rev ids) rs in
      Fn (lv, params, rets)
  | [] -> error l "Fn needs a level"

(* Elaborates source entries into a closed telescope, binding each name for the entries after it.
   [ids]: binders already in force, innermost first; [mults] maps an entry's index and declared multiplicity to its actual one. *)
and elab_tele env ?(subterm = false) ?(ids = []) ?(mults = fun _ m -> m) entries =
  let entries = List.concat_map (parse_entry env) entries in
  let _, env, ids, tele =
    List.fold_left
      (fun (i, env, ids, tele) e ->
        if e.s_subterm && not subterm then error e.s_loc "subterm is not allowed here";
        let mult = match mults i e.s_mult with Some m -> m | None -> error e.s_loc "entry %s needs a multiplicity" e.s_name in
        let sg, ty =
          match (e.s_ty, e.s_is) with
          | Some t, _ -> let t = elab_type env t in (Ty t, t)
          | None, Some t -> let t = elab_term env t in (Is t, infer env e.s_loc t)
          | None, None -> error e.s_loc "entry %s needs a type or an is clause" e.s_name
        in
        let name = name_or_anon e.s_name in
        let x, env = bind env name mult Dyn ty ~rule:(match sg with Is t -> Some t | Ty _ -> None) in
        (i + 1, env, x :: ids, { name; subterm = e.s_subterm; mult; sg = map_sg (abstract ids) sg } :: tele))
      (0, env, ids, []) entries
  in
  (env, List.rev ids, List.rev tele)

(* Checks [args] against [tele] with [elab env mult arg]; returns the argument terms innermost first, and their code. *)
and check_args env loc tele args elab =
  if List.length tele <> List.length args then error loc "expected %d arguments, got %d" (List.length tele) (List.length args);
  let env, acc, codes =
    List.fold_left2
      (fun (env, acc, codes) e arg ->
        let env, r, code = elab env e.mult arg in
        check_sg env (Reader.loc arg) (map_sg (instantiate acc) e.sg) r;
        (env, r.term :: acc, if e.mult = Many then code :: codes else codes))
      (env, [], []) tele args
  in
  (env, acc, List.rev codes)

and elab_term_args env loc tele args =
  let _, acc, _ = check_args env loc tele args (fun env _ a -> (env, term_res env (Reader.loc a) (elab_term env a), V.CErased)) in
  acc

(* [ids] as in [open_tele]. *)
let check_results env loc ?(ids = []) tele ress =
  if List.length tele <> List.length ress then error loc "expected %d values, got %d" (List.length tele) (List.length ress);
  ignore (List.fold_left2 (fun acc e r -> check_sg env loc (map_sg (instantiate acc) e.sg) r; r.term :: acc) ids tele ress)

let born env ty =
  let x, env = bind env None Erased Dyn ty in
  (env, res_of env x)

let prove_subterm env l a b =
  if not (is_strict_subterm (canon env a) (canon env b)) then error l "%s is not a strict subterm of %s" (show env a) (show env b);
  born env (proof_type Prelude.subterm [ infer env l a; a; infer env l b; b ])

let prove_predates env l x lvl =
  if not (entry env lvl).level_born then error l "%s is not a level born by def-lvl" (name_of env lvl);
  let x = match canon env (Var x) with Var y when x >= lvl -> y | _ -> x in
  if x >= lvl then error l "%s was not in scope when level %s was born" (name_of env x) (name_of env lvl);
  born env (proof_type Prelude.predates [ type_of env x; Var x; Var lvl ])

let rec elab_expr ?(cc = V.Plain) ?tele env expect raw : Env.t * res list * V.code =
  let l = loc raw in
  let env, ress, code = elab_form cc tele env expect raw in
  if List.length ress <> List.length expect then error l "expected %d values, got %d" (List.length expect) (List.length ress);
  List.iter2 (fun m r -> if m = Many && r.erasure = Erased then error l "erased value %s : %s used in a non-erased position" (show env r.term) (show env r.ty)) expect ress;
  (env, ress, code)

and elab_expr1 ?cc env mult raw =
  let env, ress, code = elab_expr ?cc env [ mult ] raw in
  (env, List.hd ress, code)

and elab_erased env raw =
  let env, r, _ = elab_expr1 env Erased raw in
  (env, r.term)

and elab_form cc tele env expect raw =
  let pos = pos_of expect in
  let arg env m a = elab_expr1 env (if pos = Erased then Erased else m) a in
  match raw with
  | Atom (l, n) ->
      let x = var env l n in
      (env, [ res_of env x ], if pos = Many then V.CVar x else V.CErased)
  | List (l, []) -> error l "empty form"
  | List (l, head :: args) -> (
      match special_of env head with
      | Some sp -> elab_special tele env expect l sp args
      | None -> (
          let env, h, hcode =
            match head with
            | Atom (_, n) -> let x = var env l n in (env, res_of env x, V.CVar x)
            | List _ -> elab_expr1 env pos head
          in
          match canon env h.ty with
          | TyCtor tele ->
              if pos = Many then error l "type constructor application in a non-erased position";
              (env, [ { term = App (h.term, List.rev (elab_term_args env l tele args)); ty = type_term; erasure = Erased } ], V.CErased)
          | ValCtor (tele, ret) ->
              if pos = Many && h.erasure = Erased then error l "erased constructor %s in a non-erased position" (show env h.term);
              let env, acc, codes = check_args env l tele args arg in
              let code = if pos = Erased then V.CErased else V.CApp (hcode, codes, V.Plain) in
              (env, [ { term = App (h.term, List.rev acc); ty = instantiate acc ret; erasure = pos } ], code)
          | Fn (lv, params, rets) -> elab_call cc env expect l h hcode lv params rets args
          | ty -> error l "%s : %s is not applicable" (show env h.term) (show env ty)))

and elab_call cc env expect l callee hcode lv params rets args =
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
  let env, acc, codes = check_args env l params args (fun env m a -> elab_expr1 env (if pos = Erased then Erased else m) a) in
  let arg_terms = List.rev acc in
  let subterm_params = List.filter_map (fun (i, e) -> if e.subterm then Some i else None) (List.mapi (fun i e -> (i, e)) params) in
  let subterm_index i = match find_index (( = ) i) subterm_params with Some k -> k | None -> error l "argument %d is not a subterm parameter" i in
  let counterpart k = match List.nth_opt env.subterms k with Some x -> x | None -> error l "the enclosing function has no subterm parameter at position %d" k in
  let env, annotation =
    match (annotation, env.level) with
    | Some (`Predates (Atom (_, "_"))), At cur ->
        let env, p = prove_predates env l (match canon env lv with Var m -> m | t -> error l "%s is not a variable" (show env t)) cur in
        (env, Some (`Predates p.term))
    | Some (`Subterm (i, Atom (_, "_"))), At _ ->
        let env, p = prove_subterm env l (List.nth arg_terms i) (Var (counterpart (subterm_index i))) in
        (env, Some (`Subterm (i, p.term)))
    | Some _, Top -> error l "the top level calls without proofs; drop the decrease annotation (section 24)"
    | None, _ -> (env, None)
    | Some (`Predates p), _ -> let env, p = elab_erased env p in (env, Some (`Predates p))
    | Some (`Subterm (i, p)), _ -> let env, p = elab_erased env p in (env, Some (`Subterm (i, p)))
  in
  (match env.level with
   | Top -> ()
   | At cur when equal (canon env lv) (Var cur) -> (
       match annotation with
       | Some (`Subterm (i, p)) ->
           let k = subterm_index i in
           List.iteri (fun j pi -> if j < k then check_equal env l (List.nth arg_terms pi) (Var (counterpart j))) subterm_params;
           (match expect_proof env l Prelude.subterm 4 p with
            | [ _; a; _; b ] ->
                check_equal env l a (List.nth arg_terms i);
                check_equal env l b (Var (counterpart k))
            | _ -> assert false)
       | _ -> error l "same-level call to %s needs a (subterm p) annotation" (show env callee.term))
   | At cur -> (
       match annotation with
       | Some (`Predates p) -> (
           match expect_proof env l Prelude.predates 3 p with
           | [ _; x; l2 ] ->
               check_equal env l l2 (Var cur);
               if not (equal (canon env x) (canon env lv)) then
                 error l "%s : %s does not relate the callee's level %s" (show env p) (show env (infer env l p)) (show env lv)
           | _ -> assert false)
       | _ -> error l "lower-level call to %s needs a (predates p) annotation" (show env callee.term)));
  let env, ids = open_tele env ~named:false ~mults:(List.map (fun e -> if pos = Erased then Erased else e.mult) rets) ~ids:acc rets in
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
  let one () = match expect with [ m ] -> m | _ -> error l "%s produces one value" (Sp.name sp) in
  let proof env ctor arity raw =
    let env, p = elab_erased env raw in
    (env, expect_proof env l ctor arity p)
  in
  let born env ty = let env, r = born env ty in (env, [ r ], V.CErased) in
  match (sp, args) with
  | (Sp.Fn | Sp.TyCtor | Sp.ValCtor | Sp.Matchable), _ ->
      ignore (one ());
      if pos = Many then error l "a type in a non-erased position";
      (env, [ { term = elab_term env (List (l, Atom (l, Sp.name sp) :: args)); ty = type_term; erasure = Erased } ], V.CErased)
  | Sp.Values, _ ->
      if List.length args <> List.length expect then error l "expected %d values, got %d" (List.length expect) (List.length args);
      let env, ress, codes =
        List.fold_left2
          (fun (env, ress, codes) m a -> let env, r, code = elab_expr1 env m a in (env, r :: ress, if m = Many then code :: codes else codes))
          (env, [], []) expect args
      in
      (env, List.rev ress, if pos = Erased then V.CErased else V.CValues (List.rev codes))
  | Sp.Match, _ -> elab_match tele env expect l args
  | (Sp.Tail | Sp.Delegate), [ (List _ as call) ] ->
      if pos = Erased then error l "%s in an erased position" (Sp.name sp);
      elab_expr ~cc:(if sp = Sp.Tail then V.Tail else V.Delegate) env expect call
  | Sp.MatchableOf, [ t ] ->
      ignore (one ());
      let x, _, _ = find_matchable env l (var env l (atom_or l t "a type constructor name")) in
      (env, [ res_of env x ], V.CErased)
  | Sp.LevelOf, [ f ] -> (
      ignore (one ());
      let f = elab_term env f in
      match canon env (infer env l f) with
      | Fn (lv, _, _) -> (env, [ { term = lv; ty = Prelude.level_term; erasure = Erased } ], V.CErased)
      | ty -> error l "level-of: %s : %s is not a function" (show env f) (show env ty))
  | Sp.ProveSubterm, [ a; b ] ->
      ignore (one ());
      let env, r = prove_subterm env l (elab_term env a) (elab_term env b) in
      (env, [ r ], V.CErased)
  | Sp.ProvePredates, [ x; lv ] -> (
      ignore (one ());
      match canon env (elab_term env lv) with
      | Var lvl ->
          let env, r = prove_predates env l (var env l (atom_or l x "a variable")) lvl in
          (env, [ r ], V.CErased)
      | t -> error l "%s is not a level born by def-lvl" (show env t))
  | Sp.PredatesTrans, [ p; q ] -> (
      ignore (one ());
      let env, p = proof env Prelude.predates 3 p in
      let env, q = proof env Prelude.predates 3 q in
      match (p, q) with
      | [ a; x; l1 ], [ _; l1'; l2 ] ->
          check_equal env l l1' l1;
          born env (proof_type Prelude.predates [ a; x; l2 ])
      | _ -> assert false)
  | Sp.SubtermTrans, [ p; q ] -> (
      ignore (one ());
      let env, p = proof env Prelude.subterm 4 p in
      let env, q = proof env Prelude.subterm 4 q in
      match (p, q) with
      | [ a; x; _; y ], [ _; y'; c; z ] ->
          check_equal env l y' y;
          born env (proof_type Prelude.subterm [ a; x; c; z ])
      | _ -> assert false)
  | Sp.PredatesSubterm, [ p; q ] -> (
      ignore (one ());
      let env, p = proof env Prelude.predates 3 p in
      let env, q = proof env Prelude.subterm 4 q in
      match (p, q) with
      | [ _; x; lv ], [ b; y; _; x' ] ->
          check_equal env l x' x;
          born env (proof_type Prelude.predates [ b; y; lv ])
      | _ -> assert false)
  | Sp.Coerce, [ a; p ] -> (
      let m = one () in
      let env, a, code = elab_expr1 env m a in
      let env, p = proof env Prelude.coercible 4 p in
      match p with
      | [ _; a'; b_ty; b ] ->
          check_equal env l a.term a';
          let x, env = bind env None m Dyn b_ty ~rule:(Some b) in
          (env, [ res_of env x ], code)
      | _ -> assert false)
  | Sp.CoercibleRefl, [ e ] ->
      ignore (one ());
      let e = elab_term env e in
      born env (proof_type Prelude.coercible [ infer env l e; e; infer env l e; e ])
  | Sp.CoercibleSym, [ p ] -> (
      ignore (one ());
      let env, p = proof env Prelude.coercible 4 p in
      match p with
      | [ a; x; b; y ] -> born env (proof_type Prelude.coercible [ b; y; a; x ])
      | _ -> assert false)
  | Sp.CoercibleTrans, [ p; q ] -> (
      ignore (one ());
      let env, p = proof env Prelude.coercible 4 p in
      let env, q = proof env Prelude.coercible 4 q in
      match (p, q) with
      | [ a; x; _; y ], [ _; y'; c; z ] ->
          check_equal env l y' y;
          born env (proof_type Prelude.coercible [ a; x; c; z ])
      | _ -> assert false)
  | Sp.CoercibleWrap, c :: args -> (
      ignore (one ());
      let c = var env l (atom_or l c "a constructor") in
      let tele, ret = ctor_type env l c in
      let _, disc, ctors = find_matchable env l (tid_of env l c) in
      if wrapper disc (shapes env l ctors) <> Some c then error l "%s is not the wrapping constructor of a transparent type" (name_of env c);
      let acc = elab_term_args env l tele args in
      let f = List.nth (List.rev acc) (Option.get (find_index (fun e -> e.mult = Many) tele)) in
      born env (proof_type Prelude.coercible [ infer env l f; f; instantiate acc ret; App (Var c, List.rev acc) ]))
  | Sp.CoercibleCtor, c :: args ->
      ignore (one ());
      let c = var env l (atom_or l c "a constructor") in
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
            match proof env Prelude.coercible 4 p with
            | env, [ sty; s; tty; t ] ->
                check env src e sty s;
                check env tgt e tty t;
                go env (s :: src) (t :: tgt) tele args
            | _ -> assert false)
        | _ -> error l "coercible-ctor: wrong number of arguments for %s" (name_of env c)
      in
      let env, src, tgt = go env [] [] tele args in
      born env (proof_type Prelude.coercible [ instantiate src ret; App (Var c, List.rev src); instantiate tgt ret; App (Var c, List.rev tgt) ])
  | Sp.CoercibleOf, [ g ] -> (
      ignore (one ());
      let g = var env l (atom_or l g "a function name") in
      match List.find_opt (fun x -> (entry env x).name = None && (match type_of env x with App (Var c, [ _; Var g'; _; _ ]) -> c = Prelude.coercible && g' = g | _ -> false)) env.scope with
      | Some x -> (env, [ res_of env x ], V.CErased)
      | None -> error l "%s has no delegate proof in scope" (name_of env g))
  | sp, _ when List.mem sp Sp.statements -> error l "%s is a statement, not an expression" (Sp.name sp)
  | sp, _ -> error l "malformed %s form" (Sp.name sp)

and elab_match tele env expect l args =
  match args with
  | m :: scrut :: ann :: branches ->
      let pos = pos_of expect in
      let smult = match mult_of env m with Some m -> m | None -> error l "match needs the scrutinee's multiplicity" in
      let smult = if pos = Erased then Erased else smult in
      let env, sres, scode = elab_expr1 env smult scrut in
      let tid = match canon env sres.ty with App (Var t, _) -> t | ty -> error l "cannot match on %s : %s" (show env sres.term) (show env ty) in
      let _, disc, ctors = find_matchable env l tid in
      let tagged = tagged disc (shapes env l ctors) in
      let env, ann_tele =
        match (ann, tele) with
        | Atom (_, "_"), Some tele -> (env, tele)
        | Atom (_, "_"), None -> error l "no telescope to inherit for _"
        | List (_, ann), _ ->
            let env', _, ann_tele = elab_tele env ~mults:(fun i -> function None -> List.nth_opt expect i | Some _ -> error l "a match annotation carries no multiplicities") ann in
            ({ env' with scope = env.scope }, ann_tele)
        | _ -> error l "malformed match annotation"
      in
      if List.length ann_tele <> List.length expect then error l "match annotation has %d entries, position needs %d" (List.length ann_tele) (List.length expect);
      let env, result_ids = open_tele env ~named:false ann_tele in
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
          | Atom (_, c) -> (c, [])
          | List (_, c :: fs) -> (atom_or bl c "a constructor", List.map (fun f -> atom_or (loc f) f "a field name") fs)
          | _ -> error bl "malformed pattern"
        in
        let c = var env bl c in
        let phantom =
          match marker ctors c with Some m -> m = Erased | None -> error bl "%s is not a constructor of %s" (name_of env c) (name_of env tid)
        in
        let tele, ret = ctor_type env bl c in
        if kind <> `Auto && List.length field_names <> List.length tele then error bl "%s has %d fields" (name_of env c) (List.length tele);
        let names = if kind = `Auto then List.map (fun _ -> None) tele else List.map name_or_anon field_names in
        let dead = phantom && smult = Many in
        let mults = List.map (fun e -> if phantom || smult = Erased then Erased else e.mult) tele in
        let envb, fids = open_tele { env with run_pos = false } ~names ~mults tele in
        let fvars = List.rev_map (fun x -> Var x) fids in
        let forced =
          try Some (unify (unify envb sres.term (App (Var c, List.rev fvars))) sres.ty (instantiate fvars ret)) with
          | Contradiction _ -> None
          | Error (0, msg) -> error bl "%s" msg
        in
        let result =
          match (kind, forced) with
          | `Auto, None -> `Absurd
          | `Auto, Some _ -> error bl "branch %s is not refuted" (name_of env c)
          | _, None -> error bl "branch %s is refuted; write (absurd %s)" (name_of env c) (name_of env c)
          | `Present, Some envb ->
              let envb, ress, code = elab_body ~tele:ann_tele envb (if dead then List.map (fun _ -> Erased) expect else expect) bl body in
              check_results envb bl ann_tele ress;
              `Present code
          | `Proof, Some envb ->
              let envb, ress, _ = elab_body envb [ Erased ] bl body in
              check_empty envb bl (single bl ress).ty;
              `Absurd
        in
        (c, non_erased envb fids, dead, result)
      in
      let branches = List.map branch branches in
      List.iter
        (fun (_, c) ->
          let c = match c with Var c -> c | _ -> assert false in
          match List.length (List.filter (fun (c', _, _, _) -> c' = c) branches) with
          | 1 -> ()
          | n -> error l "constructor %s has %d branches" (name_of env c) n)
        ctors;
      let real =
        List.filter_map
          (fun (c, fids, dead, r) -> match r with `Present code when not dead -> Some (V.CVar c, fids, code) | _ -> None)
          branches
      in
      if pos = Many && ((not tagged) || smult = Erased) && List.length real > 1 then
        error l "a match without a runtime discriminant can have only one real branch";
      let code =
        match real with
        | _ when pos = Erased -> V.CErased
        | [] -> V.CAbsurd
        | [ (_, _, body) ] when smult = Erased -> body
        | _ -> V.CMatch (scode, tagged, real)
      in
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

and elab_stmt env raw : Env.t * (V.code -> V.code) =
  match raw with
  | List (l, head :: args) -> (
      match (special_of env head, args) with
      | Some Sp.Let, _ -> elab_let env l args
      | Some Sp.DefLvl, [ n ] ->
          let _, env = bind env ~level_born:true (name_or_anon (atom_or l n "a name")) Erased (const env V.VToken) Prelude.level_term in
          (env, Fun.id)
      | Some Sp.DefFns, _ -> elab_def_fns env l args
      | Some Sp.DefAdts, _ -> elab_def_adts env args
      | Some Sp.ComptimeMatch, _ -> elab_comptime_match env l args
      | _ -> error l "%s is not a statement" (Reader.show raw))
  | _ -> error (loc raw) "%s is not a statement" (Reader.show raw)

and run_code env code = Eval.eval env.values code

and elab_let env l args =
  let binders, rhs = split_returns env args in
  let binders = List.concat_map (parse_entry env) binders in
  let expect = List.map (fun b -> match b.s_mult with Some m -> m | None -> error b.s_loc "let binder needs a multiplicity") binders in
  let inner, ress, code = elab_body env expect l rhs in
  let values = ref (if env.run_pos && pos_of expect = Many then run_code env code else []) in
  let next_value () = match !values with v :: rest -> values := rest; v | [] -> V.VToken in
  let bind_one (env, ids) (b, r) =
    Option.iter (fun t -> check_type env b.s_loc r.ty (elab_type env t)) b.s_ty;
    Option.iter (fun t -> check_equal env b.s_loc r.term (elab_term env t)) b.s_is;
    let state =
      if env.run_pos then Const (if b.s_mult = Some Many then next_value () else V.VToken)
      else match r.term with Var y -> (entry env y).state | _ -> Dyn
    in
    let x, env = bind env (name_or_anon b.s_name) (Option.get b.s_mult) state r.ty ~rule:(Some r.term) in
    (env, x :: ids)
  in
  let env', ids = List.fold_left bind_one ({ inner with scope = env.scope }, []) (List.combine binders ress) in
  let ids = non_erased env' (List.rev ids) in
  (env', if env.run_pos || ids = [] then Fun.id else fun rest -> V.CLet (ids, code, rest))

and elab_comptime_match env l args =
  match args with
  | [ x; List (pl, c :: fields) ] ->
      if not env.run_pos then error l "comptime-match is a run-position statement (section 15)";
      let x = var env l (atom_or l x "a variable") in
      let value = match entry env x with { state = Const v; mult = Many; _ } -> v | _ -> error l "comptime-match needs a Const, non-erased scrutinee" in
      let c = var env pl (atom_or pl c "a constructor") in
      let tele, ret = ctor_type env pl c in
      let tid = match canon env (type_of env x) with App (Var t, _) -> t | _ -> error l "scrutinee is not a datatype value" in
      let _, disc, ctors = find_matchable env l tid in
      if disc = Union then error l "comptime-match needs a non-erased discriminant";
      (match marker ctors c with
       | Some Erased -> error pl "comptime-match: %s is phantom, so no non-erased value is headed by it" (name_of env c)
       | Some Many -> ()
       | None -> error pl "%s is not a constructor of %s" (name_of env c) (name_of env tid));
      let many_values =
        if not (tagged disc (shapes env l ctors)) then V.untuple (List.length (List.filter (fun e -> e.mult = Many) tele)) value
        else match value with
          | V.VCtor (c', vs) when c'.cid = c -> vs
          | _ -> error l "comptime-match: expected %s, got %s" (name_of env c) (V.show value)
      in
      if List.length fields <> List.length tele then error pl "%s has %d fields" (name_of env c) (List.length tele);
      let names = List.map (fun f -> name_or_anon (atom_or (loc f) f "a field name")) fields in
      let env, fids = open_tele env ~names tele in
      let env = List.fold_left2 (fun env x v -> set_state env x (Const v)) env (non_erased env fids) many_values in
      let env = List.fold_left (fun env x -> if (entry env x).mult = Erased then set_state env x (Const V.VToken) else env) env fids in
      let fvars = List.rev_map (fun x -> Var x) fids in
      (try (unify (unify env (Var x) (App (Var c, List.rev fvars))) (type_of env x) (instantiate fvars ret), Fun.id) with
       | Contradiction msg -> error l "internal: the verified value contradicts the facts in force (%s)" msg
       | Error (0, msg) -> error l "%s" msg)
  | _ -> error l "malformed comptime-match: expected (comptime-match x (C field ...))"

and elab_def_fns env l args =
  match args with
  | [] -> error l "def-fns needs a level"
  | lv :: fns ->
      let env, lvl =
        match lv with
        | Atom (_, "_") -> let x, env = bind env ~level_born:true None Erased (Const V.VToken) Prelude.level_term in (env, x)
        | _ -> (env, match canon env (elab_term env lv) with Var x when equal (type_of env x) Prelude.level_term -> x | t -> error l "%s is not a level" (show env t))
      in
      let header raw =
        match raw with
        | List (fl, m :: rest) -> (
            let mult = match mult_of env m with Some m -> m | None -> error fl "function needs a multiplicity" in
            let absurd, rest = match rest with a :: rest when is_special env a Sp.Absurd -> (true, rest) | _ -> (false, rest) in
            match rest with
            | n :: colon :: sg when is_special env colon Sp.Colon ->
                let ps, rest = split_arrow env fl sg in
                let rs, body = split_returns env rest in
                let _, _, params = elab_tele env ~subterm:true ps in
                let env_p, pids = open_tele env params in
                let _, _, rets = elab_tele env_p ~ids:(List.rev pids) rs in
                (fl, atom_or fl n "a function name", mult, absurd, Fn (Var lvl, params, rets), body)
            | _ -> error fl "malformed function header")
        | _ -> error (loc raw) "malformed function definition"
      in
      let headers = List.map header fns in
      let env, fids = List.fold_left_map (fun env (_, name, mult, _, ty, _) -> let x, env = bind env (Some name) mult Dyn ty in (env, x)) env headers in
      let define x (fl, name, mult, absurd, ty, body) =
        let params, rets = match ty with Fn (_, ps, rs) -> (ps, rs) | _ -> assert false in
        let envb, pids = open_tele env params in
        let subterms = List.filter_map (fun (e, x) -> if e.subterm then Some x else None) (List.combine params pids) in
        let envb = { envb with level = At lvl; subterms; run_pos = false } in
        let envb, code =
          if absurd then (
            let envb, ress, _ = elab_body envb [ Erased ] fl body in
            check_empty envb fl (single fl ress).ty;
            (envb, V.CAbsurd))
          else
            let pvars = List.rev_map (fun x -> Var x) pids in
            let tele = List.map (fun e -> { e with sg = map_sg (instantiate pvars) e.sg }) rets in
            let envb, ress, code = elab_body ~tele envb (List.map (fun e -> if mult = Erased then Erased else e.mult) rets) fl body in
            check_results envb fl ~ids:pvars rets ress;
            (envb, if mult = Erased then V.CErased else code)
        in
        ((x, (name, non_erased envb pids, code)), Option.map (fun callee -> (x, ty, callee)) (check_marks envb fl pids code))
      in
      let fns, proofs = List.split (List.map2 define fids headers) in
      let env =
        List.fold_left
          (fun env -> function
            | Some (g, gty, callee) -> snd (bind env None Erased (const env V.VToken) (proof_type Prelude.coercible [ gty; Var g; infer env l callee; callee ]))
            | None -> env)
          env proofs
      in
      if env.run_pos then
        let values = Eval.close env.values fns in
        (List.fold_left (fun env (x, _) -> set_state env x (Const (IntMap.find x values))) env fns, Fun.id)
      else (env, fun rest -> V.CLetRec (fns, rest))

(* Validates every tail/delegate-marked call in a compiled body (section 9) and returns the delegated callee, if any.
   Read after erasure and after resolving lets that only rename, which is all a coerce leaves behind. *)
and check_marks env l pids code =
  let non_erased = non_erased env in
  let rec resolve sub x = match List.assoc_opt x sub with Some y -> resolve sub y | None -> x in
  let vars_of cs = List.map (function V.CVar x -> x | _ -> -1) cs in
  let rec norm sub = function
    | V.CVar x -> V.CVar (resolve sub x)
    | V.CLet (ids, rhs, rest) -> (
        match norm sub rhs with
        | V.CVar y when List.length ids = 1 -> norm ((List.hd ids, y) :: sub) rest
        | V.CValues cs when List.length cs = List.length ids && not (List.mem (-1) (vars_of cs)) ->
            norm (List.combine ids (vars_of cs) @ sub) rest
        | rhs -> V.CLet (ids, rhs, norm sub rest))
    | V.CValues cs -> V.CValues (List.map (norm sub) cs)
    | V.CApp (f, args, cc) -> V.CApp (norm sub f, List.map (norm sub) args, cc)
    | V.CLetRec (fns, rest) -> V.CLetRec (List.map (fun (x, (n, ps, c)) -> (x, (n, ps, norm sub c))) fns, norm sub rest)
    | V.CMatch (s, t, brs) -> V.CMatch (norm sub s, t, List.map (fun (c, ids, b) -> (norm sub c, ids, norm sub b)) brs)
    | (V.CConst _ | V.CErased | V.CAbsurd) as c -> c
  in
  let code = norm [] code in
  let rec marked acc = function
    | V.CApp (f, args, cc) as c -> List.fold_left marked (marked (if cc = V.Plain then acc else c :: acc) f) args
    | V.CLet (_, a, b) -> marked (marked acc a) b
    | V.CLetRec (fns, b) -> List.fold_left (fun acc (_, (_, _, c)) -> marked acc c) (marked acc b) fns
    | V.CMatch (s, _, brs) -> List.fold_left (fun acc (_, _, c) -> marked acc c) (marked acc s) brs
    | V.CValues cs -> List.fold_left marked acc cs
    | V.CVar _ | V.CConst _ | V.CErased | V.CAbsurd -> acc
  in
  let returns ids = function V.CValues cs -> vars_of cs = ids | V.CVar x -> ids = [ x ] | _ -> false in
  let rec tails ~direct = function
    | V.CApp (_, _, (V.Tail | V.Delegate)) as c -> [ c ]
    | V.CLet (ids, (V.CApp (_, _, (V.Tail | V.Delegate)) as c), rest) -> if returns ids rest then [ c ] else []
    | V.CLet (_, _, rest) | V.CLetRec (_, rest) -> if direct then [] else tails ~direct rest
    | V.CMatch (_, _, brs) -> if direct then [] else List.concat_map (fun (_, _, c) -> tails ~direct c) brs
    | _ -> []
  in
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
        | _ -> error l "delegate needs exactly one call to a named function"

and elab_def_adts env adts =
  let header raw =
    match raw with
    | List (al, n :: colon :: rest) when is_special env colon Sp.Colon -> (
        let ps, rest = split_arrow env al rest in
        match rest with
        | ty :: d :: ctors -> (al, atom_or al n "a type constructor name", ps, ty, disc_of env al d, ctors)
        | _ -> error al "malformed def-adts entry")
    | _ -> error (loc raw) "malformed def-adts entry"
  in
  let headers = List.map header adts in
  let env, tids =
    List.fold_left_map
      (fun env (al, name, ps, ty, _, _) ->
        let env', _, tele = elab_tele env ~mults:(no_mults al) ps in
        check_equal env' al (elab_term env' ty) type_term;
        let x, env = bind env ~rigid:true (Some name) Erased (const env V.VToken) (TyCtor tele) in
        (env, x))
      env headers
  in
  let define (env, cids) tid (_, _, _, _, disc, ctors) =
    let ctor env raw =
      match raw with
      | List (cl, m :: n :: colon :: rest) when is_special env colon Sp.Colon ->
          let mult = match mult_of env m with Some m -> m | None -> error cl "constructor needs a multiplicity" in
          let name = atom_or cl n "a constructor name" in
          let ps, ret = split_arrow env cl rest in
          let env', ids, tele = elab_tele env ps in
          let ret = match ret with [ r ] -> elab_type env' r | _ -> error cl "constructor returns one type" in
          (match canon env' ret with App (Var t, _) when t = tid -> () | _ -> error cl "%s must return an application of %s" name (name_of env tid));
          if mult = Erased && List.exists (fun e -> e.mult = Many) tele then Printf.eprintf "warning (line %d): phantom constructor %s has a many field\n" cl name;
          let c, env = bind env ~rigid:true (Some name) mult Dyn (ValCtor (tele, abstract (List.rev ids) ret)) in
          (env, (mult, c))
      | _ -> error (loc raw) "malformed constructor"
    in
    let env, ctors = List.fold_left_map ctor env ctors in
    let tagged = tagged disc (shapes env 0 (List.map (fun (m, c) -> (m, Var c)) ctors)) in
    let values = List.map (fun (_, c) -> (c, V.VCtorFn { V.cname = name_of env c; cid = c; tagged })) ctors in
    let env = if env.run_pos then List.fold_left (fun env (c, v) -> set_state env c (Const v)) env values else env in
    let env = snd (bind env None Erased (const env V.VToken) (Matchable (disc, Var tid, List.map (fun (m, c) -> (m, Var c)) ctors))) in
    (env, cids @ values)
  in
  let env, cids = List.fold_left2 define (env, []) tids headers in
  (env, if env.run_pos || cids = [] then Fun.id else fun rest -> V.CLet (List.map fst cids, V.CValues (List.map (fun (_, v) -> V.CConst v) cids), rest))

let run_toplevel ?(print = print_endline) env items =
  let rec go env = function
    | [] -> env
    | [ item ] when not (is_statement env item) ->
        let env, _, code = elab_expr env [ Many ] item in
        List.iter (fun v -> print (V.show v)) (run_code env code);
        env
    | item :: rest ->
        if not (is_statement env item) then error (loc item) "only the last top-level form may be an expression";
        go (fst (elab_stmt env item)) rest
  in
  go env items
