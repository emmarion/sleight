open Term
open Reader
open Env
module V = Value
module Sp = Special

exception BranchAbsurd of Env.t

type entry = Term.entry = { name : string option; subterm : bool; mult : mult; sg : sg }

type res = { term : term; ty : term; erasure : mult }

let type_term = Prelude.type_term
let single loc = function [ r ] -> r | rs -> error loc "expected one value, got %d" (List.length rs)
let pos_of expect = if List.for_all (( = ) Erased) expect then Erased else Many
let atom = function Atom (_, n) -> Some n | List _ -> None
let atom_or loc raw what = match atom raw with Some n -> n | None -> error loc "expected %s, got %s" what (Reader.show raw)
let name_or_anon n = if n = "_" then None else Some n

(* Dispatch tier 2 (section 4): a name whose Const, non-erased value is a Special variant. *)
let special_of env raw =
  match raw with
  | Atom (_, n) -> (
      match lookup env n with
      | Some x -> (
          match ((entry env x).state, (entry env x).mult) with
          | Const (V.VCtor (c, [])), Many -> Hashtbl.find_opt Sp.table c
          | _ -> None)
      | None -> None)
  | List _ -> None

let is_special env raw s = special_of env raw = Some s
let mult_of env raw = match special_of env raw with Some Sp.Erased -> Some Erased | Some Sp.Many -> Some Many | _ -> None
let is_statement env = function List (_, h :: _) -> List.exists (is_special env h) Sp.statements | _ -> false

let var env loc n = match lookup env n with Some x -> x | None -> error loc "unbound name %s" n

let find_index p l = let rec go i = function [] -> None | x :: xs -> if p x then Some i else go (i + 1) xs in go 0 l

let check_type env loc actual expected =
  if not (equal (canon env actual) (canon env expected)) then
    error loc "type mismatch: expected %s, got %s" (show env expected) (show env actual)

let check_equal env loc actual expected =
  if not (equal (canon env actual) (canon env expected)) then
    error loc "value mismatch: expected %s, got %s" (show env expected) (show env actual)

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

let is_empty_type env ty =
  match canon env ty with
  | App (Var t, _) -> (match matchables env t with [ (_, _, []) ] -> true | _ -> false)
  | _ -> false

let check_empty env loc ty = if not (is_empty_type env ty) then error loc "%s is not an empty type" (show env ty)

(* ---- source telescopes ---- *)

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

(* Return entries are the leading items headed by a multiplicity token; what follows is the body. *)
let split_returns env items =
  let rec go acc = function
    | List (_, m :: _) as r :: rest when mult_of env m <> None -> go (r :: acc) rest
    | rest -> (List.rev acc, rest)
  in
  go [] items

(* Binds a closed telescope into the scope, one fresh entry per item. *)
let open_tele env ?(named = true) ?names ?mults ?(state = Dyn) ?(ids = []) tele =
  let nth l i = Option.map (fun l -> List.nth l i) l in
  let outer = List.length ids in
  let _, (env, ids) =
    List.fold_left
      (fun (i, (env, ids)) e ->
        let sg = map_sg (instantiate ids) e.sg in
        let ty, rule = match sg with Ty t -> (t, None) | Is t -> (infer env 0 t, Some t) in
        let name = match nth names i with Some n -> n | None -> if named then e.name else None in
        let mult = match nth mults i with Some m -> m | None -> e.mult in
        let x, env = bind env name mult state ty ~rule in
        (i + 1, (env, Var x :: ids)))
      (0, (env, ids)) tele
  in
  (env, List.rev_map (function Var x -> x | _ -> assert false) (List.filteri (fun i _ -> i < List.length ids - outer) ids))

(* ---- the restricted grammar of types and is-expressions (section 5) ---- *)

let rec elab_term env raw =
  match raw with
  | Atom (l, n) -> Var (var env l n)
  | List (l, []) -> error l "empty form"
  | List (l, head :: args) -> (
      match special_of env head with
      | Some Sp.Fn -> elab_fn_type env l args
      | Some Sp.TyCtor ->
          let ps, ret = split_arrow env l args in
          let env', _, tele = elab_tele env ~mults:(fun _ -> function None -> Erased | Some _ -> error l "type constructor entries carry no multiplicity") ps in
          (match ret with [ r ] -> check_equal env' l (elab_term env' r) type_term | _ -> error l "TyCtor returns Type");
          TyCtor tele
      | Some Sp.ValCtor ->
          let ps, ret = split_arrow env l args in
          let env', ids, tele = elab_tele env ps in
          let ret = match ret with [ r ] -> elab_term env' r | _ -> error l "ValCtor returns one type" in
          check_type env' l (infer env' l ret) type_term;
          ValCtor (tele, abstract (List.rev ids) ret)
      | Some Sp.Matchable -> (
          match args with
          | d :: t :: cs ->
              let disc = match special_of env d with Some Sp.Enum -> Enum | Some Sp.Union -> Union | _ -> error l "expected enum or union" in
              let ctor = function
                | List (l, [ m; c ]) -> (Option.get (mult_of env m), Var (var env l (atom_or l c "a constructor name")))
                | r -> error (loc r) "expected (multiplicity Constructor)"
              in
              Matchable (disc, Var (var env l (atom_or l t "a type constructor name")), List.map ctor cs)
          | _ -> error l "malformed Matchable")
      | Some sp -> error l "%s cannot appear in a type" (Sp.name sp)
      | None -> (
          let h = Var (var env l (atom_or l head "a constructor")) in
          match canon env (infer env l h) with
          | TyCtor tele | ValCtor (tele, _) ->
              let acc, _ = check_args env l tele args (fun _ a -> (elab_term_res env a, V.CErased)) in
              App (h, List.rev acc)
          | ty -> error l "%s has type %s and cannot be applied in a type" (show env h) (show env ty)))

and elab_term_res env raw = let t = elab_term env raw in { term = t; ty = infer env (loc raw) t; erasure = Erased }

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
   [mults] decides an entry's multiplicity from its declared one; [ids] are binders already in force. *)
and elab_tele env ?(subterm = false) ?(ids = []) ?(mults = fun _ m -> Option.get m) entries =
  let entries = List.concat_map (parse_entry env) entries in
  let _, (env, ids, tele) =
    List.fold_left
      (fun (i, (env, ids, tele)) e ->
        if e.s_subterm && not subterm then error e.s_loc "subterm is not allowed here";
        let mult = try mults i e.s_mult with Invalid_argument _ -> error e.s_loc "missing multiplicity" in
        let sg, ty = match (e.s_ty, e.s_is) with
          | Some t, _ -> let t = elab_type env t in (Ty t, t)
          | None, Some t -> let t = elab_term env t in (Is t, infer env e.s_loc t)
          | None, None -> error e.s_loc "entry %s needs a type or an is clause" e.s_name
        in
        let rule = match sg with Is t -> Some t | Ty _ -> None in
        let x, env = bind env (name_or_anon e.s_name) mult Dyn ty ~rule in
        let entry = { name = name_or_anon e.s_name; subterm = e.s_subterm; mult; sg = map_sg (abstract ids) sg } in
        (i + 1, (env, x :: ids, entry :: tele)))
      (0, (env, ids, [])) entries
  in
  (env, List.rev ids, List.rev tele)

(* Checks [args] against [tele]; returns their terms innermost first, and their code. *)
and check_args env loc tele args elab =
  if List.length tele <> List.length args then error loc "expected %d arguments, got %d" (List.length tele) (List.length args);
  let acc, codes =
    List.fold_left2
      (fun (acc, codes) e arg ->
        let r, code = elab e.mult arg in
        (match map_sg (instantiate acc) e.sg with
         | Ty ty -> check_type env (Reader.loc arg) r.ty ty
         | Is t -> check_equal env (Reader.loc arg) r.term t);
        (r.term :: acc, code :: codes))
      ([], []) tele args
  in
  (acc, List.rev codes)

(* [ids] are the terms of binders already in force, innermost first. *)
let check_results env loc ?(ids = []) tele ress =
  if List.length tele <> List.length ress then error loc "expected %d values, got %d" (List.length tele) (List.length ress);
  ignore
    (List.fold_left2
       (fun acc e r ->
         (match map_sg (instantiate acc) e.sg with Ty ty -> check_type env loc r.ty ty | Is t -> check_equal env loc r.term t);
         r.term :: acc)
       ids tele ress)

let res_of env x = { term = Var x; ty = type_of env x; erasure = (entry env x).mult }

let fresh_result env ?rule ty =
  let x, env = bind env None Erased Dyn ty ~rule in
  (env, res_of env x)

let proof_type ctor args = App (Var ctor, args)

let expect_proof env loc ctor arity p =
  match canon env (infer env loc p) with
  | App (Var c, args) when c = ctor && List.length args = arity -> args
  | ty -> error loc "expected a %s proof, got %s : %s" (name_of env ctor) (show env p) (show env ty)

let rec is_strict_subterm a b =
  match b with App (_, args) -> List.exists (fun x -> equal a x || is_strict_subterm a x) args | _ -> false

(* ---- expressions ---- *)

let rec elab_expr ?(cc = V.Plain) env expect raw : Env.t * res list * V.code =
  let l = loc raw in
  let env, ress, code = elab_expr_inner cc env expect raw in
  if List.length ress <> List.length expect then error l "expected %d values, got %d" (List.length expect) (List.length ress);
  let code = match code with V.CErased when List.length expect <> 1 -> V.CValues (List.map (fun _ -> V.CErased) expect) | c -> c in
  List.iter2
    (fun m r -> if m = Many && r.erasure = Erased then error l "erased value %s used in a non-erased position" (show env r.term))
    expect ress;
  (env, ress, code)

and elab_expr1 ?cc env mult raw =
  let env, ress, code = elab_expr ?cc env [ mult ] raw in
  (env, List.hd ress, code)

and elab_expr_inner cc env expect raw =
  let pos = pos_of expect in
  match raw with
  | Atom (l, n) ->
      let x = var env l n in
      (env, [ res_of env x ], if pos = Many then V.CVar x else V.CErased)
  | List (l, []) -> error l "empty form"
  | List (l, head :: args) -> (
      match special_of env head with
      | Some sp -> elab_special cc env expect l sp args
      | None -> (
          let env, h, hcode =
            match head with
            | Atom (_, n) -> let x = var env l n in (env, res_of env x, V.CVar x)
            | List _ -> elab_expr1 env pos head
          in
          match canon env h.ty with
          | TyCtor tele ->
              if pos = Many then error l "type constructor application in a non-erased position";
              let acc, _ = check_args env l tele args (fun _ a -> (elab_term_res env a, V.CErased)) in
              (env, [ { term = App (h.term, List.rev acc); ty = type_term; erasure = Erased } ], V.CErased)
          | ValCtor (tele, ret) ->
              if pos = Many && h.erasure = Erased then error l "erased constructor %s in a non-erased position" (show env h.term);
              let env = ref env in
              let acc, codes =
                check_args !env l tele args (fun m a ->
                    let env', r, code = elab_expr1 !env (if pos = Erased then Erased else m) a in
                    env := env';
                    (r, code))
              in
              let code = if pos = Erased then V.CErased else V.CApp (hcode, codes, V.Plain) in
              (!env, [ { term = App (h.term, List.rev acc); ty = instantiate acc ret; erasure = pos } ], code)
          | Fn (lv, params, rets) -> elab_call cc env expect l h hcode lv params rets args
          | ty -> error l "%s : %s is not applicable" (show env h.term) (show env ty)))

and elab_call cc env expect l callee hcode lv params rets args =
  let pos = pos_of expect in
  if pos = Many && callee.erasure = Erased then error l "erased function %s called in a non-erased position" (show env callee.term);
  let annotation, args =
    let rec go i acc = function
      | List (_, [ k; p ]) :: rest when is_special env k Sp.Predates && i = 0 -> (Some (`Predates p), List.rev acc @ rest)
      | List (_, [ k; p ]) :: rest when is_special env k Sp.Subterm -> (Some (`Subterm (i, p)), List.rev acc @ rest)
      | a :: rest -> go (i + 1) (a :: acc) rest
      | [] -> (None, List.rev acc)
    in
    go 0 [] args
  in
  let env = ref env in
  let acc, codes =
    check_args !env l params args (fun m a ->
        let env', r, code = elab_expr1 !env (if pos = Erased then Erased else m) a in
        env := env';
        (r, code))
  in
  let arg_terms = List.rev acc in
  let proof_arg raw =
    let env', r, _ = elab_expr1 !env Erased raw in
    env := env';
    r.term
  in
  let annotation = Option.map (function `Predates p -> `Predates (proof_arg p) | `Subterm (i, p) -> `Subterm (i, proof_arg p)) annotation in
  let env = !env in
  (match env.level with
   | Top -> ()
   | At cur ->
       let lv = canon env lv in
       if equal lv (Var cur) then (
         match annotation with
         | Some (`Subterm (i, p)) ->
             let subterm_params = List.filter_map (fun (i, e) -> if e.subterm then Some i else None) (List.mapi (fun i e -> (i, e)) params) in
             let k = match find_index (( = ) i) subterm_params with Some k -> k | None -> error l "argument %d is not a subterm parameter" i in
             if k >= List.length env.subterms then error l "the enclosing function has no subterm parameter at position %d" k;
             List.iteri
               (fun j pi ->
                 if j < k then check_equal env l (List.nth arg_terms pi) (Var (List.nth env.subterms j)))
               subterm_params;
             (match expect_proof env l Prelude.subterm 4 p with
              | [ _; a; _; b ] ->
                  check_equal env l a (List.nth arg_terms i);
                  check_equal env l b (Var (List.nth env.subterms k))
              | _ -> assert false)
         | _ -> error l "same-level call to %s needs a (subterm p) annotation" (show env callee.term))
       else
         match annotation with
         | Some (`Predates p) -> (
             match expect_proof env l Prelude.predates 3 p with
             | [ _; x; l2 ] ->
                 check_equal env l l2 (Var cur);
                 let x = canon env x in
                 if not (equal x lv || equal x (canon env callee.term)) then
                   error l "%s does not relate the callee or its level %s" (show env p) (show env lv)
             | _ -> assert false)
         | _ -> error l "lower-level call to %s needs a (predates p) annotation" (show env callee.term));
  let env, ids = open_tele env ~named:false ~mults:(List.map (fun e -> if pos = Erased then Erased else e.mult) rets) ~ids:acc rets in
  let ress = List.map (res_of env) ids in
  (env, ress, if pos = Erased then V.CErased else V.CApp (hcode, codes, cc))

and elab_special _cc env expect l sp args =
  let pos = pos_of expect in
  let one () = match expect with [ m ] -> m | _ -> error l "%s produces one value" (Sp.name sp) in
  let envr = ref env in
  let erased_result ?rule ty =
    let env, r = fresh_result !envr ?rule ty in
    (env, [ r ], V.CErased)
  in
  (* An argument in the restricted grammar, or an arbitrary erased expression (a proof). *)
  let term_arg raw = elab_term !envr raw in
  let proof_arg raw =
    let env, r, _ = elab_expr1 !envr Erased raw in
    envr := env;
    r.term
  in
  let expect_proof ctor arity p = expect_proof !envr l ctor arity p in
  let check_equal a b = check_equal !envr l a b in
  let infer t = infer !envr l t in
  match (sp, args) with
  | (Sp.Fn | Sp.TyCtor | Sp.ValCtor | Sp.Matchable), _ ->
      ignore (one ());
      if pos = Many then error l "a type in a non-erased position";
      (env, [ { term = elab_term env (List (l, Atom (l, Sp.name sp) :: args)); ty = type_term; erasure = Erased } ], V.CErased)
  | Sp.Values, _ ->
      if List.length args <> List.length expect then error l "expected %d values, got %d" (List.length expect) (List.length args);
      let env, ress, codes =
        List.fold_left2
          (fun (env, ress, codes) m a ->
            let env, r, code = elab_expr1 env m a in
            (env, r :: ress, code :: codes))
          (env, [], []) expect args
      in
      (env, List.rev ress, V.CValues (List.rev codes))
  | Sp.Match, _ -> elab_match env expect l args
  | (Sp.Tail | Sp.Delegate), [ (List _ as call) ] ->
      if pos = Erased then error l "%s in an erased position" (Sp.name sp);
      elab_expr ~cc:(if sp = Sp.Tail then V.Tail else V.Delegate) env expect call
  | Sp.MatchableOf, [ t ] ->
      ignore (one ());
      let tid = var env l (atom_or l t "a type constructor name") in
      let x, _, _ = find_matchable env l tid in
      (env, [ res_of env x ], V.CErased)
  | Sp.LevelOf, [ f ] -> (
      ignore (one ());
      let f = term_arg f in
      match canon env (infer f) with
      | Fn (lv, _, _) -> (env, [ { term = lv; ty = Prelude.level_term; erasure = Erased } ], V.CErased)
      | ty -> error l "level-of: %s : %s is not a function" (show env f) (show env ty))
  | Sp.ProveSubterm, [ a; b ] ->
      ignore (one ());
      let a = term_arg a and b = term_arg b in
      if not (is_strict_subterm (canon env a) (canon env b)) then error l "%s is not a strict subterm of %s" (show env a) (show env b);
      erased_result (proof_type Prelude.subterm [ infer a; a; infer b; b ])
  | Sp.ProvePredates, [ x; lv ] -> (
      ignore (one ());
      let x = match canon env (Var (var env l (atom_or l x "a variable"))) with Var x -> x | t -> error l "%s is not a variable" (show env t) in
      match canon env (term_arg lv) with
      | Var lvl when (entry env lvl).level_born ->
          if x >= lvl then error l "%s was not in scope when level %s was born" (name_of env x) (name_of env lvl);
          erased_result (proof_type Prelude.predates [ type_of env x; Var x; Var lvl ])
      | t -> error l "%s is not a level born by def-lvl" (show env t))
  | Sp.PredatesTrans, [ p; q ] -> (
      ignore (one ());
      let p = proof_arg p and q = proof_arg q in
      match (expect_proof Prelude.predates 3 p, expect_proof Prelude.predates 3 q) with
      | [ a; x; l1 ], [ _; l1'; l2 ] ->
          check_equal l1' l1;
          erased_result (proof_type Prelude.predates [ a; x; l2 ])
      | _ -> assert false)
  | Sp.SubtermTrans, [ p; q ] -> (
      ignore (one ());
      let p = proof_arg p and q = proof_arg q in
      match (expect_proof Prelude.subterm 4 p, expect_proof Prelude.subterm 4 q) with
      | [ a; x; _; y ], [ _; y'; c; z ] ->
          check_equal y' y;
          erased_result (proof_type Prelude.subterm [ a; x; c; z ])
      | _ -> assert false)
  | Sp.PredatesSubterm, [ p; q ] -> (
      ignore (one ());
      let p = proof_arg p and q = proof_arg q in
      match (expect_proof Prelude.predates 3 p, expect_proof Prelude.subterm 4 q) with
      | [ _; x; lv ], [ b; y; _; x' ] ->
          check_equal x' x;
          erased_result (proof_type Prelude.predates [ b; y; lv ])
      | _ -> assert false)
  | Sp.Coerce, [ a; p ] -> (
      let m = one () in
      let env, a, code = elab_expr1 env m a in
      envr := env;
      let p = proof_arg p in
      match expect_proof Prelude.coercible 4 p with
      | [ _; a'; b_ty; b ] ->
          check_equal a.term a';
          let x, env = bind !envr None m Dyn b_ty ~rule:(Some b) in
          (env, [ res_of env x ], code)
      | _ -> assert false)
  | Sp.CoercibleRefl, [ e ] ->
      ignore (one ());
      let e = term_arg e in
      let ty = infer e in
      erased_result (proof_type Prelude.coercible [ ty; e; ty; e ])
  | Sp.CoercibleSym, [ p ] -> (
      ignore (one ());
      let p = proof_arg p in
      match expect_proof Prelude.coercible 4 p with
      | [ a; x; b; y ] -> erased_result (proof_type Prelude.coercible [ b; y; a; x ])
      | _ -> assert false)
  | Sp.CoercibleTrans, [ p; q ] -> (
      ignore (one ());
      let p = proof_arg p and q = proof_arg q in
      match (expect_proof Prelude.coercible 4 p, expect_proof Prelude.coercible 4 q) with
      | [ a; x; _; y ], [ _; y'; c; z ] ->
          check_equal y' y;
          erased_result (proof_type Prelude.coercible [ a; x; c; z ])
      | _ -> assert false)
  | Sp.CoercibleWrap, c :: args -> (
      ignore (one ());
      let c = var env l (atom_or l c "a constructor") in
      match (Hashtbl.find_opt V.ctors c, canon env (type_of env c)) with
      | Some { V.repr = V.Field i; _ }, ValCtor (tele, ret) ->
          let acc, _ = check_args env l tele args (fun _ a -> (elab_term_res env a, V.CErased)) in
          let f = List.nth (List.rev acc) i in
          erased_result (proof_type Prelude.coercible [ infer f; f; instantiate acc ret; App (Var c, List.rev acc) ])
      | _ -> error l "%s is not the wrapping constructor of a transparent type" (name_of env c))
  | Sp.CoercibleCtor, c :: args -> (
      ignore (one ());
      let c = var env l (atom_or l c "a constructor") in
      match (Hashtbl.find_opt V.ctors c, canon env (type_of env c)) with
      | Some { V.phantom = false; _ }, ValCtor (tele, ret) ->
          let check side (e : entry) ty t =
            match map_sg (instantiate side) e.sg with Ty ty' -> check_type !envr l ty ty' | Is i -> check_equal t i
          in
          let rec go src tgt tele args =
            match (tele, args) with
            | [], [] -> (src, tgt)
            | ({ mult = Erased; _ } as e) :: tele, s :: t :: args ->
                let s = term_arg s and t = term_arg t in
                check src e (infer s) s;
                check tgt e (infer t) t;
                go (s :: src) (t :: tgt) tele args
            | ({ mult = Many; _ } as e) :: tele, p :: args -> (
                match expect_proof Prelude.coercible 4 (proof_arg p) with
                | [ sty; s; tty; t ] ->
                    check src e sty s;
                    check tgt e tty t;
                    go (s :: src) (t :: tgt) tele args
                | _ -> assert false)
            | _ -> error l "coercible-ctor: wrong number of arguments for %s" (name_of env c)
          in
          let src, tgt = go [] [] tele args in
          erased_result
            (proof_type Prelude.coercible [ instantiate src ret; App (Var c, List.rev src); instantiate tgt ret; App (Var c, List.rev tgt) ])
      | _ -> error l "%s is not a non-phantom value constructor" (name_of env c))
  | Sp.CoercibleOf, [ g ] -> (
      ignore (one ());
      let g = var env l (atom_or l g "a function name") in
      let proofs =
        List.filter
          (fun x -> match type_of env x with App (Var c, [ _; Var g'; _; _ ]) -> c = Prelude.coercible && g' = g && (entry env x).name = None | _ -> false)
          env.scope
      in
      match proofs with
      | x :: _ -> (env, [ res_of env x ], V.CErased)
      | [] -> error l "%s has no delegate proof in scope" (name_of env g))
  | sp, _ when List.mem sp Sp.statements -> error l "%s is a statement, not an expression" (Sp.name sp)
  | sp, _ -> error l "malformed %s form" (Sp.name sp)

(* ---- match ---- *)

and elab_match env expect l args =
  match args with
  | m :: scrut :: List (_, ann) :: branches ->
      let pos = pos_of expect in
      let smult = match mult_of env m with Some m -> m | None -> error l "match needs the scrutinee's multiplicity" in
      let smult = if pos = Erased then Erased else smult in
      let env, sres, scode = elab_expr1 env smult scrut in
      let tid = match canon env sres.ty with App (Var t, _) -> t | ty -> error l "cannot match on %s : %s" (show env sres.term) (show env ty) in
      let _, disc, ctors = find_matchable env l tid in
      let outer = env in
      let env, _, ann_tele =
        elab_tele env ~mults:(fun i m -> if m <> None then error l "a match annotation carries no multiplicities"; List.nth expect i) ann
      in
      if List.length ann_tele <> List.length expect then error l "match annotation has %d entries, position needs %d" (List.length ann_tele) (List.length expect);
      let env = { env with scope = outer.scope } in
      let env, result_ids = open_tele env ~named:false ann_tele in
      let branch raw =
        let kind, pat, body =
          match raw with
          | List (_, [ a; Atom (_, _) as c ]) when is_special env a Sp.Absurd -> (`Auto, c, [])
          | List (_, a :: pat :: body) when is_special env a Sp.Absurd -> (`Proof, pat, body)
          | List (_, pat :: body) -> (`Present, pat, body)
          | _ -> error (loc raw) "malformed branch"
        in
        let bl = loc pat in
        let c, field_names = match pat with Atom (_, c) -> (c, []) | List (_, c :: fs) -> (atom_or bl c "a constructor", List.map (fun f -> atom_or (loc f) f "a field name") fs) | _ -> error bl "malformed pattern" in
        let c = var env bl c in
        let phantom = match List.find_opt (fun (_, c') -> c' = Var c) ctors with Some (m, _) -> m = Erased | None -> error bl "%s is not a constructor of %s" (name_of env c) (name_of env tid) in
        let tele, ret = match canon env (type_of env c) with ValCtor (tele, ret) -> (tele, ret) | _ -> assert false in
        if kind <> `Auto && List.length field_names <> List.length tele then error bl "%s has %d fields" (name_of env c) (List.length tele);
        let names = if kind = `Auto then List.map (fun _ -> None) tele else List.map name_or_anon field_names in
        let mults = List.map (fun e -> if phantom || smult = Erased then Erased else e.mult) tele in
        let envb, fids = open_tele env ~names ~mults tele in
        let fvars = List.rev_map (fun x -> Var x) fids in
        let forced =
          try Some (unify (unify envb sres.term (App (Var c, List.rev fvars))) sres.ty (instantiate fvars ret)) with Contradiction _ -> None
        in
        let result =
          match (kind, forced) with
          | `Auto, None -> `Absurd
          | `Auto, Some _ -> error bl "branch %s is not refuted" (name_of env c)
          | _, None -> error bl "branch %s is refuted; write (absurd %s)" (name_of env c) (name_of env c)
          | `Present, Some envb -> (
              try
                let envb, ress, code = elab_body envb (if phantom then List.map (fun _ -> Erased) expect else expect) bl body in
                check_results envb bl ann_tele ress;
                `Present code
              with BranchAbsurd _ -> `Absurd)
          | `Proof, Some envb ->
              let envb, ress, _ = elab_body envb [ Erased ] bl body in
              check_empty envb bl (single bl ress).ty;
              `Absurd
        in
        (c, fids, phantom, result)
      in
      let branches = List.map branch branches in
      List.iter
        (fun (_, c) ->
          let c = match c with Var c -> c | _ -> assert false in
          match List.length (List.filter (fun (c', _, _, _) -> c' = c) branches) with
          | 1 -> ()
          | n -> error l "constructor %s has %d branches" (name_of env c) n)
        ctors;
      let real = List.filter_map (fun (c, fids, phantom, r) -> match r with `Present code when not phantom -> Some (c, fids, code) | _ -> None) branches in
      if pos = Many && (disc = Union || smult = Erased) && List.length real > 1 then error l "a match without a runtime discriminant can have only one real branch";
      let code =
        if pos = Erased then V.CErased
        else
          match real with
          | [] -> V.CAbsurd
          | [ (_, _, body) ] when smult = Erased -> body
          | [ (c, fids, body) ] when (Hashtbl.find V.ctors c).repr <> V.Tagged -> (
              match (Hashtbl.find V.ctors c).repr with V.Field i -> V.CLet ([ List.nth fids i ], scode, body) | _ -> body)
          | _ -> V.CMatch (scode, real)
      in
      (env, List.map (res_of env) result_ids, code)
  | _ -> error l "malformed match"

(* ---- bodies: statements followed by a final expression ---- *)

and elab_body env expect l items =
  match items with
  | [] -> error l "a body needs a final expression"
  | [ final ] -> elab_expr env expect final
  | stmt :: rest ->
      let env, wrap = elab_stmt env stmt in
      let env, ress, code = elab_body env expect l rest in
      (env, ress, wrap code)

and elab_stmt env raw : Env.t * (V.code -> V.code) =
  match raw with
  | List (l, head :: args) -> (
      match special_of env head with
      | Some Sp.Let -> elab_let env l args
      | Some Sp.DefLvl -> (
          match args with
          | [ n ] ->
              let _, env = bind env ~level_born:true (name_or_anon (atom_or l n "a name")) Erased (Const V.VToken) Prelude.level_term in
              (env, Fun.id)
          | _ -> error l "malformed def-lvl")
      | Some Sp.DefFns -> elab_def_fns env l args
      | Some Sp.DefAdts -> elab_def_adts env l args
      | Some Sp.ComptimeMatch -> elab_comptime_match env l args
      | _ -> error l "%s is not a statement" (Reader.show raw))
  | _ -> error (loc raw) "%s is not a statement" (Reader.show raw)

and run_code code = Eval.eval V.IntMap.empty code

and elab_let env l args =
  let binders, rhs = split_returns env args in
  let binders = List.concat_map (parse_entry env) binders in
  let expect = List.map (fun b -> match b.s_mult with Some m -> m | None -> error b.s_loc "let binder needs a multiplicity") binders in
  let inner, ress, code = elab_body env expect l rhs in
  let values = if env.run_pos then run_code code else [] in
  let env', ids =
    List.fold_left
      (fun (env', ids) (i, (b, r)) ->
        (match b.s_ty with Some t -> check_type env' b.s_loc r.ty (elab_type env' t) | None -> ());
        (match b.s_is with Some t -> check_equal env' b.s_loc r.term (elab_term env' t) | None -> ());
        let state =
          if env.run_pos then Const (if b.s_mult = Some Many then List.nth values i else V.VToken)
          else match r.term with Var y -> (entry env' y).state | _ -> Dyn
        in
        let x, env' = bind env' (name_or_anon b.s_name) (Option.get b.s_mult) state r.ty ~rule:(Some r.term) in
        (env', x :: ids))
      ({ inner with scope = env.scope }, [])
      (List.mapi (fun i br -> (i, br)) (List.combine binders ress))
  in
  let ids = List.rev ids in
  (env', if env.run_pos then Fun.id else fun rest -> V.CLet (ids, code, rest))

and elab_comptime_match env l args =
  match args with
  | [ x; List (pl, c :: fields) ] ->
      let x = var env l (atom_or l x "a variable") in
      let value = match ((entry env x).state, (entry env x).mult) with Const v, Many -> v | _ -> error l "comptime-match needs a Const, non-erased scrutinee" in
      let c = var env pl (atom_or pl c "a constructor") in
      let info = match Hashtbl.find_opt V.ctors c with Some i -> i | None -> error pl "%s is not a value constructor" (name_of env c) in
      let tid = match canon env (type_of env x) with App (Var t, _) -> t | _ -> error l "scrutinee is not a datatype value" in
      let _, disc, _ = find_matchable env l tid in
      if disc = Union then error l "comptime-match needs a non-erased discriminant";
      let field_values =
        match (info.repr, value) with
        | V.Tagged, V.VCtor (c', vs) when c' = c -> vs
        | V.Tagged, _ -> error l "comptime-match: expected %s, got %s" info.cname (V.show value)
        | V.Field i, v -> List.mapi (fun j _ -> if i = j then v else V.VToken) info.fields
        | V.Unspecified, _ -> List.map (fun _ -> V.VToken) info.fields
      in
      let tele, ret = match canon env (type_of env c) with ValCtor (tele, ret) -> (tele, ret) | _ -> assert false in
      if List.length fields <> List.length tele then error pl "%s has %d fields" (name_of env c) (List.length tele);
      let names = List.map (fun f -> name_or_anon (atom_or (loc f) f "a field name")) fields in
      let env, fids = open_tele env ~names tele in
      let env =
        List.fold_left2
          (fun env x v -> set_state env x (Const (if (entry env x).mult = Many then v else V.VToken)))
          env fids field_values
      in
      let fvars = List.rev_map (fun x -> Var x) fids in
      (try (unify (unify env (Var x) (App (Var c, List.rev fvars))) (type_of env x) (instantiate fvars ret), Fun.id)
       with Contradiction _ -> raise (BranchAbsurd env))
  | _ -> error l "malformed comptime-match: expected (comptime-match x (C field ...))"

and elab_def_fns env l args =
  match args with
  | lv :: fns ->
      let lvl = match canon env (elab_term env lv) with Var x when equal (type_of env x) Prelude.level_term -> x | t -> error l "%s is not a level" (show env t) in
      let header raw =
        match raw with
        | List (fl, m :: rest) -> (
            let mult = match mult_of env m with Some m -> m | None -> error fl "function needs a multiplicity" in
            let absurd, rest = match rest with a :: rest when is_special env a Sp.Absurd -> (true, rest) | _ -> (false, rest) in
            match rest with
            | n :: colon :: sg when is_special env colon Sp.Colon ->
                let name = atom_or fl n "a function name" in
                let ps, rest = split_arrow env fl sg in
                let rs, body = split_returns env rest in
                let _, _, params = elab_tele env ~subterm:true ps in
                let env_p, pids = open_tele env params in
                let _, _, rets = elab_tele env_p ~ids:(List.rev pids) rs in
                (fl, name, mult, absurd, Fn (Var lvl, params, rets), body)
            | _ -> error fl "malformed function header")
        | _ -> error (loc raw) "malformed function definition"
      in
      let headers = List.map header fns in
      let env, fids =
        List.fold_left_map (fun env (_, name, mult, _, ty, _) -> let x, env = bind env (Some name) mult Dyn ty in (env, x)) env headers
      in
      let define x (fl, name, mult, absurd, ty, body) =
        let params, rets = match ty with Fn (_, ps, rs) -> (ps, rs) | _ -> assert false in
        let envb, pids = open_tele env params in
        let envb = { envb with level = At lvl; subterms = List.filter_map (fun (e, x) -> if e.subterm then Some x else None) (List.combine params pids); run_pos = false } in
        let pvars = List.rev_map (fun x -> Var x) pids in
        let code =
          if absurd then (
            let envb, ress, _ = elab_body envb [ Erased ] fl body in
            check_empty envb fl (single fl ress).ty;
            V.CAbsurd)
          else
            let expect = List.map (fun e -> if mult = Erased then Erased else e.mult) rets in
            let envb, ress, code = elab_body envb expect fl body in
            check_results envb fl ~ids:pvars rets ress;
            if mult = Erased then V.CErased else code
        in
        let delegate = check_marks envb fl pids code in
        ((x, (name, pids, code)), Option.map (fun callee -> (x, ty, callee)) delegate)
      in
      let defs = List.map2 define fids headers in
      let env =
        List.fold_left
          (fun env (_, proof) ->
            match proof with
            | Some (g, gty, callee) ->
                snd (bind env None Erased (Const V.VToken) (proof_type Prelude.coercible [ gty; Var g; infer env l callee; callee ]))
            | None -> env)
          env defs
      in
      let fns = List.map fst defs in
      if env.run_pos then
        (List.fold_left (fun env (x, (fname, params, body)) -> set_state env x (Const (V.VFn { V.fname; params; body; env = lazy IntMap.empty }))) env fns, Fun.id)
      else (env, fun rest -> V.CLetRec (fns, rest))
  | [] -> error l "def-fns needs a level"

(* Validates every tail/delegate-marked call in a compiled body (section 9); returns the delegated callee, if any. *)
and check_marks env l pids code =
  let non_erased ids = List.filter (fun x -> (entry env x).mult = Many) ids in
  let rec marked acc = function
    | V.CApp (f, args, cc) as c ->
        let acc = if cc <> V.Plain then c :: acc else acc in
        List.fold_left marked (marked acc f) args
    | V.CLet (_, a, b) -> marked (marked acc a) b
    | V.CLetRec (fns, b) -> List.fold_left (fun acc (_, (_, _, c)) -> marked acc c) (marked acc b) fns
    | V.CMatch (s, brs) -> List.fold_left (fun acc (_, _, c) -> marked acc c) (marked acc s) brs
    | V.CValues cs -> List.fold_left marked acc cs
    | V.CVar _ | V.CErased | V.CAbsurd -> acc
  in
  let vars_of cs = List.filter_map (function V.CVar x -> Some x | V.CErased -> None | _ -> Some (-1)) cs in
  let rec returns ids = function
    | V.CLet (_, V.CErased, rest) -> returns ids rest
    | V.CValues cs -> vars_of cs = non_erased ids
    | V.CVar x -> non_erased ids = [ x ]
    | _ -> false
  in
  let rec tails ~direct = function
    | V.CApp (_, _, (V.Tail | V.Delegate)) as c -> [ c ]
    | V.CLet (ids, (V.CApp (_, _, (V.Tail | V.Delegate)) as c), rest) -> if returns ids rest then [ c ] else []
    | V.CLet (_, V.CErased, rest) -> tails ~direct rest
    | V.CLet (_, _, rest) | V.CLetRec (_, rest) -> if direct then [] else tails ~direct rest
    | V.CMatch (_, brs) -> if direct then [] else List.concat_map (fun (_, _, c) -> tails ~direct c) brs
    | _ -> []
  in
  let marks = marked [] code in
  if marks = [] then None
  else
    let delegate = List.exists (function V.CApp (_, _, V.Delegate) -> true | _ -> false) marks in
    let ok = tails ~direct:delegate code in
    List.iter (fun c -> if not (List.memq c ok) then error l "a %s-marked call is not in tail position" (if delegate then "delegate" else "tail")) marks;
    if delegate then
      match ok with
      | [ V.CApp (f, args, _) ] ->
          if vars_of args <> non_erased pids then error l "a delegate call must pass the function's non-erased parameters straight through";
          (match f with V.CVar x -> Some (Var x) | _ -> error l "delegate callee must be a name")
      | _ -> error l "delegate needs exactly one call"
    else None

and elab_def_adts env _ adts =
  let header raw =
    match raw with
    | List (al, n :: colon :: rest) when is_special env colon Sp.Colon -> (
        let name = atom_or al n "a type constructor name" in
        let ps, rest = split_arrow env al rest in
        match rest with
        | ty :: d :: ctors ->
            let disc = match special_of env d with Some Sp.Enum -> Enum | Some Sp.Union -> Union | _ -> error al "expected enum or union" in
            (al, name, ps, ty, disc, ctors)
        | _ -> error al "malformed def-adts entry")
    | _ -> error (loc raw) "malformed def-adts entry"
  in
  let headers = List.map header adts in
  let env, tids =
    List.fold_left_map
      (fun env (al, name, ps, ty, _, _) ->
        let env', _, tele = elab_tele env ~mults:(fun _ -> function None -> Erased | Some _ -> error al "type constructor entries carry no multiplicity") ps in
        check_equal env' al (elab_term env' ty) type_term;
        let x, env = bind env ~rigid:true (Some name) Erased (Const V.VToken) (TyCtor tele) in
        (env, x))
      env headers
  in
  let define env tid (al, _, _, _, disc, ctors) =
    let ctor env raw =
      match raw with
      | List (cl, m :: n :: colon :: rest) when is_special env colon Sp.Colon ->
          let mult = match mult_of env m with Some m -> m | None -> error cl "constructor needs a multiplicity" in
          let name = atom_or cl n "a constructor name" in
          let ps, ret = split_arrow env cl rest in
          let env', ids, tele = elab_tele env ps in
          let ret = match ret with [ r ] -> elab_term env' r | _ -> error cl "constructor returns one type" in
          (match canon env' ret with App (Var t, _) when t = tid -> () | _ -> error cl "%s must return an application of %s" name (name_of env tid));
          check_type env' cl (infer env' cl ret) type_term;
          let fields = List.map (fun e -> e.mult) tele in
          if mult = Erased && List.mem Many fields then Printf.eprintf "warning (line %d): phantom constructor %s has a many field\n" cl name;
          let c, env = bind env ~rigid:true (Some name) mult Dyn (ValCtor (tele, abstract (List.rev ids) ret)) in
          let env = set_state env c (Const (V.VCtorFn c)) in
          Hashtbl.replace V.ctors c { V.cname = name; adt = tid; fields; phantom = mult = Erased; repr = V.Tagged };
          (env, (mult, c))
      | _ -> error (loc raw) "malformed constructor"
    in
    let env, ctors = List.fold_left_map ctor env ctors in
    let info c = Hashtbl.find V.ctors c in
    let many_fields c = List.length (List.filter (( = ) Many) (info c).fields) in
    let wrapper =
      match List.filter (fun (m, c) -> m = Many && many_fields c = 1) ctors with
      | [ (_, w) ] ->
          let others = List.filter (fun (_, c) -> c <> w) ctors in
          let transparent = match disc with Enum -> List.for_all (fun (m, _) -> m = Erased) others | Union -> List.for_all (fun (_, c) -> many_fields c = 0) others in
          if transparent then Some w else None
      | _ -> None
    in
    Option.iter
      (fun w ->
        List.iter
          (fun (_, c) ->
            let i = info c in
            let repr = if c = w then V.Field (Option.get (find_index (( = ) Many) i.fields)) else V.Unspecified in
            Hashtbl.replace V.ctors c { i with repr })
          ctors)
      wrapper;
    ignore al;
    snd (bind env None Erased (Const V.VToken) (Matchable (disc, Var tid, List.map (fun (m, c) -> (m, Var c)) ctors)))
  in
  (List.fold_left2 define env tids headers, Fun.id)

(* ---- top level ---- *)

let run_toplevel ?(print = print_endline) env items =
  let rec go env = function
    | [] -> env
    | [ item ] when not (is_statement env item) ->
        let env, _, code = elab_expr env [ Many ] item in
        List.iter (fun v -> print (V.show v)) (run_code code);
        env
    | item :: rest ->
        if not (is_statement env item) then error (loc item) "only the last top-level form may be an expression";
        go (fst (elab_stmt env item)) rest
  in
  go env items
