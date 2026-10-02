open Term
module V = Value

let token = Env.Const V.VToken
let ty name sg = { name = Some name; subterm = false; mult = Erased; sg = Ty sg; place = None; loc = Reader.nowhere }

let env = Env.empty
let univ, env = Env.bind env (Some "Univ") Erased token (TyCtor [])
let type_term = App (Var univ, [])
let type_, env = Env.bind env ~rule:type_term (Some "Type") Erased token type_term
let level, env = Env.bind env (Some "Level") Erased token (TyCtor [])
let level_term = App (Var level, [])

let slot, env = Env.bind env (Some "Slot") Erased token (TyCtor [])
let slot_term = App (Var slot, [])
let null, env = Env.bind env None Many token type_term
let () = Term.vacant := null
let () = Term.univ := univ

let heterogeneous = [ ty "A" type_term; ty "a" (Bound 0); ty "B" type_term; ty "b" (Bound 0) ]

let predates, env =
  Env.bind env (Some "Predates") Erased token (TyCtor [ ty "A" type_term; ty "a" (Bound 0); ty "l" level_term ])

let subterm, env = Env.bind env (Some "Subterm") Erased token (TyCtor heterogeneous)
let sharing, env = Env.bind env (Some "Sharing") Erased token (TyCtor [])
let sharing_term = App (Var sharing, [])
let sharing_ctors, env =
  let adt = { V.tname = "Sharing"; tagged = true; newtype = false; ctors = []; ext = None } in
  let env, cs = List.fold_left_map (fun env (index, name) ->
    let x, env = Env.bind env (Some name) Many token (ValCtor ([], sharing_term)) in
    let c = { V.cname = name; cid = x; index; arity = 0; adt } in
    (Env.set_state env x (Env.Const (V.VCtorFn c)), c)) env [0, "Unique"; 1, "Shared"] in
  adt.ctors <- cs;
  let x, env = Env.bind env None Many (Env.Const (V.VMatchable adt))
    (Matchable (Enum, false, false, Var sharing, List.map (fun c -> Many, Var c.V.cid) cs)) in
  (cs, Env.merge_opens (Env.forcing (Env.opens_add env x)))
let unique_term = App (Var (List.nth sharing_ctors 0).V.cid, [])
let shared_term = App (Var (List.nth sharing_ctors 1).V.cid, [])
let coercible, env = Env.bind env (Some "Coercible") Erased token
  (TyCtor [ ty "sa" sharing_term; ty "A" type_term; ty "a" (Bound 0);
            ty "sb" sharing_term; ty "B" type_term; ty "b" (Bound 0) ])
let delegate, env = Env.bind env (Some "Delegate") Erased token
  (TyCtor [ ty "sg" sharing_term; ty "G" type_term; ty "g" (Bound 0);
            ty "sf" sharing_term; ty "F" type_term; ty "f" (Bound 0) ])

let special, env = Env.bind env (Some "Special") Erased token (TyCtor [])
let special_term = App (Var special, [])

(* [specials]: each special form by its variant's constructor entry. *)
let specials, env =
  let adt = { V.tname = "Special"; tagged = true; newtype = false; ctors = []; ext = None } in
  let ctor (env, index) (sp, n) =
    let c, env = Env.bind env (Some ("%" ^ n)) Many token (ValCtor ([], special_term)) in
    let ctor = { V.cname = "%" ^ n; cid = c; index; arity = 0; adt } in
    let env = Env.set_state env c (Env.Const (V.VCtorFn ctor)) in
    ((env, index + 1), (sp, n, c, ctor))
  in
  let (env, _), ctors = List.fold_left_map ctor (env, 0) Special.all in
  adt.ctors <- List.map (fun (_, _, _, c) -> c) ctors;
  let matchable = Matchable (Enum, false, false, Var special, List.map (fun (_, _, c, _) -> (Many, Var c)) ctors) in
  let m, env = Env.bind env None Many (Env.Const (V.VMatchable adt)) matchable in
  let env = Env.merge_opens (Env.forcing (Env.opens_add env m)) in
  ( List.map (fun (sp, _, c, _) -> (c, sp)) ctors,
    List.fold_left
      (fun env (_, n, c, ctor) ->
        snd (Env.bind env ~rule:(App (Var c, [])) (Some n) Many (Env.Const (V.VCtor (ctor, [||]))) special_term))
      env ctors )
