open Term
module V = Value

let token = Env.Const V.VToken
let ty name sg = { name = Some name; subterm = false; mult = Erased; sg = Ty sg; place = None }

let env = Env.empty
let univ, env = Env.bind env (Some "Univ") Erased token (TyCtor [])
let type_term = App (Var univ, [])
let type_, env = Env.bind env ~rule:type_term (Some "Type") Erased token type_term
let level, env = Env.bind env (Some "Level") Erased token (TyCtor [])
let level_term = App (Var level, [])

let slot, env = Env.bind env (Some "Slot") Erased token (TyCtor [])
let slot_term = App (Var slot, [])
let null, env = Env.bind env None Many token type_term

let heterogeneous = [ ty "A" type_term; ty "a" (Bound 0); ty "B" type_term; ty "b" (Bound 0) ]

let predates, env =
  Env.bind env (Some "Predates") Erased token (TyCtor [ ty "A" type_term; ty "a" (Bound 0); ty "l" level_term ])

let subterm, env = Env.bind env (Some "Subterm") Erased token (TyCtor heterogeneous)
let coercible, env = Env.bind env (Some "Coercible") Erased token (TyCtor heterogeneous)

let special, env = Env.bind env (Some "Special") Erased token (TyCtor [])
let special_term = App (Var special, [])

(* [specials]: each special form by its variant's constructor entry. *)
let specials, env =
  let adt = { V.tname = "Special"; tagged = true; ctors = []; ext = None } in
  let ctor (env, index) (sp, n) =
    let c, env = Env.bind env (Some ("%" ^ n)) Many token (ValCtor ([], special_term)) in
    let ctor = { V.cname = "%" ^ n; cid = c; index; arity = 0; adt } in
    let env = Env.set_state env c (Env.Const (V.VCtorFn ctor)) in
    ((env, index + 1), (sp, n, c, ctor))
  in
  let (env, _), ctors = List.fold_left_map ctor (env, 0) Special.all in
  adt.ctors <- List.map (fun (_, _, _, c) -> c) ctors;
  let matchable = Matchable (Enum, Var special, List.map (fun (_, _, c, _) -> (Many, Var c)) ctors) in
  let m, env = Env.bind env None Many (Env.Const (V.VMatchable adt)) matchable in
  let env = Env.merge_opens (Env.forcing (Env.opens_add env m)) in
  ( List.map (fun (sp, _, c, _) -> (c, sp)) ctors,
    List.fold_left
      (fun env (_, n, c, ctor) ->
        snd (Env.bind env ~rule:(App (Var c, [])) (Some n) Many (Env.Const (V.VCtor (ctor, []))) special_term))
      env ctors )
