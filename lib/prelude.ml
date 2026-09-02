open Term
module V = Value

let token = Env.Const V.VToken
let ty name sg = { name = Some name; subterm = false; mult = Erased; sg = Ty sg }

let env = Env.empty
let univ, env = Env.bind env ~rigid:true (Some "Univ") Erased token (TyCtor [])
let type_term = App (Var univ, [])
let type_, env = Env.bind env ~rule:type_term (Some "Type") Erased token type_term
let level, env = Env.bind env ~rigid:true (Some "Level") Erased token (TyCtor [])
let level_term = App (Var level, [])

let heterogeneous = [ ty "A" type_term; ty "a" (Bound 0); ty "B" type_term; ty "b" (Bound 0) ]

let predates, env =
  Env.bind env ~rigid:true (Some "Predates") Erased token (TyCtor [ ty "A" type_term; ty "a" (Bound 0); ty "l" level_term ])

let subterm, env = Env.bind env ~rigid:true (Some "Subterm") Erased token (TyCtor heterogeneous)
let coercible, env = Env.bind env ~rigid:true (Some "Coercible") Erased token (TyCtor heterogeneous)

let special, env = Env.bind env ~rigid:true (Some "Special") Erased token (TyCtor [])
let special_term = App (Var special, [])

let env =
  let adt = { V.tname = "Special"; tagged = true; ctors = []; ext = None } in
  let ctor (env, index) (sp, n) =
    let c, env = Env.bind env ~rigid:true (Some ("%" ^ n)) Many token (ValCtor ([], special_term)) in
    let ctor = { V.cname = "%" ^ n; cid = c; index; arity = 0; adt } in
    let env = Env.set_state env c (Env.Const (V.VCtorFn ctor)) in
    Hashtbl.replace Special.table c sp;
    ((env, index + 1), (sp, n, c, ctor))
  in
  let (env, _), ctors = List.fold_left_map ctor (env, 0) Special.all in
  adt.ctors <- List.map (fun (_, _, _, c) -> c) ctors;
  let matchable = Matchable (Enum, Var special, List.map (fun (_, _, c, _) -> (Many, Var c)) ctors) in
  let _, env = Env.bind env None Erased token matchable in
  List.fold_left
    (fun env (_, n, c, ctor) ->
      snd (Env.bind env ~rule:(App (Var c, [])) (Some n) Many (Env.Const (V.VCtor (ctor, []))) special_term))
    env ctors
