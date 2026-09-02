open Term
module IntMap = Value.IntMap

exception Error of Reader.loc * string
exception Contradiction of string

let error loc fmt = Printf.ksprintf (fun s -> raise (Error (loc, s))) fmt

type state = Const of Value.value | Dyn

type entry = { name : string option; mult : mult; state : state; level_born : bool; rigid : bool }
type fact = { ty : term; rule : term option }
type level = Top | At of id

type t = {
  scope : id list;
  entries : entry IntMap.t;
  facts : fact IntMap.t;
  level : level;
  subterms : id list;
  run_pos : bool;
  values : Value.venv;
}

let empty = { scope = []; entries = IntMap.empty; facts = IntMap.empty; level = Top; subterms = []; run_pos = true; values = IntMap.empty }

let counter = ref 0
let fresh () = incr counter; !counter

let entry env x = IntMap.find x env.entries
let fact env x = IntMap.find x env.facts
let name_of env x = match (entry env x).name with Some n -> n | None -> "_" ^ string_of_int x

let set_state env x state =
  let values = match state with Const v -> IntMap.add x v env.values | Dyn -> env.values in
  { env with entries = IntMap.add x { (entry env x) with state } env.entries; values }

let bind env ?(rigid = false) ?(level_born = false) ?(rule = None) name mult state ty =
  let x = fresh () in
  let entries = IntMap.add x { name; mult; state = Dyn; level_born; rigid } env.entries in
  let env = { env with scope = x :: env.scope; entries; facts = IntMap.add x { ty; rule } env.facts } in
  (x, set_state env x state)
let add_rule env x t = { env with facts = IntMap.add x { (fact env x) with rule = Some t } env.facts }

let lookup env name = List.find_opt (fun x -> (entry env x).name = Some name) env.scope

let rec canon env t =
  map_vars (fun _ t -> match t with Var x -> (match (fact env x).rule with Some r -> canon env r | None -> t) | t -> t) 0 t

let type_of env x = canon env (fact env x).ty
let show env t = to_string (name_of env) (canon env t)

let rec unify env depth a b =
  let a = canon env a and b = canon env b in
  if equal a b then env
  else
    let no_binders x t =
      if has_dangling depth t then error 0 "cannot unify %s with %s, which mentions a telescope binder" (name_of env x) (show env t)
    in
    let contradiction () = raise (Contradiction (show env a ^ " vs " ^ show env b)) in
    match (a, b) with
    | Var x, Var y when (entry env x).rigid && (entry env y).rigid -> contradiction ()
    | Var x, Var y ->
        let rigid z = (entry env z).rigid in
        if rigid y || ((not (rigid x)) && x > y) then add_rule env x (Var y) else add_rule env y (Var x)
    | Var x, t | t, Var x ->
        if (entry env x).rigid then contradiction ();
        no_binders x t;
        if occurs x t then raise (Contradiction (name_of env x ^ " occurs in " ^ show env t));
        add_rule env x t
    | App (h, xs), App (k, ys) when List.length xs = List.length ys ->
        List.fold_left2 (fun env a b -> unify env depth a b) (unify env depth h k) xs ys
    | Fn (l, ps, rs), Fn (m, qs, ss) ->
        let env, d = unify_tele (unify env depth l m) depth ps qs in
        fst (unify_tele env d rs ss)
    | TyCtor ps, TyCtor qs -> fst (unify_tele env depth ps qs)
    | ValCtor (ps, r), ValCtor (qs, s) ->
        let env, d = unify_tele env depth ps qs in
        unify env d r s
    | Matchable (d, t, cs), Matchable (e, u, ds) when d = e && List.length cs = List.length ds ->
        List.fold_left2
          (fun env (m, c) (n, d) -> if m <> n then contradiction () else unify env depth c d)
          (unify env depth t u) cs ds
    | Newtype t, Newtype u -> unify env depth t u
    | _ -> contradiction ()

and unify_tele env depth ps qs =
  if not (List.length ps = List.length qs && List.for_all2 (fun p q -> p.subterm = q.subterm && p.mult = q.mult) ps qs)
  then raise (Contradiction "telescopes differ");
  List.fold_left2
    (fun (env, d) p q ->
      match (p.sg, q.sg) with
      | Ty a, Ty b | Is a, Is b -> (unify env d a b, d + 1)
      | _ -> raise (Contradiction "type entry vs is entry"))
    (env, depth) ps qs

let unify env a b = unify env 0 a b
