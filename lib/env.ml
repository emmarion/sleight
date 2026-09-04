open Term
module IntMap = Value.IntMap

exception Error of Reader.loc * string
exception Contradiction of string

let error loc fmt = Printf.ksprintf (fun s -> raise (Error (loc, s))) fmt

type state = Const of Value.value | Dyn

type entry = { name : string option; mult : mult; state : state; minted_level : bool }
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
  prelude : id list;
  literals : (string * (id * id option)) list;
}

let empty =
  { scope = []; entries = IntMap.empty; facts = IntMap.empty; level = Top; subterms = []; run_pos = true; values = IntMap.empty; prelude = []; literals = [] }

let counter = ref 0
let fresh () = incr counter; !counter
let names : (id, string) Hashtbl.t = Hashtbl.create 64

type item = Fns of (id * Value.fn) list | Final of Value.value * term * string

let trace : item list ref = ref []

let entry env x = IntMap.find x env.entries
let fact env x = IntMap.find x env.facts
let name_of env x = match (entry env x).name with Some n -> n | None -> "_" ^ string_of_int x

let set_state env x state =
  let values = match state with Const v -> IntMap.add x v env.values | Dyn -> env.values in
  { env with entries = IntMap.add x { (entry env x) with state } env.entries; values }

let bind env ?(minted_level = false) ?rule name mult state ty =
  Option.iter (fun n -> if Literal.classify n <> `Name then error 0 "%s is a literal, not a name" n) name;
  let x = fresh () in
  Option.iter (Hashtbl.replace names x) name;
  let entries = IntMap.add x { name; mult; state = Dyn; minted_level } env.entries in
  let env = { env with scope = x :: env.scope; entries; facts = IntMap.add x { ty; rule } env.facts } in
  (x, set_state env x state)
let add_rule env x t = { env with facts = IntMap.add x { (fact env x) with rule = Some t } env.facts }

let lookup env name = List.find_opt (fun x -> (entry env x).name = Some name) env.scope

let rec canon env t =
  map_vars (fun _ t -> match t with Var x -> (match (fact env x).rule with Some r -> canon env r | None -> t) | t -> t) 0 t

let type_of env x = canon env (fact env x).ty
let show env t = to_string (name_of env) (canon env t)

(* Constructors one Matchable in scope lists are distinct (section 19), first-class ones included. *)
let listed env x y =
  let lists cs z = List.exists (fun (_, c) -> c = Var z) cs in
  List.exists (fun m -> match type_of env m with Matchable (_, _, cs) -> lists cs x && lists cs y | _ -> false) env.scope

(* The Matchable in scope a type constructor heads, if any. *)
let matchable_of env t =
  List.find_map (fun m -> match type_of env m with Matchable (_, Var t', _) as ty when t' = t -> Some ty | _ -> None) env.scope

(* Two atoms equated: a contradiction where one Matchable lists both; otherwise the newer becomes an alias of
   the older, and what follows is checked -- the two must have one signature, and type constructors heading
   Matchables must head one Matchable -- so two declared types are told apart exactly by their Matchables,
   never by a name's identity (section 19). *)
let rec unify env a b =
  let a = canon env a and b = canon env b in
  if equal a b then env
  else
    let contradiction () = raise (Contradiction (show env a ^ " vs " ^ show env b)) in
    match (a, b) with
    | Var x, Var y when listed env x y -> contradiction ()
    | Var x, Var y ->
        let x, y = if x > y then (x, y) else (y, x) in
        let signature z = match type_of env z with (TyCtor _ | ValCtor _) as s -> Some s | _ -> None in
        let sx, sy = (signature x, signature y) and mx, my = (matchable_of env x, matchable_of env y) in
        let env = add_rule env x (Var y) in
        let env = match (sx, sy) with Some s, Some s' -> unify env s s' | _ -> env in
        (match (mx, my) with Some m, Some m' -> unify env m m' | _ -> env)
    | Var x, t | t, Var x ->
        if has_dangling t then contradiction ();
        if occurs x t then raise (Contradiction (name_of env x ^ " occurs in " ^ show env t));
        add_rule env x t
    | _ when blank a = blank b -> List.fold_left2 (fun env (_, x) (_, y) -> unify env x y) env (parts a) (parts b)
    | _ -> contradiction ()
