open Term
module IntMap = Value.IntMap

exception Error of Reader.loc * string
exception Contradiction of string

let error loc fmt = Printf.ksprintf (fun s -> raise (Error (loc, s))) fmt

type state = Const of Value.value | Dyn

type entry = { name : string option; mult : mult; state : state; minted_level : bool; meta : bool }
type fact = { ty : term; rule : term option }
type level = Top | At of id

type t = {
  scope : id list;
  entries : entry IntMap.t;
  facts : fact IntMap.t;
  opens : id list;
  level : level;
  subterms : id list;
  run_pos : bool;
  values : Value.venv;
  prelude : id list;
  literals : (string * (id * id option)) list;
}

let empty =
  { scope = []; entries = IntMap.empty; facts = IntMap.empty; opens = []; level = Top; subterms = []; run_pos = true; values = IntMap.empty; prelude = []; literals = [] }

let counter = ref 0
let fresh () = incr counter; !counter
let names : (id, string) Hashtbl.t = Hashtbl.create 64

type item = Fns of (id * Value.fn) list | Final of Value.value * term * string

let trace : item list ref = ref []

let entry env x = IntMap.find x env.entries
let fact env x = IntMap.find x env.facts
let name_of env x = match entry env x with { name = Some n; _ } -> n | { meta = true; _ } -> "_" | _ -> "_" ^ string_of_int x

let set_state env x state =
  let values = match state with Const v -> IntMap.add x v env.values | Dyn -> env.values in
  { env with entries = IntMap.add x { (entry env x) with state } env.entries; values }

let add_rule env x t = { env with facts = IntMap.add x { (fact env x) with rule = Some t } env.facts }

let lookup env name = List.find_opt (fun x -> (entry env x).name = Some name) env.scope

(* Leaving a let's right-hand side: the entries it added since [outer] stay in scope, anonymously (section 16),
   so no fact or open record outlives an entry it mentions. *)
let hide env outer =
  let added = List.filteri (fun i _ -> i < List.length env.scope - List.length outer.scope) env.scope in
  { env with entries = List.fold_left (fun es x -> IntMap.add x { (IntMap.find x es) with name = None } es) env.entries added }

let rec canon env t =
  map_vars (fun _ t -> match t with Var x -> (match (fact env x).rule with Some r -> canon env r | None -> t) | t -> t) 0 t

let type_of env x = canon env (fact env x).ty
let show env t = to_string (name_of env) (canon env t)
let is_meta env x = (entry env x).meta

(* Whether a canonical term still mentions an unsolved meta. *)
let has_meta env t = fold_vars (fun _ b t -> b || (match t with Var x -> is_meta env x | _ -> false)) 0 false (canon env t)

(* Every solved meta replaced by its solution, the rest of the term as written. *)
let metaless env t = map_vars (fun _ t -> match t with Var x when is_meta env x -> canon env t | t -> t) 0 t

(* A meta (a `_` argument's unification variable, SUGAR.md 6) enters no scope: nothing reaches it by name or by
   type, and it is solved by unification alone. No other entry's type or rule may mention one still unsolved
   -- the invariant behind the sugar -- except while a telescope with holes is being built ([holes]). *)
let bind env ?(minted_level = false) ?(meta = false) ?(holes = false) ?rule name mult state ty =
  Option.iter (fun n -> if Literal.classify n <> `Name then error 0 "%s is a literal, not a name" n) name;
  if (not meta) && (not holes) && (has_meta env ty || Option.fold ~none:false ~some:(has_meta env) rule) then
    error 0 "cannot infer the _ in %s" (show env (match rule with Some r when has_meta env r -> r | _ -> ty));
  let x = fresh () in
  Option.iter (Hashtbl.replace names x) name;
  let entries = IntMap.add x { name; mult; state = Dyn; minted_level; meta } env.entries in
  let scope = if meta then env.scope else x :: env.scope in
  let env = { env with scope; entries; facts = IntMap.add x { ty; rule } env.facts } in
  (x, set_state env x state)


(* [opens] holds the Matchables and Newtypes opened so far (section 19), one entry per merged group; nothing
   consults one that is not in it. Constructors one opened Matchable lists are distinct, first-class ones
   included. *)
let listed env x y =
  let lists cs z = List.exists (fun (_, c) -> c = Var z) cs in
  List.exists (fun m -> match type_of env m with Matchable (_, _, cs) -> lists cs x && lists cs y | _ -> false) env.opens

(* A Matchable's value, where its entry is Const (section 34); a Dyn one is read when the code runs. *)
let adt_of env x = match (entry env x).state with Const (Value.VMatchable adt) -> Some adt | _ -> None

(* A match that dispatches at runtime reads its Matchable's value: stamped in where the entry is Const, else read
   from a non-erased entry still bound. Of the entries one opened group holds, the record keeps the best-ranked:
   one whose ADT the elaborator sees, then a readable one, then any. *)
let readable env x = adt_of env x <> None || ((entry env x).mult = Many && List.mem x env.scope)
let rank env x = if adt_of env x <> None then 0 else if readable env x then 1 else 2

(* The type constructor and constructors an opened object names, canonically: what relates two opens. *)
let opened_names env x =
  match type_of env x with Matchable (_, t, cs) -> `Matchable (t :: List.map snd cs) | Newtype c -> `Newtype [ c ] | _ -> `Other []

(* Two atoms equated, forcing (section 18): a contradiction where one opened Matchable lists both; otherwise the
   newer becomes an alias of the older, and the two must have one signature. Whoever forces then restores
   [merge_opens]'s invariant, which is how two declared types are told apart exactly by their Matchables, never
   by a name's identity (section 19). Solving (not forcing): only a meta may be bound, and the two sides must
   otherwise be identical; a meta against a meta binds the newer. *)
let rec unify ?(force = false) env a b =
  let a = canon env a and b = canon env b in
  if equal a b then env
  else
    let contradiction () = raise (Contradiction (show env a ^ " vs " ^ show env b)) in
    let assign x t =
      if has_dangling t then contradiction ();
      if occurs x t then raise (Contradiction (name_of env x ^ " occurs in " ^ show env t));
      add_rule env x t
    in
    match (a, b) with
    | Var x, Var y when is_meta env x || is_meta env y ->
        let x, y = if is_meta env x && ((not (is_meta env y)) || x > y) then (x, y) else (y, x) in
        assign x (Var y)
    | Var x, Var y when force && listed env x y -> contradiction ()
    | Var x, Var y when force ->
        let x, y = if x > y then (x, y) else (y, x) in
        let signature z = match type_of env z with (TyCtor _ | ValCtor _) as s -> Some s | _ -> None in
        let sx, sy = (signature x, signature y) in
        let env = add_rule env x (Var y) in
        (match (sx, sy) with Some s, Some s' -> unify ~force env s s' | _ -> env)
    | Var x, t when force || is_meta env x -> assign x t
    | t, Var x when force || is_meta env x -> assign x t
    | _ when blank a = blank b -> List.fold_left2 (fun env (_, x) (_, y) -> unify ~force env x y) env (parts a) (parts b)
    | _ -> contradiction ()

(* At most one opened Matchable names a given type constructor or value constructor, and at most one opened
   Newtype a given constructor (section 19): two that would are unified, forcing, and the better-ranked entry
   kept, the older on a tie, until no two name one thing. Restored after every forcing (Elab.refine, Elab.open_adt).
   Failure is a Contradiction. *)
let rec merge_opens env =
  let shares x y =
    match (opened_names env x, opened_names env y) with
    | `Matchable nx, `Matchable ny | `Newtype nx, `Newtype ny -> List.exists (fun n -> List.mem n ny) nx
    | _ -> false
  in
  let rec pair = function [] -> None | x :: rest -> (match List.find_opt (shares x) rest with Some y -> Some (x, y) | None -> pair rest) in
  match pair env.opens with
  | None -> env
  | Some (newer, older) ->
      let env = unify ~force:true env (type_of env newer) (type_of env older) in
      let drop = if rank env newer < rank env older then older else newer in
      merge_opens { env with opens = List.filter (( <> ) drop) env.opens }
