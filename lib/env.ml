open Term
module IntMap = Value.IntMap

exception Error of Reader.loc * string
exception Contradiction of string

let error loc fmt = Printf.ksprintf (fun s -> raise (Error (loc, s))) fmt

type state = Const of Value.value | Dyn

type entry = { name : string option; mult : mult; state : state; minted_level : bool; meta : bool; word : bool; temporary : bool }
type fact = { ty : term; rule : term option }
type level = Top | At of id

module StringMap = Map.Make (String)

(* The scope (section 3): its entries newest first, and the newest named entry of each name, for lookup. *)
type scope = { ids : id list; named : id StringMap.t }

(* An opened Matchable (section 19) with the names its type holds canonically, the type constructor
   first. The names are read again whenever a variable is ruled out ([add_rule]), so they are current under the
   facts in force; [touched] holds the objects whose names changed since [merge_opens] last ran. *)
type opened = { obj : id; kind : [ `Matchable | `Other ]; names : term list }
type opens = { opened : opened list; touched : id list }

type use = Shared | Consumed

type t = {
  locations : id IntMap.t;
  signature : id list;
  in_extern : bool;
  uses : use IntMap.t;
  captures : id list;
  usage_erased : bool;
  scope : scope;
  entries : entry IntMap.t;
  facts : fact IntMap.t;
  opens : opens;
  level : level;
  subterms : id list;
  run_pos : bool;
  values : Value.venv;
  prelude : scope;
  literals : (string * (id * id option)) list;
}

let empty =
  { locations = IntMap.empty; signature = []; in_extern = false; uses = IntMap.empty; captures = []; usage_erased = false; scope = { ids = []; named = StringMap.empty }; entries = IntMap.empty; facts = IntMap.empty; opens = { opened = []; touched = [] }; level = Top; subterms = []; run_pos = true; values = IntMap.empty; prelude = { ids = []; named = StringMap.empty }; literals = [] }

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


let lookup env name = StringMap.find_opt name env.scope.named

(* Leaving a let's right-hand side: the entries it added since [outer] stay in scope, anonymously (section 16),
   so no fact or open record outlives an entry it mentions. *)
let hide env outer =
  let n = List.length env.scope.ids - List.length outer.scope.ids in
  let added = List.filteri (fun i _ -> i < n) env.scope.ids in
  let entries = List.fold_left (fun es x -> IntMap.add x { (IntMap.find x es) with name = None; word = (let e = IntMap.find x es in e.word && not e.temporary) } es) env.entries added in
  { env with entries; scope = { env.scope with named = outer.scope.named } }

let rec location env x = match IntMap.find_opt x env.locations with Some y -> location env y | None -> x
let rec location_term env = function
  | Var x when (entry env x).meta -> (match (fact env x).rule with Some r -> location_term env r | None -> Var x)
  | Var x -> Var (location env x)
  | t -> t
let at_merge env a b =
  match location_term env a, location_term env b with
  | Var x, Var y when x <> y -> { env with locations = IntMap.add (max x y) (min x y) env.locations }
  | a, b when equal a b -> env
  | _ -> raise (Contradiction "locations must be variables")
let at_equal env a b = equal (location_term env a) (location_term env b)

let rec canon env t =
  map_vars ~location:(fun _ t -> location_term env t) (fun _ t -> match t with Var x -> (match (fact env x).rule with Some r -> canon env r | None -> t) | t -> t) 0 t

let type_of env x = canon env (fact env x).ty

let opened_of env x =
  match type_of env x with
  | Matchable (_, _, _, t, cs) -> { obj = x; kind = `Matchable; names = t :: List.map snd cs }
  | _ -> { obj = x; kind = `Other; names = [] }

let opens_add env x = { env with opens = { opened = opened_of env x :: env.opens.opened; touched = x :: env.opens.touched } }
let opens_drop env x = { env with opens = { opened = List.filter (fun o -> o.obj <> x) env.opens.opened; touched = List.filter (( <> ) x) env.opens.touched } }

(* A variable ruled out is canonical no longer, so every opened object naming it reads its names again. *)
let opens_ruled env v =
  let names_v o = List.mem (Var v) o.names in
  let opened = List.map (fun o -> if names_v o then opened_of env o.obj else o) env.opens.opened in
  let touched = List.filter_map (fun o -> if names_v o then Some o.obj else None) env.opens.opened in
  { env with opens = { opened; touched = touched @ env.opens.touched } }

let add_rule env x t = opens_ruled { env with facts = IntMap.add x { (fact env x) with rule = Some t } env.facts } x
let show env t = to_string (name_of env) (canon env t)
let is_meta env x = (entry env x).meta

(* Whether a canonical term still mentions an unsolved meta. *)
let has_meta env t = fold_vars (fun _ b t -> b || (match t with Var x -> is_meta env x | _ -> false)) 0 false (canon env t)

(* Every solved meta replaced by its solution, the rest of the term as written. *)
let metaless env t = map_vars (fun _ t -> match t with Var x when is_meta env x -> canon env t | t -> t) 0 t

(* A meta (a `_` argument's unification variable, SUGAR.md 6) enters no scope: nothing reaches it by name or by
   type, and it is solved by unification alone. No other entry's type or rule may mention one still unsolved
   -- the invariant behind the sugar -- except while a telescope with holes is being built ([holes]). *)
let bind env ?(minted_level = false) ?(meta = false) ?(word = false) ?(temporary = false) ?(holes = false) ?rule name mult state ty =
  Option.iter (fun n -> if Literal.classify n <> `Name then error 0 "%s is a literal, not a name" n) name;
  if (not meta) && (not holes) && (has_meta env ty || Option.fold ~none:false ~some:(has_meta env) rule) then
    error 0 "cannot infer the _ in %s" (show env (match rule with Some r when has_meta env r -> r | _ -> ty));
  let x = fresh () in
  Option.iter (Hashtbl.replace names x) name;
  let entries = IntMap.add x { name; mult; state = Dyn; minted_level; meta; word; temporary } env.entries in
  let scope = if meta then env.scope else { ids = x :: env.scope.ids; named = Option.fold ~none:env.scope.named ~some:(fun n -> StringMap.add n x env.scope.named) name } in
  let env = { env with scope; entries; facts = IntMap.add x { ty; rule } env.facts } in
  (x, set_state env x state)


(* [opens] holds the Matchables opened so far (section 19), one entry per merged group; nothing
   consults one that is not in it. Constructors one opened Matchable lists are distinct, first-class ones
   included. *)
let listed env x y =
  List.exists (fun o -> match (o.kind, o.names) with `Matchable, _ :: cs -> List.mem (Var x) cs && List.mem (Var y) cs | _ -> false) env.opens.opened

(* A Matchable's value, where its entry is Const (section 34); a Dyn one is read when the code runs. *)
let adt_of env x = match (entry env x).state with Const (Value.VMatchable adt) -> Some adt | _ -> None

(* A match that dispatches at runtime reads its Matchable's value: stamped in where the entry is Const, else read
   from a non-erased entry still bound. Of the entries one opened group holds, the record keeps the best-ranked:
   one whose ADT the elaborator sees, then a readable one, then any. *)
let readable env x = adt_of env x <> None || ((entry env x).mult = Many && List.mem x env.scope.ids)
let rank env x = if adt_of env x <> None then 0 else if readable env x then 1 else 2

(* Two atoms equated, forcing (section 18): a contradiction where one opened Matchable lists both; otherwise the
   newer becomes an alias of the older, and the two must have one signature. Whoever forces then restores
   [merge_opens]'s invariant, which is how two declared types are told apart exactly by their Matchables, never
   by a name's identity (section 19). Solving (not forcing): only a meta may be bound, and the two sides must
   otherwise be identical; a meta against a meta binds the newer. *)
let rec unify_in ?(force = false) env a b =
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
    | SlotHolds a, SlotHolds b -> if force then at_merge env a b else contradiction ()
    | Var x, Var y when is_meta env x || is_meta env y ->
        let x, y = if is_meta env x && ((not (is_meta env y)) || x > y) then (x, y) else (y, x) in
        assign x (Var y)
    | Var x, Var y when force && listed env x y -> contradiction ()
    | Var x, Var y when force ->
        let x, y = if x > y then (x, y) else (y, x) in
        let signature z = match type_of env z with (TyCtor _ | ValCtor _) as s -> Some s | _ -> None in
        let sx, sy = (signature x, signature y) in
        let env = add_rule env x (Var y) in
        (match (sx, sy) with Some s, Some s' -> unify_in ~force env s s' | _ -> env)
    | Var x, t when force || is_meta env x -> assign x t
    | t, Var x when force || is_meta env x -> assign x t
    | _ when blank a = blank b -> List.fold_left2 (fun env (_, x) (_, y) -> unify_in ~force env x y) env (parts a) (parts b)
    | _ -> contradiction ()

(* Solving, for a check. *)
let unify env a b = unify_in env a b

(* A forcing leaves the opened objects it touched to be merged, so its environment comes back as [forced], which
   only [merge_opens] reads an environment out of; the next forcing is on the [forced]. *)
type forced = Forcing of t

let forcing env = Forcing env
let unify_force (Forcing env) a b = Forcing (unify_in ~force:true env a b)

(* At most one opened Matchable names a given type constructor or value constructor
   (section 19): two that would are unified, forcing, and the better-ranked entry
   kept, the older on a tie, until no two name one thing. Restored after every forcing (Elab.refine, Elab.open_adt).
   Failure is a Contradiction. Only a pair with a touched object can share, the rest having been disjoint when
   the invariant last held, so the pair sought is the newest object sharing a name with an older one (of a
   smaller id, the objects being opened in id order) and the newest such older one, among those pairs. *)
let rec merge_opens (Forcing env) =
  match env.opens.touched with
  | [] -> env
  | touched -> (
      let env = { env with opens = { env.opens with touched = [] } } in
      let shares x y = x.kind = y.kind && x.kind <> `Other && List.exists (fun n -> List.mem n y.names) x.names in
      let is_touched o = List.mem o.obj touched in
      let touched_objs = List.filter is_touched env.opens.opened in
      let rec pair = function
        | [] -> None
        | x :: rest -> (
            let among = if is_touched x then rest else List.filter (fun y -> y.obj < x.obj) touched_objs in
            match List.find_opt (shares x) among with Some y -> Some (x.obj, y.obj) | None -> pair rest)
      in
      match pair env.opens.opened with
      | None -> env
      | Some (newer, older) ->
          let (Forcing env) = unify_force (Forcing env) (type_of env newer) (type_of env older) in
          let drop = if rank env newer < rank env older then older else newer in
          merge_opens (Forcing (opens_drop { env with opens = { env.opens with touched = env.opens.touched @ touched } } drop)))

let join_uses a b = IntMap.union (fun _ x y -> Some (if x = Consumed || y = Consumed then Consumed else Shared)) a b

let use env loc ?(sharing = false) mult x =
  if mult = Erased || env.usage_erased then env else
  let e = entry env x in
  if e.mult = Erased then error loc "erased value %s : %s used in a non-erased position" (show env (Var x)) (show env (type_of env x));
  if mult = Unique && e.mult <> Unique then error loc "many value %s used at unique" (name_of env x);
  if e.mult <> Unique then env else (
    if mult = Many && not sharing then error loc "unique value %s needs an explicit share" (name_of env x);
    if mult = Unique && List.mem x env.captures then error loc "def-fns cannot capture %s at unique" (name_of env x);
    let prior = IntMap.find_opt x env.uses in
    if prior = Some Consumed || (mult = Unique && prior = Some Shared) then
      error loc "unique value %s has conflicting non-erased uses" (name_of env x);
    { env with uses = IntMap.add x (if mult = Unique then Consumed else Shared) env.uses })
