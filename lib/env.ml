open Term
module IntMap = Value.IntMap

exception Error of Reader.loc * string
exception Contradiction of string Lazy.t
exception Ill_typed of id * term

(* A session's third output channel, beside a program's own stdout and stderr and the message a refusal
   carries: a warning names something legal that the session reads as a mistake. Writing it through a hook is
   what lets the runner capture one, stderr being the process's own here rather than the world's. *)
let warn = ref prerr_string

(* An unsolved meta or an anonymous entry is printed as a marker holding its kind, its id and where it was
   written (name_of). Markers are numbered when a message is printed, in order of first mention and once for the
   whole run, so a number names one thing in every message; each message names where each one stands in a note. *)
let numbering : (string, int) Hashtbl.t = Hashtbl.create 16

let marker kind x at = Printf.sprintf "\001%c%d\001%s\002" kind x (Reader.where "" at)

let hint_line s =
  let sub = ": hint: " in
  let rec go i = i + String.length sub <= String.length s && (String.sub s i (String.length sub) = sub || go (i + 1)) in
  String.starts_with ~prefix:"hint: " s || go 0

let resolve here s =
  let seen = ref [] in
  let number key =
    match Hashtbl.find_opt numbering key with
    | Some n -> n
    | None ->
        let kind k = if k.[0] = '?' || k.[0] = 'k' then k.[0] else '_' in
        let n = 1 + Hashtbl.fold (fun k _ c -> if kind k = kind key then c + 1 else c) numbering 0 in
        Hashtbl.replace numbering key n; n in
  let note (key, (shown, at)) =
    if key.[0] = 'k' then
      let b = String.sub shown 2 (String.length shown - 2) in
      if at = "" then Printf.sprintf "\n%s `%s` is `%s`, shadowed" (Reader.label here "note:") shown b else Printf.sprintf "\n%s: note: `%s` is `%s`, shadowed here" at shown b
    else
    let written, supplied =
      match key.[0] with
      | '?' -> ("the `_` written here", "a `_` the elaborator supplied, not one written in the source")
      | 'm' -> ("the slot of the `_` written here", "")
      | 's' -> ("the slot of the entry bound here", "")
      | _ -> ("anonymous, minted here", "anonymous, minted by the elaborator rather than written in the source") in
    if at = "" then Printf.sprintf "\n%s `%s` is %s" (Reader.label here "note:") shown supplied else Printf.sprintf "\n%s: note: `%s` is %s" at shown written in
  let line s =
    let b = Buffer.create (String.length s) and fresh = ref [] in
    let rec go i =
      match String.index_from_opt s i '\001' with
      | None -> Buffer.add_string b (String.sub s i (String.length s - i))
      | Some j ->
          let k = String.index_from s (j + 1) '\001' and e = String.index_from s (j + 1) '\002' in
          let key = String.sub s (j + 1) (k - j - 1) and at = String.sub s (k + 1) (e - k - 1) in
          let shown = if key.[0] = 'k' then "__" ^ String.sub key 1 (String.length key - 1) else (if key.[0] = '?' then "__?" else "__") ^ string_of_int (number key) in
          if not (List.mem key !seen) then (seen := key :: !seen; fresh := !fresh @ [ (key, (shown, at)) ]);
          Buffer.add_string b (String.sub s i (j - i) ^ shown);
          go (e + 1)
    in
    go 0;
    let notes = String.concat "" (List.map note !fresh) and body = Buffer.contents b in
    if notes <> "" && hint_line body then String.sub notes 1 (String.length notes - 1) ^ "\n" ^ body else body ^ notes
  in
  String.concat "\n" (List.map line (String.split_on_char '\n' s))

type held = Said of string | Shadow of int * int * Reader.loc * Reader.name * Reader.loc
let held : held list ref = ref []

let warn_at l notes fmt =
  let note (nl, m) = Printf.sprintf "\n%s %s" (Reader.labelled "-" nl "note:") m in
  Printf.ksprintf
    (fun s ->
      let here = Reader.where "-" l in
      let s = resolve here (Printf.sprintf "%s %s%s" (Reader.label here "warning:") s (String.concat "" (List.map note notes))) ^ "\n" in
      if !held = [] then !warn s else held := Said s :: !held)
    fmt

(* An error about two places names both: each note is a second location, written on its own line under the
   message as a warning's note is, rather than described in the message's prose (ASSUMPTIONS 194). *)
let error_with ?hint ?(hints = "") loc notes fmt =
  let note s (l, m) = Printf.sprintf "%s\n%s %s" s (Reader.labelled "-" l "note:") m in
  Printf.ksprintf (fun s -> raise (Error (loc, List.fold_left note s notes ^ Option.fold ~none:"" ~some:(( ^ ) "\nhint: ") hint ^ hints))) fmt

let error loc fmt = error_with loc [] fmt

type state = Settled of Value.value | Hypothetical

(* [at] is where the source wrote the binder, for a message about it to point at; an entry the elaborator
   mints for itself carries no position (ASSUMPTIONS 195). A binder bound again from a stored telescope --
   a function's parameter inside its own body -- keeps the position its declaration gave it and is bound
   [~written:false], the declaration having already been read once. *)
type entry = { name : Reader.name option; mult : mult; state : state; minted : id; minted_level : bool; introduced : id; meta : bool; word : bool; temporary : bool; at : Reader.loc; slot : id }
type fact = { ty : term; rule : term option }
type level = Top | At of id

module NameMap = Map.Make (struct
  type t = Reader.name
  let compare a b = match a, b with
    | Reader.Src a, Reader.Src b -> String.compare a b
    | Src _, Gen _ -> -1 | Gen _, Src _ -> 1
    | Gen (m, _), Gen (n, _) -> Z.compare m n
end)

(* The scope (section 5): its entries newest first, and the newest named entry of each name, for lookup. *)
type scope = { ids : id list; named : id NameMap.t }

(* An opened Matchable (section 8) with the names its type holds canonically, the type constructor
   first. The names are read again whenever a variable is ruled out ([add_rule]), so they are current under the
   facts in force; [touched] holds the objects whose names changed since [merge_opens] last ran. *)
type opened = { obj : id; kind : [ `Matchable | `AtFn | `Other ]; names : term list }
type opens = { opened : opened list; touched : id list }

(* A use, with where it was: what the other one of a conflicting pair names. *)
type use = Shared | Consumed

type t = {
  signature : id list;
  ctor_tele : id list;
  in_extern : bool;
  unwarned : bool;
  externs : bool;
  warned : (Reader.loc * string) IntMap.t;
  uses : (use * Reader.loc) IntMap.t;
  captures : id list;
  usage_erased : bool;
  scope : scope;
  entries : entry IntMap.t;
  facts : fact IntMap.t;
  opens : opens;
  level : level;
  subterms : id list;
  enclosing : id option;
  run_pos : bool;
  trusted : fact IntMap.t;
  values : Value.venv;
  pending : (id * Value.code) list;
  prelude : scope;
}

let empty =
  { signature = []; ctor_tele = []; in_extern = false; unwarned = false; externs = false; warned = IntMap.empty; uses = IntMap.empty; captures = []; usage_erased = false; scope = { ids = []; named = NameMap.empty }; entries = IntMap.empty; facts = IntMap.empty; opens = { opened = []; touched = [] }; level = Top; subterms = []; enclosing = None; run_pos = true; trusted = IntMap.empty; values = IntMap.empty; pending = []; prelude = { ids = []; named = NameMap.empty } }

let counter = ref 0
let fresh () = incr counter; !counter
let names : (id, Reader.name) Hashtbl.t = Hashtbl.create 64
let fresh_literal () = - (fresh ())

type literal = { lit : Literal.t; lit_id : id; lit_proof : id option; minted : (id * entry * fact) list }

let literal_rows : (string, literal) Hashtbl.t = Hashtbl.create 64
let literal_of : (id, literal) Hashtbl.t = Hashtbl.create 64
let ladder : Value.value array ref = ref [||]
let () = Reader.handle_name := fun x -> match Hashtbl.find_opt literal_of x, Hashtbl.find_opt names x with Some r, _ -> Literal.spell r.lit | None, Some n -> Literal.name n | None, None -> "_"
let reset_literals () = Hashtbl.reset literal_rows; Hashtbl.reset literal_of; Hashtbl.reset Value.literal_values; ladder := [||]

type item = Fns of (id * Value.fn) list | Final of Value.value * term * string

let trace : item list ref = ref []

let entry env x = IntMap.find x env.entries
let fact env x = IntMap.find x env.facts
let entry_name env x = match (entry env x).name with Some n -> Literal.name n | None -> "__" ^ string_of_int x
let anonymous env x =
  let e = entry env x in
  let owner = if e.slot = x then Some (entry env (x - 1)) else None in
  match owner with
  | Some o when Reader.placed o.at -> marker (if o.meta then 'm' else 's') x o.at
  | _ -> marker (if e.meta then '?' else '_') x e.at

let rec set_state ?minted env x state =
  let values = match state with Settled v -> IntMap.add x v env.values | Hypothetical -> env.values in
  let minted = Option.value minted ~default:x in
  let e = entry env x in
  let env = { env with entries = IntMap.add x { e with state; minted } env.entries; values } in
  match state with
  | Settled v when e.slot <> x && IntMap.mem e.slot env.entries && (entry env e.slot).state = Hypothetical -> set_state env e.slot (Settled (if e.mult = Erased then Value.VToken else v))
  | _ -> env

let record_literal row =
  Hashtbl.replace literal_rows (Literal.key row.lit) row;
  Hashtbl.replace literal_of row.lit_id row;
  List.iter (fun (x, e, _) -> match e.state with Settled v -> Hashtbl.replace Value.literal_values x v | Hypothetical -> ()) row.minted

let enter env row =
  if IntMap.mem row.lit_id env.entries then env
  else List.fold_left (fun env (x, e, f) -> set_state { env with entries = IntMap.add x e env.entries; facts = IntMap.add x f env.facts } x e.state) env row.minted

let present_literals env = List.of_seq (Seq.filter_map (fun (x, _) -> Hashtbl.find_opt literal_of x) (Seq.take_while (fun (x, _) -> x < 0) (IntMap.to_seq env.entries)))
let carry outer inner = List.fold_left enter outer (present_literals inner)

let trusted env = if env.run_pos then env.facts else env.trusted
let leave_run env = { env with run_pos = false; trusted = trusted env }


let lookup env name = NameMap.find_opt name env.scope.named

let distance a b =
  let a = String.lowercase_ascii a and b = String.lowercase_ascii b in
  let d = Array.make_matrix (String.length a + 1) (String.length b + 1) 0 in
  Array.iteri (fun i row -> Array.iteri (fun j _ ->
    row.(j) <-
      if i = 0 || j = 0 then i + j
      else
        let best = min (min d.(i - 1).(j) row.(j - 1) + 1) (d.(i - 1).(j - 1) + Bool.to_int (a.[i - 1] <> b.[j - 1])) in
        if i > 1 && j > 1 && a.[i - 1] = b.[j - 2] && a.[i - 2] = b.[j - 1] then min best (d.(i - 2).(j - 2) + 1) else best) row) d;
  d.(String.length a).(String.length b)

let hint env name =
  let source n = match n with Reader.Src s -> Some s | Gen _ -> None in
  let visible = match source name with None -> [] | Some _ -> List.filter_map (fun x -> Option.bind (entry env x).name (fun n -> if lookup env n = Some x then source n else None)) env.scope.ids in
  let name = Option.value (source name) ~default:"" in
  let best = List.fold_left (fun b n -> min b (distance name n)) max_int visible in
  match List.filter (fun n -> distance name n = best) visible with
  | [] -> ""
  | nearest -> "\nhint: nearest in scope: " ^ String.concat " " nearest

(* Leaving a let's right-hand side: the entries it added since [outer] stay in scope, anonymously (section 27),
   so no fact or open record outlives an entry it mentions. *)
let hide env outer =
  let n = List.length env.scope.ids - List.length outer.scope.ids in
  let added = List.filteri (fun i _ -> i < n) env.scope.ids in
  let entries = List.fold_left (fun es x -> IntMap.add x { (IntMap.find x es) with name = None } es) env.entries added in
  { env with entries; scope = { env.scope with named = outer.scope.named } }

(* The type `(Slot)`, set once the prelude binds its constructor, for the automatic slot every entry is minted
   with, erased where the entry is (section 35). *)
let slot_type = ref (Var (-1))
let atfn_ctor = ref (-1)

(* `(slot-of x)` is read by `x`'s binder and never through `x`'s rule (section 35): a forced `x is y` says
   nothing about where the two words sit. *)
let rec canon env t =
  match t with
  | SlotOf (Var x) when (entry env x).meta ->
      (match canon env (Var x) with
       | Var y when y <> x -> canon env (SlotOf (Var y))
       | Var _ -> t
       | _ -> canon env (Var (entry env x).slot))
  | SlotOf (Var x) -> canon env (Var (entry env x).slot)
  | Var x -> (match (fact env x).rule with Some r -> canon env r | None -> t)
  | t -> map_shallow (canon env) t

let slot_of x = SlotOf (Var x)
let same_slot env a b = equal (canon env a) (canon env b)

let type_of env x = canon env (fact env x).ty

let names_var v = List.exists (function Var c -> c = v | _ -> false)

let opened_of env x =
  match type_of env x with
  | Matchable (_, _, _, t, cs) -> { obj = x; kind = `Matchable; names = t :: List.map snd cs }
  | App (Var c, [ _; f ]) when c = !atfn_ctor -> { obj = x; kind = `AtFn; names = [ f ] }
  | _ -> { obj = x; kind = `Other; names = [] }

(* Whether an `AtFn` proof about [f] is open (section 39), keyed by [f]'s canonical atom as section 8's
   opens are. *)
let atfn_open env f = match canon env f with
  | Var f -> List.exists (fun o -> o.kind = `AtFn && names_var f o.names) env.opens.opened
  | _ -> false

let opens_add env x = { env with opens = { opened = opened_of env x :: env.opens.opened; touched = x :: env.opens.touched } }
let opens_drop env x = { env with opens = { opened = List.filter (fun o -> o.obj <> x) env.opens.opened; touched = List.filter (( <> ) x) env.opens.touched } }

(* A variable ruled out is canonical no longer, so every opened object naming it reads its names again. *)
let opens_ruled env v =
  let names_v o = names_var v o.names in
  let opened = List.map (fun o -> if names_v o then opened_of env o.obj else o) env.opens.opened in
  let touched = List.filter_map (fun o -> if names_v o then Some o.obj else None) env.opens.opened in
  { env with opens = { opened; touched = touched @ env.opens.touched } }

let add_rule env x t = opens_ruled { env with facts = IntMap.add x { (fact env x) with rule = Some t } env.facts } x
(* An atom is shown by the best of the entries equal to it that a reader can name where the message is: a
   numeral or string literal, by its spelling, else the newest binding the scope still names, else its id. What
   canonicalization picks to represent a class is an accident of minting order, so it does not decide the name.
   [namer] chooses once for every atom the canonical [terms] hold, so that several terms print under one naming. *)
(* The built-in name of the special form an entry holds, if it holds one (section 6); set by the elaborator. *)
let special_name : (t -> id -> string option) ref = ref (fun _ _ -> None)
let delegate_ctor = ref (-1)

(* A keyword as the newest name in scope holding its special form spells it, or as `_` and its built-in name,
   placed at the binder that shadows it. *)
let speller ?except env =
  let holds x = match !special_name env x with
    | Some b -> Some b
    | None -> if Some x <> except && equal (canon env (Var x)) (App (Var !Term.univ, [])) then Some Term.universe else None in
  let held = lazy (List.fold_left (fun acc (n, x) -> match holds x with
    | Some b when (match List.assoc_opt b acc with Some (y, _) -> y < x | None -> true) -> (b, (x, n)) :: List.remove_assoc b acc
    | _ -> acc) [] (NameMap.bindings env.scope.named)) in
  fun b -> match List.assoc_opt b (Lazy.force held) with
    | Some (_, n) -> Literal.name n
    | None when b = Term.universe -> b
    | None -> Printf.sprintf "\001k%s\001%s\002" b (match lookup env (Src b) with Some x -> Reader.where "" (entry env x).at | None -> "")

(* A message's own template with each keyword that stands for syntax spelled as [speller] spells it: inside
   backticks, or anywhere in [code], a piece of syntax such as a usage hint. Only a template is respelled,
   never text a name or term was interpolated into, which may hold a binder that merely shares a keyword's name. *)
let respell ?(code = false) ?(escape = false) env s =
  let kw = speller env and b = Buffer.create (String.length s) and tok = Buffer.create 16 and quoted = ref code in
  let flush () =
    let t = Buffer.contents tok in
    Buffer.clear tok;
    Buffer.add_string b
      (if !quoted && List.exists (fun (_, n) -> n = t) Special.all then
         let k = kw t in if escape then String.concat "%%" (String.split_on_char '%' k) else k
       else t) in
  String.iter (fun c -> match c with
    | '`' -> flush (); Buffer.add_char b c; if not code then quoted := not !quoted
    | ' ' | '(' | ')' | '\n' -> flush (); Buffer.add_char b c
    | c -> Buffer.add_char tok c) s;
  flush ();
  Buffer.contents b

(* Help text from lib/specials.txt: its prose as any template, and each usage line, pure syntax, in full. *)
let help env s =
  let usage = "hint: usage: " in
  String.concat "\n" (List.map (fun line ->
    if String.starts_with ~prefix:usage line then usage ^ respell ~code:true env (String.sub line (String.length usage) (String.length line - String.length usage))
    else respell env line) (String.split_on_char '\n' s))

let respelled env fmt = Scanf.format_from_string (respell ~escape:true env (string_of_format fmt)) fmt
let error_in env loc fmt = error_with loc [] (respelled env fmt)
let error_with_in env loc notes fmt = error_with loc notes (respelled env fmt)
let warn_in env loc notes fmt = warn_at loc notes (respelled env fmt)
let sprintf_in env fmt = Printf.sprintf (respelled env fmt)

(* The newest of the candidates [cands] keyed by [a]. *)
let newest cands a = List.fold_left (fun best (a', (x, n)) -> if a' = a && (match best with Some (y, _) -> x > y | None -> true) then Some (x, n) else best) None cands

(* An atom no name reaches may still be what a fetch form yields here, written with a name as its argument:
   each candidate keyed by the canonical atom the form yields. *)
let fetches ?except env =
  let kw = speller env in
  let form head arg = "(" ^ kw head ^ " " ^ arg ^ ")" in
  let named = List.filter_map (fun (n, x) -> if Some x = except then None else match canon env (Var x) with Var a -> Some (a, (x, Literal.name n)) | _ -> None) (NameMap.bindings env.scope.named) in
  let name_for a = Option.map snd (newest named a) in
  List.filter_map (fun (_, (x, n)) -> match canon env (type_of env x) with Fn (Var l, _, _) | UniqueFn (Var l, _, _) -> Some (l, (x, form "level-of" n)) | _ -> None) named
  @ List.filter_map (fun (n, x) -> if Some x = except then None else match canon env (slot_of x) with Var a -> Some (a, (x, form "slot-of" (Literal.name n))) | _ -> None) (NameMap.bindings env.scope.named)
  @ List.filter_map (fun o -> match o.kind, canon env (Var o.obj), type_of env o.obj with
      | `Matchable, Var m, Matchable (_, _, _, Var t, _) -> Option.map (fun n -> (m, (o.obj, form "matchable-of" n))) (name_for t)
      | _ -> None) env.opens.opened
  @ snd (List.fold_left (fun (seen, acc) y -> match (entry env y).name, type_of env y with
      | None, App (Var c, [ _; _; Var g; _; _; _ ]) when c = !delegate_ctor && not (List.mem (c, g) seen) ->
          ((c, g) :: seen, match name_for g with Some n -> (y, (y, form "delegate-of" n)) :: acc | None -> acc)
      | None, App (Var c, [ _; Var g ]) when c = !atfn_ctor && not (List.mem (c, g) seen) ->
          ((c, g) :: seen, match name_for g with Some n -> (y, (y, form "at-fn-of" n)) :: acc | None -> acc)
      | _ -> (seen, acc)) ([], []) env.scope.ids)
  @ List.filter_map (fun r -> Option.bind r.lit_proof (fun p -> match canon env (Var p) with Var a -> Some (a, (p, form "numeral-of" (Literal.spell r.lit))) | _ -> None)) (present_literals env)

(* An entry by its own name, else by the numeral or string literal it is, else by a fetch form yielding it, else as
   an anonymous marker. *)
let name_of env x = match (entry env x).name with
  | Some n -> Literal.name n
  | None ->
    match Hashtbl.find_opt literal_of x with
    | Some { lit = (Literal.Numeral _ | Literal.Str _) as lit; _ } -> Literal.spell lit
    | _ -> (match if (entry env x).meta then None else newest (fetches env) x with Some (_, n) -> n | None -> anonymous env x)

let namer ?except env terms =
  let atoms = List.fold_left (fold_vars (fun _ acc t -> match t with Var x when not (entry env x).meta -> x :: acc | _ -> acc) 0) [] terms in
  let of_atom x = match canon env (Var x) with Var a when List.mem a atoms -> Some a | _ -> if List.mem x atoms then Some x else None in
  let lits = List.filter_map (fun r -> match r.lit with
    | (Literal.Numeral _ | Literal.Str _) as lit -> Option.map (fun a -> (a, (r.lit_id, Literal.spell lit))) (of_atom r.lit_id)
    | _ -> None) (present_literals env) in
  let names = List.filter_map (fun (n, x) -> if Some x = except then None else Option.map (fun a -> (a, (x, Literal.name n))) (of_atom x)) (NameMap.bindings env.scope.named) in
  let fetched = lazy (fetches ?except env) in
  fun x ->
    if (entry env x).meta then anonymous env x
    else match newest lits x, newest names x with
      | Some (_, n), _ | None, Some (_, n) -> n
      | None, None -> (match newest (Lazy.force fetched) x with Some (_, n) -> n | None -> anonymous env x)

let rec shown ?except env t =
  match canon env t with
  | Fn (l, ps, rs) -> Fn (shown ?except env l, shown_tele ?except env ps, shown_tele ?except env rs)
  | UniqueFn (l, ps, rs) -> UniqueFn (shown ?except env l, shown_tele ?except env ps, shown_tele ?except env rs)
  | t -> map_shallow (shown ?except env) t

and shown_tele ?except env tele =
  let place p = match canon env p with
    | Var _ as p -> (match List.find_opt (fun x -> Some x <> except && equal (canon env (slot_of x)) p) (List.rev env.scope.ids) with Some x -> slot_of x | None -> p)
    | p -> p in
  List.map (fun e -> { e with sg = map_sg (shown ?except env) e.sg; place = Option.map place e.place }) tele

(* [except]: an entry not to name anything by, for a message about that entry's own rule. *)
let show ?except env t = let c = shown ?except env t in to_string ~kw:(speller ?except env) (namer ?except env [ c ]) c

(* A telescope's entries under one naming, each entry's terms canonical; the marks are the entries' own. *)
let show_tele ?marks env tele =
  let tele = shown_tele env tele in
  let terms = List.concat_map (fun (e : Term.entry) -> sg_term e.sg :: Option.to_list e.place) tele in
  snd (tele_strings ?marks ~kw:(speller env) (namer env terms) [] tele)

(* A name or term in a message is set off in backticks; a literal already reads as one and is left bare. *)
let tick s = match Literal.classify s with `Lit _ -> s | _ -> "`" ^ s ^ "`"
let tick_name n = tick (Literal.name n)
let spell_binder = function Some n -> Literal.name n | None -> "_"
let qshow env t = tick (show env t)
let qname env x = tick (name_of env x)
let is_meta env x = (entry env x).meta

(* Whether a canonical term still mentions an unsolved meta. *)
let metas env t = List.rev (fold_vars (fun _ xs t -> match t with Var x when is_meta env x && not (List.mem x xs) -> x :: xs | _ -> xs) 0 [] (canon env t))
let has_meta env t = metas env t <> []

let hole_hints env t =
  let line l s = "\n" ^ (if Reader.placed l then Reader.where "-" l ^ ": " else "") ^ "hint: " ^ s in
  let hints x =
    let ty = type_of env x in
    if has_meta env ty || equal ty (App (Var !Term.univ, [])) then ""
    else
      let typed = List.filter_map (fun y -> Option.bind (entry env y).name (fun n -> if lookup env n = Some y && equal (type_of env y) ty then Some (y, n) else None)) env.scope.ids in
      let same (y, _) (z, _) = equal (canon env (Var y)) (canon env (Var z)) in
      let found = List.rev (List.fold_left (fun acc c -> if List.exists (same c) acc then acc else c :: acc) [] typed) in
      let k = List.length found in
      if k = 0 || k > 5 then ""
      else
        line (entry env x).at (Printf.sprintf "%s has type %s, as %s:" (qshow env (Var x)) (qshow env ty) (if k = 1 then "does" else "do"))
        ^ String.concat "" (List.map (fun (y, n) -> let l = (entry env y).at in line l (tick_name n ^ if Reader.placed l then ", bound here" else "")) found) in
  String.concat "" (List.map hints (metas env t))

let unsolved ?(about = ("", [])) loc env t =
  error_with ~hints:(hole_hints env t) loc (snd about) "%scannot infer %s in %s" (fst about) (String.concat " and " (List.map (fun x -> qshow env (Var x)) (metas env t))) (qshow env t)

(* Every solved meta replaced by its solution, the rest of the term as written. *)
let rec metaless env t = match t with (Var x | SlotOf (Var x)) when is_meta env x -> canon env t | t -> map_shallow (metaless env) t

(* A meta (a `_` argument's unification variable, DESIGN.md section 50) enters no scope: nothing reaches it by name or by
   type, and it is solved by unification alone. No other entry's type or rule may mention one still unsolved
   -- the invariant behind the sugar -- except while a telescope with holes is being built ([holes]). *)
let bind env ?minted ?(minted_level = false) ?introduced ?(literal = false) ?(meta = false) ?(word = false) ?(temporary = false) ?(holes = false) ?(at = Reader.nowhere) ?(written = true) ?rule name mult state ty =
  if (not meta) && (not holes) && (has_meta env ty || Option.fold ~none:false ~some:(has_meta env) rule) then
    unsolved Reader.nowhere env (match rule with Some r when has_meta env r -> r | _ -> ty);
  let mint = if literal then fresh_literal else fresh in
  let x = mint () in
  let slot = mint () in
  let entries = IntMap.add slot { name = None; mult = (if mult = Erased then Erased else Many); state = Hypothetical; minted = slot; minted_level = false; introduced = slot; meta = false; word = false; temporary = false; at = Reader.nowhere; slot } env.entries in
  let facts = IntMap.add slot { ty = !slot_type; rule = None } env.facts in
  if written && Reader.placed at then
    Option.iter
      (fun n ->
         match NameMap.find_opt n env.scope.named with
         | Some prior ->
             (* An entry with no position was minted by the built-ins rather than read from a file: a
                special form, an annotation token, or one of the opaque types (section 54). A binder the
                source wrote carries its position even where it is bound again from a stored telescope,
                the telescope entry holding it (Term.entry). *)
             let prior_at = (IntMap.find prior env.entries).at in
             if Reader.placed prior_at then held := Shadow (x, prior, prior_at, n, at) :: !held
             else warn_at at [] "declaration of %s shadows a built-in" (tick_name n)
         | _ -> ())
      name;
  Option.iter (Hashtbl.replace names x) name;
  let entries = IntMap.add x { name; mult; state = Hypothetical; minted = x; minted_level; introduced = Option.value introduced ~default:x; meta; word; temporary; at; slot } entries in
  let scope = if meta || literal then env.scope else { ids = x :: env.scope.ids; named = Option.fold ~none:env.scope.named ~some:(fun n -> NameMap.add n x env.scope.named) name } in
  let env = { env with scope; entries; facts = IntMap.add x { ty; rule } facts } in
  (x, set_state ?minted env x state)

let covers env prior x =
  IntMap.mem x env.entries && IntMap.mem prior env.entries
  && (try canon env (Var x) = canon env (Var prior) with Contradiction _ | Not_found -> false)
  && match ((entry env x).mult, (entry env prior).mult) with Erased, _ -> true | Many, Many -> same_slot env (slot_of x) (slot_of prior) | _ -> false

let report_shadows ?env () =
  let pending = List.rev !held in
  held := [];
  List.iter
    (function
      | Said s -> !warn s
      | Shadow (x, prior, prior_at, n, at) ->
          let hint = match env with Some env when covers env prior x -> [ (at, "using `_` here instead would be equivalent") ] | _ -> [] in
          warn_at at ((prior_at, "shadowed binder is here") :: hint) "declaration of %s shadows a previous binder" (tick_name n))
    pending


(* [opens] holds the Matchables opened so far (section 8), one entry per merged group; nothing
   consults one that is not in it. Constructors one opened Matchable lists are distinct, first-class ones
   included. *)
let listed env x y =
  List.exists (fun o -> match (o.kind, o.names) with `Matchable, _ :: cs -> names_var x cs && names_var y cs | _ -> false) env.opens.opened

(* A Matchable's value, where its entry is Settled (section 29); a Hypothetical one is read when the code runs. *)
let adt_of env x = match (entry env x).state with Settled (Value.VMatchable adt) -> Some adt | _ -> None

(* A match that dispatches at runtime reads its Matchable's value: stamped in where the entry is Settled, else read
   from a non-erased entry still bound. Of the entries one opened group holds, the record keeps the best-ranked:
   one whose ADT the elaborator sees, then a readable one, then any. *)
let readable env x = adt_of env x <> None || ((entry env x).mult = Many && List.mem x env.scope.ids)
let rank env x = if adt_of env x <> None then 0 else if readable env x then 1 else 2

(* Two atoms equated, forcing (section 7): a contradiction where one opened Matchable lists both; otherwise the
   newer becomes an alias of the older, and the two must have one signature. Whoever forces then restores
   [merge_opens]'s invariant, which is how two declared types are told apart exactly by their Matchables, never
   by a name's identity (section 8). Solving (not forcing): only a meta may be bound, and the two sides must
   otherwise be identical; a meta against a meta binds the newer. *)
let rec infer env loc t =
  match t with
  | Var x -> type_of env x
  | App (h, args) -> (
      match canon env (infer env loc h) with
      | TyCtor _ -> App (Var !univ, [])
      | ValCtor (_, r) -> instantiate (List.rev args) r
      | ty -> error loc "%s has type %s and cannot be applied" (qshow env h) (qshow env ty))
  | Fn _ | UniqueFn _ | TyCtor _ | ValCtor _ | Matchable _ | Cell _ -> App (Var !univ, [])
  | SlotOf _ -> !slot_type
  | Bound _ -> error loc "internal: dangling binder"

let rec unify_in ?(force = false) env a b =
  let a = canon env a and b = canon env b in
  if equal a b then env
  else
    let contradiction () = raise (Contradiction (lazy (qshow env a ^ " vs " ^ qshow env b))) in
    let assign x t =
      if has_dangling t then contradiction ();
      if occurs x t then raise (Contradiction (lazy (qname env x ^ " occurs in " ^ qshow env t)));
      let env = add_rule env x t in
      if force then env else try unify_in env (type_of env x) (infer env Reader.nowhere t) with Contradiction _ -> raise (Ill_typed (x, t))
    in
    match (a, b) with
    | Var x, Var y when is_meta env x || is_meta env y ->
        let x, y = if is_meta env x && ((not (is_meta env y)) || x > y) then (x, y) else (y, x) in
        assign x (Var y)
    | Var x, Var y when force && listed env x y -> contradiction ()
    | Var x, Var y when force ->
        let age z = (z >= 0, abs z) in
        let x, y = if age x > age y then (x, y) else (y, x) in
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

(* [x] is at the slot [p]: a rule on its automatic slot (section 35). While the slot is still the fresh atom it was
   minted as, with no rule, named by no opened object and absent from [p], the rule is added outright, which
   is what forcing it would do; a slot a forcing has already ruled is forced as any atom is. *)
let place env x p =
  let s = (entry env x).slot in
  if (fact env s).rule <> None then unify_in ~force:true env (Var s) p
  else match canon env p with Var t when t = s -> env | t -> { env with facts = IntMap.add s { (fact env s) with rule = Some t } env.facts }
let placed env x = function Some p -> place env x p | None -> env

(* A forcing leaves the opened objects it touched to be merged, so its environment comes back as [forced], which
   only [merge_opens] reads an environment out of; the next forcing is on the [forced]. *)
type forced = Forcing of t

let forcing env = Forcing env
let unify_force (Forcing env) a b = Forcing (unify_in ~force:true env a b)

(* At most one opened Matchable names a given type constructor or value constructor
   (section 8): two that would are unified, forcing, and the better-ranked entry
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

let join_uses a b =
  IntMap.union (fun _ (x, lx) (y, ly) -> Some (if x = Consumed then (x, lx) else if y = Consumed then (y, ly) else (x, lx))) a b

let misuse demand supply =
  if demand <> Erased && supply = Erased then Some "used in a non-erased position"
  else if demand = Unique && supply = Many then Some "used at unique"
  else if demand = Many && supply = Unique then Some "used at many without `share`"
  else None

let check_mult env loc explain demand supply =
  if not env.usage_erased then Option.iter (fun how -> let notes, what = explain () in error_with loc notes "%s, %s" what (respell env how)) (misuse demand supply)

let declared env ?(how = "") x =
  let e = entry env x in
  if Reader.placed e.at then [ (e.at, Printf.sprintf "%s is declared%s here" (qname env x) how) ] else []

let kind_name env ty =
  match canon env ty with Fn _ -> "function" | UniqueFn _ -> "unique function" | ValCtor _ -> "value constructor" | TyCtor _ -> "type constructor" | _ -> "value"

let declared_as env x = declared env x |> List.map (fun (l, m) -> (l, kind_name env (type_of env x) ^ " " ^ m))

type binder_kind = Let of int * bool | Param | Field | Optional | Definition
type tracked = { binder : Reader.name; at : Reader.loc; kind : binder_kind; mult : mult; erased_scope : bool }

let warn_unused = ref false
type ref_state = Level of int | Target of id

let tracked : (id, tracked) Hashtbl.t = Hashtbl.create 64
let refs : (id, ref_state) Hashtbl.t = Hashtbl.create 64

let level x = match Hashtbl.find_opt refs x with
  | Some (Level n) -> n
  | Some (Target y) -> (match Hashtbl.find_opt refs y with Some (Level n) -> n | _ -> 0)
  | None -> 0

let pend x = if !warn_unused && not (Hashtbl.mem refs x) then Hashtbl.replace refs x (Level 0)

let track env kind x =
  if !warn_unused then
    let e = entry env x in
    match e.name with
    | Some binder when Reader.placed e.at -> Hashtbl.replace tracked x { binder; at = e.at; kind; mult = e.mult; erased_scope = env.usage_erased }; pend x
    | _ -> ()

let stand_for x y = if !warn_unused then (Hashtbl.replace refs y (Level (max (level x) (level y))); Hashtbl.replace refs x (Target y))

let reset_tracking () = Hashtbl.reset tracked; Hashtbl.reset refs

let refer ?(live = false) x =
  if !warn_unused then
    match Hashtbl.find_opt refs x with
    | None -> ()
    | Some s ->
        let x = match s with Target y -> y | Level _ -> x and want = if live then 2 else 1 in
        if level x < want then Hashtbl.replace refs x (Level want)

let use env loc ?(sharing = false) ?written ?made mult x =
  refer ~live:(mult <> Erased && not env.usage_erased) x;
  if mult = Erased || env.usage_erased then env else
  let e = entry env x in
  let explain () = match made, Hashtbl.find_opt literal_of x with
    | (None | Some Many), Some r -> ([], Printf.sprintf "%s, a literal and so %s" (tick (Option.value written ~default:(Literal.key r.lit))) (mult_name e.mult))
    | Some d, _ -> ([], Printf.sprintf "a handle to %s, made `%s`" (qshow env (Var x)) (speller env (mult_name d)))
    | None, None -> (declared env x, Printf.sprintf "%s, declared `%s`" (qname env x) (speller env (mult_name e.mult))) in
  check_mult env loc explain mult (if sharing && mult = Many then Many else Option.value made ~default:e.mult);
  if e.mult <> Unique then env else (
    if mult = Unique && List.mem x env.captures then error_in env loc "`def-fns` cannot capture %s at unique" (qname env x);
    (match IntMap.find_opt x env.uses with
     | Some (Consumed, pl) -> error_with loc [ (pl, "already used at unique here") ] "unique value %s has conflicting non-erased uses" (qname env x)
     | Some (Shared, pl) when mult = Unique -> error_with loc [ (pl, "already shared here") ] "unique value %s has conflicting non-erased uses" (qname env x)
     | _ -> ());
    { env with uses = IntMap.add x ((if mult = Unique then Consumed else Shared), loc) env.uses })
