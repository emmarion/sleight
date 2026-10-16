(* `dump-context` (ASSUMPTIONS 196): stops elaboration where it is written and reports, as one error, what the
   checker knows there -- the goal, the position, every entry in scope with its canonical type and rule, the
   unique binders' uses, the at-database, the opened objects and the literals with rules. Everything is shown
   canonically, through Env.show, so a name is one the reader can write where the form stands. *)
open Term
open Env
module V = Value

type goal = Statement | Type | Values of mult list * tele option

let where l = Reader.where "-" l
let is_prelude env x = List.mem x env.prelude.ids
let proofs = [ Prelude.predates; Prelude.subterm; Prelude.coercible; Prelude.delegate; Prelude.atfn ]

let kind env x =
  match type_of env x with
  | Fn _ -> "function"
  | UniqueFn _ -> "unique function"
  | TyCtor _ -> "type constructor"
  | ValCtor _ -> "constructor"
  | Matchable _ -> "Matchable"
  | Cell _ -> "cell"
  | App (Var h, _) when h = Prelude.level -> if (entry env x).minted_level then respell env "level minted by `def-lvl`" else "level"
  | App (Var h, _) when h = Prelude.univ -> "type"
  | App (Var h, _) when h = Prelude.special -> "special form"
  | App (Var h, _) when List.mem h proofs -> "proof"
  | _ -> "value"

let flags env x =
  let e = entry env x in
  let shadowed = match e.name with Some n -> lookup env n <> Some x | None -> false in
  List.concat
    [ [ mult_name e.mult; (match e.state with Settled _ -> "Settled" | Hypothetical -> "Hypothetical"); kind env x ];
      (match find_index (( = ) x) env.subterms with Some i -> [ Printf.sprintf "subterm parameter %d of the enclosing function" (i + 1) ] | None -> []);
      (if e.name = None then [ "anonymous" ] else []);
      (if e.temporary then [ "the elaborator's own binder for a head or an argument" ] else []);
      (if shadowed then [ "shadowed by a newer binder of the same name" ] else []);
      [ (if Reader.placed e.at then "bound at " ^ where e.at else if is_prelude env x then "built in" else "minted by the elaborator") ] ]

let unique_status env x =
  let e = entry env x in
  if e.mult <> Unique then []
  else
    (match IntMap.find_opt x env.uses with
     | Some (Consumed, l) -> [ "unique: consumed at " ^ where l ^ ", so usable only erased from here on" ]
     | Some (Shared, l) -> [ "unique: shared at " ^ where l ^ ", so usable at many, written `(" ^ speller env "share" ^ " " ^ name_of env x ^ ")`, and never again at unique" ]
     | None -> [ "unique: live, neither consumed nor shared on this path" ])
    @ if List.mem x env.captures then [ respell env "unique: closed over by the enclosing `def-fns`, so usable here only erased or through `share`" ] else []

(* A value the final's printer can spell (section 45); a function or a Matchable adds nothing to its kind. *)
let value ~show_value env l x =
  match (entry env x).state, (entry env x).mult with
  | Settled v, (Many | Unique) -> (match show_value env l (type_of env x) v with "_" -> [] | s -> [ "= " ^ s ])
  | _ -> []

let entry_lines ~show_value env l x =
  (* An alias of an anonymous entry, a let forwarding a call's result, says nothing a reader can use. *)
  let rule = match Option.map (canon env) (fact env x).rule with
    | Some (Var y) when (entry env y).name = None -> []
    | Some r -> [ "is " ^ show ~except:x env r ]
    | None -> [] in
  (Printf.sprintf "%s : %s  [%s]" (name_of env x) (show env (type_of env x)) (String.concat ", " (flags env x)))
  :: List.map (( ^ ) "    ") (rule @ value ~show_value env l x @ unique_status env x)

(* The opened Matchable for the head of [ty], if any, as its constructors with their types. *)
let constructors env ty =
  match canon env ty with
  | App (Var tid, _) -> (
      match List.find_opt (fun o -> match o.names with Var t :: _ -> t = tid | _ -> false) env.opens.opened with
      | Some o -> (
          match type_of env o.obj with
          | Matchable (_, _, _, _, cs) ->
              [ Printf.sprintf "constructors of `%s`: %s" (name_of env tid)
                  (String.concat "; " (List.map (fun (_, c) -> show env c ^ " : " ^ show env (match c with Var c -> type_of env c | _ -> c)) cs)) ]
          | _ -> [])
      | None -> [])
  | _ -> []

let goal_lines env goal =
  match goal with
  | Statement -> [ respell env "goal: none; `dump-context` stands as a statement here, so nothing is expected of it" ]
  | Type -> [ "goal: a type, in an erased position" ]
  | Values (expect, None) ->
      [ Printf.sprintf "goal: %d value%s at %s; the position fixes no type" (List.length expect) (if List.length expect = 1 then "" else "s") (String.concat ", " (List.map mult_name expect)) ]
  | Values (expect, Some tele) ->
      let tele = if List.length tele = List.length expect then List.map2 (fun m (e : Term.entry) -> { e with mult = m }) expect tele else tele in
      ("goal: " ^ String.concat " " (show_tele env tele))
      :: List.concat_map (fun (e : Term.entry) -> match e.sg with Ty t when not (has_dangling t) -> constructors env t | _ -> []) tele

let position_lines env goal =
  let pos = match goal with Statement -> None | Type -> Some Erased | Values (expect, _) -> Some (if expect <> [] && List.for_all (( = ) Erased) expect then Erased else if expect = [ Unique ] then Unique else Many) in
  List.concat
    [ (match pos with Some m -> [ "position: " ^ mult_name m ] | None -> []);
      (if env.usage_erased then [ "erased context: nothing here counts as a use, so no unique binder is consumed or shared by this code" ] else []);
      [ (if env.run_pos then "run position: a statement here runs at once and its binders are Settled"
         else "inside a function body or a match branch: binders here are Hypothetical and calls need their proofs") ];
      [ (match env.level with
         | Top -> "level: the top level, above every function's level"
         | At lvl ->
             Printf.sprintf "level: %s%s" (qname env lvl)
               (match env.subterms with [] -> "; the enclosing function has no subterm parameter" | xs -> "; its subterm arguments, in order: " ^ String.concat ", " (List.map (qname env) xs))) ];
      (if env.in_extern then [ "inside an extern function's model, so extern types' constructors have cells" ] else []) ]

(* The entries sharing a slot, shown by the members a reader can name: the entries in scope, a literal by its
   spelling, and `vacant-slot`; a class without two such members, or without an entry the program bound, says
   nothing about anything the program bound, a character sharing its code's word being the newtype's doing. *)
let at_lines env =
  let literal x = Option.map (fun r -> Literal.spell r.lit) (Hashtbl.find_opt literal_of x) in
  let bound x = List.mem x env.scope.ids && not (is_prelude env x) in
  let member x = match literal x with Some s -> Some s | None -> if bound x || x = Prelude.null then Some (name_of env x) else None in
  let slotted = Prelude.null :: List.map (fun r -> r.lit_id) (present_literals env) @ env.scope.ids in
  let classes = List.fold_left (fun acc x ->
    let k = canon env (slot_of x) in
    match List.assoc_opt k acc with Some c -> c := x :: !c; acc | None -> acc @ [ (k, ref [ x ]) ]) [] slotted in
  let classes = List.filter_map (fun (_, c) -> let c = List.sort_uniq compare !c in let shown = List.filter_map member c in if List.length shown > 1 && List.exists bound c then Some shown else None) classes in
  match classes with
  | [] -> [ "slots: every entry is at a slot of its own" ]
  | cs -> [ "slots, the entries at one slot: " ^ String.concat " " (List.map (fun c -> "{" ^ String.concat ", " c ^ "}") cs) ]

let mine env = List.filter (fun x -> not (is_prelude env x)) env.scope.ids

let opened_lines env =
  let os, prelude = List.partition (fun o -> not (is_prelude env o.obj)) env.opens.opened in
  let n = List.length prelude in
  let header, listed = match mine env with
    | [] -> Printf.sprintf "opened (the program has bound nothing, so the prelude's %d are listed)" n, env.opens.opened
    | _ -> Printf.sprintf "opened, beyond the prelude's %d" n, os in
  [ header ^ ": " ^ (if listed = [] then "none" else String.concat " " (List.map (fun o -> show env (type_of env o.obj)) listed)) ]

let literal_lines env =
  let rules = List.filter_map (fun r -> match r.lit, canon env (Var r.lit_id) with
    | (Literal.Numeral _ as lit), (App _ as t) -> Some (Literal.spell lit ^ " is " ^ show env t)
    | _ -> None) (present_literals env) in
  if rules = [] then [] else [ "numerals with rules: " ^ String.concat "; " rules ]

let scope_lines ~show_value env l =
  let mine = mine env in
  let n = List.length env.prelude.ids in
  let header, listed = match mine with
    | [] -> Printf.sprintf "in scope, newest first (the program has bound nothing, so the prelude's %d are listed):" n, env.scope.ids
    | _ -> sprintf_in env "in scope, newest first (%d entries; the prelude's %d are not listed, and `(dump-context x)` shows any one):" (List.length mine) n, mine in
  header :: List.concat_map (fun x -> List.map (( ^ ) "  ") (entry_lines ~show_value env l x)) listed

(* [focus]: the form's arguments, each a term in section 9's grammar with its type where it has one. A variable
   is shown as its entry, anything else by what it canonicalizes to. *)
let focus_lines ~show_value env l focus =
  List.concat_map
    (fun (written, t, ty) ->
      match t with
      | Var x when not (is_meta env x) -> entry_lines ~show_value env l x
      | _ -> [ Printf.sprintf "%s canonicalizes to %s%s" (tick written) (qshow env t) (match ty with Some ty -> " : " ^ qshow env ty | None -> "") ])
    focus

let report ~show_value env l goal focus =
  let body =
    goal_lines env goal @ position_lines env goal
    @ (if focus = [] then scope_lines ~show_value env l else focus_lines ~show_value env l focus)
    @ at_lines env @ opened_lines env @ literal_lines env
  in
  error_with_in env l [] "%s" (String.concat "\n" (respell env "`dump-context` stops elaboration here and reports what the checker knows" :: List.map (( ^ ) "  ") body))
