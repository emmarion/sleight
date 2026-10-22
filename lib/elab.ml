open Term
open Reader
open Env
module V = Value
module Sp = Special

type entry = Term.entry = { name : Reader.name option; subterm : bool; mult : mult; sg : sg; place : term option; loc : Reader.loc }
type res = { term : term; ty : term; erasure : mult; place : term option }
type demand = Fixed | CallableHead of mult | Driver

(* A variable the caller holds physically whose slot is [p], the word an `at` entry is read from (section 36). *)
let location_var env l p =
  let readable x = (entry env x).mult <> Erased && ((entry env x).word || IntMap.mem x env.values) in
  match p with
  | SlotOf (Var x) when readable x -> x
  | _ ->
      let p = canon env p in
      (match List.find_opt (fun x -> readable x && same_slot env p (slot_of x)) (env.scope.ids @ List.map (fun r -> r.lit_id) (present_literals env)) with
      | Some x -> x
      | None -> error_in env l "no caller word for `at` %s" (qshow env p))

let type_term = Prelude.type_term

(* An anonymous entry whose type is the `AtFn` proof about [g] (section 39), as a `Delegate` proof is found. *)
let is_atfn_proof env x g = match type_of env x with App (Var c, [ _; Var g' ]) -> c = Prelude.atfn && g' = g | _ -> false


let single loc = function [ r ] -> r | rs -> error loc "expected one value, got %d" (List.length rs)
let pos_of env expect = if expect = [] && env.usage_erased || expect <> [] && List.for_all (( = ) Erased) expect then Erased else if expect = [ Unique ] then Unique else Many
let atom = function Atom (_, n) -> Some n | _ -> None
let not_name loc what raw = match raw with
  | Nat _ | Char _ | Str _ -> error loc "%s is a literal, not a name" (Reader.show raw)
  | Handle (_, x, MintedIs, Many, _) when Hashtbl.mem literal_of x -> error loc "%s is a literal, not a name" (Reader.show raw)
  | Handle _ -> error loc "a handle to %s is not a name" (tick (Reader.show raw))
  | _ -> error loc "expected %s, got %s" what (tick (Reader.show raw))
let atom_or loc raw what = match atom raw with Some n -> n | None -> not_name loc what raw
let binder = function Atom (_, n) -> Some (Some n) | Wild _ -> Some None | _ -> None
let binder_or loc raw what = match binder raw with Some b -> b | None -> not_name loc what raw

let minted_row y = match Hashtbl.find_opt minted_rows y with Some r -> Some r | None -> Seq.find (List.exists (fun (i, _, _) -> i = y)) (Hashtbl.to_seq_values minted_rows)

let rec enter_mentioned env t =
  fold_vars (fun _ env t -> match t with
    | Var y when y < 0 && not (IntMap.mem y env.facts) -> (
        match minted_row y with
        | Some row ->
            List.fold_left (fun env (_, _, (f : fact)) -> List.fold_left enter_mentioned env (f.ty :: Option.to_list f.rule)) (admit env row) row
        | None -> env)
    | _ -> env) 0 env t

(* A special form's head: a Settled, non-erased entry of type (Special) holding one of its variants (section 6). *)
let minted_fact env m = Option.value (IntMap.find_opt m (trusted env).facts) ~default:(fact env m)
let minted_type env x = canon (comptime_boundary env) (minted_fact env (entry env x).minted).ty
let minted_is env x = Var (entry env x).minted
let settled_value env x ty = let env = enter_mentioned env (Var x) in match entry env x with
  | { state = Settled v; mult = (Many | Unique); _ } when equal (minted_type env x) ty -> Some v
  | _ -> None
let special_value env x = match settled_value env x Prelude.special_term with Some (V.VCtor (c, [||])) -> List.assoc_opt c.cid Prelude.specials | _ -> None
let () = Env.special_name := (fun env x -> Option.map Sp.name (special_value env x)); Env.delegate_ctor := Prelude.delegate; Env.atfn_ctor := Prelude.atfn

let rec special_of env raw =
  let value = special_value env in
  match raw with
  | Atom (_, n) -> Option.bind (lookup env n) value
  | Handle (_, x, _, m, _) -> if m = Erased then None else value x
  | List (_, [head; (Atom _ | Handle _ as a)]) when special_of env head = Some Sp.Share -> special_of env a
  | _ -> None

let is_special env raw s = special_of env raw = Some s
let named_share env = function List (_, [ h; (Atom _ | Handle _) ]) -> is_special env h Sp.Share | _ -> false
let mult_of env raw = match special_of env raw with Some Sp.Erased -> Some Erased | Some Sp.Many -> Some Many | Some Sp.Unique -> Some Unique | _ -> None
let mult_or env loc raw = match mult_of env raw with Some m -> m | None -> error loc "expected a multiplicity, got %s" (tick (Reader.show raw))
let is_statement env = function List (_, h :: _) -> List.exists (is_special env h) Sp.statements | _ -> false
let misplaced env = function List (_, h :: _) -> Option.to_list (Option.bind (special_of env h) (fun sp -> if Sp.has_role sp then Some sp else None)) | _ -> []
let brief = function
  | List (_, ((Atom _ | Handle _) as h) :: args) -> tick ("(" ^ Reader.show h ^ (if args = [] then ")" else " ...)"))
  | List (_, []) -> tick "()"
  | List _ -> "this form"
  | r -> tick (Reader.show r)
let not_a env what raw = error (loc raw) "%s is %s%s" (brief raw) what (help env (String.concat "" (List.map Sp.role_hints (misplaced env raw))))
let at loc f = try f () with Error (Reader.Unknown, msg) -> error loc "%s" msg
let var env loc n = match find env n with Found (x, _) -> refer x; x | Unbound -> error loc "unbound name %s%s" (tick_name n) (hint env n)
let reference env loc raw what = match raw with
  | Atom (_, n) -> var env loc n
  | Handle (_, x, MintedIs, _, _) when x >= 0 || IntMap.mem x env.entries -> refer x; x
  | _ -> not_name loc what raw
let handle_made = function Handle (_, _, _, m, _) -> Some m | _ -> None
let made env raw x = Option.value (handle_made raw) ~default:(entry env x).mult

let resolve env x = match canon env (Var x) with Var y -> y | _ -> x

(* An atom naming an entry, read through any alias rule the fact table holds for it (section 19). *)
let named_of env loc what x = match canon env (Var x) with Var x -> x | t -> error loc "%s is not %s" (qshow env t) what
let named env loc what raw = named_of env loc what (reference env loc raw what)

let tyname env loc = named env loc "a type constructor"

let rec is_strict_subterm a b =
  match b with App (_, args) -> List.exists (fun x -> equal a x || is_strict_subterm a x) args | _ -> false

(* A literal is an atom to the unifier (DESIGN.md section 45): checking fails where one meets a Succ shape or another
   literal, and forcing binds one where a contradiction was wanted. The notes name each literal [hit] picks out
   among the numeral and character literals, by its canonical form, a character standing for its code, and the
   first of [within] it sits in. *)
let literal_notes env l ~within hit =
  let lits = List.filter_map (fun r -> match r.lit with (Literal.Numeral _ | Literal.Char _) as lit -> Some (lit, canon env (Var r.lit_id)) | _ -> None) (present_literals env) in
  let hits = List.filter (fun (_, t) -> hit t) lits in
  let code_of_char t = List.exists (function (Literal.Char _, ct) -> is_strict_subterm t ct | _ -> false) hits in
  let hits = List.sort_uniq compare (List.filter (function (Literal.Numeral _, t) -> not (code_of_char t) | _ -> true) hits) in
  let note (lit, t) =
    let place = List.find_opt (fun c -> is_strict_subterm t (canon env c)) within in
    let kind, opaque = match lit with Literal.Char _ -> ("character", "whose code is opaque") | _ -> ("numeral", "opaque") in
    (l, sprintf_in env "%s%s is a %s literal, %s to the checker by default; `unary`, `prove-literal-lt` or `numeral-of` can expose more"
          (Literal.spell lit) (match place with Some c -> " in " ^ qshow env c | None -> "") kind opaque)
  in
  List.map note hits

(* Where two canonical terms part: the pairs of subterms at which they first differ. *)
let rec differ a b =
  match (a, b) with
  | _ when equal a b -> []
  | App (h, xs), App (h', ys) when equal h h' && List.length xs = List.length ys -> List.concat (List.map2 differ xs ys)
  | _ -> [ (a, b) ]

let ctor_result env t = match canon env t with TyCtor ps -> Some (ps, type_term) | ValCtor (ps, r) -> Some (ps, r) | _ -> None
let head = function App (h, _) -> h | t -> t

(* Identity after canonicalization (section 9), solving any metas either side holds (Env.unify). *)
let solve ?raw ?(about = lazy ("", [])) what env loc actual expected =
  try unify env actual expected
  with
  | Ill_typed (x, t) ->
      let prefix, more = Lazy.force about in
      error_with loc more "%stype mismatch: expected %s, got %s: %s would be %s" prefix (qshow env (type_of env x)) (qshow env (infer env loc t)) (qshow env (Var x)) (qshow env t)
  | Contradiction _ ->
    let pairs = List.filter (fun (a, b) -> not (has_meta env a || has_meta env b)) (differ (canon env actual) (canon env expected)) in
    let side t (a, b) = equal t a || equal t b || is_strict_subterm a t || is_strict_subterm b t in
    let notes = literal_notes env loc ~within:[ expected; actual ] (fun t -> List.exists (side t) pairs) in
    let hint = match raw, ctor_result env actual with
      | Some raw, Some (ps, r) when equal (head r) (head (canon env expected)) -> Some (Printf.sprintf "did you mean %s?" (tick (Reader.show (List (Reader.loc raw, raw :: List.map (fun _ -> Wild (Reader.loc raw)) ps)))))
      | _ -> None in
    let prefix, more = Lazy.force about in
    error_with ?hint loc (notes @ more) "%s%s mismatch: expected %s, got %s" prefix what (qshow env expected) (qshow env actual)

(* The literals a forcing trial bound, which is what leaves a branch standing that a literal index was meant
   to refute: those whose canonical form the trial changed, and any literal one was bound to. *)
let forced_notes env l r trial =
  let bound = List.filter_map (fun r -> let t = canon env (Var r.lit_id) in if equal (canon trial t) t then None else Some (canon trial t)) (present_literals env) in
  literal_notes env l ~within:[ r.ty; r.term ] (fun t -> List.exists (equal (canon trial t)) bound)

let check what env loc actual expected = ignore (solve what env loc actual expected)
let check_type = check "type" and check_equal = check "value"
let under pos m = if pos = Erased then Erased else m
let written ?(noun = "") env pos l what m =
  if pos = Erased && m <> Erased then error_in env l "%s %s%s written `%s` in an erased position; write `erased` here" (if String.contains "aeiou" what.[0] then "an" else "a") (tick (speller env what)) noun (mult_name m) else m
let field_under pos m = if pos = Many && m = Unique then Many else under pos m
let wild = function Wild _ -> true | _ -> false

(* A boundary (DESIGN.md section 50): a term reaching one with a `_` still open is refused. *)
let settle env loc t = if has_meta env t then unsolved loc env t

let solve_sg ?raw ?about env loc sg r = match sg with
  | Ty ty -> solve ?raw ?about "type" env loc r.ty ty
  | Is t -> let env = solve ?about "value" env loc r.term t in solve ?about "type" env loc r.ty (infer env loc t)
let check_sg env loc sg r = ignore (solve_sg env loc sg r)

let res_of env x = { term = Var x; ty = type_of env x; erasure = (entry env x).mult; place = Some (slot_of x) }
let settle_res env loc r = settle env loc r.term; settle env loc r.ty
let non_erased env ids = List.filter (fun x -> (entry env x).mult <> Erased) ids

(* What a signature passes or returns at runtime: its non-erased entries without a written `at` (section 36). *)
let stored (e : entry) = e.mult <> Erased && e.place = None
let runtime tele = List.filter stored tele
let runtime_ids tele ids = List.filter_map (fun (e, x) -> if stored e then Some x else None) (List.combine tele ids)
let field_renames env l tele ids body =
  let _, lets = List.fold_left2 (fun (acc, lets) (e : entry) x -> (Var x :: acc, match e.place with
    | Some p when (entry env x).mult <> Erased -> (x, location_var env l (instantiate acc p)) :: lets
    | _ -> lets)) ([], []) tele ids in
  List.fold_left (fun body (x, y) -> V.CLet ([ x ], V.CVar y, body)) body lets

let slot_named_params params rets =
  let rec go i d acc t = match t with
    | SlotOf (Bound k) when k >= d -> (i - 1 - (k - d)) :: acc
    | t -> List.fold_left (fun acc (dd, t) -> go i (d + dd) acc t) acc (parts t) in
  List.concat (List.mapi (fun i (e : entry) -> List.fold_left (go i 0) [] (sg_term e.sg :: Option.to_list e.place)) (params @ rets))
let abstract_slots env ids t =
  let rec slots t = match t with Var s -> (match List.find_opt (fun x -> (entry env x).slot = s) ids with Some x -> SlotOf (Var x) | None -> t) | t -> map_shallow slots t in
  abstract ids (slots t)
let with_words ?(word = true) env ids = List.fold_left (fun env x -> { env with entries = IntMap.add x { (entry env x) with word } env.entries }) env ids
let closing env ids code = (with_words ~word:false env ids, code)
let head_name env h = match h.term with Var x -> qname env x | t -> qshow env t
let head_notes env h = match h.term with Var x -> declared env ~how:(Printf.sprintf " `%s`" (speller env (mult_name (entry env x).mult))) x | _ -> []

type callee = { subject : string Lazy.t; apposed : bool; notes : (Reader.loc * string) list Lazy.t; used : mult -> mult; marks : bool }

let expected = function [] -> "" | ss -> ": expected " ^ tick (String.concat " " ss)
let counted n what = Printf.sprintf "%d %s%s" n what (if n = 1 then "" else "s")
let with_mults used tele = List.map (fun (e : entry) -> { e with mult = used e.mult }) tele

let computed env = function Handle (_, x, MintedIs, _, _) -> x >= 0 && (entry env x).temporary && (entry env x).name = None | _ -> false

let describe env pos raw term ty =
  let raw = if computed env raw then List (Reader.loc raw, []) else raw in
  let used, marks = match ty with Fn _ | UniqueFn _ -> (under pos, true) | TyCtor _ -> (Fun.id, false) | _ -> (field_under pos, true) in
  let apposed = match ty, raw with Cell _, (Atom _ | Handle _) -> true | _ -> false in
  let view = lazy (
    let kind = kind_name env ty in
    match ty, raw, term with
    | Cell (Var c, _), (Atom _ | Handle _), Var x -> (sprintf_in env "%s, a `Cell` of %s" (qname env x) (qname env c), declared_as env c)
    | Cell (Var c, _), _, _ -> (sprintf_in env "the computed `Cell` of %s" (qname env c), (Reader.loc raw, respell env "the `Cell` is computed here") :: declared_as env c)
    | _, (Atom _ | Handle _), Var x -> (qname env x, declared_as env x)
    | _ -> ("the computed " ^ kind, [ (Reader.loc raw, Printf.sprintf "the %s is computed here" kind) ])) in
  { subject = lazy (fst (Lazy.force view)); apposed; notes = lazy (snd (Lazy.force view)); used; marks }

let count_error env l c what tele got =
  error_with l (Lazy.force c.notes) "%s%s expects %s, got %d%s" (Lazy.force c.subject) (if c.apposed then "," else "") (counted (List.length tele) what) got
    (expected (show_tele ~marks:c.marks env (with_mults c.used tele)))

let argument c i name = Printf.sprintf "argument %d%s of %s" (i + 1) (match name with Some n -> ", " ^ tick_name n ^ "," | None -> "") (Lazy.force c.subject)

(* Opens [x], a Matchable entry (section 8): its constructors must be distinct after canonicalization,
   and it then merges with whatever open names one of them or its type constructor (Env.merge_opens). Failure is
   a Contradiction. *)
let open_adt env x =
  let rec dup = function [] -> None | c :: rest -> if List.mem c rest then Some c else dup rest in
  (match type_of env x with
  | Matchable (_, _, _, _, cs) -> Option.iter (fun c -> raise (Contradiction (lazy (qshow env c ^ " is listed twice")))) (dup (List.map snd cs))
  | _ -> ());
  merge_opens (forcing (opens_add env x))

(* The opened Matchable for a type, at most one (Env.merge_opens). *)
let matchables env tid =
  let of_type o = match o.Env.names with Var t :: _ when t = tid -> (match type_of env o.obj with Matchable (d, _, _, _, cs) -> Some (o.obj, d, cs) | _ -> None) | _ -> None in
  List.filter_map of_type env.opens.opened

let find_matchable env loc tid =
  match matchables env tid with [] -> error_in env loc "%s has no `Matchable` open" (qname env tid) | m :: _ -> m

let type_head env ty = match canon env ty with App (Var t, _) -> Some t | _ -> None

let held_needs_many env loc tid mid =
  if not (readable env mid) then (
    if (entry env mid).mult = Unique && List.mem mid env.scope.ids then ignore (use env loc Many mid);
    error_in env loc "the `Matchable` for %s is erased or out of scope, so a non-erased match cannot take a value of it apart" (qname env tid))

let ctor_type env loc c =
  match canon env (type_of env c) with ValCtor (tele, ret) -> (tele, ret) | _ -> error loc "%s is not a value constructor" (qname env c)

let tid_of env loc c = Option.get (type_head env (snd (ctor_type env loc c)))
let marker env loc tid ctors c =
  match List.find_opt (fun (_, c') -> c' = Var c) ctors with
  | Some (m, _) -> m
  | None -> error_with loc (declared_as env tid) "%s is not a constructor of %s" (qname env c) (qname env tid)

(* A Matchable's constructors, each with its phantom marker and its number of non-erased fields (section 33). *)
let shapes env loc ctors =
  List.map (fun (m, c) -> match c with Var c -> (m, c, List.length (runtime (fst (ctor_type env loc c)))) | _ -> assert false) ctors

let non_phantom shapes = List.filter_map (fun (m, c, n) -> if m = Many then Some (c, n) else None) shapes

(* A phantom constructor heads no runtime value (section 14 rule 2), so discriminants number the others only. *)
let discriminant shapes c = find_index (fun (c', _) -> c' = c) (non_phantom shapes)

let tagged disc shapes = disc = Enum && List.length (non_phantom shapes) > 1

let wrappers disc shapes =
  let cs = non_phantom shapes in
  if tagged disc shapes || List.exists (fun (_, n) -> n <> 1) cs then [] else List.map fst cs

let hollow env c =
  match matchables env (tid_of env Reader.nowhere c) with
  | (mid, d, cs) :: _ when List.exists (fun (_, c') -> c' = Var c) cs ->
      let shapes = shapes env Reader.nowhere cs in
      (match type_of env mid with Matchable (_, _, ext, _, _) -> not ext | _ -> false)
      && not (tagged d shapes) && List.for_all (fun (_, n) -> n = 0) (non_phantom shapes)
  | _ -> false

let newtype_of env c =
  List.find_map (fun o -> if not (names_var c o.Env.names) then None else match type_of env o.Env.obj with
    | Matchable (d, true, _, _, cs) when List.mem c (wrappers d (shapes env Reader.nowhere cs)) -> Some o.obj
    | _ -> None) env.opens.opened

let rec term_place env = function
  | Var x | SlotOf (Var x) -> Some (slot_of x)
  | App (h, args) -> (
      match canon env h with
      | Var c when newtype_of env c <> None ->
          Option.bind (List.find_opt (fun ((e : entry), _) -> e.mult <> Erased) (List.combine (fst (ctor_type env Reader.nowhere c)) args)) (fun (_, a) -> term_place env a)
      | _ -> None)
  | _ -> None
let term_res env loc t = { term = t; ty = infer env loc t; erasure = Erased; place = None }

let ctor_of env loc c = match (entry env c).state with Settled (V.VCtorFn ct) -> ct | _ -> error loc "%s is not a run-position constructor" (qname env c)
let settled env v = if env.run_pos then Settled v else Hypothetical
let ran env mult code = if not env.run_pos then None else Some (if mult = Erased then V.VToken else List.hd (Eval.eval env.values code))
let ran_state env mult code = Option.fold ~none:Hypothetical ~some:(fun v -> Settled v) (ran env mult code)
let forwarded env mult r ran =
  let src = match r.term with Var y -> Some (entry env y) | _ -> None in
  let state, minted = match (src, ran) with
    | Some ({ state = Settled v; _ } as e), _ when mult <> Unique -> (Settled (if mult = Erased then V.VToken else v), Some e.minted)
    | Some { state = Settled _; _ }, _ when not env.run_pos -> (Hypothetical, None)
    | _, Some v -> (Settled v, None)
    | Some e, None -> (e.state, Some e.minted)
    | None, None -> (Hypothetical, None) in
  (state, minted, Option.fold ~none:false ~some:(fun e -> e.minted_level) src, Option.bind src (fun e -> if e.introduced < 0 then None else Some e.introduced))
let ctor_var env loc = named env loc "a constructor"
let proof_type ctor args = App (Var ctor, args)

let sharing_of_fn env t = match canon env t with UniqueFn _ -> Prelude.unique_term | Fn _ -> Prelude.shared_term | _ -> assert false
let sharing_mult env l t =
  let t = canon env t in
  if equal t Prelude.unique_term then Unique else if equal t Prelude.shared_term then Many
  else error_in env l "`coerce` needs a canonical `Unique` or `Shared` side, got %s" (qshow env t)

let expect_proof ?(alt = "") env loc ctor p =
  match canon env (infer env loc p) with
  | App (Var c, args) when c = ctor -> args
  | ty -> error loc "expected a %s proof%s, got %s : %s" (qname env ctor) alt (qshow env p) (qshow env ty)


type src_entry = { s_loc : loc; s_subterm : bool; s_mult : mult option; s_sg : [ `Ty of raw | `Is of raw ] option; s_name : Reader.name option; s_place : raw option }

let parse_entry env raw =
  match raw with
  | List (l, items) -> (
      let s_subterm, items = match items with t :: rest when is_special env t Sp.Subterm -> (true, rest) | _ -> (false, items) in
      let s_mult, items = match items with t :: rest when mult_of env t <> None -> (mult_of env t, rest) | _ -> (None, items) in
      let s_place, items = match List.rev items with
        | v :: a :: rest when is_special env a Sp.At -> (Some v, List.rev rest)
        | _ -> (None, items)
      in
      let mk s_sg s_name = { s_loc = l; s_subterm; s_mult; s_sg; s_name; s_place } in
      match items with
      | [ e; i; n ] when is_special env i Sp.Is && binder n <> None -> [ mk (Some (`Is e)) (Option.get (binder n)) ]
      | [ n ] when binder n <> None -> [ mk None (Option.get (binder n)) ]
      | ty :: names when names <> [] && List.for_all (fun n -> binder n <> None) names ->
          List.map (fun n -> mk (Some (`Ty ty)) (Option.get (binder n))) names
      | _ -> (match List.rev items with (Nat _ | Char _ | Str _ | Handle _) as r :: _ -> not_name (loc r) "a name" r | _ -> ());
          error l "malformed telescope entry %s%s" (tick (Reader.show raw)) (help env (Sp.hints "telescope-entry")))
  | r -> error (loc r) "expected a telescope entry, got %s" (tick (Reader.show raw))

let split_arrow env loc items =
  let rec go acc = function
    | [] -> error_in env loc "missing `->`"
    | t :: rest when is_special env t Sp.Arrow -> (List.rev acc, rest)
    | t :: rest -> go (t :: acc) rest
  in
  go [] items

let no_mult env what l m = error l "%s take no multiplicity; drop `%s`" what (speller env (mult_name m))

(* Leading annotation tokens drawn from [allowed], in any order. *)
let marks env allowed items =
  let rec go acc = function
    | t :: rest when List.exists (is_special env t) allowed -> go (List.find (is_special env t) allowed :: acc) rest
    | rest -> (acc, rest)
  in
  go [] items

let def_marks env l allowed items =
  let ms, rest = marks env allowed items in
  if List.mem Sp.Extern ms && not env.externs then error_in env l "only the prelude may mark a definition `extern`; a program that declares its own runs with `--no-prelude`";
  (ms, rest)

let fact_of env loc = function Ty t -> (t, None) | Is t -> (infer env loc t, Some t)

let anon tele = List.map (fun _ -> None) tele
type sink = { owner : string; noun : string; shown : string list; anchors : (Reader.loc * string) list }

let count_check ?sink l expect got =
  let n = List.length expect and m = List.length got in
  if n <> m then match Option.map Lazy.force sink with
    | None -> error l "expected %d values, got %d" n m
    | Some s -> error_with l s.anchors "%s expects %s, got %d%s" s.owner (counted n s.noun) m (expected s.shown)
let ctor_result head mvars = [ { name = None; subterm = false; mult = Erased; sg = Is (App (head, List.rev mvars)); place = None; loc = Reader.nowhere } ]
let field_names fields = List.map (fun f -> binder_or (loc f) f "a field name") fields

let field_ats tele fields = if List.length fields = List.length tele then List.map loc fields else List.map (fun _ -> Reader.nowhere) tele

(* [ids]: terms of the binders already in force, innermost first. Binds one fresh entry per item and returns
   their ids in order. [ats] given means this site is where the source writes the binders -- a pattern's
   fields -- so they are the ones shadowing warns at; without it the telescope is being read back and each
   entry keeps the position its declaration carried (Env.bind).
   A form's results are opened with [open_results], and only after everything the form elaborates: `delegate-of`
   and `at-fn-of` fetch an anonymous entry in scope by its type (ASSUMPTIONS 114), so a result entry opened
   earlier could, it seems, be fetched as the proof of itself. *)
let open_tele env ?(word = true) ?names ?ats ?mults ?states ?(ids = []) ?meta tele =
  let nth l i default = match l with Some l -> List.nth l i | None -> default in
  let _, env, _, fresh =
    List.fold_left
      (fun (i, env, ids, fresh) e ->
        let ty, rule = fact_of env Reader.nowhere (map_sg (instantiate ids) e.sg) in
        let x, env = bind env ?meta ~word:(word && meta <> Some true) ~at:(nth ats i e.loc) ~written:(ats <> None) (nth names i e.name) (nth mults i e.mult) (nth states i Hypothetical) ty ?rule in
        let env = match Option.map (instantiate ids) e.place with
          | Some p when meta <> Some true -> place env x p
          | _ -> env in
        (i + 1, env, Var x :: ids, x :: fresh))
      (0, env, ids, []) tele
  in
  (env, List.rev fresh)

let open_results env ?ats ?mults ?ids tele = open_tele env ~word:false ~names:(anon tele) ?ats ?mults ?ids tele

(* Printing a value against its type (section 27's printed final; section 45). The three literal types print
   as the literals they read back from (Literal.spell); a value whose type names a readable Matchable prints as
   its constructor -- read from the tag where there is one, and the sole non-phantom constructor where there is
   no choice -- over its fields, each erased one printing as `_`. Everything else prints `_`, so the walk is total
   and never reaches Value.show's untyped rendering. *)
let prelude_id env name = Env.lookup { env with scope = env.prelude } (Src name)

let nullary env name ty = match (type_head env ty, prelude_id env name) with Some t, Some p -> t = p | _ -> false

(* An extern Nat is its integer; the model's is the Peano chain, walked one constructor at a time. A Char and a
   U8 are their Nat (section 33), so neither needs unwrapping. *)
let nat_z env loc v =
  let c = ctor_of env loc (Option.get (prelude_id env "Zero")) in
  let rec go acc v =
    match v with
    | V.VExt (_, V.Int n) -> Z.add acc n
    | v -> ( match V.destruct c v with 0, _ -> acc | _, [ p ] -> go (Z.succ acc) p | _ -> raise Not_found)
  in
  go Z.zero v

(* The byte a Char's code and a String's elements are, by the Lt proof MkU8 carries (section 42). A Nat outside
   that range has no literal spelling, so the walk falls back rather than spelling it back unreadably; it also
   keeps Z.to_int, whose Z.Overflow the fallback below does not catch, off an unbounded value. *)
let nat_byte env loc v =
  let n = nat_z env loc v in
  if Z.leq Z.zero n && Z.lt n (Z.of_int 256) then Z.to_int n else raise Not_found

(* An extern String is its slice; the model's is a cons list of characters. *)
let str_host env loc v =
  let c = ctor_of env loc (Option.get (prelude_id env "SNil")) in
  let buf = Buffer.create 16 in
  let rec go v =
    match v with
    | V.VExt (_, V.Slice (s, o, l)) -> Buffer.add_string buf (String.sub s o l)
    | v -> ( match V.destruct c v with 0, _ -> () | _, [ ch; rest ] -> Buffer.add_char buf (Char.chr (nat_byte env loc ch)); go rest | _ -> raise Not_found)
  in
  go v;
  Buffer.contents buf

(* What a literal is bound to, minted directly as slc's `intern` mints it (DESIGN.md section 45). A model Nat comes off
   the program's one Peano chain, extended on demand, so numerals and characters share it wherever they stand
   and the extractor, which shares by identity, emits each Nat once per program. *)
let papp env n args = App (Var (Option.get (prelude_id env n)), args)
let pctor ?(loc = Reader.nowhere) env n = ctor_of env loc (match prelude_id env n with Some x -> x | None -> error loc "unbound name %s" (tick n))
let pbuild ?loc env n args = V.construct (pctor ?loc env n) args

(* The FFI's ADT for the prelude type [c] constructs, where the FFI holds it and is in use. *)
let ext_adt env c = match (ctor_of env Reader.nowhere (Option.get (prelude_id env c))).V.adt with { ext = Some _; _ } as adt when !V.use_externs -> Some adt | _ -> None

let peano env k =
  let l = Array.length !ladder in
  if k >= l then (
    let a = Array.append !ladder (Array.make (k + 1 - l) V.VToken) in
    for i = l to k do a.(i) <- (if i = 0 then pbuild env "Zero" [] else pbuild env "Succ" [ a.(i - 1) ]) done;
    ladder := a);
  (!ladder).(k)

let nat_value env z = match ext_adt env "Zero" with Some adt -> V.VExt (adt, V.Int z) | None -> peano env (Z.to_int z)

let str_value env s =
  match ext_adt env "SNil" with
  | Some adt -> V.VExt (adt, V.Slice (s, 0, String.length s))
  | None -> String.fold_right (fun c rest -> pbuild env "SCons" [ pbuild env "MkChar" [ pbuild env "MkU8" [ peano env (Char.code c) ] ]; rest ]) s (pbuild env "SNil" [])

(* The bijective base-2 spelling of [z] as a term: (B1 b) is 2b+1, (B2 b) is 2b+2. *)
let rec bin_term env z =
  match Ffi_core.half_view ~z:Fun.id ~nat:Fun.id z with HZ -> papp env "BZ" [] | H1 b -> papp env "B1" [ bin_term env b ] | H2 b -> papp env "B2" [ bin_term env b ]

(* Interns a literal once per program, its entries minted in the literal half of the id space and outside the scope
   (DESIGN.md section 45): a numeral is a Settled Nat beside an erased token typed by its spelling; a character is its
   code's Nat under the rule `is (MkChar (MkU8 n p))`, `p` a token of its bound, its proof its code's; a string is
   opaque. A scope that meets a literal without its entries has them entered as they were minted. *)
let rec intern env loc lit =
  let env = match lit with Literal.Char c -> intern env loc (Literal.Numeral (Z.of_int c)) | _ -> env in
  match Hashtbl.find_opt literal_rows (Literal.key lit) with
  | Some row -> enter env row
  | None ->
      let what, ty = match lit with Literal.Numeral _ -> ("a numeral", "Nat") | Char _ -> ("a character literal", "Char") | Str _ -> ("a string literal", "String") in
      if prelude_id env ty = None then error loc "%s needs the prelude's %s, which `--no-prelude` leaves out" what (tick ty);
      let token env ty = bind env ~literal:true None Erased (Settled V.VToken) ty in
      let value env ?rule v ty = bind env ~literal:true None Many (Settled v) ty ?rule in
      let env, x, lit_proof, own =
        match lit with
        | Literal.Numeral z ->
            let x, env = value env (nat_value env z) (papp env "Nat" []) in
            let p, env = token env (papp env "Numeral" [ bin_term env z; Var x ]) in
            (env, x, Some p, [ x; p ])
        | Literal.Char c ->
            let code = Hashtbl.find literal_rows (Z.to_string (Z.of_int c)) in
            let p, env = token env (papp env "Lt" [ Var code.lit_id; Var (Option.get (prelude_id env "u8-modulus")) ]) in
            let x, env = value env (pbuild env "MkChar" [ pbuild env "MkU8" [ nat_value env (Z.of_int c) ] ]) (papp env "Char" []) ~rule:(papp env "MkChar" [ papp env "MkU8" [ Var code.lit_id; Var p ] ]) in
            (env, x, code.lit_proof, [ x; p ])
        | Literal.Str s ->
            let x, env = value env (str_value env s) (papp env "String" []) in
            (env, x, None, [ x ])
      in
      record_literal { lit; lit_id = x; lit_proof; minted = List.concat_map (fun x -> List.map (fun i -> (i, entry env i, fact env i)) [ x; (entry env x).slot ]) own };
      env

let lit_of = function
  | Nat (_, z) -> Some (Literal.Numeral z) | Char (_, c) -> Some (Literal.Char c) | Str (_, s) -> Some (Literal.Str s)
  | Handle (_, x, MintedIs, Many, _) -> Option.map (fun r -> r.lit) (Hashtbl.find_opt literal_of x)
  | _ -> None

let expansions = ref 0
let sources : (string * string) list ref = ref []
type goal_mode = Unrequired | Open | Proved
let goal_mode = ref Unrequired
let goal : (Reader.loc * mult * term * Env.t) option ref = ref None
let discharged : Reader.loc option ref = ref None
let source_dir f = match String.rindex_opt f '/' with None -> "." | Some 0 -> "/" | Some i -> String.sub f 0 i
let gensyms = ref 0
let on_run : (Env.t -> unit) ref = ref ignore
let primitives = [ Sp.Gensym; Sp.GensymUnique; Sp.SettledType; Sp.SettledErase; Sp.SettledEq; Sp.Resolve; Sp.ReadFile; Sp.SettledMult; Sp.SettledValue; Sp.InternNat; Sp.InternChar; Sp.InternString; Sp.MintSettled; Sp.MintSettledErased; Sp.PlaceAt; Sp.PlaceAtMany; Sp.UnplaceAt; Sp.UnplaceAtMany; Sp.PlacedSlot; Sp.PlacedEq; Sp.SlotEq ]
let prims : (Sp.t, mult * entry list * entry list) Hashtbl.t = Hashtbl.create 4
let implemented = [ Sp.Gensym; Sp.SettledType; Sp.SettledErase; Sp.SettledEq; Sp.Resolve; Sp.ReadFile; Sp.SettledMult; Sp.SettledValue; Sp.InternNat; Sp.InternChar; Sp.InternString; Sp.MintSettled; Sp.MintSettledErased; Sp.SlotEq ]
let literal_handle env lit =
  ignore (intern env Reader.nowhere lit);
  let x = (Hashtbl.find literal_rows (Literal.key lit)).lit_id in
  V.VHandle (x, MintedIs, Many, Hashtbl.find V.literal_values x)

let denoted env x r = let f = minted_fact env x in match r with Ffi_core.MintedIs -> [ Var x; f.ty ] | MintedType -> [ f.ty; type_term ]

let mint_entry env ?rule ty mult v =
  let env = List.fold_left enter_mentioned env (ty :: Option.to_list rule) in
  let x, env = bind env ~literal:true None mult (Settled v) ?rule ty in
  record_minted x (List.map (fun i -> (i, entry env i, fact env i)) [ x; (entry env x).slot ]);
  V.VHandle (x, MintedIs, mult, v)

let mint env y r mult v = let env = enter_mentioned env (Var y) in mint_entry env (List.hd (denoted env y r)) mult v

let applied_handles : (Env.t -> Reader.loc -> Sp.t -> term -> raw list -> term * term * tele) ref = ref (fun _ _ _ _ _ -> assert false)

let report l m =
  let saved = Hashtbl.copy numbering in
  Hashtbl.reset numbering;
  let here = Reader.where "" l in
  let text = Env.resolve here (Reader.label here "error: " ^ m) in
  Hashtbl.reset numbering;
  Hashtbl.iter (Hashtbl.replace numbering) saved;
  text

let implement env p args = match p, args with
  | Sp.Gensym, _ -> incr gensyms; [ nat_value env (Z.of_int !gensyms) ]
  | (Sp.InternNat | Sp.InternChar | Sp.InternString), [ _; v ] ->
      [ literal_handle env (match p with Sp.InternNat -> Literal.Numeral (nat_z env Reader.nowhere v) | Sp.InternChar -> Literal.Char (nat_byte env Reader.nowhere v) | _ -> Literal.Str (str_host env Reader.nowhere v)) ]
  | Sp.SettledEq, [ _; V.VHandle (x, rx, _, _); V.VHandle (y, ry, _, _) ] ->
      let snap = List.fold_left enter_mentioned (comptime_boundary env) [ Var x; Var y ] in
      let a = denoted snap x rx and b = denoted snap y ry in
      let snap = List.fold_left enter_mentioned snap (a @ b) in
      [ (if List.for_all2 (fun s t -> equal (canon snap s) (canon snap t)) a b then pbuild env "Some" [ pbuild env "JMRefl" [] ] else pbuild env "None" []) ]
  | Sp.MintSettled, [ _; V.VHandle (y, r, _, _); v ] -> [ mint env y r Many v ]
  | Sp.MintSettledErased, [ _; V.VHandle (y, r, _, _) ] -> [ mint env y r Erased V.VToken ]
  | (Sp.SettledTyApply | Sp.SettledValApply), pos :: _ :: hs ->
      let l = match Ffi.unpos pos with Ffi_core.MkPos (f, line, col) -> Reader.At { file = str_host env Reader.nowhere f; line = nat_z env Reader.nowhere line; col = nat_z env Reader.nowhere col } | NoPos -> Reader.NoLoc in
      let hs = List.map (function V.VHandle (x, r, m, v) -> (x, r, m, v) | _ -> raise (Eval.Runtime "expected a handle")) hs in
      let snap = List.fold_left (fun env (x, r, _, _) -> let env = enter_mentioned env (Var x) in List.fold_left enter_mentioned env (denoted env x r)) (comptime_boundary env) hs in
      let x, r, _, _ = List.hd hs in
      [ (match !applied_handles snap l p (List.hd (denoted snap x r)) (List.map (fun (x, r, m, v) -> Handle (l, x, r, m, Obj.repr v)) hs) with
         | exception Error (l', m) -> pbuild env "Fail" [ str_value env (report l' m) ]
         | exception Contradiction m -> pbuild env "Fail" [ str_value env (report l ("contradiction: " ^ Lazy.force m)) ]
         | t, ty, tele ->
             let _, _, mult, c = List.hd hs in
             let fields = List.filter_map (fun ((e : entry), (_, _, _, v)) -> if e.mult = Erased then None else Some v) (List.combine tele (List.tl hs)) in
             let v = if mult = Many then List.hd (Eval.apply c fields) else V.VToken in
             pbuild env "Ok" [ mint_entry env ~rule:t ty mult v ]) ]
  | Sp.Resolve, [ _; s ] ->
      let name = match Ffi.unsymbol s with Ffi_core.SName t -> Reader.Src (str_host env Reader.nowhere t) | SGen (n, t) -> Gen (nat_z env Reader.nowhere n, str_host env Reader.nowhere t) in
      [ (match find env name with
         | Unbound -> pbuild env "RUnbound" []
         | Found (_, { state = Hypothetical; _ }) -> pbuild env "RHypothetical" []
         | Found (_, { state = Settled v; mult; minted; _ }) -> pbuild env "RSettled" [ V.VHandle (minted, MintedIs, mult, if mult = Many then v else V.VToken) ]) ]
  | Sp.ReadFile, [ _; here; path ] ->
      let text = str_host env Reader.nowhere in
      let read = match Ffi.unpos here with
        | Ffi_core.MkPos (f, _, _) -> (match List.assoc_opt (text f) !sources with Some dir -> Driver_core.read_within dir (text path) | None -> Error (text f ^ ": not a source file or a name given to --comptime-unconfine"))
        | NoPos -> Error "no position to read relative to" in
      [ (match read with Ok s -> pbuild env "Ok" [ str_value env s ] | Error m -> pbuild env "Fail" [ str_value env m ]) ]
  | p, _ -> raise (Eval.Runtime ("`" ^ Sp.name p ^ "` has no implementation"))

let rec macro_of env raw =
  let held x = Option.bind (prelude_id env "Macro") (fun m -> settled_value env x (App (Var m, []))) in
  match raw with
  | Atom (_, n) -> (match find env n with Found (x, _) -> held x | Unbound -> None)
  | Handle (_, x, _, m, _) when m <> Erased -> held x
  | List (_, [ h; a ]) when special_of env h = Some Sp.Share -> macro_of env a
  | _ -> None

let raw_ctor env l = ctor_of env l (Option.get (prelude_id env "RawSymbol"))

let rec raw_value env r =
  match ext_adt env "RawSymbol" with
  | Some adt -> V.VExt (adt, V.Raw r)
  | None ->
      let i, fs = Ffi_core.raw_fields (Ffi_core.raw_view ~handle:(fun (x, r, m, v) -> V.VHandle (x, r, m, Obj.obj v)) ~symbol:Ffi.symbol ~get:Fun.id ~str:(str_value env) ~nat:(nat_value env) ~pos:Ffi.pos ~list:Ffi.list ~raw:(raw_value env) r) in
      V.construct (List.nth (raw_ctor env Reader.nowhere).V.adt.ctors i) fs

let rec value_raw env l = function
  | V.VExt (_, V.Raw r) -> r
  | v -> let i, fs = V.destruct (raw_ctor env l) v in Ffi_core.raw_of ~unhandle:(fun l -> function V.VHandle (x, r, m, v) -> Handle (l, x, r, m, Obj.repr v) | _ -> assert false) ~unsymbol:Ffi.unsymbol ~text:(str_host env l) ~z:(nat_z env l) ~pos:Ffi.unpos ~list:Ffi.unlist ~raw:(value_raw env l) (Ffi_core.raw_model i fs)

let atom_entry ?at env raw =
  let l = Option.value at ~default:(loc raw) in
  match raw, lit_of raw with
  | Atom (_, n), _ -> (env, var env l n)
  | Handle (_, x, MintedIs, _, _), _ -> refer x; ((match Hashtbl.find_opt literal_of x with Some row -> intern env l row.lit | None -> enter_mentioned env (Var x)), x)
  | Handle (_, x, MintedType, _, _), _ -> let t = (minted_fact env x).ty in let y, env = bind (enter_mentioned env t) None Erased (settled env V.VToken) ~rule:t type_term in (env, y)
  | _, Some lit -> let env = intern env l lit in (env, (Hashtbl.find literal_rows (Literal.key lit)).lit_id)
  | Wild _, _ -> error l "`_` is not a name, and nothing is inferred here"
  | _ -> error l "expected a name or a literal, got %s" (tick (Reader.show raw))
let atom_entry_or env l raw what = match raw with List _ -> error l "expected %s, got %s" what (tick (Reader.show raw)) | _ -> atom_entry ~at:l env raw
let admitted env raw = match raw with Handle (_, _, MintedIs, _, _) -> fst (atom_entry env raw) | _ -> env
let entry_named env l raw what = match raw with Handle (_, _, MintedType, _, _) -> not_name l what raw | _ -> atom_entry_or env l raw what

let read_special pos env raw =
  match raw with
  | Atom (l, _) | Handle (l, _, _, _, _) | Nat (l, _) | Char (l, _) | Str (l, _) -> let env, x = atom_entry env raw in use env l ?made:(handle_made raw) Many x
  | List (l,[h;(Atom _ | Handle _ as a)]) when special_of env h = Some Sp.Share ->
      if pos = Erased then error_in env l "`share` in an erased position";
      let env = admitted env a in
      let x = reference env (loc a) a "a name" in
      if made env a x <> Unique then error_in env l "`share` needs a unique value";
      use env l ~sharing:true Many x
  | _ -> env

let macro_refused env l head =
  let shown = tick (Reader.show head) in
  let rec held = function Atom (_, n) -> find env n | Handle (_, x, MintedIs, _, _) -> Found (x, entry env x) | List (_, [ h; a ]) when special_of env h = Some Sp.Share -> held a | _ -> Unbound in
  let bound x how where = let e = entry env x in if Reader.placed e.at then [ (e.at, respell env (Printf.sprintf "%s is bound%s here%s" (qname env x) how where)) ] else [] in
  let dyn = ", where every binding is `Hypothetical`" in
  match held head with
  | Found (x, { mult = Erased; state = Settled _; _ }) -> error_with ~hint:(respell env "bind it `many` to expand it") l (bound x " `erased`" "") "%s is an erased macro, and only a non-erased one is expanded" shown
  | Found (x, { mult = Erased; _ }) -> error_with_in env l (bound x " `erased`" dyn) "%s is an erased macro, expanded only where its head is constant-known and non-erased" shown
  | Found (x, { state = Hypothetical; _ }) -> error_with ~hint:(respell env "a macro reaches a body through a run-position binding, named directly or forwarded by a `let`") l (bound x "" dyn) "%s is a macro, expanded only where its head is constant-known" shown
  | _ -> error l "%s is a macro, expanded only where its head is constant-known" shown

let expand env raw =
  match raw with
  | List (l, head :: args) ->
      Option.map
        (fun f ->
          incr expansions;
          if !expansions > 10000 then error l "more than 10000 macro expansions";
          let env = read_special Many env head in
          let here = Ffi.pos (Ffi_core.pos_view ~str:(str_value env) ~nat:(nat_value env) l) in
          let args = List.fold_right (fun a rest -> Ffi.list (Cons (raw_value env a, rest))) args (Ffi.list Nil) in
          Eval.prim := implement env;
          let out = try Eval.apply f [ V.VToken; here; args ] with Eval.Runtime m -> error l "macro %s failed: %s" (tick (Reader.show head)) m in
          let rec items v = match Ffi.unlist v with Nil -> [] | Cons (x, rest) -> value_raw env l x :: items rest in
          (env, items (List.hd out)))
        (macro_of env head)
  | _ -> None

let settle_head : (mult -> Env.t -> raw -> Env.t * raw) ref = ref (fun _ env raw -> (env, raw))

let named_head env = function List (_, List (l, _) :: _) -> error l "no function is called while a type is elaborated, so a head in a type cannot be a form (section 9)" | raw -> (env, raw)

let rec expand_one head env raw =
  let env, raw = head env raw in
  match expand env raw with
  | None -> (env, raw)
  | Some (env, [ r ]) -> expand_one head env r
  | Some (_, rs) -> error (loc raw) "%s must expand to one form here, and expanded to %d" (brief raw) (List.length rs)

let rec expand_seq pos env = function
  | item :: rest ->
      let env, item = !settle_head pos env item in
      (match expand env item with Some (env, out) -> expand_seq pos env (out @ rest) | None -> (env, item :: rest))
  | [] -> (env, [])

let rec spliced env = function
  | item :: rest -> (
      match expand env item with
      | Some (env, out) -> spliced env (out @ rest)
      | None -> let env, rest = spliced env rest in (env, item :: rest))
  | [] -> (env, [])

let erased_reads f env x = let env', r = f { env with usage_erased = true } x in ({ env' with usage_erased = env.usage_erased }, r)

let spliced_entries env entries =
  let env, entries = spliced env entries in
  List.fold_left_map (fun env -> function List (l, items) -> let env, items = spliced env items in (env, List (l, items)) | e -> (env, e)) env entries

let listed_ctors env loc tid =
  let _, _, cs = find_matchable env loc tid in
  List.filter_map (fun (_, c) -> match c with Var c -> (try Some (c, ctor_of env loc c) with Contradiction _ | Error _ | Not_found -> None) | _ -> None) cs
let listed_entry named ct = Option.map fst (List.find_opt (fun (_, ct') -> ct'.V.cid = ct.V.cid) named)

(* The constructor a value prints as (section 45), chosen off the type's opened Matchable and never by
   refuting candidates: the tag where the type is tagged, else the one non-phantom constructor where the type has
   exactly one. `adt.ctors` is already the non-phantom list, indexed by discriminant. *)
let shown_ctor env loc ty v =
  let named = listed_ctors env loc (Option.get (type_head env ty)) in
  let entry_of = listed_entry named in
  match named with
  | [] -> None
  | (_, first) :: _ ->
      let adt = first.V.adt in
      let ct = if adt.V.tagged then match V.dispatch adt.V.ext adt.V.tagged v with Some (i, _) -> List.nth_opt adt.V.ctors i | None -> None
        else ( match adt.V.ctors with [ c ] -> Some c | _ -> None) in
      Option.bind ct (fun ct -> Option.map (fun c -> (c, ct)) (entry_of ct))

(* A constructor's fields against an instance of its type, in declaration order with each one's multiplicity, as
   entering a branch computes them: the unification types the children, it no longer decides the constructor. *)
let ctor_fields env loc c ty =
  let tele, ret = ctor_type env loc c in
  let env', fids = open_tele env tele in
  let env' = merge_opens (unify_force (forcing env') (instantiate (List.rev_map (fun x -> Var x) fids) ret) ty) in
  (env', List.map (fun x -> ((entry env' x).mult, type_of env' x)) fids)

let rec show_value env loc ty v =
  try
    let ty = canon env ty in
    if equal ty Prelude.slot_term || (match ty with Cell _ -> true | _ -> false) then "_"
    else if nullary env "Nat" ty then Literal.spell (Literal.Numeral (nat_z env loc v))
    else if nullary env "Char" ty then Literal.spell (Literal.Char (nat_byte env loc v))
    else if nullary env "String" ty then Literal.spell (Literal.Str (str_host env loc v))
    else
      match shown_ctor env loc ty v with
      | None -> "_"
      | Some (c, ct) ->
          let env', specs = ctor_fields env loc c ty in
          let _, fs = V.destruct ct v in
          (* an erased field has no word, so it takes none from the destructure *)
          let rec args specs fs = match specs, fs with
            | [], _ -> []
            | (Erased, _) :: rest, fs | _ :: rest, ([] as fs) -> "_" :: args rest fs
            | (_, t) :: rest, f :: fs -> show_value env' loc t f :: args rest fs
          in
          Ffi_core.show_app ct.V.cname (args specs fs)
  with Contradiction _ | Error _ | Not_found | Invalid_argument _ -> "_"


let spread mults values =
  snd (List.fold_left_map (fun vs m -> match (m, vs) with (Many | Unique), v :: rest -> (rest, v) | _ -> (vs, V.VToken)) values mults)
let settled_fields env l c mults value =
  let ct = ctor_of env l c in
  let i, vs = V.destruct ct value in
  (i = ct.V.index, List.map (fun v -> Settled v) (spread mults vs))

let witness env ?(mult = Erased) ?(value = V.VToken) ty = bind env None mult (settled env value) ty

let matchable_code env pos x =
  if pos = Erased then V.CErased else match adt_of env x with Some adt -> V.CConst (V.VMatchable adt) | None -> V.CVar x

let mint_adt ?(newtype = false) env name disc shapes =
  let adt = { V.tname = name; tagged = tagged disc shapes; newtype; ctors = []; ext = None } in
  adt.ctors <- List.mapi (fun index (c, arity) -> { V.cname = entry_name env c; cid = c; index; arity; adt }) (non_phantom shapes);
  adt

(* A match on an ADT the elaborator can see reads no Matchable at runtime (section 24); one on a held Matchable
   reads it as the shape the Matchable's type gives its values. *)
let match_shape env x tid disc shapes = match adt_of env x with Some adt -> V.Known adt | None -> V.Held (V.CVar x, mint_adt ~newtype:(match type_of env x with Matchable (_, n, _, _, _) -> n | _ -> false) env (entry_name env tid) disc shapes)
let cell_shape env l pos c =
  let tid = tid_of env l c in
  let mid, disc, cs = find_matchable env l tid in
  let phantom = marker env l tid cs c = Erased in
  (match type_of env mid with
   | Matchable (_, true, _, _, _) when not phantom -> error l "newtype constructors have no cells"
   | Matchable (_, _, true, _, _) when not env.in_extern -> error l "extern constructors have no cells outside an extern model"
   | _ -> ());
  if phantom && pos <> Erased then error_in env l "%s is phantom, so its cell is used only in an erased position" (qname env c);
  let params, ret = ctor_type env l c in
  let shapes = shapes env l cs in
  let a = mint_adt env (entry_name env tid) disc shapes in
  let ct = { V.cname = entry_name env c; cid = c; index = Option.value (discriminant shapes c) ~default:0;
    arity = List.length (runtime params); adt = a } in
  (ct, params, ret)

let cells_allowed ?(phantom = false) env mid = match type_of env mid with
  | Matchable (_, nt, ext, _, _) -> (phantom || not nt) && (not ext || env.in_extern)
  | _ -> false

let missing env l form sres cs =
  let note (c, trial) =
    let e = entry env c in
    (if Reader.placed e.at then (e.at, Printf.sprintf "value constructor %s, which is declared here" (qname env c)) else (l, Printf.sprintf "value constructor %s, which is built in" (qname env c)))
    :: forced_notes env l sres trial in
  error_with l (List.concat_map note cs) "this %s is missing a branch for the following unrefuted constructor%s:" (tick (speller env form)) (if List.length cs = 1 then "" else "s")

let field_count env l what noun c params needed got rule =
  error_with l (declared_as env c) "%s of %s expects %s, got %d%s" (respell env what) (qname env c) (counted needed noun) got
    (match show_tele env params with [] -> "" | ss -> ": expected " ^ rule ^ " " ^ tick (String.concat " " ss))

let slot_count env l what noun c params got =
  field_count env l what noun c params (List.length (runtime params)) got "one for each non-erased field of"

let annotated env form ann tele expect = lazy (
  let enclosing = "the enclosing `" ^ form ^ "`" in
  { owner = respell env enclosing; noun = "return value"; shown = show_tele env (List.map2 (fun m (e : entry) -> { e with mult = m }) expect tele);
    anchors = [ (Reader.loc ann, respell env ("the return annotation of " ^ enclosing ^ " is here")) ] })

let binder_count env l what c mode ?(extra = false) got tele =
  let n = List.length tele in
  error_with l (declared_as env c) "%s on %s under `%s` expects %s, got %d%s" (respell env what) (qname env c) (speller env (mult_name mode))
    (if extra then Printf.sprintf "%d or %d binders" (n - 1) n else counted n "binder") (List.length got) (expected (show_tele env tele))

let is_entry ?(mult = Many) ?place t = { name = None; subterm = false; mult; sg = Is t; place; loc = Reader.nowhere }

let cell_entry c tele mode place =
  let n = List.length tele in
  let slots = List.concat (List.mapi (fun j (e : entry) -> if stored e then [ SlotOf (Bound (n - 1 - j)) ] else []) tele) in
  { name = None; subterm = false; mult = mode; sg = Ty (Cell (Var c, slots)); place; loc = Reader.nowhere }

(* The cell binder after the fields is optional, at `many` as at `unique` (the owner's decision in chat;
   DESIGN.md section 23). *)
let pattern env what mode (scrut : res) l c mults extra fields =
  let tele, _ = ctor_type env l c in
  let n = List.length tele in
  let has_cell = extra && List.length fields = n + 1 in
  if List.length fields <> n && not has_cell then
    binder_count env l what c mode ~extra fields (List.map2 (fun m (e : entry) -> { e with mult = m }) mults tele @ if extra then [ cell_entry c tele mode scrut.place ] else []);
  if not has_cell then (fields, None) else
  let cell = List.nth fields n in
  (List.filteri (fun i _ -> i < n) fields, Some ((binder_or l cell "a cell binder"), loc cell))

let pattern_cell env l mult scrut c fids name =
  match name with
  | None -> (env, None)
  | Some (name, at) ->
      let _, params, _ = cell_shape env l mult c in
      let slots = List.map slot_of (runtime_ids params fids) in
      let state = match scrut.term with Var x -> (entry env x).state | _ -> Hypothetical in
      let x, env = bind env ~word:true ~at name mult state (Cell (Var c, slots)) in
      track env Optional x;
      (placed env x scrut.place, Some x)

let bind_cell code cell body = match cell with None -> body | Some x -> V.CLet ([x],code,body)

let warn_use env l what t =
  match canon env t with
  | Var x when not env.unwarned -> (
      let means r = match NameMap.find_opt (Src r.Reader.name) env.scope.named with Some y -> canon env (Var y) = Var x | None -> false in
      match IntMap.find_opt x env.warned, List.filter (fun r -> Reader.covers r l && means r) (Option.value ~default:[] (Hashtbl.find_opt Reader.regions (Reader.file_of l))) with
      | Some (pl, msg), [] -> warn_at l [ (pl, Printf.sprintf "`;! warn` for %s is here" (qshow env t)) ] "%s %s: %s" what (qshow env t) msg
      | Some _, rs -> List.iter (fun r -> r.Reader.used <- true) rs
      | None, _ -> ())
  | _ -> ()

let pragma env l = function
  | [ Atom (_, Src "warn"); Atom (nl, n); Atom (_, Src msg) ] -> (
      let x = match NameMap.find_opt n env.scope.named with Some x -> x | None -> error nl "`;! warn` names %s, which is not in scope%s" (tick_name n) (hint env n) in
      match canon env (Var x), canon env (type_of env x) with
      | Var c, (TyCtor _ | ValCtor _ | Fn _ | UniqueFn _) -> (
          match IntMap.find_opt c env.warned with
          | Some (pl, _) -> error_with l [ (pl, "the first is here") ] "second `;! warn` for %s" (tick_name n)
          | None -> { env with warned = IntMap.add c (l, msg) env.warned })
      | _ -> error nl "`;! warn` names %s, which is neither a constructor nor a function" (tick_name n))
  | [ Atom (_, Src "warn") ] -> error l "`;! warn` needs a name and a message"
  | [ Atom (_, Src "warn"); _ ] -> error l "`;! warn` needs a message after the name"
  | _ -> error l "`;! warn` needs a name and a message"

let mint_level env ~at name = bind env ~minted_level:true ~at name Erased (settled env V.VToken) Prelude.level_term

let rec elab_term ?expect env raw =
  let env, raw = erased_reads (expand_one named_head) env raw in
  match raw with
  | Wild l -> let x, env = bind env ~meta:true ~at:l None Erased Hypothetical type_term in (env, Var x)
  | Handle (_, x, MintedType, _, _) -> refer x; let t = (minted_fact env x).ty in (enter_mentioned env t, t)
  | Atom _ | Handle _ | Nat _ | Char _ | Str _ -> let env, x = atom_entry env raw in (env, Var x)
  | List (l, []) -> error l "empty form"
  | List (l, head :: args) -> (
      match special_of env head with
      | Some sp -> elab_type_form env l sp args
      | None -> (
          let env, args = erased_reads spliced env args in
          let env, x = entry_named env l head "a constructor" in
          let h = Var x in
          match canon env (infer env l h) with
          | (TyCtor tele | ValCtor (tele, _)) as ty -> let env, acc = elab_term_args env l ~callee:(describe env Erased head h ty) ?expect tele h args in (env, App (h, List.rev acc))
          | ty -> error l "%s has type %s and cannot be applied in a type" (qshow env h) (qshow env ty)))

and elab_type_form env l sp args =
  match (sp, args) with
  | Sp.Cell, c :: slots ->
      let c = ctor_var env l c in
      let ct, params, _ = cell_shape env l Erased c in
      if List.length slots <> ct.V.arity then slot_count env l "the type former `Cell`" "slot" c params (List.length slots);
      let env, slots = List.fold_left_map (fun env s -> let env, s = elab_term env s in check_type env l (infer env l s) Prelude.slot_term; (env, s)) env slots in
      (env, Cell (Var c, slots))
  | (Sp.Fn | Sp.UniqueFn), lv :: rest ->
      let env, lv = elab_term env lv in
      check_type env l (infer env l lv) Prelude.level_term;
      let ps, rs = split_arrow env l rest in
      let env, ty, _ = elab_fn_type ~unique:(sp = Sp.UniqueFn) env lv ps rs in
      (env, ty)
  | Sp.TyCtor, _ -> let ps, ret = split_arrow env l args in elab_tyctor env l ps ret
  | Sp.ValCtor, _ -> let env', _, _, t = elab_valctor env l args in (carry env env', t)
  | Sp.Matchable, d :: rest ->
      let ms, rest = marks env [ Sp.NewtypeMark; Sp.Extern ] rest in
      let t, cs = match rest with t :: cs -> (t, cs) | _ -> error l "%s" (help env (Sp.misuse sp)) in
      let ctor env = function
        | List (cl, [ m; c ]) -> let m = mult_or env cl m in
            if m = Unique then error_in env cl "a `Matchable` constructor cannot be `unique`";
            let env, x = atom_entry_or env cl c "a constructor" in
            (env, (m, Var (named_of env cl "a constructor" x)))
        | raw -> error (loc raw) "expected a constructor marker" in
      let env, cs = List.fold_left_map ctor env cs in
      (env, Matchable (disc_of env l d, List.mem Sp.NewtypeMark ms, List.mem Sp.Extern ms, Var (tyname env l t), cs))
  | (Sp.Fn | Sp.UniqueFn | Sp.Matchable), _ -> error l "%s" (help env (Sp.misuse sp))
  | Sp.DumpContext, _ -> dump_context env l Dump.Type args
  | Sp.CompileError, _ -> compile_error named_head Erased env l args
  | (Sp.LevelOf | Sp.MatchableOf | Sp.DelegateOf | Sp.NumeralOf | Sp.SlotOf | Sp.AtFnOf), _ -> fetched env l sp args
  | _ -> error l "%s cannot appear in a type" (tick (speller env (Sp.name sp)))

(* `(slot-of x)`: the automatic slot of `x`'s binder (section 35), a direct variable reference and no use. *)
and slot_var env l = function
  | [ a ] ->
      let env, x = atom_entry_or env (loc a) a "a direct variable reference" in
      unwritten env (loc a) "`slot-of`" x;
      (env, x)
  | _ -> error l "%s" (help env (Sp.misuse Sp.SlotOf))

and unwritten env l form x = if List.mem x env.ctor_tele then error_in env l "%s cannot name %s, an entry of a constructor's telescope still being written" form (qname env x)

and fetched env l sp args =
  match (sp, args) with
  | Sp.SlotOf, _ -> let env, x = slot_var env l args in (env, Var (entry env x).slot)
  | Sp.AtFnOf, [ g ] -> (
      let env = admitted env g in
      let g = named env l "a function name" g in
      match List.find_opt (fun x -> (entry env x).name = None && is_atfn_proof env x g) env.scope.ids with
      | Some y -> (env, Var y)
      | None -> error l "%s has no `AtFn` proof in scope" (qname env g))
  | Sp.LevelOf, [ f ] -> (
      let env, f = elab_term env f in
      settle env l f;
      match canon env (infer env l f) with
      | Fn (lv, _, _) | UniqueFn (lv, _, _) -> (env, lv)
      | ty -> error_in env l "`level-of`: %s : %s is not a function" (qshow env f) (qshow env ty))
  | Sp.MatchableOf, [ t ] -> let env = admitted env t in let x, _, _ = find_matchable env l (tyname env l t) in (env, Var x)
  | Sp.NumeralOf, [ e ] -> (
      match lit_of e with
      | None -> error_in env l "`numeral-of` takes a literal, not %s" (tick (Reader.show e))
      | Some lit -> (
          let env = intern env l lit in
          match (Hashtbl.find literal_rows (Literal.key lit)).lit_proof with
          | Some p -> (env, Var p)
          | None -> error l "%s is a string literal, which carries no `Numeral` proof" (Reader.show e)))
  | Sp.DelegateOf, [ g ] -> (
      let env = admitted env g in
      let g = named env l "a function name" g in
      let about x = (entry env x).name = None && (match type_of env x with App (Var c, [ _; _; Var g'; _; _; _ ]) -> c = Prelude.delegate && g' = g | _ -> false) in
      match List.find_opt about env.scope.ids with Some y -> (env, Var y) | None -> error l "%s has no `Delegate` proof in scope" (qname env g))
  | _ -> error l "%s" (help env (Sp.misuse sp))

and compile_text head pos env l sp = function
  | [ raw ] ->
      let env, x, m = match raw with
        | Atom _ | Handle _ | Nat _ | Char _ | Str _ -> let env, x = atom_entry env raw in (env, x, made env raw x)
        | _ -> (match head env (List (loc raw, [ raw ])) with
            | env, List (_, [ Handle (_, x, _, m, _) ]) -> (env, x, m)
            | env, List (_, [ List (_, [ _; a ]) ]) -> let env = admitted env a in let x = reference env (loc a) a "a name" in (env, x, made env a x)
            | _ -> assert false) in
      let str = match prelude_id env "String" with Some t -> App (Var t, []) | None -> error l "%s needs the prelude's `String`, which `--no-prelude` leaves out" (tick (speller env (Sp.name sp))) in
      (match (if m = Erased then None else settled_value env x str) with
       | Some v -> (read_special pos env raw, str_host env l v)
       | None ->
           let e = entry env x in
           error_in env (loc raw) "the message of %s must be a `Settled`, non-erased `String`; %s %s" (tick (speller env (Sp.name sp))) (qname env x)
             (if m = Erased then "is erased" else if e.state = Hypothetical then "is `Hypothetical`" else "has type " ^ qshow env (minted_type env x) ^ ", not the prelude's `String`"))
  | _ -> error l "%s" (help env (Sp.misuse sp))

and compile_error : 'a. (Env.t -> raw -> Env.t * raw) -> mult -> Env.t -> Reader.loc -> Reader.raw list -> 'a = fun head pos env l args -> error l "%s" (snd (compile_text head pos env l Sp.CompileError args))

(* The form's arguments are terms in section 9's grammar, each shown with its type where it has one. *)
and dump_context : 'a. Env.t -> Reader.loc -> Dump.goal -> Reader.raw list -> 'a = fun env l goal args ->
  let env, focus = List.fold_left_map (fun env raw ->
    let env, t = elab_term env raw in
    (env, (Reader.show raw, t, try Some (infer env l t) with Error _ -> None))) env args in
  Dump.report ~show_value env l goal focus

and elab_fn_type ?(unique = false) env lv ps rs =
  let env', ids, params = elab_tele env ~places:true ~subterm:true ps in
  let env', _, rets = elab_tele env' ~places:true ~ids:(List.rev ids) rs in
  (carry env env', (if unique then UniqueFn (lv, params, rets) else Fn (lv, params, rets)), ids)

and elab_tyctor env l ps ret =
  let env', _, tele = elab_tele env ~ctor:true ~mults:(fun _ l -> function None -> Some Erased | Some m -> no_mult env "a type constructor's parameters" l m) ps in
  let env' = match ret with [ r ] -> let env', r = elab_term env' r in check_equal env' l r type_term; env' | _ -> error_in env l "`TyCtor` returns `Type`" in
  (carry env env', TyCtor tele)

and elab_valctor env l items =
  let ps, ret = split_arrow env l items in
  let env', ids, tele = elab_tele env ~ctor:true ps in
  let env', ret = match ret with [ r ] -> elab_type env' r | _ -> error l "a constructor returns one type" in
  settle env' l ret;
  (match canon env' ret with
  | App (Var t, _) when (not (List.mem t ids)) && (match type_of env' t with TyCtor _ -> true | _ -> false) -> ()
  | _ -> error l "a constructor returns an application of a type constructor in scope, not %s" (qshow env' ret));
  (env', tele, ret, ValCtor (tele, abstract_slots env' (List.rev ids) ret))

and disc_of env l d = match special_of env d with Some Sp.Enum -> Enum | Some Sp.Union -> Union | _ -> error_in env l "expected `enum` or `union`"

and elab_type env raw =
  let env, t = elab_term env raw in
  ignore (solve ~raw "type" env (loc raw) (infer env (loc raw) t) type_term);
  (env, t)

and elab_sg env = function
  | `Ty t -> let env, t = elab_type env t in (env, Ty t)
  | `Is t -> let env, t = elab_term env t in (env, Is t)

and level_var ?(alt = "") env l raw =
  let env, t = elab_term env raw in
  match canon env t with Var x when equal (type_of env x) Prelude.level_term -> (env, x) | t -> error l "%s is not a level%s" (qshow env t) alt

and level_binder env l raw =
  let env, t = elab_term env raw in
  match t with Var x -> (env, x) | t -> error l "%s is not a level" (qshow env t)

(* Elaborates source entries into a closed telescope, binding each name for the entries after it.
   [ids]: binders already in force, innermost first; [mults] maps an entry's index and declared multiplicity to its actual one. *)
and elab_tele env ?(places = false) ?(ctor = false) ?(subterm = false) ?(ids = []) ?(mults = fun _ _ m -> m) ?holes ?written entries =
  let env, entries = erased_reads spliced_entries env entries in
  let entries = List.concat_map (parse_entry env) entries in
  let _, env, ids, tele =
    List.fold_left
      (fun (i, env, ids, tele) e ->
        if e.s_subterm && not subterm then error_in env e.s_loc "`subterm` is not allowed here";
        let mult = match mults i e.s_loc e.s_mult with Some m -> m | None -> error e.s_loc "entry %s needs a multiplicity" (tick (spell_binder e.s_name)) in
        let env, sg = match e.s_sg with Some s -> elab_sg env s | None -> error_in env e.s_loc "entry %s needs a type or an `is` clause" (tick (spell_binder e.s_name)) in
        let ty, rule = fact_of env e.s_loc sg in
        let env = Option.fold ~none:env ~some:(admitted env) e.s_place in
        let place = Option.map (fun raw ->
          if not places then error_in env e.s_loc "`at` is allowed only on function telescope and match annotation entries";
          if lit_of raw <> None then error_in env (loc raw) "`at` names a variable, not a literal";
          let x = reference env (loc raw) raw "a location variable" in
          unwritten env (loc raw) "`at`" x;
          refer ~live:(mult <> Erased && not env.usage_erased) x;
          if (entry env x).mult = Erased && mult <> Erased then error_in env (loc raw) "`at` needs a variable declared `many` or `unique`";
          slot_of x) e.s_place in
        let name = e.s_name in
        let x, env = at e.s_loc (fun () -> bind env ?holes ?written ~at:e.s_loc name mult Hypothetical ty ?rule) in
        pend x;
        let env = placed env x place in
        (i + 1, { env with ctor_tele = (if ctor then x :: env.ctor_tele else env.ctor_tele) }, x :: ids, { name; subterm = e.s_subterm; mult; sg = map_sg (abstract_slots env ids) sg; place = Option.map (abstract_slots env ids) place; loc = e.s_loc } :: tele))
      (0, env, ids, []) entries
  in
  (env, List.rev ids, List.rev tele)

(* Checks [args] against [tele] with [elab env mult arg expect]; returns the argument terms innermost first,
   and their code. A meta stands for each parameter (DESIGN.md section 50): an argument written `_` is left to it, and
   is an error unless erased where it stands; any other argument is checked against its parameter and bound
   to its meta. [result] is the application's result telescope over the parameters' metas, unified with
   [expect] eagerly, where a `_` is present, before any argument is read, and again, reporting the mismatch,
   when a `_` would otherwise stay unsolved at the closing paren; every `_` is solved by then or refused. *)
and check_args env loc ~callee:c ?(what = "argument") ?expect ?(result = fun _ -> []) ?(pos = Erased) ?(boundary = true) ?(bind_args = false) ?(ctor = false) ?(named = []) tele args elab =
  if List.length tele <> List.length args then count_error env loc c what tele (List.length args);
  let ats = List.map (fun a -> if wild a then Reader.loc a else Reader.nowhere) args in
  let env, metas = open_tele env ~meta:true ~names:(anon tele) ~ats ~mults:(List.map (fun _ -> Erased) tele) tele in
  let mvars = List.rev_map (fun x -> Var x) metas in
  let wilds = List.exists wild args in
  let against ~strict env = match expect with Some tele when wilds -> solve_tele ~strict env loc tele (result mvars) | _ -> env in
  let env = against ~strict:false env in
  let env, acc, codes, ats =
    List.fold_left2
      (fun (env, acc, codes, ats) (i, e, m) arg ->
        let sg = map_sg (instantiate acc) e.sg in
        let about = lazy (argument c i e.name ^ ": ", Lazy.force c.notes) in
        if wild arg then (
          if under pos e.mult <> Erased then error_with (Reader.loc arg) (Lazy.force c.notes) "%s`_` stands only for an erased argument, and this one is not erased" (fst (Lazy.force about));
          if e.place <> None then error_with (Reader.loc arg) (Lazy.force c.notes) "%s`_` cannot stand for an argument written `at`" (fst (Lazy.force about));
          if List.mem i named then error_with (Reader.loc arg) (Lazy.force c.notes) "%s`_` cannot stand for an argument whose slot the signature names" (fst (Lazy.force about));
          (env, Var m :: acc, codes, ats))
        else
          let env, r, code = elab env (c.used e.mult) arg (Some [ { e with sg } ]) in
          let r = if r.place = None && (e.place <> None || List.mem i named) then { r with place = term_place env r.term } else r in
          let env = solve_sg ~raw:arg ~about env (Reader.loc arg) sg r in
          let env, r, code =
            if bind_args && pos <> Erased && e.mult <> Erased then (
              match r.term, code with
              | Var _, V.CVar _ -> (env, r, code)
              | _ ->
                  let x, env = bind env ~holes:true ~word:true ~temporary:true None r.erasure (ran_state env r.erasure code) r.ty ~rule:r.term in
                  let env = if env.run_pos then env else { env with pending = (x, code) :: env.pending } in
                  (placed env x r.place, { r with term = Var x; place = Some (slot_of x) }, V.CVar x))
            else if bind_args && not ctor && List.mem i named && (match r.term with Var _ -> false | _ -> true) then
              let x, env = bind env ~holes:true ~temporary:true None r.erasure (ran_state env r.erasure code) r.ty ~rule:r.term in
              (placed env x r.place, { r with term = Var x; place = Some (slot_of x) }, code)
            else (env, r, code)
          in
          (* an argument for a parameter written `at` must sit where its target does, and is not passed (section 36) *)
          let target = function SlotOf (Bound k) as p -> Option.value (term_place env (List.nth acc k)) ~default:(instantiate acc p) | p -> instantiate acc p in
          let ats = match e.place with Some p -> (arg, i, e.name, target p, r.place) :: ats | None -> ats in
          let env = solve ~about "value" env (Reader.loc arg) r.term (Var m) in
          let env = match r.term with Var y when not (is_meta env y) -> placed env m (Some (slot_of y)) | _ -> env in
          (env, r.term :: acc, (if e.mult <> Erased && e.place = None then code :: codes else codes), ats))
      (env, [], [], []) (List.mapi (fun i (e, m) -> (i, e, m)) (List.combine tele metas)) args
  in
  let env = if boundary && List.exists (has_meta env) acc then against ~strict:true env else env in
  if boundary then List.iteri (fun i t -> if has_meta env t then
    let what = argument c i (List.nth tele i).name and arg = List.nth args i in
    if wild arg then error_with ~hints:(hole_hints env t) (Reader.loc arg) (Lazy.force c.notes) "%s is `_` and cannot be inferred" what
    else unsolved ~about:(what ^ ": ", Lazy.force c.notes) (Reader.loc arg) env t) (List.rev acc);
  List.iter (fun (arg, i, name, p, place) -> if not (Option.fold ~none:false ~some:(same_slot env p) place) then
    error_with (Reader.loc arg) (Lazy.force c.notes) "%s does not satisfy `at` %s" (argument c i name) (qshow env p)) (List.rev ats);
  (env, List.map (metaless env) acc, List.rev codes)

(* [result] entrywise against [expect]: terms where both are `is` entries, types always. Not [strict]: a
   failure leaves the environment as it was. *)
and solve_tele ~strict env loc expect result =
  let attempt () =
    count_check loc expect result;
    List.fold_left2
      (fun env e r ->
        let env = match (e.sg, r.sg) with Is a, Is b -> solve "value" env loc b a | _ -> env in
        let ty = function Ty t -> Some t | Is t -> if has_dangling t then None else Some (infer env loc t) in
        match (ty r.sg, ty e.sg) with Some a, Some b -> solve "type" env loc a b | _ -> env)
      env expect result
  in
  if strict then attempt () else try attempt () with Error _ -> env

(* A constructor application is a pure term (DESIGN.md section 9), so it is no boundary: its holes may stay
   open past its paren for the arguments after it, or the position, to solve. *)
and elab_term_args env loc ~callee ?what ?expect tele ret args =
  let env, acc, _ =
    check_args env loc ~callee ?what ?expect ~result:(ctor_result ret) ~boundary:false ~bind_args:true ~ctor:true tele args (fun env _ a expect ->
        let env, t = elab_term ?expect env a in
        (env, term_res env (Reader.loc a) t, V.CErased))
  in
  (env, acc)

let ctor_tele env l sp h = match canon env (infer env l h), sp with
  | TyCtor tele, Sp.SettledTyApply | ValCtor (tele, _), Sp.SettledValApply -> tele
  | ty, _ -> error l "%s takes a handle to a %s first, and %s has type %s" (tick (Sp.name sp)) (if sp = Sp.SettledTyApply then "type constructor" else "value constructor") (qshow env h) (qshow env ty)

let () = applied_handles := fun env l sp h raws ->
  let tele = ctor_tele env l sp h in
  let env, t = elab_term env (List (l, raws)) in
  (t, infer env l t, tele)

(* [ids] as in [open_tele]. *)
(* Where each of a body's results is written: the entries of a final values form holding one per result, else
   the final expression, which is what a mismatch with the returns points at. *)
let result_sites env loc body n =
  match List.rev body with
  | List (_, v :: entries) :: _ when is_special env v Sp.Values && List.length entries = n -> List.map (fun e -> (Reader.loc e, Some e)) entries
  | final :: _ -> List.init n (fun _ -> (Reader.loc final, if n = 1 then Some final else None))
  | [] -> List.init n (fun _ -> (loc, None))

(* A result that is not a variable is bound to an anonymous one for the entries after it, so that a later
   entry's `at` can name the slot it sits in (section 15). *)
let check_results env loc ?(ids = []) body tele ress =
  count_check loc tele ress;
  let env = List.fold_left2 (fun (env, acc) (e, (rl, raw)) r ->
    let env = solve_sg ?raw env rl (map_sg (instantiate acc) e.sg) r in
    (match Option.map (instantiate acc) e.place with
     | Some p ->
         if not (Option.fold ~none:false ~some:(same_slot env p) r.place) then error_in env rl "return does not satisfy `at` %s" (qshow env p)
     | _ -> ());
    let env, t = match r.term, r.place with
      | Var _, _ | _, None -> (env, r.term)
      | t, Some p -> let y, env = bind env ~holes:true None r.erasure Hypothetical r.ty ~rule:t in (place env y p, Var y) in
    (env, t :: acc)) (env, ids) (List.combine tele (result_sites env loc body (List.length tele))) ress |> fst in
  List.iter2 (fun (l, _) -> settle_res env l) (result_sites env loc body (List.length ress)) ress

let rec project_code keep code =
  if List.for_all Fun.id keep then code else
  match code with
  | V.CLet (ids, rhs, rest) -> V.CLet (ids, rhs, project_code keep rest)
  | V.CLetRec (fs, rest) -> V.CLetRec (fs, project_code keep rest)
  | V.CMatch m -> V.CMatch { m with branches = List.map (fun (i, ids, b) -> (i, ids, project_code keep b)) m.branches; default = Option.map (project_code keep) m.default }
  | V.CValues cs ->
      let bindings, results = List.fold_left2 (fun (bs, rs) k c ->
        match c with
        | V.CVar _ | V.CConst _ | V.CErased -> (bs, if k then c :: rs else rs)
        | _ -> let x = fresh () in (([x], c) :: bs, if k then V.CVar x :: rs else rs)) ([], []) keep cs in
      List.fold_left (fun rest (ids, rhs) -> V.CLet (ids, rhs, rest)) (V.CValues (List.rev results)) bindings
  | V.CVar _ | V.CConst _ | V.CErased -> V.CValues []
  | V.CAbsurd -> V.CAbsurd
  | _ ->
      let ids = List.map (fun _ -> fresh ()) keep in
      V.CLet (ids, code, V.CValues (List.filter_map (fun (x, k) -> if k then Some (V.CVar x) else None) (List.combine ids keep)))

let mint env ty =
  let x, env = bind env None Erased Hypothetical ty in
  (env, res_of env x)

(* [code] produces the runtime entries of [tele], bound to [ids]; the entries written `at` are read from the
   words the caller holds (section 36). [init]: the terms the telescope's earlier binders stand for, innermost first. *)
let reconstruct ?(always = false) ?(init = []) ?expect env l tele ids code =
  if not always && List.for_all (fun (e : entry) -> e.place = None) tele then code else
  let physical = runtime_ids tele ids in
  let env = with_words env physical in
  let expect = Option.value expect ~default:(List.map (fun (e : entry) -> e.mult) tele) in
  let _, results = List.fold_left2 (fun (acc, rs) ((e : entry), m) x ->
    (Var x :: acc, if m = Erased then rs else V.CVar (match e.place with Some p -> location_var env l (instantiate acc p) | None -> x) :: rs)) (init, []) (List.combine tele expect) ids in
  if physical = [] && code = V.CValues [] then V.CValues (List.rev results) else V.CLet (physical, code, V.CValues (List.rev results))

let keeps tele = List.filter_map (fun (e : entry) -> if e.mult = Erased then None else Some (e.place = None)) tele

let provable_subterm env a b = is_strict_subterm (canon env a) (canon env b)

let prove_subterm env l a b =
  if not (provable_subterm env a b) then error l "%s is not a strict subterm of %s" (qshow env a) (qshow env b);
  mint env (proof_type Prelude.subterm [ infer env l a; a; infer env l b; b ])

let introduced env x = (entry env x).introduced
let provable_predates env x lvl = (entry env lvl).minted_level && introduced env x >= 0 && introduced env x < introduced env lvl

let prove_predates env l x lvl =
  let who y = if (entry env y).name = None then qshow env (Var y) else qname env y in
  if not (entry env lvl).minted_level then error_in env l "%s is not a level minted by `def-lvl`" (who lvl);
  if introduced env x < 0 then error l "%s is %s, which has no introduction order" (qname env x) (if Hashtbl.mem literal_of x then "a literal" else "a constant a macro minted");
  if introduced env x >= introduced env lvl then error l "%s was not in scope when level %s was minted" (who x) (who lvl);
  mint env (proof_type Prelude.predates [ type_of env x; Var x; Var lvl ])

(* The post-erasure normalizer behind the `tail` and `delegate` checks (section 19, ASSUMPTIONS 164, 189): lets
   that only rename, return exactly what they bind, or bind constants nothing mentions are folded away, so a
   marked call stands in tail position in the code that runs. *)
let normalize code =
  let rec resolve sub x = match List.assoc_opt x sub with Some y -> resolve sub y | None -> x in
  let vars_of cs = List.map (function V.CVar x -> x | _ -> -1) cs in
  let returns ids = function V.CValues cs -> vars_of cs = ids | V.CVar x -> ids = [ x ] | _ -> false in
  let constant = function V.CValues cs -> List.for_all (function V.CConst _ -> true | _ -> false) cs | _ -> false in
  let atoms = function V.CVar _ -> true | V.CValues cs -> List.for_all (function V.CVar _ | V.CConst _ | V.CErased -> true | _ -> false) cs | _ -> false in
  let rec mentions x c =
    (match c with V.CVar y -> y = x | V.CLetRec (fns, _) -> List.exists (fun (_, f) -> mentions x f.V.body) fns | _ -> false)
    || List.exists (mentions x) (V.subcodes c)
  in
  let rec norm sub = function
    | V.CVar x -> V.CVar (resolve sub x)
    | V.CLet (ids, rhs, rest) -> (
        match norm sub rhs with
        | V.CLet (xs, a, b) -> norm sub (V.CLet (xs, a, V.CLet (ids, b, rest)))
        | V.CLetRec (fs, b) -> norm sub (V.CLetRec (fs, V.CLet (ids, b, rest)))
        | V.CMatch m when atoms (norm sub rest) -> norm sub (V.CMatch { m with branches = List.map (fun (i,xs,b) -> i,xs,V.CLet(ids,b,rest)) m.branches; default = Option.map (fun b -> V.CLet(ids,b,rest)) m.default })
        | V.CVar y when List.length ids = 1 -> norm ((List.hd ids, y) :: sub) rest
        | V.CValues cs when List.length cs = List.length ids && not (List.mem (-1) (vars_of cs)) ->
            norm (List.combine ids (vars_of cs) @ sub) rest
        | rhs ->
            let rest = norm sub rest in
            if returns ids rest then rhs
            else if constant rhs && not (List.exists (fun x -> mentions x rest) ids) then rest
            else V.CLet (ids, rhs, rest))
    | V.CLetRec (fns, rest) ->
        V.CLetRec (List.map (fun (x, f) -> (x, { f with V.body = norm sub f.V.body })) fns, norm sub rest)
    | c -> V.map_code (norm sub) c
  in
  norm [] code

(* Normalized code that erases to nothing, or to a reordering of variables (section 40; section
   39): renames, loads and a match whose every branch erases to nothing, dispatch included; never a store, an
   allocation or a call that was not skipped. *)
let rec erases_to_nothing = function
  | V.CApp _ | V.CCellAlloc _ | V.CCellWrite _ | V.CCellCopy _ | V.CWorldDo _ | V.CPrim _ -> false
  | V.CLetRec (_, rest) -> erases_to_nothing rest
  | c -> List.for_all erases_to_nothing (V.subcodes c)

let must_erase env l what code =
  if not (erases_to_nothing (normalize code)) then error_in env l "%s must erase to nothing, or to a reordering of variables; this one stores, allocates or calls" what

let demanded env demand mult ty =
  if mult = Erased then mult else
  match demand with
  | Fixed -> mult
  | CallableHead pos -> (match canon env ty with Cell _ -> pos | UniqueFn _ -> Unique | _ -> Many)
  | Driver -> if nullary env "Program" ty then Unique else Many

let rec elab_expr ?sink ?(demand = Fixed) ?(cc = V.Plain) ?tele ?(final = false) env expect raw : Env.t * res list * V.code =
  let l = loc raw in
  let outer_erased = env.usage_erased in
  let env = { env with usage_erased = outer_erased || pos_of env expect = Erased } in
  let start = !counter in
  let env, ress, code = elab_form ?sink ~final demand cc tele env expect raw in
  let ress = List.map (fun r -> { r with term = metaless env r.term; ty = metaless env r.ty }) ress in
  count_check ?sink l expect ress;
  List.iter2 (fun m r ->
    let m = demanded env demand m r.ty in
    if not outer_erased then Option.iter (fun how -> error l "internal: an unchecked result %s" how) (misuse m r.erasure)) expect ress;
  let env, code = if env.run_pos then run_form env l start expect ress code else (env, code) in
  ({ env with usage_erased = outer_erased }, ress, code)

and run_form env l start expect ress code =
  let erased = pos_of env expect = Erased in
  let values = spread expect (if erased then [] else run_code env code) in
  let minted env x = x > start && (entry env x).state = Hypothetical && not (entry env x).meta in
  let env = List.fold_left2 (fun env r v -> match r.term with Var y when minted env y -> set_state env y (Settled v) | _ -> env) env ress values in
  let rec sweep env = function
    | x :: rest when x > start ->
        if not (minted env x) then sweep env rest
        else if (entry env x).mult = Erased then sweep (set_state env x (Settled V.VToken)) rest
        else error_in env l "internal: run-position entry %s has no value" (qname env x)
    | _ -> env in
  let env = sweep env env.scope.ids in
  let word r v = match r.term with Var y when (entry env y).state <> Hypothetical -> V.CVar y | _ -> V.CConst v in
  let codes = List.filter_map (fun ((m, r), v) -> if m = Erased then None else Some (word r v)) (List.combine (List.combine expect ress) values) in
  (env, if erased then V.CErased else match codes with [ c ] -> c | cs -> V.CValues cs)

and elab_expr1 ?demand ?cc ?tele env mult raw =
  let env, ress, code = elab_expr ?demand ?cc ?tele env [ mult ] raw in
  (env, List.hd ress, code)

and elab_erased env raw =
  let env, r, _ = elab_expr1 env Erased raw in
  settle_res env (loc raw) r;
  (env, r.term)

and elab_form ?sink ~final demand cc expect_tele env expect raw =
  let pos = pos_of env expect in
  let env, raw = expand_one (!settle_head pos) env raw in
  match raw with
  | Atom (l, _) | Handle (l, _, _, _, _) | Nat (l, _) | Char (l, _) | Str (l, _) | Wild l ->
      let env, x = atom_entry env raw in
      (use env l ~written:(Reader.show raw) ?made:(handle_made raw) (demanded env demand pos (type_of env x)) x, [ { (res_of env x) with erasure = made env raw x } ], if pos <> Erased then V.CVar x else V.CErased)
  | List (l, []) -> error l "empty form"
  | List (l, head :: args) -> (
      match special_of env head with
      | Some sp when Sp.has_role sp -> not_a env "not an expression" raw
      | Some sp -> elab_special ?sink ?final:(if final then Some (loc head) else None) demand expect_tele (read_special pos env head) expect l sp args
      | None -> (
          let env, args = spliced env args in
          let env, h, hcode = elab_head env pos l head in
          let hty = canon env h.ty in
          if nullary env "Macro" hty then macro_refused env l head;
          let callee pos = describe env pos head h.term hty in
          let env, rs, code = match hty with
          | TyCtor tele ->
              let c = callee pos in
              if pos <> Erased then error_with l (Lazy.force c.notes) "%s applied in a non-erased position" (match head with Atom _ | Handle _ -> "type constructor " ^ Lazy.force c.subject | _ -> Lazy.force c.subject);
              let env, acc = elab_term_args env l ~callee:c ?expect:expect_tele tele h.term args in
              (env, [ { term = App (h.term, List.rev acc); ty = type_term; erasure = Erased; place = None } ], V.CErased)
          | ValCtor (tele, ret) ->
              if pos <> Erased && h.erasure = Erased then error_with l (head_notes env h) "erased constructor %s in a non-erased position" (head_name env h);
              let pos = demanded env demand pos ret in
              if pos <> Erased then warn_use env (loc head) "application of" h.term;
              let env = match h.term with Var x -> use env l (under pos Many) x | _ -> env in
              let env, acc, codes = check_args env l ~callee:(callee pos) ~bind_args:true ~ctor:true ?expect:expect_tele ~result:(ctor_result h.term) ~pos ~boundary:false tele args elab_arg in
              let ctor = match canon env h.term with Var c -> c | _ -> -1 in
              let hollow = ctor >= 0 && hollow env ctor in
              let code = if pos = Erased then V.CErased else if hollow then V.CConst V.VVacant else if newtype_of env ctor <> None then List.hd codes else V.CApp (hcode, codes, V.Ctor) in
              let place = if hollow then Some (slot_of Prelude.null) else term_place env (App (h.term, List.rev acc)) in
              (env, [ { term = App (h.term, List.rev acc); ty = instantiate acc ret; erasure = pos; place } ], code)
          | Cell (c, slots) -> elab_cell_invoke env expect l (callee pos) h hcode c slots args
          | UniqueFn (lv, params, rets) -> elab_call ~unique:true ?sink ~demand cc env ?tele:expect_tele expect l (loc head) (callee pos) h hcode lv params rets args
          | Fn (lv, params, rets) -> elab_call ?sink ~demand cc env ?tele:expect_tele expect l (loc head) (callee pos) h hcode lv params rets args
          | ty -> error l "%s : %s is not applicable" (qshow env h.term) (qshow env ty) in
          (env, rs, code)))

and elab_arg env m a tele = elab_expr1 ?tele env m a

and elab_head env pos l raw =
  match raw with
  | Atom (_,n) -> let x = var env l n in (env,res_of env x,V.CVar x)
  | Handle (_, x, _, _, _) when computed env raw -> (env,res_of env x,V.CVar x)
  | Wild _ -> error l "`_` is not a name, and nothing is inferred here"
  | _ ->
      let demand = if pos = Erased then Fixed else CallableHead pos in
      let env,r,code = elab_expr1 ~demand env (under pos Many) raw in
      let state, minted, minted_level, order = forwarded env r.erasure r (ran env pos code) in
      let x, env = bind env ?minted ~minted_level ?introduced:order ~word:true ~temporary:true None r.erasure state r.ty ~rule:r.term in
      let env = if env.run_pos || pos = Erased then env else { env with pending = (x, code) :: env.pending } in
      (placed env x r.place,res_of env x,V.CVar x)

and computed_head pos env raw =
  match raw with
  | List (l, (List (hl, _) as h) :: args) when not (named_share env h) ->
      let env, r, _ = elab_head env pos hl h in
      let x = match r.term with Var x -> x | _ -> assert false in
      (env, List (l, Handle (hl, x, MintedIs, (entry env x).mult, Obj.repr V.VToken) :: args))
  | _ -> (env, raw)

and elab_call ?(unique = false) ?(assert_at = false) ?sink ?(demand = Fixed) cc env ?tele expect l hl c callee hcode lv params rets args =
  let pos = pos_of env expect in
  if assert_at && pos = Erased then error l "%s in an erased position" (tick (speller env (Sp.name Sp.At)));
  (* a call of an at-function is skipped (section 39): the proof opened for the callee is what licenses it *)
  let skipped = pos <> Erased && atfn_open env callee.term in
  if assert_at && not skipped then error_with_in env l (head_notes env callee) "%s is not an at-function here: no `AtFn` proof for it is open" (head_name env callee);
  if skipped && cc <> V.Plain then error_in env l "%s marks a call that compiles to one, and a call of at-function %s is skipped" (tick (speller env (match cc with V.Tail -> "tail" | V.NoTail -> "notail" | _ -> "delegate"))) (head_name env callee);
  if pos <> Erased && not skipped then warn_use env hl "call of" callee.term;
  let erased_head = assert_at && not unique in
  if pos <> Erased && not erased_head && callee.erasure = Erased then error_with l (head_notes env callee) "erased function %s called in a non-erased position" (head_name env callee);
  if unique && pos <> Erased && callee.erasure = Many then error_with_in env l (head_notes env callee) "a shared `UniqueFn` %s is callable only erased" (head_name env callee);
  let env = match callee.term with Var x when not erased_head -> use env l (under pos (if unique then Unique else Many)) x | _ -> env in
  let written, args =
    let rec go i found acc = function
      | List (al, [ k; p ]) :: rest when is_special env k Sp.Predates || is_special env k Sp.Subterm ->
          let predates = is_special env k Sp.Predates in
          if found <> None then error al "a call carries at most one decrease annotation";
          if predates && i > 0 then error_in env al "`predates` is written immediately after the callee";
          go i (Some (al, if predates then `Predates p else `Subterm (i, p))) acc rest
      | a :: rest -> go (i + 1) found (a :: acc) rest
      | [] -> (found, List.rev acc)
    in
    go 0 None [] args
  in
  let env, acc, codes = check_args env l ~callee:c ~bind_args:true ~named:(slot_named_params params rets) ?expect:tele ~result:(fun mvars -> instantiate_tele mvars rets) ~pos params args elab_arg in
  let arg_terms = List.rev acc in
  let subterm_params = List.filter_map (fun (i, e) -> if e.subterm then Some i else None) (List.mapi (fun i e -> (i, e)) params) in
  let arg_name i = argument c i (Option.bind (List.nth_opt params i) (fun e -> e.name)) in
  let counterpart al k = match List.nth_opt env.subterms k, env.enclosing with
    | Some x, _ -> x
    | None, g ->
        let i = List.nth subterm_params k in
        let g, notes = match g with Some g -> (Printf.sprintf " %s %s" (kind_name env (type_of env g)) (qname env g), declared_as env g) | None -> ("", []) in
        error_with_in env al (Lazy.force c.notes @ notes) "%s is its `subterm` parameter %d, but the enclosing%s has %s" (arg_name i) (k + 1) g (if k = 0 then "none" else Printf.sprintf "only %d" k) in
  let proof env prove = function Wild _ -> let env, p = prove env in (env, p.term) | p -> elab_erased env p in
  let same cur = equal (canon env lv) (canon env (Var cur)) in
  let inferred () =
    let wild = Wild l in
    let differs j pi = match List.nth_opt env.subterms j with Some x -> not (equal (canon env (List.nth arg_terms pi)) (canon env (Var x))) | None -> false in
    match env.level with
    | At cur when same cur -> (
        match List.find_opt (fun (j, pi) -> differs j pi) (List.mapi (fun j pi -> (j, pi)) subterm_params) with
        | Some (_, i) -> Some (`Subterm (i, wild))
        | None ->
            let hint = match env.enclosing with
              | Some g when not (equal (canon env callee.term) (canon env (Var g))) ->
                  Some (Printf.sprintf "a call to a strictly lower level needs no decreasing argument; consider defining %s at a lower level, or %s at a higher one" (qshow env callee.term) (qshow env (Var g)))
              | _ -> None in
            error_with ?hint l [] "same-level call to %s decreases no subterm argument" (qshow env callee.term))
    | At _ -> Some (`Predates wild)
    | Top -> None
  in
  let check al annotation =
    match (env.level, annotation) with
    | Top, None -> env
    | Top, Some _ -> error l "the top level calls without proofs; drop the decrease annotation (section 20)"
    | At cur, Some (`Subterm (i, p)) when same cur -> (
        let k = match find_index (( = ) i) subterm_params with
          | Some k -> k
          | None ->
              let notes = List.map (fun pi -> (Reader.loc (List.nth args pi), sprintf_in env "%s is a `subterm` parameter" (arg_name pi))) subterm_params in
              error_with_in env al (notes @ Lazy.force c.notes) "%s is not a `subterm` parameter" (arg_name i) in
        List.iteri (fun j pi -> if j < k then check_equal env l (List.nth arg_terms pi) (Var (counterpart al j))) subterm_params;
        let env, p = proof env (fun env -> prove_subterm env l (List.nth arg_terms i) (Var (counterpart al k))) p in
        match expect_proof ~alt:" or `_`" env l Prelude.subterm p with
        | [ _; a; _; b ] -> check_equal env l a (List.nth arg_terms i); check_equal env l b (Var (counterpart al k)); env
        | _ -> assert false)
    | At cur, Some (`Predates p) when not (same cur) -> (
        let callee_level env = match canon env lv with Var m -> m | t -> error l "%s is not a variable" (qshow env t) in
        let env, p = proof env (fun env -> prove_predates env l (callee_level env) cur) p in
        match expect_proof ~alt:" or `_`" env l Prelude.predates p with
        | [ _; x; l2 ] ->
            check_equal env l l2 (Var cur);
            if not (equal (canon env x) (canon env lv)) then
              error l "%s : %s does not relate the callee's level %s" (qshow env p) (qshow env (infer env l p)) (qshow env lv);
            env
        | _ -> assert false)
    | At cur, _ ->
        let kind, ann, other = if same cur then ("same", "subterm", "predates") else ("lower", "predates", "subterm") in
        error l "%s-level call to %s takes a `(%s p)` annotation, not `(%s p)`" kind (qshow env callee.term) (speller env ann) (speller env other)
  in
  let env = match written with
    | None -> check l (inferred ())
    | Some (al, a) ->
        let env' = check al (Some a) in
        let unnecessary = match env.level, a with
          | At _, `Subterm (i, _) -> provable_subterm env (List.nth arg_terms i) (Var (counterpart al (Option.get (find_index (( = ) i) subterm_params))))
          | At cur, `Predates _ -> (match canon env lv with Var m -> provable_predates env m cur | _ -> false)
          | Top, _ -> false in
        if unnecessary then
          warn_in env al [] "unnecessary %s; drop it" (tick (Printf.sprintf "(%s _)" (speller env (match a with `Predates _ -> "predates" | `Subterm _ -> "subterm"))));
        env'
  in
  let callee_name () = match callee.term with Var x -> qname env x | _ -> "this call" in
  call_returns ?sink ~demand env expect l callee_name acc rets (fun env ->
    let cc = match env.level with At cur when cc = V.Plain && same cur -> V.Same (l, lazy (qshow env callee.term)) | _ -> cc in
    if skipped then V.CValues [] else V.CApp (hcode, codes, cc))

and call_returns ?sink ~demand env expect l callee_name acc rets inner =
  let pos = pos_of env expect in
  let env, ids = open_results env ~ats:(List.map (fun _ -> l) rets) ~mults:(List.map (fun e -> under pos e.mult) rets) ~ids:acc rets in
  count_check ?sink l expect ids;
  List.iter2 (fun (m, (e : entry)) x ->
    let name = match e.name with Some n -> tick_name n ^ " " | None -> "" in
    let notes = if Reader.placed e.loc && e.name <> None then [ (e.loc, Printf.sprintf "%sis declared here" name) ] else [] in
    check_mult env l (fun () -> (notes, Printf.sprintf "the return %sof %s, declared `%s`" name (callee_name ()) (speller env (mult_name e.mult)))) (demanded env demand m (type_of env x)) (entry env x).mult)
    (List.combine expect rets) ids;
  let build expect = reconstruct ~always:true ~init:acc ~expect env l rets ids (inner env) in
  let kept = List.map2 (fun m (e : entry) -> under m e.mult) expect rets in
  let env, code =
    if pos = Erased then (env, V.CErased)
    else if not env.run_pos then (env, build kept)
    else
      let all = List.map (fun x -> (entry env x).mult) ids in
      let env = List.fold_left2 (fun env x v -> set_state env x (Settled v)) env ids (spread all (run_code env (build all))) in
      (env, V.CValues (List.filter_map (fun (m, x) -> if m = Erased then None else Some (V.CVar x)) (List.combine kept ids)))
  in
  (env, List.map (res_of env) ids, code)

and elab_special ?sink ?final demand tele env expect l sp args =
  let pos = pos_of env expect in
  let m =
    if List.mem sp (Sp.WorldDo :: Sp.SettledTyApply :: Sp.SettledValApply :: primitives @ Sp.CellMatch :: Sp.CellMatch :: Sp.Values :: Sp.Match :: Sp.OpenAbsurd :: Sp.Tail :: Sp.NoTail :: Sp.Delegate :: Sp.At :: Sp.statements) then pos
    else match expect with [ m ] -> m | _ -> error l "%s produces one value" (tick (speller env (Sp.name sp)))
  in
  let expected_type env = match tele with
    | Some [ { sg = Ty t; _ } ] -> Some (canon env t)
    | Some [ { sg = Is t; _ } ] -> Some (canon env (infer env l t))
    | _ -> None in
  let expected_sides env = match expected_type env with
    | Some (App (Var c, [ sa; _; _; sb; _; _ ])) when c = Prelude.coercible -> Some (sa, sb)
    | _ -> None in
  let proof ?sides env ctor raw =
    let env, tele = match sides with
      | None -> (env, None)
      | Some (sa, sb) ->
          let a, env = bind env ~meta:true None Erased Hypothetical type_term in
          let x, env = bind env ~meta:true None Erased Hypothetical (Var a) in
          let b, env = bind env ~meta:true None Erased Hypothetical type_term in
          let y, env = bind env ~meta:true None Erased Hypothetical (Var b) in
          (env, Some [ { name = None; subterm = false; mult = Erased; place = None; loc = Reader.nowhere;
            sg = Ty (proof_type ctor [sa; Var a; Var x; sb; Var b; Var y]) } ]) in
    let env, p, _ = elab_expr1 ?tele env Erased raw in
    settle_res env l p;
    (env, expect_proof env l ctor p.term) in
  let form () = tick ("(" ^ String.concat " " (speller env (Sp.name sp) :: List.map Reader.show args) ^ ")") in
  let produced env notes what ty supply = check_mult env l (fun () -> (notes, form () ^ ", " ^ what)) (demanded env demand m ty) supply in
  let erased (env, r) =
    produced env [] (if sp = Sp.LevelOf then "a `Level` and so erased" else "a proof and so erased") r.ty Erased;
    (env, [ r ], V.CErased) in
  let mint env ty =
    let env = match expected_type env with Some want -> solve "type" env l ty want | None -> env in
    erased (mint env (metaless env ty)) in
  let side env raw =
    if wild raw then let x, env = bind env ~meta:true ~at:(Reader.loc raw) None Erased Hypothetical Prelude.sharing_term in (env, Var x)
    else let env, t = elab_term env raw in check_type env l (infer env l t) Prelude.sharing_term; (env, t) in
  let compose (c1, p) (c2, q) k =
    let env, p = proof env c1 p in
    let env, q = proof env c2 q in
    let (a, b), (ctor, args) = k (p, q) in
    check_equal env l a b;
    mint env (proof_type ctor args)
  in
  match (sp, args) with
  | (Sp.Fn | Sp.UniqueFn | Sp.TyCtor | Sp.ValCtor | Sp.Matchable | Sp.Cell), _ ->
      if pos <> Erased then error l "a type in a non-erased position";
      let env, t = elab_type_form env l sp args in
      erased (env, term_res env l t)
  | Sp.SlotOf, _ ->
      let env, x = slot_var env l args in
      refer ~live:(pos <> Erased && not env.usage_erased) x;
      if pos <> Erased && (entry env x).mult = Erased then error_in env l "%s is erased, as %s is, and stands in a non-erased position" (qshow env (slot_of x)) (qname env x);
      (env, [ { term = Var (entry env x).slot; ty = Prelude.slot_term; erasure = pos; place = Some (slot_of x) } ], if pos = Erased then V.CErased else V.CVar x)
  | Sp.CellAlloc, [ raw ] ->
      let c, items = match raw with List (_, c :: ss) -> (c, Some ss) | Atom _ | Handle _ -> (raw, None) | _ -> error l "%s" (help env (Sp.misuse Sp.CellAlloc)) in
      let c = ctor_var env l c in
      let ct, params, _ = cell_shape env l pos c in
      let env, slots, writes, wrap = cell_items env pos l ("`cell-alloc`", loc raw, c, params) (List.init ct.V.arity (fun _ -> Var Prelude.null))
        (Option.value items ~default:(List.init ct.arity (fun _ -> Wild l))) in
      let values = List.init ct.arity (fun i -> Option.value (List.assoc_opt i writes) ~default:(V.CConst V.VVacant)) in
      let x, env = bind env None (under pos Unique) Hypothetical (Cell (Var c, slots)) in
      produced env [] "a fresh cell and so unique" (type_of env x) (entry env x).mult;
      let hollow = hollow env c in
      let env, place = if hollow then (place env x (slot_of Prelude.null), Some (slot_of Prelude.null)) else (env, None) in
      (env, [ { (res_of env x) with place } ], if pos = Erased then V.CErased else if hollow then V.CConst V.VVacant else wrap (V.CCellAlloc (ct, values)))
  | Sp.CellWrite, [ m; u; List (il, c :: items) ] ->
      (* a write into a cell at `many` copies: the result is a fresh cell, at unique and at nothing (section 37) *)
      let mode = written env pos l "cell-write" (mult_or env l m) in
      if pos <> Erased && mode = Erased then error_in env l "`cell-write` takes its cell at `many` or `unique` in a non-erased position";
      let env, r, input = elab_expr1 env (under pos mode) u in
      let shared = mode = Many in
      let input_id = fresh () in
      let code = V.CVar input_id in
      let c = ctor_var env l c in
      let existing, slots = match canon env r.ty with Cell (Var c, ss) -> c, ss | _ -> error_in env l "`cell-write` needs a `Cell`" in
      check_equal env l (Var c) (Var existing);
      let ct, params, _ = cell_shape env l pos c in
      let env, slots, writes, wrap = cell_items env pos l ("`cell-write`", il, c, params) slots items in
      let x, env = bind env None (under pos Unique) Hypothetical (Cell (Var c, slots)) in
      produced env [] "a cell and so unique" (type_of env x) (entry env x).mult;
      let place = if shared then None else r.place in
      (placed env x place, [ { (res_of env x) with place } ], if pos = Erased then V.CErased else V.CLet ([input_id], input, wrap ((if shared then V.CCellCopy (ct, code, writes) else V.CCellWrite (ct, code, writes)))))
  | Sp.CellMatch, _ -> elab_cell_match ~demand tele env expect l args
  | Sp.At, [ m; List (_, head :: args) ] ->
      let m = mult_or env l m in
      let env, h, hcode = elab_head env (if m = Erased then Erased else pos) l head in
      let hty = canon env h.ty in
      let desc = describe env pos head h.term hty in
      let taken want = if m <> want then error_in env l "the head %s : %s is taken at %s here; write %s" (qshow env h.term) (qshow env hty) (tick (speller env (mult_name want))) (tick (Printf.sprintf "(%s %s (...))" (speller env (Sp.name Sp.At)) (speller env (mult_name want)))) in
      let env,rs,code = match hty with
       | Cell (c, slots) -> taken pos; elab_cell_invoke ~full:true env expect l desc h hcode c slots args
       | UniqueFn (lv, params, rets) -> taken Unique; elab_call ~unique:true ~assert_at:true ?sink ~demand V.Plain env ?tele expect l (loc head) desc h hcode lv params rets args
       | Fn (lv, params, rets) -> taken Erased; elab_call ~assert_at:true ?sink ~demand V.Plain env ?tele expect l (loc head) desc h hcode lv params rets args
       | _ -> error_in env l "`at` wraps a `Cell` invocation or a call, and %s : %s is neither" (qshow env h.term) (qshow env h.ty) in
      (env,rs,code)
  | Sp.At, [ List _ ] -> error_in env l "`at` around a call or a `Cell` invocation names the multiplicity its head is taken at: `(at erased (f ...))` for an `Fn`, `(at unique (k ...))` for a `UniqueFn`, and the position's for a `Cell`"
  | Sp.Share, [ a ] ->
      if pos = Erased then error_in env l "`share` in an erased position";
      let env, r, code = match a with
        | Atom (al, _) | Handle (al, _, _, _, _) | Nat (al, _) | Char (al, _) | Str (al, _) ->
            let env, x = atom_entry env a in
            if made env a x <> Unique then error_in env al "`share` needs a unique value";
            (use env al ~sharing:true Many x, res_of env x, V.CVar x)
        | _ -> elab_expr1 env Unique a
      in
      produced env [] "shared and so many" r.ty Many;
      (env, [ { r with erasure = Many } ], code)
  | (Sp.CellSame | Sp.FnSame), [ a; b ] ->
      let name = Sp.name sp and cells = sp = Sp.CellSame in
      if not (cells || !fn_same) then error l "`fn-same` needs `--fn-same` (OPEN.md 36)";
      if pos = Erased then error_in env l "`%s` in an erased position" name;
      let id s = match prelude_id env s with Some i -> Var i | None -> error l "`%s` needs the prelude's `%s`, which `--no-prelude` leaves out" name s in
      let arg env raw =
        let env, r, code = elab_expr1 env Many raw in
        (match cells, canon env r.ty with
         | true, Cell _ | false, (Fn _ | UniqueFn _) -> ()
         | _, t -> error_in env (loc raw) "`%s` takes %s, and %s : %s is not one" name (if cells then "cells" else "functions") (qshow env r.term) (qshow env t));
        let env = match r.term, code with
          | Var _, V.CVar _ -> env
          | _ -> let x, env = bind env ~holes:true ~word:true ~temporary:true None r.erasure (ran_state env r.erasure code) r.ty ~rule:r.term in
                 if env.run_pos then env else { env with pending = (x, code) :: env.pending } in
        (env, (r, Option.fold ~none:(term_place env r.term) ~some:Option.some r.place)) in
      let env, (ra, pa) = arg env a in
      let env, (rb, pb) = arg env b in
      let listed r = match canon env r.ty with
        | Cell (Var c, _) -> (match matchables env (tid_of env l c) with (m, d, cs) :: _ when List.exists (fun (_, c') -> c' = Var c) cs -> Some (m, d, tid_of env l c) | _ -> None)
        | _ -> None in
      if cells then
        (match listed ra, listed rb with
         | Some (m, Enum, _), Some (m', _, _) when m = m' -> ()
         | Some (m, Union, t), Some (m', _, _) when m = m' -> error_in env l "`cell-same` takes cells of an `enum`, and %s is a `union`" (qname env t)
         | _ -> error_in env l "`cell-same` takes cells of constructors one opened `Matchable` lists, and %s and %s are not" (qshow env ra.term) (qshow env rb.term))
      else if not (equal (canon env ra.ty) (canon env rb.ty)) then
        error_in env l "`fn-same` takes functions of one type, and %s : %s and %s : %s are not" (qshow env ra.term) (qshow env ra.ty) (qshow env rb.term) (qshow env rb.ty);
      (match pa, pb with Some p, Some q when same_slot env p q -> () | _ -> error_in env l "%s and %s are not at one slot" (qshow env ra.term) (qshow env rb.term));
      let erased_or = id "ErasedOr" in
      let eq = if cells then App (id "JMEq", [ ra.ty; ra.term; rb.ty; rb.term ]) else App (id "Eq", [ ra.ty; ra.term; rb.term ]) in
      let x, env = bind env None Many Hypothetical (App (erased_or, [ eq ])) in
      produced env [] "many" (type_of env x) Many;
      let env = place env x (slot_of Prelude.null) in
      (env, [ { (res_of env x) with place = Some (slot_of Prelude.null) } ], V.CVar Prelude.null)
  | Sp.Values, _ ->
      let env, args = spliced env args in
      count_check ?sink l expect args;
      let entry i = Option.map (fun t -> List.nth t i) tele in
      let env, ress, codes =
        List.fold_left2
          (fun (env, ress, codes) (i, m) a ->
            let tele = Option.map (fun e -> [ { e with sg = map_sg (instantiate (List.map (fun r -> r.term) ress)) e.sg } ]) (entry i) in
            let env, r, code = elab_expr1 ~demand ?tele env m a in
            (env, r :: ress, if m <> Erased then code :: codes else codes))
          (env, [], []) (List.mapi (fun i m -> (i, m)) expect) args
      in
      (env, List.rev ress, if pos = Erased then V.CErased else V.CValues (List.rev codes))
  | Sp.Match, _ -> elab_match ~demand ?final tele env expect l args
  | Sp.WorldDo, _ ->
      let request = match prelude_id env "Request" with Some r -> r | None -> error l "`world-do` needs the prelude's `Request`" in
      let e ?place name mult t = { name = Some (Src name); subterm = false; mult; sg = Ty t; place; loc = Reader.nowhere } in
      let params = [ e "A" Erased type_term; e "w" Unique Prelude.world_term; e "req" Unique (App (Var request, [ Bound 1 ])) ] in
      let rets = [ e ~place:(SlotOf (Bound 1)) "w2" Unique Prelude.world_term; e "r" Many (Bound 3) ] in
      let c = { subject = lazy "`world-do`"; apposed = false; notes = lazy []; used = under pos; marks = true } in
      let env, acc, codes = check_args env l ~callee:c ~bind_args:true ~named:(slot_named_params params rets) ?expect:tele ~result:(fun mvars -> instantiate_tele mvars rets) ~pos params args elab_arg in
      call_returns ?sink ~demand env expect l (fun () -> "`world-do`") acc rets (fun _ -> V.CWorldDo (List.nth codes 1))
  | Sp.SettledOf, [ mraw; a ] ->
      let mode = mult_or env l mraw in
      let env, x = entry_named env (loc a) a "a name" in
      refer ~live:(mode <> Erased && not env.usage_erased) x;
      if (match (entry env x).state with Hypothetical -> true | Settled _ -> false) then error_in env (loc a) "%s is `Hypothetical`, and a handle names a `Settled` entry" (qname env x);
      if mode <> Erased && made env a x <> mode then error_in env (loc a) "%s is not declared `%s`" (qname env x) (speller env (mult_name mode));
      let id s = match prelude_id env s with Some i -> Var i | None -> error l "`settled-of` needs the prelude's `%s`, which `--no-prelude` leaves out" s in
      let m = App (id (match mode with Erased -> "MErased" | Many -> "MMany" | Unique -> "MUnique"), []) in
      let h, env = bind env None (under pos Many) Hypothetical (App (id "Settled", [ m; minted_type env x; minted_is env x ])) in
      produced env [] "a handle and so many" (type_of env h) Many;
      (env, [ res_of env h ], if pos = Erased then V.CErased else V.CConst (V.VHandle ((entry env x).minted, MintedIs, mode, match (entry env x).state with Settled v when mode = Many -> v | _ -> V.VToken)))
  | (Sp.SettledTyApply | Sp.SettledValApply), mw :: (_ :: _ as hs) ->
      let shown () = tick (speller env (Sp.name sp)) in
      let id s = match prelude_id env s with Some i -> Var i | None -> error l "%s needs the prelude's `%s`, which `--no-prelude` leaves out" (shown ()) s in
      let entry ?name ?place mult t = { name = Option.map (fun n -> Src n) name; subterm = false; mult; sg = Ty t; place; loc = Reader.nowhere } in
      let meta env ty = let x, env = bind env ~meta:true None Erased Hypothetical ty in (env, Var x) in
      let env, indices = List.fold_left_map (fun env _ ->
        let env, m = meta env (App (id "Mult", [])) in
        let env, ty = meta env type_term in
        let env, t = meta env ty in (env, (m, ty, t))) env hs in
      let params = entry ~name:"mw" Unique (App (id "MacroWorld", [])) :: List.mapi (fun i (m, ty, t) -> entry ~name:(if i = 0 then "c" else "a" ^ string_of_int i) Many (App (id "Settled", [ m; ty; t ]))) indices in
      let c = { subject = lazy (shown ()); apposed = false; notes = lazy []; used = under pos; marks = true } in
      let env, acc, codes = check_args env l ~callee:c ~bind_args:true ~pos params (mw :: hs) elab_arg in
      let hds = List.combine hs (List.map (fun (m, ty, t) -> (canon env (metaless env m), metaless env ty, metaless env t)) indices) in
      let at_mult s m = equal m (App (id s, [])) in
      let mult_error raw m want = error_in env (Reader.loc raw) "%s takes this handle at %s, and its `Mult` is %s" (shown ()) want (qshow env m) in
      let (_, (mc, _, tc)) = List.hd hds in
      let tele = ctor_tele env l sp tc in
      if sp = Sp.SettledTyApply then List.iter (fun (raw, (m, _, _)) -> if not (at_mult "MErased" m) then mult_error raw m "`(MErased)`") hds
      else (
        if not (at_mult "MErased" mc || at_mult "MMany" mc) then mult_error (List.hd hs) mc "`(MErased)` or `(MMany)`";
        List.iteri (fun i (raw, (m, _, _)) -> match List.nth_opt tele i with
          | Some (e : entry) -> let want = if e.mult = Erased then App (id "MErased", []) else mc in if not (equal m want) then mult_error raw m (qshow env want)
          | None -> ()) (List.tl hds));
      let env, raws = List.fold_left_map (fun env (_, (_, _, t)) -> match t with
        | Var x -> (env, Handle (l, x, MintedIs, Erased, Obj.repr V.VToken))
        | t -> let x, env = bind env None Erased Hypothetical (infer env l t) ~rule:t in (env, Handle (l, x, MintedIs, Erased, Obj.repr V.VToken))) env hds in
      let env, t = elab_term env (List (l, raws)) in
      let ty = infer env l t in
      let result = App (id "Result", [ App (id "Settled", [ (if sp = Sp.SettledTyApply then App (id "MErased", []) else mc); ty; t ]) ]) in
      let rets = [ entry ~name:"mw2" ~place:(SlotOf (Bound (List.length acc - 1))) Unique (App (id "MacroWorld", [])); entry ~name:"r" Many result ] in
      let here = Ffi.pos (Ffi_core.pos_view ~str:(str_value env) ~nat:(nat_value env) l) in
      call_returns ?sink ~demand env expect l shown acc rets (fun _ -> V.CPrim (sp, V.CConst here :: codes))
  | sp, _ when List.mem sp primitives -> (
      let shown () = tick (speller env (Sp.name sp)) in
      match Hashtbl.find_opt prims sp with
      | None -> error_in env l "%s has no signature until `def-prim` declares it" (shown ())
      | Some (m, params, rets) ->
          let rets = if m = Erased then List.map (fun (e : entry) -> { e with mult = Erased }) rets else rets in
          let c = { subject = lazy (shown ()); apposed = false; notes = lazy []; used = under pos; marks = true } in
          let env, acc, codes = check_args env l ~callee:c ~bind_args:true ~named:(slot_named_params params rets) ?expect:tele ~result:(fun mvars -> instantiate_tele mvars rets) ~pos params args elab_arg in
          let ctors = List.map (pctor ~loc:l env) (match sp with
            | Sp.SettledMult -> [ "MErased"; "MMany"; "MUnique" ] | Sp.SlotEq -> [ "None"; "Some"; "Refl" ] | Sp.SettledEq -> [ "None"; "Some"; "JMRefl" ]
            | Sp.Resolve -> [ "RSettled"; "RHypothetical"; "RUnbound" ] | Sp.ReadFile -> [ "Ok"; "Fail" ] | _ -> []) in
          let codes = codes @ match sp, ctors with
            | Sp.SettledMult, _ -> List.map (fun c -> V.CConst (V.construct c [])) ctors
            | Sp.SlotEq, [ none; some; refl ] -> [ V.CConst (V.construct none []); V.CConst (V.construct some [ V.construct refl [] ]) ]
            | _ -> [] in
          call_returns ?sink ~demand env expect l shown acc rets (fun _ -> if List.mem sp implemented then V.CPrim (sp, codes) else V.CValues []))
  | (Sp.Tail | Sp.NoTail | Sp.Delegate), [ (List _ as call) ] ->
      if pos = Erased then error l "%s in an erased position" (tick (speller env (Sp.name sp)));
      let cc = match sp with Sp.Tail -> V.Tail | Sp.NoTail -> V.NoTail | _ -> V.Delegate in
      let env, ress, code = elab_expr ?sink ~demand ~cc ?tele env expect call in
      let rec has_call c = (match c with V.CApp (_, _, cc') -> cc' = cc | _ -> false) || List.exists has_call (V.subcodes c) in
      if not (has_call code) then error l "%s marks a function call, not %s" (tick (speller env (Sp.name sp))) (tick (Reader.show call));
      (env, ress, code)
  | Sp.MatchableOf, _ ->
      let x = match fetched env l sp args with _, Var x -> x | _ -> assert false in
      let e = entry env x in
      let notes = if Reader.placed e.at then [ (e.at, respell env "the `open-adt` is here") ] else [] in
      produced env notes (sprintf_in env "opened `%s` by an `open-adt`" (speller env (mult_name e.mult))) (type_of env x) e.mult;
      (env, [ res_of env x ], matchable_code env m x)
  | Sp.OpenAbsurd, [ e; ann ] ->
      open_contradicts env l e;
      let env, ann_tele, _ = result_tele ~demand tele env expect l ann in
      let env, ids = open_results env ann_tele in
      (env, List.map (res_of env) ids, if pos = Erased then V.CErased else V.CAbsurd)
  | (Sp.NumeralOf | Sp.DelegateOf | Sp.AtFnOf), _ -> (match fetched env l sp args with env, Var y -> erased (env, res_of env y) | _ -> assert false)
  | Sp.LevelOf, _ -> let env, lv = fetched env l sp args in erased (env, { term = lv; ty = Prelude.level_term; erasure = Erased; place = None })
  | Sp.ProveSubterm, [ a; b ] ->
      let env, a = elab_term env a in
      let env, b = elab_term env b in
      settle env l a; settle env l b;
      erased (prove_subterm env l a b)
  | Sp.ProvePredates, [ x; lv ] ->
      let env, lv = level_binder env l lv in
      let env, x = match x with
        | Atom _ | Handle _ | Nat _ | Char _ | Str _ | Wild _ -> atom_entry ~at:l env x
        | _ -> (match elab_term env x with env, Var x -> (env, x) | _ -> error l "expected a variable or a fetch form, got %s" (tick (Reader.show x))) in
      erased (prove_predates env l x lv)
  | Sp.PredatesTrans, [ p; q ] ->
      compose (Prelude.predates, p) (Prelude.predates, q)
        (function [ a; x; l1 ], [ _; l1'; l2 ] -> ((l1', l1), (Prelude.predates, [ a; x; l2 ])) | _ -> assert false)
  | Sp.SubtermTrans, [ p; q ] ->
      let c = Prelude.subterm in
      compose (c, p) (c, q) (function [ a; x; _; y ], [ _; y'; b; z ] -> ((y', y), (c, [ a; x; b; z ])) | _ -> assert false)
  | Sp.PredatesSubterm, [ p; q ] ->
      compose (Prelude.predates, p) (Prelude.subterm, q)
        (function [ _; x; lv ], [ b; y; _; x' ] -> ((x', x), (Prelude.predates, [ b; y; lv ])) | _ -> assert false)
  | Sp.Coerce, [ a; praw ] -> (
      let env, p = proof env Prelude.coercible praw in
      match p with
      | [ sa; _; a'; sb; b_ty; b ] ->
          let src = if pos = Erased then Erased else sharing_mult env l sa in
          let dst = if pos = Erased then Erased else sharing_mult env l sb in
          let env, a, code = elab_expr1 env src a in
          settle_res env l a;
          check_equal env l a.term a';
          let x, env = bind env None dst Hypothetical b_ty ~rule:b in
          let notes = match praw with Atom (_, n) -> (match lookup env n with Some y -> declared env y | None -> []) | _ -> [] in
          produced env notes (Printf.sprintf "at %s by the target side of %s's type" (qshow env sb) (tick (Reader.show praw))) b_ty dst;
          (placed env x a.place, [ { (res_of env x) with place = a.place } ], code)
      | _ -> assert false)
  | Sp.CoercibleRefl, [ s; e ] ->
      let env, s = side env s in
      let env, e = elab_term env e in
      settle env l e;
      mint env (proof_type Prelude.coercible [ s; infer env l e; e; s; infer env l e; e ])
  | Sp.CoercibleSym, [ p ] -> (
      let sides = Option.map (fun (a,b) -> b,a) (expected_sides env) in
      let env, p = proof ?sides env Prelude.coercible p in
      match p with
      | [ sa; a; x; sb; b; y ] -> mint env (proof_type Prelude.coercible [ sb; b; y; sa; a; x ])
      | _ -> assert false)
  | Sp.CoercibleShare, [ p ] -> (
      let env, p = proof env Prelude.coercible p in
      match p with
      | [ _; a; x; _; b; y ] -> mint env (proof_type Prelude.coercible [ Prelude.shared_term; a; x; Prelude.shared_term; b; y ])
      | _ -> assert false)
  | Sp.CoercibleTrans, [ p; q ] -> (
      let middle, env = bind env ~meta:true None Erased Hypothetical Prelude.sharing_term in
      let first = Option.map (fun (a,_) -> a, Var middle) (expected_sides env) in
      let env, p = proof ?sides:first env Prelude.coercible p in
      let sa,a,x,sm,b,y = match p with [sa;a;x;sm;b;y] -> sa,a,x,sm,b,y | _ -> assert false in
      let second = Some (sm, match expected_sides env with Some (_,b) -> b | None -> Var middle) in
      let env, q = proof ?sides:second env Prelude.coercible q in
      match q with
      | [ sm'; b'; y'; sb; c; z ] ->
          check_equal env l sm sm'; check_type env l b b'; check_equal env l y y';
          mint env (proof_type Prelude.coercible [ sa;a;x;sb;c;z ])
      | _ -> assert false)
  | Sp.CoercibleWrap, s :: c :: args -> (
      let env, s = side env s in
      let c = ctor_var env l c in
      let params, ret = ctor_type env l c in
      if newtype_of env c = None then error_in env l "%s has no opened newtype `Matchable` for its wrapping constructor" (qname env c);
      let callee = { subject = lazy (sprintf_in env "`coercible-wrap` of %s" (qname env c)); apposed = false; notes = lazy (declared_as env c); used = (fun _ -> Erased); marks = true } in
      let env, acc = elab_term_args env l ~callee ~what:"more argument" params (Var c) args in
      List.iter (settle env l) acc;
      let e, f = List.find (fun (e, _) -> e.mult <> Erased) (List.combine params (List.rev acc)) in
      let src = if e.mult = Unique then s else Prelude.shared_term in
      mint env (proof_type Prelude.coercible [ src; infer env l f; f; s; instantiate acc ret; App (Var c, List.rev acc) ]))
  | Sp.CoercibleCtor, s :: c :: args ->
      let env, s = side env s in
      let env = match expected_sides env with Some (sa,_) -> solve "sharing" env l s sa | None -> env in
      let c = ctor_var env l c in
      let params, ret = ctor_type env l c in
      let needed = List.fold_left (fun n (e : entry) -> n + if e.mult = Erased then 2 else 1) 0 params in
      if List.length args <> needed then
        field_count env l "`coercible-ctor`" "more argument" c params needed (List.length args)
          "a source and a target for each erased field and a `Coercible` proof for each other field, in the order of";
      let check env side e ty t = check_sg env l (map_sg (instantiate side) e.sg) { term = t; ty; erasure = Erased; place = None } in
      let rec go env src tgt tele args =
        match (tele, args) with
        | [], [] -> (env, src, tgt)
        | ({ mult = Erased; _ } as e) :: tele, a :: b :: args ->
            let env, a = elab_term env a in
            let env, b = elab_term env b in
            settle env l a; settle env l b;
            check env src e (infer env l a) a;
            check env tgt e (infer env l b) b;
            go env (a :: src) (b :: tgt) tele args
        | ({ mult = (Many | Unique); _ } as e) :: tele, p :: args -> (
            let fs = if e.mult = Many then Prelude.shared_term else s in
            match proof ~sides:(fs,fs) env Prelude.coercible p with
            | env, [ sa; sty; a; sb; tty; b ] ->
                let env = solve "sharing" (solve "sharing" env l sa fs) l sb fs in
                check env src e sty a;
                check env tgt e tty b;
                go env (a :: src) (b :: tgt) tele args
            | _ -> assert false)
        | _ -> assert false in
      let env, src, tgt = go env [] [] params args in
      mint env (proof_type Prelude.coercible [ s; instantiate src ret; App (Var c, List.rev src); s; instantiate tgt ret; App (Var c, List.rev tgt) ])
  | Sp.CoercibleOf, [ d ] -> (
      let env, d = proof ?sides:(expected_sides env) env Prelude.delegate d in
      match d with
      | [ sg; gty; g; sf; fty; f ] -> mint env (proof_type Prelude.coercible [ sg; gty; g; sf; fty; f ])
      | _ -> assert false)
  | Sp.DumpContext, _ -> dump_context env l (Dump.Values (expect, tele)) args
  | Sp.CompileError, _ -> compile_error (!settle_head Many) pos env l args
  | sp, _ when List.mem sp Sp.statements -> error l "%s is a statement, not an expression%s" (tick ("(" ^ speller env (Sp.name sp) ^ if args = [] then ")" else " ...)")) (help env (Sp.hints (Sp.name sp)))
  | sp, _ -> error l "%s" (help env (Sp.misuse sp))

and cell_items env pos l (what, il, c, params) slots items =
  if List.length slots <> List.length items then slot_count env il what "slot item" c params (List.length items);
  let env, slots, writes, bindings = List.fold_left2 (fun (env, ss, ws, bs) (i, old) item ->
    if wild item then (env, old :: ss, ws, bs) else
    let env, r, code = elab_expr1 env (under pos Many) item in
    (try ignore (unify env r.ty Prelude.slot_term) with Contradiction _ | Ill_typed _ -> error l "expected a `(Slot)` or `_`, got %s" (qshow env r.ty));
    settle_res env l r;
    let x = fresh () in
    (env, r.term :: ss, (i, V.CVar x) :: ws, (x, code) :: bs)) (env, [], [], []) (List.mapi (fun i s -> i,s) slots) items in
  (env, List.rev slots, List.rev writes, fun body -> List.fold_left (fun b (x,c) -> V.CLet ([x], c, b)) body bindings)

and elab_cell_invoke ?(full = false) env expect l callee h hcode ctor slots args =
  let pos = pos_of env expect in
  let c = match canon env ctor with Var c -> c | _ -> error_in env l "`Cell` constructor is not a variable" in
  let ct, params, ret = cell_shape env l pos c in
  (* the cell is taken at the position's multiplicity: read and copied at `many` where it stores, consumed at
     `unique` (section 37) *)
  let shared = pos = Many in
  let env = match h.term with Var x -> use env l pos x | _ -> env in
  let rec marks mark args = match args with
    | List (_, [a]) :: rest when is_special env a Sp.At -> marks true rest
    | a :: rest -> (mark, a) :: marks false rest
    | [] -> if mark then error_in env l "`at` must precede an argument" else [] in
  let marked = marks false args in
  let raw = List.map snd marked in
  let env, acc, codes = check_args env l ~callee ~bind_args:true ~ctor:true ~result:(ctor_result (Var c)) ~pos ~boundary:false params raw elab_arg in
  let _, writes = List.fold_left2 (fun (i, writes) ((e : entry), t) (skip, _) ->
    if e.mult = Erased then (if skip then error_in env l "`at` cannot mark an erased argument"; (i, writes)) else
    let same = same_slot env (List.nth slots i) (SlotOf t) in
    if (full || skip) && not same then error_in env l "`at` argument %d is not in its slot's location class" (i+1);
    (i+1, if full || skip then writes else (i, List.nth codes i) :: writes)) (0, []) (List.combine params (List.rev acc)) marked in
  let copies = shared && writes <> [] in
  let code = if pos = Erased then V.CErased else if copies then V.CCellCopy (ct, hcode, List.rev writes) else if writes = [] then hcode else V.CCellWrite (ct, hcode, List.rev writes) in
  (env, [{term = App (Var c, List.rev acc); ty = instantiate acc ret; erasure = pos; place = if copies then None else h.place}], code)

and elab_cell_match ?(demand = Fixed) tele env expect l args =
  match args with
  | m :: u :: ann :: List (pl, c :: names) :: body ->
      if pos_of env expect = Erased then error_in env l "`cell-match` in an erased position";
      let mode = mult_or env l m in
      if mode = Erased then error_in env l "`cell-match` takes its cell at `many` or `unique`";
      let env, r, code = elab_expr1 env mode u in
      let c = ctor_var env pl c in
      let c', slots = match canon env r.ty with Cell (Var c, ss) -> c, ss | _ -> error_in env l "`cell-match` needs a `Cell`" in
      check_equal env l (Var c) (Var c');
      let ct, _, _ = cell_shape env l mode c in
      let given = List.length names in
      if given <> ct.V.arity && not (mode = Unique && given = ct.arity + 1) then
        binder_count env pl "`cell-match`" c mode ~extra:(mode = Unique) names (List.map is_entry slots @ if mode = Unique then [ is_entry ~mult:Unique ?place:r.place r.term ] else []);
      let env, ann_tele, atmatch = result_tele ~demand tele env expect l ann in
      let expect = match demand with Fixed -> expect | _ -> List.map (fun e -> e.mult) ann_tele in
      let sid, env = bind env ~word:true ~temporary:true None mode (ran_state env mode code) r.ty ~rule:r.term in
      let env = placed env sid r.place in
      let envb, ids = List.fold_left_map (fun env n -> let x, env = bind env ~word:true ~at:(loc n) ((binder_or pl n "a slot binder")) Many Hypothetical Prelude.slot_term in track env Field x; (env,x)) { (leave_run env) with unwarned = env.unwarned || atmatch } (List.filteri (fun i _ -> i < ct.arity) names) in
      let envb = merge_opens (unify_force (forcing envb) (Cell (Var c,List.map (fun x -> Var x) ids)) (Cell (Var c,slots))) in
      let envb, back = if given = ct.arity then (envb, None) else
        let x, envb = bind envb ~word:true ~at:(loc (List.nth names ct.arity)) ((binder_or pl (List.nth names ct.arity) "a cell binder")) Unique Hypothetical r.ty ~rule:r.term in
        track envb Field x;
        (place envb x (slot_of sid), Some x) in
      let envb, rs, bcode = elab_body ~tele:ann_tele ~sink:(annotated env "cell-match" ann ann_tele expect) envb expect l body in
      check_results envb l body ann_tele rs;
      if atmatch then must_erase env l "the body of an at-`cell-match`" (project_code (keeps ann_tele) bcode);
      let body = if atmatch then V.CValues [] else
      let body = match back with None -> bcode | Some x -> V.CLet ([x], V.CVar sid, bcode) in
      List.fold_right (fun (i,x) b -> V.CLet ([x], V.CCellRead (ct, i, V.CVar sid), b)) (List.mapi (fun i x -> i,x) ids) (project_code (keeps ann_tele) body) in
      let env = {env with uses = envb.uses} in
      let env, result_ids = open_results env ann_tele in
      let env, code = closing env [sid] (V.CLet ([sid], code, reconstruct env l ann_tele result_ids body)) in
      (env, List.map (res_of env) result_ids, code)
  | _ -> error l "%s" (help env (Sp.misuse Sp.CellMatch))

and scrutinee ?res env l smult scrut =
  let env, sres, scode = match res with Some (r, c) -> (env, r, c) | None -> elab_expr1 env smult scrut in
  settle_res env l sres;
  let tid = match type_head env sres.ty with Some t -> t | None -> error l "cannot match on %s : %s" (qshow env sres.term) (qshow env sres.ty) in
  let mid, disc, ctors = find_matchable env l tid in
  let env = if smult = Erased then env else (held_needs_many env l tid mid; use env l Many mid) in
  if smult = Erased then (env,sres,scode,(fun env code -> (env, code)),tid,mid,disc,ctors) else
  let x, env = bind env ~word:true ~temporary:true None smult (ran_state env smult scode) sres.ty ~rule:sres.term in
  (placed env x sres.place,res_of env x,V.CVar x,(fun env body -> closing env [x] (V.CLet ([x],scode,body))),tid,mid,disc,ctors)

and elab_match ?(demand = Fixed) ?(refute = false) ?(form = "match") ?res ?cells ?(skip = []) ?sink ?final tele env expect l args =
  match args with
  | m :: scrut :: ann :: branches ->
      let env, branches = spliced env branches in
      let pos = pos_of env expect in
      let smult = if res <> None then Erased else written env pos l "match" (mult_or env l m) in
      let env, sres, scode, swrap, tid, mid, disc, ctors = scrutinee ?res env l smult scrut in
      let extra = match cells with Some c -> c | None -> cells_allowed env mid in
      let branch_uses = ref env.uses and deep = ref [] in
      let deepen envb body flat = if deep_body envb body then deep := flat :: !deep in
      let shapes = shapes env l ctors in
      let tagged = tagged disc shapes in
      if pos <> Erased && smult <> Erased then held_needs_many env l tid mid;
      let env, ann_tele, atmatch = if refute then (env, [], false) else result_tele ~demand tele env expect l ann in
      if smult <> Erased && not atmatch then warn_use env l "match on" (Var tid);
      let inner env = { (leave_run env) with unwarned = env.unwarned || atmatch } in
      let expect = match demand with Fixed -> expect | _ -> List.map (fun e -> e.mult) ann_tele in
      (* an at-match skips its runtime (section 40): each branch must erase to nothing, dispatch and loads included *)
      let erasable bl code = let code = project_code (keeps ann_tele) code in
        if atmatch && pos <> Erased then must_erase env bl "a branch of an at-match" code;
        code in
      let sink expect = match sink with Some s -> s | None -> annotated env form ann ann_tele expect in
      let mults_of bl c = let phantom = marker env bl tid ctors c = Erased in List.map (fun e -> if phantom then Erased else field_under smult e.mult) (fst (ctor_type env bl c)) in
      let enter bl c names ats =
        let phantom = marker env bl tid ctors c = Erased in
        let tele, ret = ctor_type env bl c in
        let mults = mults_of bl c in
        let envb, fids = open_tele (inner env) ~names:(names tele) ~ats:(ats tele) ~mults tele in
        List.iter (track envb Field) fids;
        (phantom, fids, envb, try Some (at bl (fun () -> refine envb sres c fids ret)) with Contradiction _ -> None)
      in
      let branch raw =
        let kind, pat, body =
          match raw with
          | List (_, [ a; ((Atom _ | Handle _) as c) ]) when is_special env a Sp.Absurd -> (`Auto, c, [])
          | List (_, a :: pat :: body) when is_special env a Sp.Absurd -> (`Proof, pat, body)
          | List (_, pat :: body) -> (`Present, pat, body)
          | _ -> error (loc raw) "malformed branch%s" (help env (Sp.hints "branch"))
        in
        let bl = loc pat in
        let c, fs = match pat with Atom _ | Handle _ -> (pat, []) | List (_, c :: fs) -> (c, fs) | _ -> error bl "malformed pattern%s" (help env (Sp.hints "branch")) in
        let c = ctor_var env bl c in
        let extra = extra || (marker env bl tid ctors c = Erased && cells_allowed ~phantom:true env mid) in
        let fs, name = if kind = `Auto then (fs, if extra then Some (None, Reader.nowhere) else None) else pattern env ("a `" ^ form ^ "` branch") smult sres bl c (mults_of bl c) extra fs in
        let tele = fst (ctor_type env bl c) in
        let phantom, fids, envb, forced =
          enter bl c (fun tele -> if kind = `Auto then anon tele else field_names fs)
            (fun tele -> if kind = `Auto then List.map (fun _ -> Reader.nowhere) tele else field_ats tele fs) in
        let forced, cell = match forced with
          | None -> (None,None)
          | Some e -> let e,x = pattern_cell e bl (if phantom then Erased else smult) sres c fids name in (Some e,x) in
        let unreachable = phantom && smult <> Erased in
        let result =
          match (kind, forced) with
          | `Auto, None -> `Absurd
          | `Auto, Some trial -> error_with bl (forced_notes env bl sres trial) "branch %s is not refuted" (qname env c)
          | _, None -> error_in env bl "branch %s is refuted; omit it or write `(absurd %s)`" (qname env c) (name_of env c)
          | `Present, Some _ when refute -> error_in env bl "a branch of a refuting match is written `absurd`"
          | `Present, Some envb ->
              deepen envb body (if unreachable then None else Some c);
              let envb = { envb with usage_erased = envb.usage_erased || unreachable } in
              let expect = if unreachable then List.map (fun _ -> Erased) expect else expect in
              let envb, ress, code = elab_body ~tele:ann_tele ~sink:(sink expect) envb expect bl body in
              check_results envb bl body ann_tele ress;
              if not unreachable then branch_uses := join_uses !branch_uses envb.uses;
              `Present (bind_cell scode cell (if unreachable then code else erasable bl (field_renames envb bl tele fids code)))
          | `Proof, Some envb -> deepen envb body None; ignore (elab_refute envb bl body); `Absurd
        in
        (c, non_erased envb (runtime_ids tele fids), unreachable, result, forced)
      in
      let elses, branches = List.partition (function List (_, a :: _) when is_special env a Sp.Else -> true | _ -> false) branches in
      let branches = List.map branch branches in
      List.iter
        (fun (_, c) ->
          match List.length (List.filter (fun (c', _, _, _, _) -> Var c' = c) branches) + if List.exists (fun x -> Var x = c) skip then 1 else 0 with
          | 0 | 1 -> ()
          | n -> error l "constructor %s has %d branches" (qshow env c) n)
        ctors;
      let covered =
        List.filter_map
          (fun (_, c) ->
            let c = match c with Var c -> c | _ -> assert false in
            if List.mem c skip || List.exists (fun (c', _, _, _, _) -> c' = c) branches then None
            else
              let phantom, _, _, forced = enter l c anon (List.map (fun _ -> Reader.nowhere)) in
              Option.map (fun trial -> (c, phantom && smult <> Erased, trial)) forced)
          ctors
      in
      let reachable = List.filter_map (fun (c, unreachable, _) -> if unreachable then None else Some c) covered in
      let else_ =
        match elses with
        | [] ->
            (match covered with
             | [] -> ()
             | (c, _, trial) :: _ when res <> None -> error_with l (forced_notes env l sres trial) "%s : %s is not refuted: it may be headed by %s" (qshow env sres.term) (qshow env sres.ty) (qname env c)
             | _ -> missing env l form sres (List.map (fun (c, _, trial) -> (c, trial)) covered));
            None
        | List (el, _) :: _ when refute -> error_in env el "a refuting match has no `else`"
        | [ List (el, _ :: body) ] ->
            if covered = [] then error_in env el "`else` covers no constructor";
            let envb = { (inner env) with usage_erased = env.usage_erased || reachable = [] } in
            let envb, cell, body = match body with
              | b :: (_ :: _ as body) when extra && binder b <> None ->
                  let x, envb = bind envb ~word:true ~at:(loc b) (Option.get (binder b)) smult Hypothetical sres.ty ~rule:sres.term in
                  track envb Optional x;
                  (placed envb x sres.place,Some x,body)
              | _ -> (envb,None,body) in
            deepen envb body None;
            let expect = if reachable = [] then List.map (fun _ -> Erased) expect else expect in
            let envb, ress, code = elab_body ~tele:ann_tele ~sink:(sink expect) envb expect el body in
            check_results envb el body ann_tele ress;
            if reachable <> [] then branch_uses := join_uses !branch_uses envb.uses;
            if reachable = [] then None else Some (bind_cell scode cell (erasable el code))
        | first :: dup :: _ -> error_with_in env (loc dup) [ (loc first, respell env "the first `else` branch") ] "a match has at most one `else` branch"
        | _ -> error_in env l "a match has at most one `else` branch"
      in
      (match final, !deep with
       | Some hl, [ Some c ] when not env.run_pos -> warn_in env hl [] "lopsided `match`; flatten it with a `let-match` on %s" (qshow env (Var c))
       | _ -> ());
      let real =
        List.filter_map (fun (c, fids, unreachable, r, _) -> match r with `Present code when not unreachable -> Some (c, fids, code) | _ -> None) branches
      in
      if pos <> Erased && not (atmatch && smult <> Erased) && ((not tagged) || smult = Erased) && List.length real + List.length (Option.to_list else_) > 1 then
        error_with l (List.sort_uniq compare (List.concat_map (function (_, _, false, `Present _, Some trial) -> forced_notes env l sres trial | _ -> []) branches))
          "a match without a runtime discriminant can have only one real branch";
      let code =
        match (real, else_) with
        | _ when pos = Erased -> V.CErased
        | _ when atmatch -> V.CValues []
        | [], None -> if not env.usage_erased then warn_in env l [] "a non-erased `match` with no non-absurd branch compiles to a runtime `absurd`; mark the enclosing branch or function `absurd` instead"; V.CAbsurd
        | [], Some body when smult = Erased || not tagged -> body
        | [ (_, _, body) ], None when smult = Erased -> body
        | _ ->
            let branch (c, fids, body) = (Option.get (discriminant shapes c), fids, body) in
            V.CMatch
              { scrut = scode; shape = match_shape env mid tid disc shapes; branches = List.map branch real; default = else_;
                live = List.filter_map (fun (c, _, _) -> discriminant shapes c) real @ List.filter_map (discriminant shapes) reachable }
      in
      let env = { env with uses = !branch_uses } in
      let env, result_ids = open_results env ann_tele in
      let env, code = swrap env (if pos = Erased then code else reconstruct env l ann_tele result_ids code) in
      (env, List.map (res_of env) result_ids, code)
  | _ -> error l "%s" (help env (Sp.misuse Sp.Match))

(* A match's or open-absurd's return annotation: a telescope of the position's size, or _ for the enclosing one. *)
and result_tele ?(demand = Fixed) tele env expect l ann =
  let atmatch, ann = match ann with
    | List (_, [ a; (List _ as inner) ]) when is_special env a Sp.At -> (true, inner)
    | List (_, [ a; Wild al ]) when is_special env a Sp.At -> error al "an at-match's annotation is written out; `_` cannot stand for it"
    | _ -> (false, ann) in
  let env, ann_tele =
    match (ann, tele) with
    | Wild _, Some tele ->
        if List.exists (fun e -> has_meta env (sg_term e.sg)) tele then error l "the telescope `_` would reuse still has a `_` to infer";
        (env, tele)
    | Wild _, None -> error l "no telescope to reuse for `_`"
    | List (_, ann), _ ->
        List.iter (function List _ -> () | a -> error (loc a) "expected a telescope or `_`, got %s" (tick (Reader.show a))) ann;
        let mults i el = function
          | Some m -> no_mult env "a match annotation's entries" el m
          | None -> (match List.nth_opt expect i with Some m -> Some m | None -> error l "match annotation has more than the %d entries the position needs" (List.length expect))
        in
        let env', _, ann_tele = elab_tele env ~places:true ~mults ~holes:true ann in
        let env = { env' with scope = env.scope } in
        let env = match tele with Some tele when List.length tele = List.length ann_tele -> solve_tele ~strict:true env l tele ann_tele | _ -> env in
        List.iter (fun e -> settle env l (sg_term e.sg)) ann_tele;
        (env, List.map (fun e -> { e with sg = map_sg (metaless env) e.sg }) ann_tele)
    | _ -> error l "malformed match annotation%s" (help env (Sp.hints "annotation"))
  in
  if List.length ann_tele <> List.length expect then error l "match annotation has %d entries, position needs %d" (List.length ann_tele) (List.length expect);
  let ann_tele = List.map (fun e ->
    let mult = match demand with
      | Fixed -> e.mult
      | _ -> demanded env demand e.mult (match e.sg with Ty t -> t | Is t -> infer env l t) in
    { e with mult }) ann_tele in
  if atmatch && runtime ann_tele <> [] then error_in env l "an at-match's annotation entries are erased or `at`";
  (env, ann_tele, atmatch)

(* An anonymous let at [mult] of a Matchable: the entry an open records (section 8). *)
and open_binding env l mult raw =
  let inner, r, code = elab_expr1 env mult raw in
  settle_res inner l r;
  (match canon inner r.ty with Matchable _ -> () | ty -> error_in env l "%s : %s is not a `Matchable`" (qshow inner r.term) (qshow inner ty));
  let state, minted, minted_level, order = forwarded inner mult r (ran inner mult code) in
  let x, env' = bind inner ?minted ~minted_level ?introduced:order ~at:l None mult state r.ty ~rule:r.term in
  (env', x, r.term, code)

and lets pending code = List.fold_left (fun body (x, rhs) -> V.CLet ([ x ], rhs, body)) code pending

and hoisted env elab =
  let env', ress, code = elab { env with pending = [] } in
  ({ env' with pending = env.pending }, ress, lets env'.pending code)

and elab_body ?tele ?sink env expect l items = hoisted env (fun env -> elab_body_items ?tele ?sink env expect l items)

and elab_body_items ?tele ?sink env expect l items =
  report_shadows ~env ();
  let env, items = expand_seq (pos_of env expect) env items in
  let env, items = match items with
    | List (ll, h :: m :: scrut :: pat :: branches) :: rest when is_special env h Sp.LetMatch -> let env, branches = spliced env branches in (env, List (ll, h :: m :: scrut :: pat :: branches) :: rest)
    | items -> (env, items) in
  match items with
  | List (ll, h :: m :: scrut :: pat :: branches) :: (_ :: _ as rest) when is_special env h Sp.LetMatch && List.exists (real_branch env) branches ->
      elab_match ?sink ~form:"let-match" tele (read_special (pos_of env expect) env h) expect ll (m :: scrut :: Wild ll :: List (loc pat, pat :: rest) :: branches)
  | stmt :: (_ :: _ as rest) ->
      let env, wrap = elab_stmt (pos_of env expect) env stmt in
      let env, ress, code = elab_body ?tele ?sink env expect l rest in
      (env, ress, wrap code)
  | items ->
      let env, _, final = elab_stmts (pos_of env expect) env l items in
      elab_expr ?tele ?sink ~final:true env expect final

and deep_body env = function
  | [ List (_, h :: _) ] -> is_special env h Sp.Match || is_special env h Sp.CellMatch
  | [] | [ _ ] -> false
  | _ -> true

and real_branch env = function List (_, a :: _) -> not (is_special env a Sp.Absurd) | _ -> true

(* The statements before a body's final expression, and the code they wrap around what follows them. *)
and elab_stmts ?within spos env l items =
  let env, items = expand_seq spos env items in
  match items with
  | [] -> error l "a body needs a final expression"
  | [ final ] -> (env, Fun.id, final)
  | stmt :: rest ->
      let env, wrap = elab_stmt ?within spos env stmt in
      let env, wrap', final = elab_stmts ?within spos env l rest in
      (env, (fun code -> wrap (wrap' code)), final)

and elab_refute env l body =
  let env = { env with usage_erased = true } in
  let env, _, final = elab_stmts Erased env l body in
  let l = loc final in
  match final with
  | List (_, head :: (_ :: _ :: ann :: _ as args)) when is_special env head Sp.Match && wild ann ->
      let env, _, _ = elab_match ~refute:true None (read_special Erased env head) [ Erased ] l args in
      env
  | List (_, [ head; e; ann ]) when is_special env head Sp.OpenAbsurd && wild ann ->
      open_contradicts (read_special Erased env head) l e;
      env
  | _ ->
      let env, r, code = elab_expr1 env Erased final in
      let env, _, _ = elab_match ~refute:true ~res:(r, code) None env [ Erased ] l [ final; final; Wild l ] in
      env

and open_contradicts env l e =
  let env', x, t, _ = open_binding env l Erased e in
  match open_adt env' x with
  | _ -> error_in env l "`open-absurd`: opening %s contradicts nothing" (qshow env' t)
  | exception Contradiction _ -> ()

and refine env scrut c fids ret =
  let labelled = runtime_ids (fst (ctor_type env Reader.nowhere c)) fids in
  let env = match scrut.place, newtype_of env c, labelled with
    | Some p, Some _, [ x ] -> place env x p
    | _ -> env in
  let fvars = List.rev_map (fun x -> Var x) fids in
  merge_opens (unify_force (unify_force (forcing env) scrut.term (App (Var c, List.rev fvars))) scrut.ty (instantiate fvars ret))

and elab_stmt ?within spos env raw : Env.t * (V.code -> V.code) =
  let env', wrap = elab_stmt_unsettled ?within spos { env with pending = [] } raw in
  report_shadows ~env:env' ();
  ({ env' with pending = env.pending }, fun rest -> lets env'.pending (wrap rest))

and elab_stmt_unsettled ?(within = "item of a body") spos env raw =
  match raw with
  | List (l, head :: args) -> (
      let env = if special_of env head <> None then read_special spos env head else env in
      match (special_of env head, args) with
      | Some Sp.Let, _ -> elab_let spos env l args
      | Some Sp.DefLvl, [ n ] ->
          let x, env = mint_level env ~at:(loc n) ((binder_or l n "a name")) in
          track env Definition x;
          (env, Fun.id)
      | Some Sp.DefFns, _ -> elab_def_fns env l args
      | Some Sp.DefUnique, _ -> elab_def_fns ~unique:true env l args
      | Some Sp.DefAdts, _ -> elab_def_adts env args
      | Some Sp.DefOpaque, _ -> (elab_def_opaque env l args, Fun.id)
      | Some Sp.DefPrim, _ -> (elab_def_prim env l args, Fun.id)
      | Some Sp.ComptimeMatch, _ -> elab_comptime_match env l args
      | Some Sp.LetMatch, _ -> elab_let_match spos env l args
      | Some Sp.DumpContext, _ -> dump_context env l Dump.Statement args
      | Some ((Sp.Goal | Sp.Qed) as f), _ -> error_in env l "`%s` is allowed only as a top-level form of a file" (Sp.name f)
      | Some Sp.CompileError, _ -> compile_error (!settle_head Many) spos env l args
      | Some Sp.CompileWarn, _ -> let env, text = compile_text (!settle_head Many) spos env l Sp.CompileWarn args in warn_at l [] "%s" text; (env, Fun.id)
      | Some Sp.SlotSelf, [ a ] ->
          let env = admitted env a in
          let x = reference env (loc a) a "a variable" in
          check_type env (loc a) (type_of env x) Prelude.slot_term;
          ((try place env x (Var x) with Contradiction msg -> error_in env l "`slot-self`: %s contradicts the facts in force (%s)" (qname env x) (Lazy.force msg)), Fun.id)
      | Some Sp.OpenAtFn, [ e ] ->
          let env', p, _ = elab_expr1 env Erased e in
          settle_res env' l p;
          (match canon env' p.ty with
           | App (Var c, [ _; _ ]) when c = Prelude.atfn -> ()
           | ty -> error_in env l "%s : %s is not an `AtFn` proof" (qshow env' p.term) (qshow env' ty));
          let x, env' = bind env' ~at:l None Erased Hypothetical p.ty ~rule:p.term in
          (merge_opens (forcing (opens_add env' x)), Fun.id)
      | Some Sp.OpenAdt, [ m; e ] ->
          let mult = written env spos l "open-adt" (mult_or env l m) in
          let env', x, t, code = open_binding env l mult e in
          let env' = try open_adt env' x with Contradiction msg -> error_in env l "`open-adt`: %s contradicts what is open (%s)" (qshow env' t) (Lazy.force msg) in
          (env', if env.run_pos || mult = Erased then Fun.id else fun rest -> V.CLet ([ x ], code, rest))
      | Some sp, _ when List.mem sp Sp.statements -> error l "%s" (help env (Sp.misuse sp))
      | _ -> not_a_statement within env raw)
  | _ -> not_a_statement within env raw

and not_a_statement within env raw =
  not_a env (if misplaced env raw = [] then Printf.sprintf "not a statement\nhint: every %s but the last must be a statement" (respell env within) else "not a statement") raw

and run_code env code = !on_run env; Eval.eval env.values code

(* Binders that all carry a type or an is clause are the telescope the right-hand side is expected to
   produce (DESIGN.md section 50); the check of each binder against its value stays as it was. The right-hand side's
   statements are statements of the enclosing expression: their code wraps the let's own, and their entries
   stay in scope after it, anonymously (section 27). *)
and elab_let spos env l args =
  let env, bl, binder_raws, rhs =
    match args with
    | List (bl, bs) :: rhs when List.for_all (function List _ -> true | _ -> false) bs -> let env, bs = erased_reads spliced_entries env bs in (env, bl, bs, rhs)
    | _ -> error l "%s" (help env (Sp.misuse Sp.Let))
  in
  let binders = List.concat_map (parse_entry env) binder_raws in
  let expect = List.map (fun b -> match b.s_mult with Some m -> written ~noun:" binder" env spos b.s_loc "let" m | None -> error_in env b.s_loc "`let` binder needs a multiplicity") binders in
  let env, tele, tele_ids =
    if binders <> [] && List.for_all (fun b -> b.s_sg <> None) binders then
      let env', ids, t = elab_tele env ~holes:true ~written:false binder_raws in
      ({ env' with scope = env.scope }, Some t, ids)
    else (env, None, [])
  in
  let after, wrap, final = elab_stmts ~within:"item of a `let`'s right-hand side" spos env l rhs in
  let sink = lazy { owner = respell env "the enclosing `let`"; noun = "value"; shown = List.map Reader.show binder_raws; anchors = [ (bl, respell env "the binders of the enclosing `let` are here") ] } in
  let inner, ress, code = elab_expr ?tele ~sink { after with pending = [] } expect final in
  let temps = inner.pending in
  let inner = { inner with pending = after.pending } in
  let values = if env.run_pos && pos_of env expect <> Erased then run_code inner code else [] in
  let raw i = snd (List.nth (result_sites env l [ final ] (List.length binders)) i) in
  let bind_one (env, ids, acc) (i, ((b, r), v)) =
    let env =
      match (tele, b.s_sg) with
      | Some t, _ -> solve_sg ?raw:(raw i) env b.s_loc (map_sg (instantiate acc) (List.nth t i).sg) r
      | None, Some s -> let env, sg = elab_sg env s in solve_sg ?raw:(raw i) env b.s_loc sg r
      | None, None -> env
    in
    settle_res env b.s_loc r;
    let state, minted, minted_level, order = forwarded env (Option.get b.s_mult) r (if env.run_pos then Some v else None) in
    if b.s_place <> None then error_in env b.s_loc "`at` is allowed only on function telescope and match annotation entries";
    let x, env = bind env ?minted ~minted_level ?introduced:order ~word:true ~at:b.s_loc b.s_name (Option.get b.s_mult) state r.ty ~rule:r.term in
    (placed env x r.place, x :: ids, r.term :: acc)
  in
  let env', ids, _ =
    List.fold_left bind_one (hide inner env, [], []) (List.mapi (fun i x -> (i, x)) (List.combine (List.combine binders ress) (spread expect values)))
  in
  let ids = List.rev ids in
  (match ids with first :: _ -> List.iter (track env' (Let (first, List.length rhs = 1))) ids | [] -> ());
  if tele_ids <> [] then List.iter2 stand_for tele_ids ids;
  let ids = non_erased env' ids in
  (env', if env.run_pos then Fun.id else fun rest -> wrap (lets temps (if pos_of env expect = Erased then rest else V.CLet (ids, code, rest))))

(* A match on a one-constructor type chooses nothing, so what it learns holds wherever the scrutinee does
   and its fields bind outward (section 27's reason for comptime-match, without a discriminant to verify). *)
and elab_let_match spos env l args =
  match args with
  | m :: scrut :: List (pl, c :: fields) :: branches ->
      let env, branches = spliced env branches in
      List.iter (fun b -> if real_branch env b then error_in env l "a `let-match` with a real branch besides its pattern must be a statement of a function, match branch or cell-match body") branches;
      let smult = written env spos l "let-match" (mult_or env l m) in
      let env, sres, scode, swrap, tid, mid, disc, ctors = scrutinee env l smult scrut in
      if smult <> Erased then warn_use env l "match on" (Var tid);
      let c = ctor_var env pl c in
      if marker env pl tid ctors c = Erased && smult <> Erased then error pl "%s is phantom" (qname env c);
      let named = List.filter_map (function List (_, _ :: ((Atom _ | Handle _) as b) :: _) | List (_, _ :: List (_, b :: _) :: _) -> Some (ctor_var env (loc b) b) | _ -> None) branches in
      (* Test each alternative before introducing the selected constructor's facts.
         Trial fields and refinements stay local, exactly as for omitted match branches. *)
      let unrefuted =
        List.filter_map
          (fun (cmult, other) ->
            let other = match other with Var x -> x | _ -> assert false in
            if other = c || List.mem other named then None
            else
              let tele, ret = ctor_type env l other in
              let mults = List.map (fun e -> if cmult = Erased then Erased else field_under smult e.mult) tele in
              let trial, fids = open_tele (leave_run env) ~names:(anon tele) ~mults tele in
              Option.map (fun trial -> (other, trial)) (try Some (at l (fun () -> refine trial sres other fids ret)) with Contradiction _ -> None))
          ctors
      in
      if unrefuted <> [] then missing env l "let-match" sres unrefuted;
      if branches <> [] then ignore (elab_match ~refute:true ~res:(sres, scode) ~cells:(cells_allowed env mid) ~skip:[ c ] None env [ Erased ] l (m :: scrut :: Wild l :: branches));
      let tele, ret = ctor_type env pl c in
      let mults = List.map (fun e -> field_under smult e.mult) tele in
      let fields, name = pattern env "a `let-match` pattern" smult sres pl c mults (cells_allowed ~phantom:(marker env pl tid ctors c = Erased) env mid) fields in
      let names = field_names fields in
      let shapes = shapes env l ctors in
      let run = env.run_pos && smult <> Erased in
      let value = if run then Some (List.hd (run_code env (snd (swrap env scode)))) else None in
      let env = match value,sres.term with Some v, Var x -> set_state env x (Settled v) | _ -> env in
      let states = Option.map (fun v -> snd (settled_fields env pl c mults v)) value in
      let env, fids = open_tele env ~names ~ats:(field_ats tele fields) ~mults ?states tele in
      List.iter (track env Field) fids;
      let env = at l (fun () -> try refine env sres c fids ret with Contradiction msg -> error l "the scrutinee contradicts the facts in force (%s)" (Lazy.force msg)) in
      let env, cell = pattern_cell env pl smult sres c fids name in
      ( env,
        if smult = Erased || run then Fun.id
        else fun rest -> snd (swrap env (
          V.CMatch
            { scrut = scode; shape = match_shape env mid tid disc shapes;
              branches = [ (Option.get (discriminant shapes c), non_erased env (runtime_ids tele fids), bind_cell scode cell (field_renames env l tele fids rest)) ]; default = None;
              live = Option.to_list (discriminant shapes c) })))
  | _ -> error l "%s" (help env (Sp.misuse Sp.LetMatch))

and elab_comptime_match env l args =
  match args with
  | [ m; x; List (pl, c :: fields) ] ->
      let smult = mult_or env l m in
      if smult = Erased then error_in env l "`comptime-match` takes `many` or `unique`, not `erased`";
      if not env.run_pos then error_in env l "`comptime-match` is a run-position statement (section 28)";
      let env, x, sharing =
        match x with
        | List (_, [ h; (Atom _ | Handle _ as a) ]) when special_of env h = Some Sp.Share ->
            let env, y = atom_entry env a in
            if made env a y <> Unique then error_in env l "`share` needs a unique value";
            if smult = Unique then error l "many value %s used at unique" (qname env y);
            (env, (y, a), true)
        | List _ ->
            let env, r, code = elab_expr1 env smult x in
            settle_res env (loc x) r;
            let y, env = bind env ~word:true ~temporary:true None smult (ran_state env smult code) r.ty ~rule:r.term in
            (placed env y r.place, (y, Wild l), false)
        | _ -> let env, y = atom_entry_or env l x "a variable" in (env, (y, x), false)
      in
      let x, r = x in
      let env = use env l ~sharing ?made:(handle_made r) smult x in
      let value = match entry env x with { state = Settled v; _ } when made env r x <> Erased -> v | _ -> error_in env l "`comptime-match` needs a Settled scrutinee that is `many` or `unique`" in
      let c = ctor_var env pl c in
      let tele, ret = ctor_type env pl c in
      let tid = match type_head env (type_of env x) with Some t -> t | None -> error l "scrutinee is not a datatype value" in
      let mid, disc, ctors = find_matchable env l tid in
      warn_use env l "match on" (Var tid);
      if adt_of env mid = None then error_in env l "the `Matchable` for %s is %s, so `comptime-match` cannot consult it" (qname env tid) (if (entry env mid).mult = Erased then "erased" else "not Settled");
      let env = use env l Many mid in
      if disc = Union then error_in env l "`comptime-match` needs an `enum`, not a `union`";
      if marker env pl tid ctors c = Erased then error_in env pl "`comptime-match`: %s is phantom, so no non-erased value is headed by it" (qname env c);
      let mults = List.map (fun e -> field_under smult e.mult) tele in
      let matched, states = settled_fields env pl c mults value in
      if not matched then error_in env l "`comptime-match`: expected %s, got %s" (qname env c) (tick (show_value env l (type_of env x) value));
      let fields, name = pattern env "a `comptime-match` pattern" smult (res_of env x) pl c mults (cells_allowed env mid) fields in
      let names = field_names fields in
      let env, fids = open_tele env ~names ~ats:(field_ats tele fields) ~mults ~states tele in
      List.iter (track env Field) fids;
      let env = at l (fun () -> try refine env (res_of env x) c fids ret with Contradiction msg -> error l "internal: the verified value contradicts the facts in force (%s)" (Lazy.force msg)) in
      let env, _ = pattern_cell env pl smult (res_of env x) c fids name in
      (env, Fun.id)
  | _ -> error l "%s" (help env (Sp.misuse Sp.ComptimeMatch))

and elab_def_fns ?(unique = false) env l args =
  match args with
  | [] -> error_in env l "`def-fns` needs a level"
  | lv :: fns ->
      if unique && List.length fns <> 1 then error_in env l "`def-unique` defines exactly one function";
      let env, lvl =
        match lv with
        | Wild al -> let x, env = mint_level env ~at:al None in (env, x)
        | _ -> level_var ~alt:" or `_`" env l lv
      in
      (* the header's marks: `at` before the name makes an at-function (section 39), `at f` after it annotates a
         delegate to f and puts it at f (section 41); a function marked `extern` and `at` has no implementation, its marks being a
         promise *)
      let header env raw =
        match raw with
        | List (_, List (fl, m :: rest) :: body) -> (
            let mult = mult_or env fl m in
            let marks, rest = def_marks env fl [ Sp.Absurd; Sp.Extern; Sp.At ] rest in
            let delegates, rest = match rest with n :: a :: f :: rest when is_special env a Sp.At -> (Some (named env (loc f) "a function name" f), n :: rest) | _ -> (None, rest) in
            match rest with
            | n :: colon :: sg when is_special env colon Sp.Colon ->
                let ps, rs = split_arrow env fl sg in
                let name = binder_or fl n "a function name" in
                let env, ty, sig_ids = elab_fn_type ~unique env (Var lvl) ps rs in
                let many_params = match ty with Fn (_, ps, _) | UniqueFn (_, ps, _) -> List.length (runtime ps) | _ -> 0 in
                let atfn = List.mem Sp.At marks and extern = List.mem Sp.Extern marks in
                if atfn && mult = Erased then error_in env fl "an `erased` function cannot be an at-function: it is called only where nothing runs";
                if atfn && runtime (match ty with Fn (_, _, rs) | UniqueFn (_, _, rs) -> rs | _ -> []) <> [] then error_in env fl "an at-function's returns are erased or `at`";
                let impl = if extern && not atfn then Some (Ffi.claim_fn fl (spell_binder name) many_params) else None in
                (env, (fl, name, mult, List.mem Sp.Absurd marks, (impl, extern, atfn, delegates), ty, sig_ids, body))
            | _ -> error fl "malformed function header%s" (help env (Sp.hints "function-header")))
        | _ -> error (loc raw) "malformed function definition%s" (help env (Sp.hints "function-definition"))
      in
      let capture_uses = ref env.uses in
      (* each header sees the functions before it in the block (section 53); the `AtFn` and `Delegate` proofs are
         minted with the header, so a call within the block to a function marked `at` is skipped (section 39) *)
      let env, fids_headers = List.fold_left_map (fun env raw ->
        let env, ((fl, name, mult, _, (_, _, atfn, delegates), ty, _, _) as h) = header env raw in
        if unique && mult = Many then error_in env fl "`def-unique` requires `unique` or `erased`" else if not unique && mult = Unique then error_in env fl "use `def-unique` to define a unique function";
        let x, env = bind env ~word:true ~at:fl name mult Hypothetical ty in
        track env Definition x;
        let env = if not atfn then env else let p, env = witness env (proof_type Prelude.atfn [ ty; Var x ]) in merge_opens (forcing (opens_add env p)) in
        let env = match delegates with
          | None -> env
          | Some f ->
              let fty = infer env fl (Var f) in
              (match canon env fty with Fn _ | UniqueFn _ -> () | t -> error_in env fl "%s is declared `at` %s, which is not a function: it has type %s" (tick (spell_binder name)) (qname env f) (qshow env t));
              snd (witness (placed env x (Some (slot_of f))) (proof_type Prelude.delegate [ sharing_of_fn env ty; ty; Var x; sharing_of_fn env fty; fty; Var f ])) in
        (env, (x, h))) env fns in
      let fids, headers = List.split fids_headers in
      let define x (fl, name, mult, absurd, (impl, extern, atfn, delegates), ty, sig_ids, body) =
        let params, rets = match ty with Fn (_, ps, rs) | UniqueFn (_, ps, rs) -> (ps, rs) | _ -> assert false in
        let body_erased = env.usage_erased || mult = Erased || absurd in
        let envb = if unique then { env with entries = IntMap.add x { (entry env x) with mult = Erased } env.entries } else env in
        let envb, pids = open_tele { envb with usage_erased = body_erased } params in
        List.iter (track envb Param) pids;
        List.iter2 stand_for sig_ids pids;
        let pvars = List.rev_map (fun x -> Var x) pids in
        (* a parameter written `at` is not passed: its word is its target's (section 36) *)
        let renames body = field_renames envb fl params pids body in
        let subterms = List.filter_map (fun (e, x) -> if e.subterm then Some x else None) (List.combine params pids) in
        let envb = { envb with level = At lvl; subterms; enclosing = Some x; run_pos = false; trusted = trusted env; in_extern = env.in_extern || extern; unwarned = env.unwarned || extern || atfn; usage_erased = body_erased; captures = (if unique then env.captures else env.scope.ids @ env.captures) } in
        let envb, code =
          if absurd then (elab_refute envb fl body, V.CAbsurd)
          else
            let tele = instantiate_tele pvars rets in
            let sink = lazy { owner = qname env x; noun = "return value"; shown = show_tele envb (with_mults (under mult) tele); anchors = declared_as env x } in
            let envb, ress, code = elab_body ~tele ~sink envb (List.map (fun e -> under mult e.mult) rets) fl body in
            check_results envb fl ~ids:pvars body rets ress;
            (envb, if mult = Erased then V.CErased else renames (project_code (List.filter_map (fun e -> if e.mult = Erased then None else Some (e.place = None)) rets) code))
        in
        capture_uses := join_uses !capture_uses (IntMap.filter (fun x _ -> IntMap.mem x env.entries) envb.uses);
        let code, delegated = check_marks envb fl (runtime_ids params pids) code in
        if extern && delegated <> None then error_in env fl "a function marked `extern` cannot have a `delegate` body: its implementation is promised only under its own signature, and a `Delegate` proof would let a `coerce` run it under the callee's; mark the call `tail`";
        (match delegates, delegated with
         | None, None -> ()
         | None, Some callee -> error_in env fl "%s delegates to %s, so its header must name the callee: write `at` and the callee after the name" (tick (spell_binder name)) (qshow envb callee)
         | Some f, Some callee ->
             if not (equal (canon envb callee) (Var f)) then error_in env fl "%s is declared `at` %s but delegates to %s" (tick (spell_binder name)) (qname env f) (qshow envb callee);
             Hashtbl.replace V.aliases x (V.resolve f)
         | Some f, None -> error_in env fl "%s is declared `at` %s but its body is not a `delegate` call" (tick (spell_binder name)) (qname env f));
        (* an at-function's body erases to nothing and is never run through the proof; what remains is the
           dummy a first-class call without the proof reaches (section 39) *)
        if atfn && not absurd && not (erases_to_nothing code) then error_in env fl "the body of at-function %s does not erase to nothing, or to a reordering of variables: it stores, allocates or calls" (tick (spell_binder name));
        let code = if atfn then V.CValues [] else code in
        (x, { V.fname = spell_binder name; params = runtime_ids params pids; body = code; impl })
      in
      let fns = List.map2 define fids headers in
      let env = { env with uses = !capture_uses } in
      let fns = List.filter (fun (x, _) -> not (Hashtbl.mem V.aliases x)) fns in
      if env.run_pos then
        let values = Eval.close env.values fns in
        if fns <> [] then trace := Fns fns :: !trace;
        (List.fold_left (fun env x -> set_state env x (Settled (IntMap.find (V.resolve x) values))) env fids, Fun.id)
      else
        let fns = List.filter (fun (x, _) -> (entry env x).mult <> Erased) fns in
        (env, if fns = [] then Fun.id else fun rest -> V.CLetRec (fns, rest))

(* Validates the tail/delegate marks in a body (section 19), returning the delegated callee if any. Lets that only
   rename (all a coerce leaves), return exactly what they bind, or bind constants nothing mentions (a nested
   def-adts the body never reads) are first folded away, so a marked call stands in tail position in the code
   that runs. *)
and check_marks env l pids code =
  let vars_of cs = List.map (function V.CVar x -> x | _ -> -1) cs in
  let code = normalize code in
  let rec calls acc c = List.fold_left calls (match c with V.CApp _ -> c :: acc | _ -> acc) (V.subcodes c) in
  let rec tails ~direct = function
    | V.CApp _ as c -> [ c ]
    | V.CLet (_, _, rest) | V.CLetRec (_, rest) -> if direct then [] else tails ~direct rest
    | V.CMatch m -> if direct then [] else List.concat_map (tails ~direct) (List.map (fun (_, _, c) -> c) m.V.branches @ Option.to_list m.V.default)
    | _ -> []
  in
  let all = calls [] code and in_tail = tails ~direct:false code in
  List.iter
    (function
      | V.CApp (_, _, V.NoTail) as c when List.memq c in_tail -> error_in env l "a `notail`-marked call is in tail position"
      | V.CApp (_, _, V.Same (cl, callee)) as c -> warn_in env cl [] "same-level call to %s is unmarked; mark it %s" (Lazy.force callee) (tick (speller env (if List.memq c in_tail then "tail" else "notail")))
      | _ -> ())
    all;
  ( code,
    match List.filter (function V.CApp (_, _, (V.Tail | V.Delegate)) -> true | _ -> false) all with
    | [] -> None
    | marks ->
        let delegate = List.exists (function V.CApp (_, _, V.Delegate) -> true | _ -> false) marks in
        let ok = if delegate then tails ~direct:true code else in_tail in
        List.iter (fun c -> if not (List.memq c ok) then error l "a %s-marked call is not in tail position" (tick (if delegate then "delegate" else "tail"))) marks;
        if not delegate then None
        else
          match ok with
          | [ V.CApp (V.CVar f, args, _) ] ->
              if vars_of args <> pids then error_in env l "a `delegate` call must pass the function's non-erased parameters straight through";
              Some (Var f)
          | _ -> error_in env l "`delegate` needs exactly one call to a named function" )

and declares_trusted env l sp = if not env.externs then error_in env l "only the prelude may write %s; a program that declares its own runs with `--no-prelude`" (tick (speller env (Sp.name sp)))

and elab_def_opaque env l entries =
  declares_trusted env l Sp.DefOpaque;
  List.fold_left (fun env raw ->
    match raw with
    | List (_, [ List (al, n :: colon :: sg) ]) when is_special env colon Sp.Colon ->
        let ps, ret = split_arrow env al sg in
        let env, ty = elab_tyctor env al ps ret in
        snd (bind env ~at:al (binder_or al n "a type constructor name") Erased (settled env V.VToken) ty)
    | _ -> error_in env (loc raw) "malformed `def-opaque` entry%s" (help env (Sp.hints "def-opaque"))) env entries

and elab_def_prim env l entries =
  declares_trusted env l Sp.DefPrim;
  List.fold_left (fun env raw ->
    match raw with
    | List (_, [ List (fl, m :: n :: colon :: sg) ]) when is_special env colon Sp.Colon ->
        let mult = mult_or env fl m in
        if mult = Unique then error_in env fl "a primitive is declared `many` or `erased`";
        let sp = match n with Atom (_, Src s) -> List.find_opt (fun p -> Sp.name p = s) primitives | _ -> None in
        let sp = match sp with Some sp -> sp | None -> error (loc n) "%s names no primitive the compilers implement" (tick (Reader.show n)) in
        if Hashtbl.mem prims sp then error fl "a second `def-prim` for %s" (tick (Sp.name sp));
        let ps, rs = split_arrow env fl sg in
        let env', ids, params = elab_tele env ~places:true ps in
        let env', _, rets = elab_tele env' ~places:true ~ids:(List.rev ids) rs in
        if mult <> Erased && not (List.mem sp implemented) && List.exists stored rets then
          error fl "the compilers have no implementation of %s, so its returns must be erased or written `at`" (tick (Sp.name sp));
        Hashtbl.replace prims sp (mult, params, rets);
        carry env env'
    | _ -> error_in env (loc raw) "malformed `def-prim` entry%s" (help env (Sp.hints "def-prim"))) env entries

and elab_def_adts env adts =
  let header env raw =
    match raw with
    | List (_, List (al, n :: colon :: sg) :: d :: rest) when is_special env colon Sp.Colon -> (
        let ps, ret = split_arrow env al sg in
        match ret with
        | [ ty ] -> let ms, ctors = def_marks env al [ Sp.NewtypeMark; Sp.Extern ] rest in let env, ctors = erased_reads spliced env ctors in (env, (al, binder_or al n "a type constructor name", ps, ty, disc_of env al d, ms, ctors))
        | _ -> error al "a type constructor declares one return")
    | _ -> error_in env (loc raw) "malformed `def-adts` entry%s" (help env (Sp.hints "def-adts-entry"))
  in
  let env, headers = List.fold_left_map header env adts in
  let env, tids =
    List.fold_left_map
      (fun env (al, name, ps, ty, _, _, _) ->
        let env, tty = elab_tyctor env al ps [ ty ] in
        let x, env = bind env ~at:al name Erased (settled env V.VToken) tty in
        (env, x))
      env headers
  in
  let define (env, cids) tid (al, name, _, _, disc, ms, ctors) =
    let ctor env raw =
      match raw with
      | List (cl, m :: n :: colon :: rest) when is_special env colon Sp.Colon ->
          let mult = mult_or env cl m in
          if mult = Unique then error_in env cl "a constructor declaration cannot be `unique`";
          let name = binder_or cl n "a constructor name" in
          let env', tele, ret, ty = elab_valctor env cl rest in
          (match canon env' ret with App (Var t, _) when t = tid -> () | _ -> error cl "%s must return an application of %s" (tick (spell_binder name)) (qname env tid));
          if mult = Erased && List.exists (fun e -> e.mult <> Erased) tele then warn_at cl [] "phantom constructor %s has a non-erased field" (tick (spell_binder name));
          let c, env = bind (carry env env') ~at:cl name mult (if mult = Erased then settled env V.VToken else Hypothetical) ty in
          (env, (mult, c))
      | _ -> error (loc raw) "malformed constructor%s" (help env (Sp.hints "constructor"))
    in
    let env, ctors = List.fold_left_map ctor env ctors in
    let ctors = List.map (fun (m, c) -> (m, Var c)) ctors in
    let shapes = shapes env al ctors in
    let name = spell_binder name in
    let adt = mint_adt ~newtype:(List.mem Sp.NewtypeMark ms) env name disc shapes in
    Ffi.note name adt;
    if List.mem Sp.Extern ms then adt.ext <- Some (Ffi.claim_type al name adt);
    let values = List.map (fun ct -> (ct.V.cid, V.VCtorFn ct)) adt.ctors in
    let env = if env.run_pos then List.fold_left (fun env (c, v) -> set_state env c (Settled v)) env values else env in
    let mid, env = witness env ~mult:Many ~value:(V.VMatchable adt) (Matchable (disc, List.mem Sp.NewtypeMark ms, List.mem Sp.Extern ms, Var tid, ctors)) in
    let env = open_adt env mid in
    if List.mem Sp.NewtypeMark ms && wrappers disc shapes = [] then error al "%s is not of newtype shape (section 33)" (tick name);
    (env, cids @ values @ [ (mid, V.VMatchable adt) ])
  in
  let env, cids = List.fold_left2 define (env, []) tids headers in
  (env, if env.run_pos then Fun.id else fun rest -> V.CLet (List.map fst cids, V.CValues (List.map (fun (_, v) -> V.CConst v) cids), rest))

let () = settle_head := computed_head

type final = Main | Program | Thunk of term | Plain

let final_form env ty =
  let bare string e = match e with { mult = Many; sg = Ty t; place = None; subterm = false; _ } -> (not string) || nullary env "String" t | _ -> false in
  match canon env ty with
  | Fn (_, [ p ], [ r ]) when bare true p && bare true r -> Some Main
  | Fn (_, [], [ ({ sg = Ty t; _ } as r) ]) when bare false r -> Some (Thunk t)
  | Fn _ | UniqueFn _ -> None
  | _ -> Some (if nullary env "Program" ty then Program else Plain)

let final env ty = Option.value (final_form env ty) ~default:Plain

let report_unused env =
  let all = List.of_seq (Hashtbl.to_seq tracked) in
  let order (x, t) (y, u) =
    let (l, c), (l', c') = (Reader.coords t.at, Reader.coords u.at) in
    match (compare (Reader.file_of t.at) (Reader.file_of u.at), Z.compare l l', Z.compare c c') with
    | 0, 0, 0 -> compare x y
    | 0, 0, n | 0, n, _ | n, _, _ -> n in
  let unused x = level x = 0 in
  let deletable g = List.for_all (fun (x, t) -> match t.kind with Let (g', _) when g' = g -> unused x | _ -> true) all in
  List.iter (fun (x, t) -> match t.binder with Gen _ -> () | Src b ->
    let name = tick_name t.binder and renamed = tick_name (Src ("_" ^ b)) in
    if lookup env t.binder = Some x || String.starts_with ~prefix:"_" b then ()
    else if unused x then
      match t.kind with
      | Optional | Definition -> warn_in env t.at [] "unused %s; delete it" name
      | Let (g, true) when deletable g -> warn_in env t.at [] "unused %s; delete its `let`" name
      | Let _ | Field -> warn_in env t.at [] "unused %s; write `_` in its place" name
      | Param -> warn_in env t.at [] "unused %s; rename it %s" name renamed
    else if level x = 1 && t.mult <> Erased && not t.erased_scope then
      match t.kind with
      | Let _ -> warn_in env t.at [] "%s is referenced only in erased positions; declare it `erased`" name
      | Param -> warn_in env t.at [] "%s is referenced only in erased positions; declare it `erased`, or rename it %s" name renamed
      | Field | Optional | Definition -> ()) (List.sort order all);
  reset_tracking ()

let rec interned env = function
  | List (l, rs) -> List (l, List.map (interned env) rs)
  | r -> (match lit_of r with Some lit -> (match at (loc r) (fun () -> literal_handle env lit) with V.VHandle (x, rd, m, v) -> Handle (loc r, x, rd, m, Obj.repr v) | _ -> r) | None -> r)

let goal_modes = [ ("none", Unrequired); ("open", Open); ("proved", Proved) ]
let goal_name m = fst (List.find (fun (_, m') -> m' = m) goal_modes)
let goal_flag m = "`--goal " ^ goal_name m ^ "`"

let set_goal env l = function
  | [ m; t ] ->
      Option.iter (fun (at, _, _, _) -> error_with_in env l [ (at, "the goal is set here") ] "a unit sets at most one `goal`") !goal;
      let mult = mult_or env (loc m) m in
      let env, ty = elab_type env t in
      settle env (loc t) ty;
      goal := Some (l, mult, ty, env);
      env
  | _ -> error l "%s" (help env (Sp.misuse Sp.Goal))

let qed env l = function
  | [ item ] -> (
      Option.iter (fun at -> error_with_in env l [ (at, "the goal is proved here") ] "a unit has at most one `qed`") !discharged;
      match !goal with
      | _ when !goal_mode = Open -> error_in env l "under %s no `qed` proves the goal" (goal_flag Open)
      | None -> error_in env l "a `qed` proves the goal a `goal` sets before it, and none is set"
      | Some (at, mult, ty, _) ->
          let tele = [ { name = None; subterm = false; mult; sg = Ty ty; place = None; loc = at } ] in
          let sink = lazy { owner = "the goal"; noun = "value"; shown = show_tele env tele; anchors = [ (at, "the goal is set here") ] } in
          let env, ress, _ = elab_expr ~tele ~sink ~final:true env [ mult ] item in
          check_results env l [ item ] tele ress;
          discharged := Some l;
          env)
  | _ -> error l "%s" (help env (Sp.misuse Sp.Qed))

let close_goal () =
  match !goal_mode, !goal, !discharged with
  | Unrequired, _, _ -> None
  | m, None, _ -> error Reader.nowhere "under %s a file sets a `goal`, and none does" (goal_flag m)
  | Proved, Some (at, _, _, env), None -> error_in env at "the goal is not discharged: under %s a `qed` proves it" (goal_flag Proved)
  | m, Some (at, mult, ty, env), by ->
      let note l text = let here = Reader.where "-" l in Env.resolve here (Reader.label here "note: " ^ text) in
      let goal = note at (sprintf_in env "%s `(goal %s %s)`" (goal_name m) (speller env (mult_name mult)) (show env ty)) in
      Some (String.concat "\n" (goal :: Option.to_list (Option.map (fun l -> note l (sprintf_in env "by this `qed`")) by)))

let run_toplevel ?(consume = fun _ _ v -> print_endline (V.show v)) ?(path = "-") ?(loading_prelude = false) env items =
  let rec go env = function
    | [] -> env
    | (List (_, Atom (_, Src ";!") :: _) as p) :: rest -> step env [ p ] rest
    | item :: rest -> step env [ interned env item ] rest
  and step env pending source =
    let env = if loading_prelude then { env with prelude = env.scope } else env in
    let env, pending = expand_seq Many env pending in
    match pending with
    | [] -> go env source
    | List (l, Atom (_, Src ";!") :: words) :: rest -> step (at l (fun () -> pragma env l words)) rest source
    | item :: rest -> (
        reset_tracking ();
        at (loc item) (fun () ->
            if rest = [] && source = [] && not (is_statement env item) then (
              if misplaced env item <> [] then not_a env "neither a statement nor an expression" item;
              let env, ress, code = elab_expr ~demand:Driver env [ Many ] item in
              settle_res env (loc item) (single (loc item) ress);
              let ty = (single (loc item) ress).ty in
              let driven = !goal_mode = Unrequired in
              if driven && final_form env ty = None then
                error_in env (loc item) "a final function must be `(Fn L (many (String) x) -> (many (String) y))` or `(Fn L -> (many T y))`; this one is %s" (qshow env ty);
              let v = List.hd (run_code env code) in
              if driven then trace := Final (v, ty, path) :: !trace;
              if !warn_unused then report_unused env;
              if driven then consume env ty v;
              env)
            else
              let env = match item with
                | List (l, h :: args) when special_of env h = Some Sp.Goal -> set_goal (read_special Many env h) l args
                | List (l, h :: args) when special_of env h = Some Sp.Qed -> qed (read_special Many env h) l args
                | _ -> fst (elab_stmt ~within:"top-level form" Many env item) in
              if !warn_unused then report_unused env;
              step env rest source))
  in
  let env = Fun.protect ~finally:report_shadows (fun () -> go env items) in
  (match items with
   | item :: _ -> List.iter (fun r -> if not r.Reader.used then warn_at r.from [] "`;! suppress warn` for %s silenced nothing" (tick r.name)) (Option.value ~default:[] (Hashtbl.find_opt Reader.regions (Reader.file_of (loc item))))
   | [] -> ());
  env

let run_file ?consume env (f : Reader.file) =
  let warned = Indent.warn f in
  run_toplevel ?consume ~path:f.name env (Reader.parse ~shape:(not warned) f)
