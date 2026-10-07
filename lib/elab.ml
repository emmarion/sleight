open Term
open Reader
open Env
module V = Value
module Sp = Special

type entry = Term.entry = { name : string option; subterm : bool; mult : mult; sg : sg; place : term option; loc : Reader.loc }
type res = { term : term; ty : term; erasure : mult; place : term option }
type demand = Fixed | CallableHead | Driver

(* A variable the caller holds physically whose slot is [p], the word an `at` entry is read from (A3). *)
let location_var env l p =
  let readable x = (entry env x).mult <> Erased && ((entry env x).word || IntMap.mem x env.values) in
  match p with
  | SlotOf (Var x) when readable x -> x
  | _ ->
      let p = canon env p in
      (match List.find_opt (fun x -> readable x && same_slot env p (slot_of x)) env.scope.ids with
      | Some x -> x
      | None -> error_in env l "no caller word for `at` %s" (qshow env p))

let type_term = Prelude.type_term

(* An anonymous entry whose type is the `AtFn` proof about [g] (A10), as a `Delegate` proof is found. *)
let is_atfn_proof env x g = match type_of env x with App (Var c, [ _; Var g' ]) -> c = Prelude.atfn && g' = g | _ -> false


let single loc = function [ r ] -> r | rs -> error loc "expected one value, got %d" (List.length rs)
let pos_of expect = if expect <> [] && List.for_all (( = ) Erased) expect then Erased else if expect = [ Unique ] then Unique else Many
let atom = function Atom (_, n) -> Some n | List _ -> None
let atom_or loc raw what = match atom raw with Some n -> n | None -> error loc "expected %s, got %s" what (tick (Reader.show raw))
let name_or_anon n = if n = "_" then None else Some n

(* A special form's head: a Const, non-erased entry of type (Special) holding one of its variants (section 4). *)
let special_value env x = match entry env x with
  | { state = Const (V.VCtor (c, [||])); mult = (Many | Unique); _ } when equal (type_of env x) Prelude.special_term -> List.assoc_opt c.cid Prelude.specials
  | _ -> None
let () = Env.special_name := (fun env x -> Option.map Sp.name (special_value env x)); Env.delegate_ctor := Prelude.delegate; Env.atfn_ctor := Prelude.atfn

let rec special_of env raw =
  let value = special_value env in
  match raw with
  | Atom (_, n) -> Option.bind (lookup env n) value
  | List (_, [head; Atom (_, n)]) when special_of env head = Some Sp.Share -> Option.bind (lookup env n) value
  | _ -> None

let read_special pos env raw =
  match raw with
  | Atom (l,n) -> use env l Many (Option.get (lookup env n))
  | List (l,[h;Atom (_,n)]) when special_of env h = Some Sp.Share ->
      if pos = Erased then error_in env l "`share` in an erased position";
      let x = Option.get (lookup env n) in
      if (entry env x).mult <> Unique then error_in env l "`share` needs a unique value";
      use env l ~sharing:true Many x
  | _ -> env

let is_special env raw s = special_of env raw = Some s
let mult_of env raw = match special_of env raw with Some Sp.Erased -> Some Erased | Some Sp.Many -> Some Many | Some Sp.Unique -> Some Unique | _ -> None
let mult_or env loc raw = match mult_of env raw with Some m -> m | None -> error loc "expected a multiplicity, got %s" (tick (Reader.show raw))
let is_statement env = function List (_, h :: _) -> List.exists (is_special env h) Sp.statements | _ -> false
let misplaced env = function List (_, h :: _) -> Option.to_list (Option.bind (special_of env h) (fun sp -> if Sp.has_role sp then Some sp else None)) | _ -> []
let brief = function
  | Atom (_, s) -> tick s
  | List (_, Atom (_, h) :: args) -> tick ("(" ^ h ^ (if args = [] then ")" else " ...)"))
  | List (_, []) -> tick "()"
  | List _ -> "this form"
let not_a env what raw = error (loc raw) "%s is %s%s" (brief raw) what (help env (String.concat "" (List.map Sp.role_hints (misplaced env raw))))
let at loc f = try f () with Error (l, msg) when not (Reader.placed l) -> error loc "%s" msg
let var env loc n =
  match Literal.classify n with
  | `Name -> (match lookup env n with Some x -> x | None -> error loc "unbound name %s%s" (tick n) (hint env n))
  | `Lit lit -> (match List.assoc_opt (Literal.key lit) env.literals with Some (x, _) -> x | None -> error loc "literal %s outside a top-level form" n)
  | `Bad msg -> error loc "%s" msg

let resolve env x = match canon env (Var x) with Var y -> y | _ -> x

(* Elaborate in the prelude's scope, so user shadowing cannot reach a generated form; the level context
   stays the caller's. *)
let in_prelude env f =
  let frame, r = f { env with scope = env.prelude } in
  ({ frame with scope = env.scope }, r)

(* The entry holding the [Nat] a numeral or character literal stands for: a character's is its code's. *)
let numeral_entry env loc raw =
  let name = atom_or loc raw "a numeral or character literal" in
  let z, lit =
    match Literal.classify name with
    | `Lit (Literal.Numeral z as lit) -> (z, lit)
    | `Lit (Literal.Char c as lit) -> (Z.of_int c, lit)
    | _ -> error loc "%s is not a numeral or character literal" (tick name)
  in
  match List.assoc_opt (Z.to_string z) env.literals with
  | Some (x, _) -> (z, x, Literal.spell lit)
  | None -> error loc "literal %s is not in scope" (Literal.spell lit)

(* An atom naming an entry, read through any alias rule the fact table holds for it (section 9). *)
let named env loc what raw =
  match canon env (Var (var env loc (atom_or loc raw what))) with Var x -> x | t -> error loc "%s is not %s" (qshow env t) what

let tyname env loc = named env loc "a type constructor"

let rec is_strict_subterm a b =
  match b with App (_, args) -> List.exists (fun x -> equal a x || is_strict_subterm a x) args | _ -> false

(* A literal is an atom to the unifier (LITERALS.md): checking fails where one meets a Succ shape or another
   literal, and forcing binds one where a contradiction was wanted. The notes name each literal [hit] picks out
   among the numeral and character literals, by its canonical form, a character standing for its code, and the
   first of [within] it sits in. *)
let literal_notes env l ~within hit =
  let lits = List.filter_map (fun (k, (x, _)) -> match Literal.classify k with
    | `Lit ((Literal.Numeral _ | Literal.Char _) as lit) -> Some (lit, canon env (Var x))
    | _ -> None) env.literals in
  let hits = List.filter (fun (_, t) -> hit t) lits in
  let code_of_char t = List.exists (function (Literal.Char _, ct) -> is_strict_subterm t ct | _ -> false) hits in
  let hits = List.sort_uniq compare (List.filter (function (Literal.Numeral _, t) -> not (code_of_char t) | _ -> true) hits) in
  let note (lit, t) =
    let place = List.find_opt (fun c -> is_strict_subterm t (canon env c)) within in
    let kind, opaque = match lit with Literal.Char _ -> ("character", "whose code is opaque") | _ -> ("numeral", "opaque") in
    (l, sprintf_in env "%s%s is a %s literal, %s to the checker by default; `unary`, `distinct` or `numeral-of` can expose more"
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

(* Identity after canonicalization (section 5), solving any metas either side holds (Env.unify). *)
let solve ?raw ?(about = lazy ("", [])) what env loc actual expected =
  try unify env actual expected
  with Contradiction _ ->
    let pairs = List.filter (fun (a, b) -> not (has_meta env a || has_meta env b)) (differ (canon env actual) (canon env expected)) in
    let side t (a, b) = equal t a || equal t b || is_strict_subterm a t || is_strict_subterm b t in
    let notes = literal_notes env loc ~within:[ expected; actual ] (fun t -> List.exists (side t) pairs) in
    let hint = match raw, ctor_result env actual with
      | Some raw, Some (ps, r) when equal (head r) (head (canon env expected)) -> Some (Printf.sprintf "did you mean %s?" (tick (Reader.show (List (Reader.loc raw, raw :: List.map (fun _ -> Atom (Reader.loc raw, "_")) ps)))))
      | _ -> None in
    let prefix, more = Lazy.force about in
    error_with ?hint loc (notes @ more) "%s%s mismatch: expected %s, got %s" prefix what (qshow env expected) (qshow env actual)

(* The literals a forcing trial bound, which is what leaves a branch standing that a literal index was meant
   to refute: those whose canonical form the trial changed, and any literal one was bound to. *)
let forced_notes env l r trial =
  let bound = List.filter_map (fun (_, (x, _)) -> let t = canon env (Var x) in if equal (canon trial t) t then None else Some (canon trial t)) env.literals in
  literal_notes env l ~within:[ r.ty; r.term ] (fun t -> List.exists (equal (canon trial t)) bound)

let check what env loc actual expected = ignore (solve what env loc actual expected)
let check_type = check "type" and check_equal = check "value"
let solve_sg ?raw ?about env loc sg r = match sg with Ty ty -> solve ?raw ?about "type" env loc r.ty ty | Is t -> solve ?about "value" env loc r.term t
let check_sg env loc sg r = ignore (solve_sg env loc sg r)
let under pos m = if pos = Erased then Erased else m
let written env pos l what m =
  if pos = Erased && m <> Erased then error_in env l "a %s in an erased position is written `erased`" (tick (speller env what)) else m
let field_under pos m = if pos = Many && m = Unique then Many else under pos m
let wild = function Atom (_, "_") -> true | _ -> false

(* A boundary (SUGAR.md 6): a term reaching one with a `_` still open is refused. *)
let settle env loc t = if has_meta env t then unsolved loc env t

let rec infer env loc t =
  match t with
  | Var x -> type_of env x
  | App (h, args) -> (
      match canon env (infer env loc h) with
      | TyCtor _ -> type_term
      | ValCtor (_, r) -> instantiate (List.rev args) r
      | ty -> error loc "%s has type %s and cannot be applied" (qshow env h) (qshow env ty))
  | Fn _ | UniqueFn _ | TyCtor _ | ValCtor _ | Matchable _ | Cell _ -> type_term
  | SlotOf _ -> Prelude.slot_term
  | Bound _ -> error loc "internal: dangling binder"

let res_of env x = { term = Var x; ty = type_of env x; erasure = (entry env x).mult; place = if (entry env x).mult = Erased then None else Some (slot_of x) }
let settle_res env loc r = settle env loc r.term; settle env loc r.ty
let non_erased env ids = List.filter (fun x -> (entry env x).mult <> Erased) ids

(* What a signature passes or returns at runtime: its non-erased entries without a written `at` (A3). *)
let runtime tele = List.filter (fun (e : entry) -> e.mult <> Erased && e.place = None) tele
let runtime_ids tele ids = List.filter_map (fun (e, x) -> if e.mult <> Erased && e.place = None then Some x else None) (List.combine tele ids)
let with_words env ids = List.fold_left (fun env x -> { env with entries = IntMap.add x { (entry env x) with word = true } env.entries }) env ids
let head_name env h = match h.term with Var x -> qname env x | t -> qshow env t
let head_notes env h = match h.term with Var x -> declared env ~how:(Printf.sprintf " `%s`" (speller env (mult_name (entry env x).mult))) x | _ -> []

type callee = { subject : string Lazy.t; apposed : bool; notes : (Reader.loc * string) list Lazy.t; used : mult -> mult; marks : bool }

let expected = function [] -> "" | ss -> ": expected " ^ tick (String.concat " " ss)
let counted n what = Printf.sprintf "%d %s%s" n what (if n = 1 then "" else "s")
let with_mults used tele = List.map (fun (e : entry) -> { e with mult = used e.mult }) tele

let describe env pos raw term ty =
  let used, marks = match ty with Fn _ | UniqueFn _ -> (under pos, true) | TyCtor _ -> (Fun.id, false) | _ -> (field_under pos, true) in
  let apposed = match ty, raw with Cell _, Atom _ -> true | _ -> false in
  let view = lazy (
    let kind = kind_name env ty in
    match ty, raw, term with
    | Cell (Var c, _), Atom _, Var x -> (sprintf_in env "%s, a `Cell` of %s" (qname env x) (qname env c), declared_as env c)
    | Cell (Var c, _), _, _ -> (sprintf_in env "the computed `Cell` of %s" (qname env c), (Reader.loc raw, respell env "the `Cell` is computed here") :: declared_as env c)
    | _, Atom _, Var x -> (qname env x, declared_as env x)
    | _ -> ("the computed " ^ kind, [ (Reader.loc raw, Printf.sprintf "the %s is computed here" kind) ])) in
  { subject = lazy (fst (Lazy.force view)); apposed; notes = lazy (snd (Lazy.force view)); used; marks }

let count_error env l c what tele got =
  error_with l (Lazy.force c.notes) "%s%s expects %s, got %d%s" (Lazy.force c.subject) (if c.apposed then "," else "") (counted (List.length tele) what) got
    (expected (show_tele ~marks:c.marks env (with_mults c.used tele)))

let argument c i name = Printf.sprintf "argument %d%s of %s" (i + 1) (match name with Some n -> ", " ^ tick n ^ "," | None -> "") (Lazy.force c.subject)

let term_res env loc t = { term = t; ty = infer env loc t; erasure = Erased; place = None }

(* Opens [x], a Matchable entry (section 19): its constructors must be distinct after canonicalization,
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
  if not (readable env mid) then
    error_in env loc "the `Matchable` for %s is erased or out of scope, so a non-erased match cannot take a value of it apart" (qname env tid)

let ctor_type env loc c =
  match canon env (type_of env c) with ValCtor (tele, ret) -> (tele, ret) | _ -> error loc "%s is not a value constructor" (qname env c)

let tid_of env loc c = Option.get (type_head env (snd (ctor_type env loc c)))
let marker env loc tid ctors c =
  match List.find_opt (fun (_, c') -> c' = Var c) ctors with
  | Some (m, _) -> m
  | None -> error_with loc (declared_as env tid) "%s is not a constructor of %s" (qname env c) (qname env tid)

(* A Matchable's constructors, each with its phantom marker and its number of non-erased fields (section 38). *)
let shapes env loc ctors =
  List.map (fun (m, c) -> match c with Var c -> (m, c, List.length (List.filter (fun e -> e.mult <> Erased) (fst (ctor_type env loc c)))) | _ -> assert false) ctors

let non_phantom shapes = List.filter_map (fun (m, c, n) -> if m = Many then Some (c, n) else None) shapes

(* A phantom constructor heads no runtime value (section 20 rule 2), so discriminants number the others only. *)
let discriminant shapes c = find_index (fun (c', _) -> c' = c) (non_phantom shapes)

let tagged disc shapes = disc = Enum && List.length (non_phantom shapes) > 1

let wrappers disc shapes =
  let cs = non_phantom shapes in
  if tagged disc shapes || List.exists (fun (_, n) -> n > 1) cs then [] else List.filter_map (fun (c, n) -> if n = 1 then Some c else None) cs

let newtype_of env c =
  List.find_map (fun o -> if not (names_var c o.Env.names) then None else match type_of env o.Env.obj with
    | Matchable (d, true, _, _, cs) when List.mem c (wrappers d (shapes env Reader.nowhere cs)) -> Some o.obj
    | _ -> None) env.opens.opened

let ctor_of env loc c = match (entry env c).state with Const (V.VCtorFn ct) -> ct | _ -> error loc "%s is not a run-position constructor" (qname env c)
let const env v = if env.run_pos then Const v else Dyn
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


type src_entry = { s_loc : loc; s_subterm : bool; s_mult : mult option; s_sg : [ `Ty of raw | `Is of raw ] option; s_name : string; s_place : raw option }

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
      | [ e; i; Atom (_, n) ] when is_special env i Sp.Is -> [ mk (Some (`Is e)) n ]
      | [ Atom (_, n) ] -> [ mk None n ]
      | ty :: names when names <> [] && List.for_all (fun n -> atom n <> None) names ->
          List.map (fun n -> mk (Some (`Ty ty)) (Option.get (atom n))) names
      | _ -> error l "malformed telescope entry %s%s" (tick (Reader.show raw)) (help env (Sp.hints "telescope-entry")))
  | Atom (l, _) -> error l "expected a telescope entry, got %s" (tick (Reader.show raw))

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

let fact_of env loc = function Ty t -> (t, None) | Is t -> (infer env loc t, Some t)

let anon tele = List.map (fun _ -> None) tele
type sink = { owner : string; noun : string; shown : string list; anchors : (Reader.loc * string) list }

let count_check ?sink l expect got =
  let n = List.length expect and m = List.length got in
  if n <> m then match Option.map Lazy.force sink with
    | None -> error l "expected %d values, got %d" n m
    | Some s -> error_with l s.anchors "%s expects %s, got %d%s" s.owner (counted n s.noun) m (expected s.shown)
let ctor_result head mvars = [ { name = None; subterm = false; mult = Erased; sg = Is (App (head, List.rev mvars)); place = None; loc = Reader.nowhere } ]
let field_names fields = List.map (fun f -> name_or_anon (atom_or (loc f) f "a field name")) fields

let field_ats tele fields = if List.length fields = List.length tele then List.map loc fields else List.map (fun _ -> Reader.nowhere) tele

(* [ids]: terms of the binders already in force, innermost first. Binds one fresh entry per item and returns
   their ids in order. [ats] given means this site is where the source writes the binders -- a pattern's
   fields -- so they are the ones shadowing warns at; without it the telescope is being read back and each
   entry keeps the position its declaration carried (Env.bind). *)
let open_tele env ?(word = true) ?names ?ats ?mults ?states ?(ids = []) ?meta tele =
  let nth l i default = match l with Some l -> List.nth l i | None -> default in
  let _, env, _, fresh =
    List.fold_left
      (fun (i, env, ids, fresh) e ->
        let ty, rule = fact_of env Reader.nowhere (map_sg (instantiate ids) e.sg) in
        let x, env = bind env ?meta ~word:(word && meta <> Some true) ~at:(nth ats i e.loc) ~written:(ats <> None) (nth names i e.name) (nth mults i e.mult) (nth states i Dyn) ty ?rule in
        let env = match Option.map (instantiate ids) e.place with
          | Some p when meta <> Some true -> place env x p
          | _ -> env in
        (i + 1, env, Var x :: ids, x :: fresh))
      (0, env, ids, []) tele
  in
  (env, List.rev fresh)

(* Printing a value against its type (section 16's printed final; ASSUMPTIONS 184). The three literal types print
   as the literals they read back from (Literal.spell); a value whose type names a readable Matchable prints as
   its constructor -- read from the tag where there is one, and the sole non-phantom constructor where there is
   no choice -- over its fields, each erased one printing as `_`. Everything else prints `_`, so the walk is total
   and never reaches Value.show's untyped rendering. *)
let prelude_id env name = Env.lookup { env with scope = env.prelude } name

let nullary env name ty = match (type_head env ty, prelude_id env name) with Some t, Some p -> t = p | _ -> false

(* An extern Nat is its integer; the model's is the Peano chain, walked one constructor at a time. A Char and a
   U8 are their Nat (section 38), so neither needs unwrapping. *)
let nat_z env loc v =
  let c = ctor_of env loc (Option.get (prelude_id env "Zero")) in
  let rec go acc v =
    match v with
    | V.VExt (_, V.Int n) -> Z.add acc n
    | v -> ( match V.destruct c v with 0, _ -> acc | _, [ p ] -> go (Z.succ acc) p | _ -> raise Not_found)
  in
  go Z.zero v

(* The byte a Char's code and a String's elements are, by the Lt proof MkU8 carries (section 41). A Nat outside
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

(* What a literal is bound to, minted directly as slc's `intern` mints it (LITERALS.md). A model Nat comes off
   the program's one Peano chain, extended on demand, so numerals and characters share it wherever they stand
   and the extractor, which shares by identity, emits each Nat once per program. *)
let papp env n args = App (Var (Option.get (prelude_id env n)), args)
let pbuild env n args = V.construct (ctor_of env Reader.nowhere (Option.get (prelude_id env n))) args

(* The FFI's ADT for the prelude type [c] constructs, where the FFI holds it and is in use. *)
let ext_adt env c = match (ctor_of env Reader.nowhere (Option.get (prelude_id env c))).V.adt with { ext = Some _; _ } as adt when !V.use_externs -> Some adt | _ -> None

let peano env k =
  let l = Array.length env.ladder in
  if k < l then (env, env.ladder.(k))
  else
    let ladder = Array.append env.ladder (Array.make (k + 1 - l) V.VToken) in
    for i = l to k do ladder.(i) <- (if i = 0 then pbuild env "Zero" [] else pbuild env "Succ" [ ladder.(i - 1) ]) done;
    ({ env with ladder }, ladder.(k))

let nat_value env z = match ext_adt env "Zero" with Some adt -> (env, V.VExt (adt, V.Int z)) | None -> peano env (Z.to_int z)

let str_value env s =
  match ext_adt env "SNil" with
  | Some adt -> (env, V.VExt (adt, V.Slice (s, 0, String.length s)))
  | None ->
      let cons c (env, rest) = let env, n = peano env (Char.code c) in (env, pbuild env "SCons" [ pbuild env "MkChar" [ pbuild env "MkU8" [ n ] ]; rest ]) in
      String.fold_right cons s (env, pbuild env "SNil" [])

(* The bijective base-2 spelling of [z] as a term (Literal.bin, as source). *)
let rec bin_term env z =
  match Ffi_core.half_view ~z:Fun.id ~nat:Fun.id z with HZ -> papp env "BZ" [] | H1 b -> papp env "B1" [ bin_term env b ] | H2 b -> papp env "B2" [ bin_term env b ]

(* The constructor a value prints as (ASSUMPTIONS 184), chosen off the type's opened Matchable and never by
   refuting candidates: the tag where the type is tagged, else the one non-phantom constructor where the type has
   exactly one. `adt.ctors` is already the non-phantom list, indexed by discriminant. *)
let shown_ctor env loc ty v =
  let _, _, cs = find_matchable env loc (Option.get (type_head env ty)) in
  let of_ctor (_, c) = match c with Var c -> (try Some (ctor_of env loc c) with Contradiction _ | Error _ | Not_found -> None) | _ -> None in
  match List.filter_map of_ctor cs with
  | [] -> None
  | first :: _ ->
      let adt = first.V.adt in
      if adt.V.tagged then match V.dispatch adt.V.ext adt.V.tagged v with Some (i, _) -> List.nth_opt adt.V.ctors i | None -> None
      else ( match adt.V.ctors with [ c ] -> Some c | _ -> None)

(* A constructor's fields against an instance of its type, in declaration order with each one's multiplicity, as
   entering a branch computes them: the unification types the children, it no longer decides the constructor. *)
let ctor_fields env loc ct ty =
  let tele, ret = ctor_type env loc ct.V.cid in
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
      | Some ct ->
          let env', specs = ctor_fields env loc ct ty in
          let _, fs = V.destruct ct v in
          (* an erased field has no word, so it takes none from the destructure *)
          let rec args specs fs = match (specs, fs) with
            | [], _ -> []
            | (Erased, _) :: rest, fs -> "_" :: args rest fs
            | (_, t) :: rest, f :: fs -> show_value env' loc t f :: args rest fs
            | _ :: rest, [] -> "_" :: args rest []
          in
          Ffi_core.show_app ct.V.cname (args specs fs)
  with Contradiction _ | Error _ | Not_found | Invalid_argument _ -> "_"


let spread mults values =
  snd (List.fold_left_map (fun vs m -> match (m, vs) with (Many | Unique), v :: rest -> (rest, v) | _ -> (vs, V.VToken)) values mults)
let const_fields env l c mults value =
  let ct = ctor_of env l c in
  let i, vs = V.destruct ct value in
  (i = ct.V.index, List.map (fun v -> Const v) (spread mults vs))

let witness env ?(mult = Erased) ?(value = V.VToken) ty = bind env None mult (const env value) ty

let matchable_code env pos x =
  if pos = Erased then V.CErased else match adt_of env x with Some adt -> V.CConst (V.VMatchable adt) | None -> V.CVar x

let mint_adt ?(newtype = false) env name disc shapes =
  let adt = { V.tname = name; tagged = tagged disc shapes; newtype; ctors = []; ext = None } in
  adt.ctors <- List.mapi (fun index (c, arity) -> { V.cname = entry_name env c; cid = c; index; arity; adt }) (non_phantom shapes);
  adt

(* A match on an ADT the elaborator can see reads no Matchable at runtime (section 17); one on a held Matchable
   reads it as the shape the Matchable's type gives its values. *)
let match_shape env x tid disc shapes = match adt_of env x with Some adt -> V.Known adt | None -> V.Held (V.CVar x, mint_adt ~newtype:(match type_of env x with Matchable (_, n, _, _, _) -> n | _ -> false) env (entry_name env tid) disc shapes)
let cell_shape env l c =
  let tid = tid_of env l c in
  let mid, disc, cs = find_matchable env l tid in
  (match type_of env mid with
   | Matchable (_, true, _, _, _) -> error l "newtype constructors have no cells"
   | Matchable (_, _, true, _, _) when not env.in_extern -> error l "extern constructors have no cells outside an extern model"
   | _ -> ());
  if marker env l tid cs c = Erased then error l "phantom constructors have no cells";
  let params, ret = ctor_type env l c in
  let shapes = shapes env l cs in
  let a = mint_adt env (entry_name env tid) disc shapes in
  let ct = { V.cname = entry_name env c; cid = c; index = Option.value (discriminant shapes c) ~default:0;
    arity = List.length (List.filter (fun e -> e.mult <> Erased) params); adt = a } in
  (ct, params, ret)

let cells_allowed env mid = match type_of env mid with
  | Matchable (_, false, ext, _, _) -> not ext || env.in_extern
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
  field_count env l what noun c params (List.length (List.filter (fun (e : entry) -> e.mult <> Erased) params)) got "one for each non-erased field of"

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
  let slots = List.concat (List.mapi (fun j (e : entry) -> if e.mult = Erased then [] else [ SlotOf (Bound (n - 1 - j)) ]) tele) in
  { name = None; subterm = false; mult = mode; sg = Ty (Cell (Var c, slots)); place; loc = Reader.nowhere }

(* The cell binder after the fields is optional, at `many` as at `unique` (the owner's decision in chat, which
   AT_REDESIGN A8's "mandatory" is to follow). *)
let pattern env what mode (scrut : res) l c mults extra fields =
  let tele, _ = ctor_type env l c in
  let n = List.length tele in
  let has_cell = extra && List.length fields = n + 1 in
  if List.length fields <> n && not has_cell then
    binder_count env l what c mode ~extra fields (List.map2 (fun m (e : entry) -> { e with mult = m }) mults tele @ if extra then [ cell_entry c tele mode scrut.place ] else []);
  if not has_cell then (fields, None) else
  let cell = List.nth fields n in
  (List.filteri (fun i _ -> i < n) fields, Some (name_or_anon (atom_or l cell "a cell binder"), loc cell))

let pattern_cell env l mult scrut c fids name =
  match name with
  | None -> (env, None)
  | Some (name, at) ->
      let _, params, _ = cell_shape env l c in
      let slots = List.filter_map (fun (e,x) -> if e.mult = Erased then None else Some (slot_of x)) (List.combine params fids) in
      let state = match scrut.term with Var x -> (entry env x).state | _ -> Dyn in
      let x, env = bind env ~word:true ~at name mult state (Cell (Var c, slots)) in
      (placed env x scrut.place, Some x)

let bind_cell code cell body = match cell with None -> body | Some x -> V.CLet ([x],code,body)

let warn_use env l what t =
  match canon env t with
  | Var x when not env.in_extern -> (
      let means r = match StringMap.find_opt r.Reader.name env.scope.named with Some y -> canon env (Var y) = Var x | None -> false in
      match IntMap.find_opt x env.warned, List.filter (fun r -> Reader.covers r l && means r) (Option.value ~default:[] (Hashtbl.find_opt Reader.regions l.file)) with
      | Some (pl, msg), [] -> warn_at l [ (pl, Printf.sprintf "`;! warn` for %s is here" (qshow env t)) ] "%s %s: %s" what (qshow env t) msg
      | Some _, rs -> List.iter (fun r -> r.Reader.used <- true) rs
      | None, _ -> ())
  | _ -> ()

let pragma env l = function
  | [ Atom (_, "warn"); Atom (nl, n); Atom (_, msg) ] -> (
      let x = match StringMap.find_opt n env.scope.named with Some x -> x | None -> error nl "`;! warn` names %s, which is not in scope%s" (tick n) (hint env n) in
      match canon env (Var x), canon env (type_of env x) with
      | Var c, (TyCtor _ | ValCtor _) -> (
          match IntMap.find_opt c env.warned with
          | Some (pl, _) -> error_with l [ (pl, "the first is here") ] "second `;! warn` for %s" (tick n)
          | None -> { env with warned = IntMap.add c (l, msg) env.warned })
      | _ -> error nl "`;! warn` names %s, which is neither a type constructor nor a value constructor" (tick n))
  | [ Atom (_, "warn") ] -> error l "`;! warn` needs a name and a message"
  | [ Atom (_, "warn"); _ ] -> error l "`;! warn` needs a message after the name"
  | _ -> error l "`;! warn` needs a name and a message"

let mint_level env ~at name = bind env ~minted_level:true ~at name Erased (const env V.VToken) Prelude.level_term

let rec elab_term ?expect env raw =
  match raw with
  | Atom (l, "_") -> let x, env = bind env ~meta:true ~at:l None Erased Dyn type_term in (env, Var x)
  | Atom (l, n) -> (env, Var (var env l n))
  | List (l, []) -> error l "empty form"
  | List (l, head :: args) -> (
      match special_of env head with
      | Some sp -> elab_type_form env l sp args
      | None -> (
          let h = Var (var env l (atom_or l head "a constructor")) in
          match canon env (infer env l h) with
          | (TyCtor tele | ValCtor (tele, _)) as ty -> let env, acc = elab_term_args env l ~callee:(describe env Erased head h ty) ?expect tele h args in (env, App (h, List.rev acc))
          | ty -> error l "%s has type %s and cannot be applied in a type" (qshow env h) (qshow env ty)))

and elab_type_form env l sp args =
  match (sp, args) with
  | Sp.Cell, c :: slots ->
      let c = ctor_var env l c in
      let ct, params, _ = cell_shape env l c in
      if List.length slots <> ct.V.arity then slot_count env l "the type former `Cell`" "slot" c params (List.length slots);
      let env, slots = List.fold_left_map (fun env s -> let env, s = elab_term env s in check_type env l (infer env l s) Prelude.slot_term; (env, s)) env slots in
      (env, Cell (Var c, slots))
  | (Sp.Fn | Sp.UniqueFn), lv :: rest ->
      let env, lv = elab_term env lv in
      check_type env l (infer env l lv) Prelude.level_term;
      let ps, rs = split_arrow env l rest in
      (env, elab_fn_type ~unique:(sp = Sp.UniqueFn) env lv ps rs)
  | Sp.TyCtor, _ -> let ps, ret = split_arrow env l args in (env, elab_tyctor env l ps ret)
  | Sp.ValCtor, _ -> let _, _, _, t = elab_valctor env l args in (env, t)
  | Sp.Matchable, d :: rest ->
      let ms, rest = marks env [ Sp.NewtypeMark; Sp.Extern ] rest in
      let t, cs = match rest with t :: cs -> (t, cs) | _ -> error l "%s" (help env (Sp.misuse sp)) in
      let ctor = function
        | List (cl, [ m; c ]) -> let m = mult_or env cl m in
            if m = Unique then error_in env cl "a `Matchable` constructor cannot be `unique`";
            (m, Var (ctor_var env cl c))
        | raw -> error (loc raw) "expected a constructor marker" in
      (env, Matchable (disc_of env l d, List.mem Sp.NewtypeMark ms, List.mem Sp.Extern ms, Var (tyname env l t), List.map ctor cs))
  | (Sp.Fn | Sp.UniqueFn | Sp.Matchable), _ -> error l "%s" (help env (Sp.misuse sp))
  | Sp.DumpContext, _ -> dump_context env l Dump.Type args
  | (Sp.LevelOf | Sp.MatchableOf | Sp.DelegateOf | Sp.NumeralOf | Sp.SlotOf | Sp.AtFnOf), _ -> fetched env l sp args
  | _ -> error l "%s cannot appear in a type" (tick (speller env (Sp.name sp)))

(* `(slot-of x)`: the automatic slot of `x`'s binder (AT_REDESIGN A6), a direct variable reference and no use. *)
and slot_var env l = function
  | [ a ] ->
      let x = var env (loc a) (atom_or (loc a) a "a direct variable reference") in
      if (entry env x).mult = Erased then error_in env (loc a) "`slot-of` needs a variable declared `many` or `unique`";
      if env.ctor_tele then error_in env (loc a) "`slot-of` cannot appear in a constructor's telescope";
      x
  | _ -> error l "%s" (help env (Sp.misuse Sp.SlotOf))

and fetched env l sp args =
  match (sp, args) with
  | Sp.SlotOf, _ -> (env, slot_of (slot_var env l args))
  | Sp.AtFnOf, [ g ] -> (
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
  | Sp.MatchableOf, [ t ] -> let x, _, _ = find_matchable env l (tyname env l t) in (env, Var x)
  | Sp.NumeralOf, [ e ] -> (
      let name = atom_or l e "a literal" in
      match Literal.classify name with
      | `Bad msg -> error l "%s" msg
      | `Name -> error_in env l "`numeral-of` takes a literal, not %s" (tick name)
      | `Lit lit -> (
          match List.assoc_opt (Literal.key lit) env.literals with
          | Some (_, Some p) -> (env, Var p)
          | Some (_, None) -> error l "%s is a string literal, which carries no `Numeral` proof" name
          | None -> error l "literal %s is not in scope" name))
  | Sp.DelegateOf, [ g ] -> (
      let g = named env l "a function name" g in
      let about x = (entry env x).name = None && (match type_of env x with App (Var c, [ _; _; Var g'; _; _; _ ]) -> c = Prelude.delegate && g' = g | _ -> false) in
      match List.find_opt about env.scope.ids with Some y -> (env, Var y) | None -> error l "%s has no `Delegate` proof in scope" (qname env g))
  | _ -> error l "%s" (help env (Sp.misuse sp))

(* The form's arguments are terms in section 5's grammar, each shown with its type where it has one. *)
and dump_context : 'a. Env.t -> Reader.loc -> Dump.goal -> Reader.raw list -> 'a = fun env l goal args ->
  let env, focus = List.fold_left_map (fun env raw ->
    let env, t = elab_term env raw in
    (env, (Reader.show raw, t, try Some (infer env l t) with Error _ -> None))) env args in
  Dump.report ~show_value env l goal focus

and elab_fn_type ?(unique = false) env lv ps rs =
  let env, ids, params = elab_tele env ~places:true ~subterm:true ps in
  let _, _, rets = elab_tele env ~places:true ~ids:(List.rev ids) rs in
  if unique then UniqueFn (lv, params, rets) else Fn (lv, params, rets)

and elab_tyctor env l ps ret =
  let env', _, tele = elab_tele { env with ctor_tele = true } ~mults:(fun _ l -> function None -> Some Erased | Some m -> no_mult env "a type constructor's parameters" l m) ps in
  (match ret with [ r ] -> let env', r = elab_term env' r in check_equal env' l r type_term | _ -> error_in env l "`TyCtor` returns `Type`");
  TyCtor tele

and elab_valctor env l items =
  let ps, ret = split_arrow env l items in
  let env', ids, tele = elab_tele { env with ctor_tele = true } ps in
  let env', ret = match ret with [ r ] -> elab_type env' r | _ -> error l "a constructor returns one type" in
  settle env' l ret;
  (match canon env' ret with
  | App (Var t, _) when (not (List.mem t ids)) && (match type_of env' t with TyCtor _ -> true | _ -> false) -> ()
  | _ -> error l "a constructor returns an application of a type constructor in scope, not %s" (qshow env' ret));
  (env', tele, ret, ValCtor (tele, abstract (List.rev ids) ret))

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

(* Elaborates source entries into a closed telescope, binding each name for the entries after it.
   [ids]: binders already in force, innermost first; [mults] maps an entry's index and declared multiplicity to its actual one. *)
and elab_tele env ?(places = false) ?(contextual = false) ?(subterm = false) ?(ids = []) ?(mults = fun _ _ m -> m) ?holes ?written entries =
  let entries = List.concat_map (parse_entry env) entries in
  let _, env, ids, tele =
    List.fold_left
      (fun (i, env, ids, tele) e ->
        if e.s_subterm && not subterm then error_in env e.s_loc "`subterm` is not allowed here";
        let mult = match mults i e.s_loc e.s_mult with Some m -> m | None -> error e.s_loc "entry %s needs a multiplicity" (tick e.s_name) in
        let env, sg = match e.s_sg with Some s -> elab_sg env s | None -> error_in env e.s_loc "entry %s needs a type or an `is` clause" (tick e.s_name) in
        let ty, rule = fact_of env e.s_loc sg in
        let place = Option.map (fun raw ->
          if not places then error_in env e.s_loc "`at` is allowed only on function telescope and match annotation entries";
          if mult = Erased && not contextual then error_in env e.s_loc "`at` needs an entry declared `many` or `unique`";
          let n = atom_or (loc raw) raw "a location variable" in
          if Literal.classify n <> `Name then error_in env (loc raw) "`at` names a variable, not a literal";
          let x = var env (loc raw) n in
          if (entry env x).mult = Erased then error_in env (loc raw) "`at` needs a variable declared `many` or `unique`";
          slot_of x) e.s_place in
        let name = name_or_anon e.s_name in
        let x, env = at e.s_loc (fun () -> bind env ?holes ?written ~at:e.s_loc name mult Dyn ty ?rule) in
        (i + 1, { env with signature = x :: env.signature }, x :: ids, { name; subterm = e.s_subterm; mult; sg = map_sg (abstract ids) sg; place = Option.map (abstract ids) place; loc = e.s_loc } :: tele))
      (0, env, ids, []) entries
  in
  (env, List.rev ids, List.rev tele)

(* Checks [args] against [tele] with [elab env mult arg expect]; returns the argument terms innermost first,
   and their code. A meta stands for each parameter (SUGAR.md 6): an argument written `_` is left to it, and
   is an error unless erased where it stands; any other argument is checked against its parameter and bound
   to its meta. [result] is the application's result telescope over the parameters' metas, unified with
   [expect] eagerly, where a `_` is present, before any argument is read, and again, reporting the mismatch,
   when a `_` would otherwise stay unsolved at the closing paren; every `_` is solved by then or refused. *)
and check_args env loc ~callee:c ?(what = "argument") ?expect ?(result = fun _ -> []) ?(pos = Erased) ?(boundary = true) ?(bind_args = false) tele args elab =
  if List.length tele <> List.length args then count_error env loc c what tele (List.length args);
  let ats = List.map (fun a -> if wild a then Reader.loc a else Reader.nowhere) args in
  let env, metas = open_tele env ~meta:true ~names:(anon tele) ~ats ~mults:(List.map (fun _ -> Erased) tele) tele in
  let mvars = List.rev_map (fun x -> Var x) metas in
  let wilds = List.exists wild args in
  let against ~strict env = match expect with Some tele when wilds -> solve_tele ~strict env loc tele (result mvars) | _ -> env in
  let env = against ~strict:false env in
  let env, acc, codes, bindings =
    List.fold_left2
      (fun (env, acc, codes, bindings) (i, e, m) arg ->
        let sg = map_sg (instantiate acc) e.sg in
        let about = lazy (argument c i e.name ^ ": ", Lazy.force c.notes) in
        if wild arg then (
          if under pos e.mult <> Erased then error_with (Reader.loc arg) (Lazy.force c.notes) "%s`_` stands only for an erased argument, and this one is not erased" (fst (Lazy.force about));
          (env, Var m :: acc, codes, bindings))
        else
          let env, r, code = elab env (c.used e.mult) arg (Some [ { e with sg } ]) in
          let env = solve_sg ~raw:arg ~about env (Reader.loc arg) sg r in
          let env, r, code, bindings =
            if bind_args && pos <> Erased && e.mult <> Erased then (
              match r.term, code with
              | Var _, V.CVar _ -> (env, r, code, bindings)
              | _ ->
                  let x, env = bind env ~holes:true ~word:true ~temporary:true None r.erasure Dyn r.ty ~rule:r.term in
                  (placed env x r.place, { r with term = Var x; place = Some (slot_of x) }, V.CVar x, (x, code) :: bindings))
            else (env, r, code, bindings)
          in
          (* an argument for a parameter written `at` must sit where its target does, and is not passed (A3, A5) *)
          let omitted = match e.place with
            | Some p when pos <> Erased ->
                if not (Option.fold ~none:false ~some:(same_slot env (instantiate acc p)) r.place) then
                  error_with (Reader.loc arg) (Lazy.force c.notes) "%s does not satisfy `at` %s" (argument c i e.name) (qshow env (instantiate acc p));
                true
            | _ -> false in
          (solve ~about "value" env (Reader.loc arg) r.term (Var m), r.term :: acc, (if e.mult <> Erased && not omitted then code :: codes else codes), bindings))
      (env, [], [], []) (List.mapi (fun i (e, m) -> (i, e, m)) (List.combine tele metas)) args
  in
  let env = if boundary && List.exists (has_meta env) acc then against ~strict:true env else env in
  if boundary then List.iteri (fun i t -> if has_meta env t then
    let what = argument c i (List.nth tele i).name and arg = List.nth args i in
    if wild arg then error_with ~hints:(hole_hints env t) (Reader.loc arg) (Lazy.force c.notes) "%s is `_` and cannot be inferred" what
    else unsolved ~about:(what ^ ": ", Lazy.force c.notes) (Reader.loc arg) env t) (List.rev acc);
  (env, List.map (metaless env) acc, List.rev codes, fun body -> List.fold_left (fun body (x, rhs) -> V.CLet ([x], rhs, body)) body bindings)

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

(* A constructor application is a pure term (DESIGN.md section 5), so it is no boundary: its holes may stay
   open past its paren for the arguments after it, or the position, to solve. *)
and elab_term_args env loc ~callee ?what ?expect tele ret args =
  let env, acc, _, _ =
    check_args env loc ~callee ?what ?expect ~result:(ctor_result ret) ~boundary:false tele args (fun env _ a expect ->
        let env, t = elab_term ?expect env a in
        (env, term_res env (Reader.loc a) t, V.CErased))
  in
  (env, acc)

(* [ids] as in [open_tele]. *)
(* Where each of a body's results is written: the entries of a final values form holding one per result, else
   the final expression, which is what a mismatch with the returns points at. *)
let result_sites env loc body n =
  match List.rev body with
  | List (_, v :: entries) :: _ when is_special env v Sp.Values && List.length entries = n -> List.map (fun e -> (Reader.loc e, Some e)) entries
  | final :: _ -> List.init n (fun _ -> (Reader.loc final, if n = 1 then Some final else None))
  | [] -> List.init n (fun _ -> (loc, None))

(* A result that is not a variable is bound to an anonymous one for the entries after it, so that a later
   entry's `at` can name the slot it sits in (U2a). *)
let check_results env loc ?(ids = []) body tele ress =
  count_check loc tele ress;
  let env = List.fold_left2 (fun (env, acc) (e, (rl, raw)) r ->
    let env = solve_sg ?raw env rl (map_sg (instantiate acc) e.sg) r in
    (match Option.map (instantiate acc) e.place with
     | Some p when not env.usage_erased ->
         if not (Option.fold ~none:false ~some:(same_slot env p) r.place) then error_in env rl "return does not satisfy `at` %s" (qshow env p)
     | _ -> ());
    let env, t = match r.term, r.place with
      | Var _, _ | _, None -> (env, r.term)
      | t, Some p -> let y, env = bind env ~holes:true None r.erasure Dyn r.ty ~rule:t in (place env y p, Var y) in
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
  let x, env = bind env None Erased Dyn ty in
  (env, res_of env x)

(* [code] produces the runtime entries of [tele], bound to [ids]; the entries written `at` are read from the
   words the caller holds (A3). [init]: the terms the telescope's earlier binders stand for, innermost first. *)
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

let predates_source env x lvl = match canon env (Var x) with Var y when x >= lvl -> y | _ -> x
let provable_predates env x lvl = (entry env lvl).minted_level && predates_source env x lvl < lvl

let prove_predates env l x lvl =
  if not (entry env lvl).minted_level then error_in env l "%s is not a level minted by `def-lvl`" (qname env lvl);
  let x = predates_source env x lvl in
  if x >= lvl then error l "%s was not in scope when level %s was minted" (qname env x) (qname env lvl);
  mint env (proof_type Prelude.predates [ type_of env x; Var x; Var lvl ])

(* The post-erasure normalizer behind the `tail` and `delegate` checks (section 9, ASSUMPTIONS 164, 189): lets
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

(* Normalized code that erases to nothing, or to a reordering of variables (AT_REDESIGN A9, A10; review item
   32): renames, loads and a match whose every branch erases to nothing, dispatch included; never a store, an
   allocation or a call that was not skipped. *)
let rec erases_to_nothing = function
  | V.CApp _ | V.CCellAlloc _ | V.CCellWrite _ | V.CCellCopy _ -> false
  | V.CLetRec (_, rest) -> erases_to_nothing rest
  | c -> List.for_all erases_to_nothing (V.subcodes c)

let demanded env demand mult ty =
  if mult = Erased then mult else
  match demand with
  | Fixed -> mult
  | CallableHead -> (match canon env ty with Cell _ | UniqueFn _ -> Unique | _ -> Many)
  | Driver -> if nullary env "IO" ty then Unique else Many

let rec elab_expr ?sink ?(demand = Fixed) ?(cc = V.Plain) ?tele ?(final = false) env expect raw : Env.t * res list * V.code =
  let l = loc raw in
  let outer_erased = env.usage_erased in
  let env = { env with usage_erased = outer_erased || pos_of expect = Erased } in
  let env, ress, code = elab_form ?sink ~final demand cc tele env expect raw in
  let ress = List.map (fun r -> { r with term = metaless env r.term; ty = metaless env r.ty }) ress in
  count_check ?sink l expect ress;
  List.iter2 (fun m r ->
    let m = demanded env demand m r.ty in
    if not outer_erased then Option.iter (fun how -> error l "internal: an unchecked result %s" how) (misuse m r.erasure)) expect ress;
  ({ env with usage_erased = outer_erased }, ress, code)

and elab_expr1 ?demand ?cc ?tele env mult raw =
  let env, ress, code = elab_expr ?demand ?cc ?tele env [ mult ] raw in
  (env, List.hd ress, code)

and elab_erased env raw =
  let env, r, _ = elab_expr1 env Erased raw in
  settle_res env (loc raw) r;
  (env, r.term)

and elab_form ?sink ~final demand cc expect_tele env expect raw =
  let pos = pos_of expect in
  match raw with
  | Atom (l, n) ->
      let x = var env l n in
      (use env l ~written:n (demanded env demand pos (type_of env x)) x, [ res_of env x ], if pos <> Erased then V.CVar x else V.CErased)
  | List (l, []) -> error l "empty form"
  | List (l, head :: args) -> (
      match special_of env head with
      | Some sp when Sp.has_role sp -> not_a env "not an expression" raw
      | Some sp -> elab_special ?sink ?final:(if final then Some (loc head) else None) demand expect_tele (read_special pos env head) expect l sp args
      | None -> (
          let env, h, hcode, headwrap = elab_head env pos l head in
          let hty = canon env h.ty in
          let callee pos = describe env pos head h.term hty in
          let env, rs, code = match hty with
          | TyCtor tele ->
              let c = callee pos in
              if pos <> Erased then error_with l (Lazy.force c.notes) "%s applied in a non-erased position" (match head with Atom _ -> "type constructor " ^ Lazy.force c.subject | _ -> Lazy.force c.subject);
              let env, acc = elab_term_args env l ~callee:c ?expect:expect_tele tele h.term args in
              (env, [ { term = App (h.term, List.rev acc); ty = type_term; erasure = Erased; place = None } ], V.CErased)
          | ValCtor (tele, ret) ->
              if pos <> Erased && h.erasure = Erased then error_with l (head_notes env h) "erased constructor %s in a non-erased position" (head_name env h);
              let pos = demanded env demand pos ret in
              if pos <> Erased then warn_use env (loc head) "application of" h.term;
              let env = match h.term with Var x -> use env l (under pos Many) x | _ -> env in
              let env, acc, codes, wrap = check_args env l ~callee:(callee pos) ~bind_args:true ?expect:expect_tele ~result:(ctor_result h.term) ~pos ~boundary:false tele args elab_arg in
              let is_wrapper = newtype_of env (match canon env h.term with Var c -> c | _ -> -1) <> None in
              let code = if pos = Erased then V.CErased else if is_wrapper then List.hd codes else V.CApp (hcode, codes, V.Ctor) in
              let place = if is_wrapper && pos <> Erased then List.find_map (fun (e, a) -> if e.mult <> Erased then Some (SlotOf a) else None) (List.combine tele (List.rev acc)) else None in
              (env, [ { term = App (h.term, List.rev acc); ty = instantiate acc ret; erasure = pos; place } ], wrap code)
          | Cell (c, slots) -> elab_cell_invoke env expect l (callee pos) h hcode c slots args
          | UniqueFn (lv, params, rets) -> elab_call ~unique:true ?sink ~demand cc env ?tele:expect_tele expect l (callee pos) h hcode lv params rets args
          | Fn (lv, params, rets) -> elab_call ?sink ~demand cc env ?tele:expect_tele expect l (callee pos) h hcode lv params rets args
          | ty -> error l "%s : %s is not applicable" (qshow env h.term) (qshow env ty) in
          (env, rs, headwrap code)))

and elab_arg env m a tele = elab_expr1 ?tele env m a

and elab_head env pos l raw =
  match raw with
  | Atom (_,n) -> let x = var env l n in (env,res_of env x,V.CVar x,Fun.id)
  | _ ->
      let demand = if pos = Erased then Fixed else CallableHead in
      let env,r,code = elab_expr1 ~demand env (under pos Many) raw in
      let state = match r.term with Var x -> (entry env x).state | _ -> Dyn in
      let x,env = bind env ~word:true ~temporary:true None r.erasure state r.ty ~rule:r.term in
      (placed env x r.place,res_of env x,V.CVar x,fun body -> V.CLet ([x],code,body))

and elab_call ?(unique = false) ?(assert_at = false) ?sink ?(demand = Fixed) cc env ?tele expect l c callee hcode lv params rets args =
  let pos = pos_of expect in
  (* a call of an at-function is skipped (A10): the proof opened for the callee is what licenses it *)
  let skipped = pos <> Erased && atfn_open env callee.term in
  if assert_at && not skipped then error_with_in env l (head_notes env callee) "%s is not an at-function here: no `AtFn` proof for it is open" (head_name env callee);
  if skipped && cc <> V.Plain then error_in env l "%s marks a call that compiles to one, and a call of at-function %s is skipped" (tick (speller env (match cc with V.Tail -> "tail" | V.NoTail -> "notail" | _ -> "delegate"))) (head_name env callee);
  if pos <> Erased && callee.erasure = Erased then error_with l (head_notes env callee) "erased function %s called in a non-erased position" (head_name env callee);
  if unique && pos <> Erased && callee.erasure = Many then error_with_in env l (head_notes env callee) "a shared `UniqueFn` %s is callable only erased" (head_name env callee);
  let env = match callee.term with Var x -> use env l (under pos (if unique then Unique else Many)) x | _ -> env in
  let written, args =
    let rec go i acc = function
      | List (al, [ k; p ]) :: rest when is_special env k Sp.Predates && i = 0 -> (Some (al, `Predates p), List.rev_append acc rest)
      | List (al, [ k; p ]) :: rest when is_special env k Sp.Subterm -> (Some (al, `Subterm (i, p)), List.rev_append acc rest)
      | a :: rest -> go (i + 1) (a :: acc) rest
      | [] -> (None, List.rev acc)
    in
    go 0 [] args
  in
  let env, acc, codes, wrap = check_args env l ~callee:c ~bind_args:true ?expect:tele ~result:(fun mvars -> instantiate_tele mvars rets) ~pos params args elab_arg in
  let arg_terms = List.rev acc in
  let subterm_params = List.filter_map (fun (i, e) -> if e.subterm then Some i else None) (List.mapi (fun i e -> (i, e)) params) in
  let arg_name i = argument c i (Option.bind (List.nth_opt params i) (fun e -> e.name)) in
  let counterpart al k = match List.nth_opt env.subterms k, env.enclosing with
    | Some x, _ -> x
    | None, g ->
        let i = List.nth subterm_params k in
        let g, notes = match g with Some g -> (Printf.sprintf " %s %s" (kind_name env (type_of env g)) (qname env g), declared_as env g) | None -> ("", []) in
        error_with_in env al (Lazy.force c.notes @ notes) "%s is its `subterm` parameter %d, but the enclosing%s has %s" (arg_name i) (k + 1) g (if k = 0 then "none" else Printf.sprintf "only %d" k) in
  let proof env prove = function Atom (_, "_") -> let env, p = prove env in (env, p.term) | p -> elab_erased env p in
  let same cur = equal (canon env lv) (canon env (Var cur)) in
  let inferred () =
    let wild = Atom (l, "_") in
    let differs j pi = match List.nth_opt env.subterms j with Some x -> not (equal (canon env (List.nth arg_terms pi)) (canon env (Var x))) | None -> false in
    match env.level with
    | At cur when same cur -> (
        match List.find_opt (fun (j, pi) -> differs j pi) (List.mapi (fun j pi -> (j, pi)) subterm_params) with
        | Some (_, i) -> Some (`Subterm (i, wild))
        | None -> error l "same-level call to %s decreases no subterm argument" (qshow env callee.term))
    | At _ -> Some (`Predates wild)
    | Top -> None
  in
  let check al annotation =
    match (env.level, annotation) with
    | Top, None -> env
    | Top, Some _ -> error l "the top level calls without proofs; drop the decrease annotation (section 24)"
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
  let env, ids = open_tele env ~word:false ~names:(anon rets) ~ats:(List.map (fun _ -> l) rets) ~mults:(List.map (fun e -> under pos e.mult) rets) ~ids:acc rets in
  count_check ?sink l expect ids;
  let callee_name () = match callee.term with Var x -> qname env x | _ -> "this call" in
  List.iter2 (fun (m, (e : entry)) x ->
    let name = match e.name with Some n -> tick n ^ " " | None -> "" in
    let notes = if Reader.placed e.loc && e.name <> None then [ (e.loc, Printf.sprintf "%sis declared here" name) ] else [] in
    check_mult env l (fun () -> (notes, Printf.sprintf "the return %sof %s, declared `%s`" name (callee_name ()) (speller env (mult_name e.mult)))) (demanded env demand m (type_of env x)) (entry env x).mult)
    (List.combine expect rets) ids;
  let code =
    if pos = Erased then V.CErased else
    let cc = match env.level with At cur when cc = V.Plain && same cur -> V.Same (l, callee.term) | _ -> cc in
    reconstruct ~always:true ~init:acc ~expect:(List.map2 (fun m (e : entry) -> under m e.mult) expect rets) env l rets ids (if skipped then V.CValues [] else V.CApp (hcode, codes, cc))
  in
  (env, List.map (res_of env) ids, wrap code)

and elab_special ?sink ?final demand tele env expect l sp args =
  let pos = pos_of expect in
  let m =
    if List.mem sp (Sp.CellMatch :: Sp.Values :: Sp.Match :: Sp.OpenAbsurd :: Sp.Tail :: Sp.NoTail :: Sp.Delegate :: Sp.At :: Sp.statements) then pos
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
          let a, env = bind env ~meta:true None Erased Dyn type_term in
          let x, env = bind env ~meta:true None Erased Dyn (Var a) in
          let b, env = bind env ~meta:true None Erased Dyn type_term in
          let y, env = bind env ~meta:true None Erased Dyn (Var b) in
          (env, Some [ { name = None; subterm = false; mult = Erased; place = None; loc = Reader.nowhere;
            sg = Ty (proof_type ctor [sa; Var a; Var x; sb; Var b; Var y]) } ]) in
    let env, p, _ = elab_expr1 ?tele env Erased raw in
    settle_res env l p;
    (env, expect_proof env l ctor p.term) in
  let form () = tick (Reader.show (List (l, Atom (l, speller env (Sp.name sp)) :: args))) in
  let produced env notes what ty supply = check_mult env l (fun () -> (notes, form () ^ ", " ^ what)) (demanded env demand m ty) supply in
  let erased (env, r) =
    produced env [] (if sp = Sp.LevelOf then "a `Level` and so erased" else "a proof and so erased") r.ty Erased;
    (env, [ r ], V.CErased) in
  let mint env ty =
    let env = match expected_type env with Some want -> solve "type" env l ty want | None -> env in
    erased (mint env (metaless env ty)) in
  let side env raw =
    if wild raw then let x, env = bind env ~meta:true ~at:(Reader.loc raw) None Erased Dyn Prelude.sharing_term in (env, Var x)
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
      let x = slot_var env l args in
      (env, [ { term = slot_of x; ty = Prelude.slot_term; erasure = pos; place = if pos = Erased then None else Some (slot_of x) } ], if pos = Erased then V.CErased else V.CVar x)
  | Sp.CellAlloc, [ raw ] ->
      let c, items = match raw with List (_, c :: ss) -> (c, Some ss) | Atom _ -> (raw, None) | _ -> error l "%s" (help env (Sp.misuse Sp.CellAlloc)) in
      let c = ctor_var env l c in
      let ct, params, _ = cell_shape env l c in
      let env, slots, writes, wrap = cell_items env pos l ("`cell-alloc`", loc raw, c, params) (List.init ct.V.arity (fun _ -> Var Prelude.null))
        (Option.value items ~default:(List.init ct.arity (fun _ -> Atom (l,"_")))) in
      let values = List.init ct.arity (fun i -> Option.value (List.assoc_opt i writes) ~default:(V.CConst V.VToken)) in
      let x, env = bind env None (under pos Unique) Dyn (Cell (Var c, slots)) in
      produced env [] "a fresh cell and so unique" (type_of env x) (entry env x).mult;
      (env, [ { (res_of env x) with place = None } ], if pos = Erased then V.CErased else wrap (V.CCellAlloc (ct, values)))
  | Sp.CellWrite, [ u; List (il, c :: items) ] ->
      (* a write into a cell at `many` copies: the result is a fresh cell, at unique and at nothing (A8) *)
      let shared = match u with Atom (al, n) -> (entry env (var env al n)).mult = Many | _ -> false in
      let env, r, input = elab_expr1 env (under pos (if shared then Many else Unique)) u in
      let input_id = fresh () in
      let code = V.CVar input_id in
      let c = ctor_var env l c in
      let existing, slots = match canon env r.ty with Cell (Var c, ss) -> c, ss | _ -> error_in env l "`cell-write` needs a `Cell`" in
      check_equal env l (Var c) (Var existing);
      let ct, params, _ = cell_shape env l c in
      let env, slots, writes, wrap = cell_items env pos l ("`cell-write`", il, c, params) slots items in
      let x, env = bind env None (under pos Unique) Dyn (Cell (Var c, slots)) in
      produced env [] "a cell and so unique" (type_of env x) (entry env x).mult;
      let place = if shared then None else r.place in
      (placed env x place, [ { (res_of env x) with place } ], if pos = Erased then V.CErased else V.CLet ([input_id], input, wrap ((if shared then V.CCellCopy (ct, code, writes) else V.CCellWrite (ct, code, writes)))))
  | Sp.CellMatch, _ -> elab_cell_match ~demand tele env expect l args
  | Sp.At, [ List (_, head :: args) ] ->
      let env, h, hcode, wrap = elab_head env pos l head in
      let hty = canon env h.ty in
      let env,rs,code = match hty with
       | Cell (c, slots) -> elab_cell_invoke ~full:true env expect l (describe env pos head h.term hty) h hcode c slots args
       | UniqueFn (lv, params, rets) -> elab_call ~unique:true ~assert_at:true ?sink ~demand V.Plain env ?tele expect l (describe env pos head h.term hty) h hcode lv params rets args
       | Fn (lv, params, rets) -> elab_call ~assert_at:true ?sink ~demand V.Plain env ?tele expect l (describe env pos head h.term hty) h hcode lv params rets args
       | _ -> error_in env l "`at` wraps a `Cell` invocation or a call, and %s : %s is neither" (qshow env h.term) (qshow env h.ty) in
      (env,rs,wrap code)
  | Sp.Share, [ a ] ->
      if pos = Erased then error_in env l "`share` in an erased position";
      let env, r, code = match a with
        | Atom (al, n) ->
            let x = var env al n in
            if (entry env x).mult <> Unique then error_in env al "`share` needs a unique value";
            (use env al ~sharing:true Many x, res_of env x, V.CVar x)
        | _ -> elab_expr1 env Unique a
      in
      produced env [] "shared and so many" r.ty Many;
      (env, [ { r with erasure = Many } ], code)
  | Sp.Values, _ ->
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
      let env, ids = open_tele env ~word:false ~names:(anon ann_tele) ann_tele in
      (env, List.map (res_of env) ids, if pos = Erased then V.CErased else V.CAbsurd)
  | (Sp.NumeralOf | Sp.DelegateOf | Sp.AtFnOf), _ -> (match fetched env l sp args with env, Var y -> erased (env, res_of env y) | _ -> assert false)
  | Sp.Distinct, [ a; b ] -> elab_distinct env l a b
  | Sp.LevelOf, _ -> let env, lv = fetched env l sp args in erased (env, { term = lv; ty = Prelude.level_term; erasure = Erased; place = None })
  | Sp.ProveSubterm, [ a; b ] ->
      let env, a = elab_term env a in
      let env, b = elab_term env b in
      settle env l a; settle env l b;
      erased (prove_subterm env l a b)
  | Sp.ProvePredates, [ x; lv ] -> let env, lv = level_var env l lv in erased (prove_predates env l (var env l (atom_or l x "a variable")) lv)
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
          let x, env = bind env None dst Dyn b_ty ~rule:b in
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
      let middle, env = bind env ~meta:true None Erased Dyn Prelude.sharing_term in
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
  | sp, _ when List.mem sp Sp.statements -> error l "%s is a statement, not an expression%s" (brief (List (l, Atom (l, speller env (Sp.name sp)) :: args))) (help env (Sp.hints (Sp.name sp)))
  | sp, _ -> error l "%s" (help env (Sp.misuse sp))

and cell_items env pos l (what, il, c, params) slots items =
  if List.length slots <> List.length items then slot_count env il what "slot item" c params (List.length items);
  let env, slots, writes, bindings = List.fold_left2 (fun (env, ss, ws, bs) (i, old) item ->
    if wild item then (env, old :: ss, ws, bs) else
    let env, r, code = elab_expr1 env (under pos Many) item in
    (try ignore (unify env r.ty Prelude.slot_term) with Contradiction _ -> error l "expected a `(Slot)` or `_`, got %s" (qshow env r.ty));
    settle_res env l r;
    let x = fresh () in
    (env, r.term :: ss, (i, V.CVar x) :: ws, (x, code) :: bs)) (env, [], [], []) (List.mapi (fun i s -> i,s) slots) items in
  (env, List.rev slots, List.rev writes, fun body -> List.fold_left (fun b (x,c) -> V.CLet ([x], c, b)) body bindings)

and elab_cell_invoke ?(full = false) env expect l callee h hcode ctor slots args =
  let pos = pos_of expect in
  let c = match canon env ctor with Var c -> c | _ -> error_in env l "`Cell` constructor is not a variable" in
  let ct, params, ret = cell_shape env l c in
  (* a cell at `many` is read, not consumed; it mints its value only at `many`, and an invocation that is not
     full-at copies it (A8) *)
  let shared = h.erasure = Many in
  let env = match h.term with Var x -> use env l (under pos (if shared then Many else Unique)) x | _ -> env in
  if pos <> Erased && h.erasure = Erased then error_in env l "`Cell` invocation needs a cell declared `many` or `unique`";
  if pos = Unique && shared then error_in env l "a cell at `many` mints its value only at `many`";
  let rec marks mark args = match args with
    | List (_, [a]) :: rest when is_special env a Sp.At -> marks true rest
    | a :: rest -> (mark, a) :: marks false rest
    | [] -> if mark then error_in env l "`at` must precede an argument" else [] in
  let marked = marks false args in
  let raw = List.map snd marked in
  let env, acc, codes, wrap = check_args env l ~callee ~bind_args:true ~result:(ctor_result (Var c)) ~pos ~boundary:false params raw elab_arg in
  let _, writes = List.fold_left2 (fun (i, writes) ((e : entry), t) (skip, _) ->
    if e.mult = Erased then (if skip then error_in env l "`at` cannot mark an erased argument"; (i, writes)) else
    let same = same_slot env (List.nth slots i) (SlotOf t) in
    if (full || skip) && not same then error_in env l "`at` argument %d is not in its slot's location class" (i+1);
    (i+1, if full || skip then writes else (i, List.nth codes i) :: writes)) (0, []) (List.combine params (List.rev acc)) marked in
  let copies = shared && not full in
  let code = if pos = Erased then V.CErased else if copies then V.CCellCopy (ct, hcode, List.rev writes) else if writes = [] then hcode else V.CCellWrite (ct, hcode, List.rev writes) in
  (env, [{term = App (Var c, List.rev acc); ty = instantiate acc ret; erasure = pos; place = if copies then None else h.place}], wrap code)

and elab_cell_match ?(demand = Fixed) tele env expect l args =
  match args with
  | m :: u :: ann :: List (pl, c :: names) :: body ->
      if pos_of expect = Erased then error_in env l "`cell-match` in an erased position";
      let mode = mult_or env l m in
      if mode = Erased then error_in env l "`cell-match` takes its cell at `many` or `unique`";
      let env, r, code = elab_expr1 env mode u in
      let c = ctor_var env pl c in
      let c', slots = match canon env r.ty with Cell (Var c, ss) -> c, ss | _ -> error_in env l "`cell-match` needs a `Cell`" in
      check_equal env l (Var c) (Var c');
      let ct, _, _ = cell_shape env l c in
      let needed = ct.V.arity + if mode = Unique then 1 else 0 in
      if List.length names <> needed then
        binder_count env pl "`cell-match`" c mode names (List.map is_entry slots @ if mode = Unique then [ is_entry ~mult:Unique ?place:r.place r.term ] else []);
      let env, ann_tele, _ = result_tele ~demand tele env expect l ann in
      let expect = match demand with Fixed -> expect | _ -> List.map (fun e -> e.mult) ann_tele in
      let sid, env = bind env ~word:true ~temporary:true None mode Dyn r.ty ~rule:r.term in
      let env = placed env sid r.place in
      let envb, ids = List.fold_left_map (fun env n -> let x, env = bind env ~word:true ~at:(loc n) (name_or_anon (atom_or pl n "a slot binder")) Many Dyn Prelude.slot_term in (env,x)) { env with run_pos = false } (List.filteri (fun i _ -> i < ct.arity) names) in
      let envb = merge_opens (unify_force (forcing envb) (Cell (Var c,List.map (fun x -> Var x) ids)) (Cell (Var c,slots))) in
      let envb, back = if mode <> Unique then (envb, None) else
        let x, envb = bind envb ~word:true ~at:(loc (List.nth names ct.arity)) (name_or_anon (atom_or pl (List.nth names ct.arity) "a cell binder")) Unique Dyn r.ty ~rule:r.term in
        (place envb x (slot_of sid), Some x) in
      let envb, rs, bcode = elab_body ~tele:ann_tele ~sink:(annotated env "cell-match" ann ann_tele expect) envb expect l body in
      check_results envb l body ann_tele rs;
      let body = match back with None -> bcode | Some x -> V.CLet ([x], V.CVar sid, bcode) in
      let body = List.fold_right (fun (i,x) b -> V.CLet ([x], V.CCellRead (ct, i, V.CVar sid), b)) (List.mapi (fun i x -> i,x) ids) (project_code (keeps ann_tele) body) in
      let env = {env with uses = envb.uses} in
      let env, result_ids = open_tele env ~word:false ~names:(anon ann_tele) ann_tele in
      (env, List.map (res_of env) result_ids, V.CLet ([sid], code, reconstruct env l ann_tele result_ids body))
  | _ -> error l "%s" (help env (Sp.misuse Sp.CellMatch))

and scrutinee ?res env l smult scrut =
  let env, sres, scode = match res with Some (r, c) -> (env, r, c) | None -> elab_expr1 env smult scrut in
  settle_res env l sres;
  let tid = match type_head env sres.ty with Some t -> t | None -> error l "cannot match on %s : %s" (qshow env sres.term) (qshow env sres.ty) in
  let mid, disc, ctors = find_matchable env l tid in
  let env = if smult = Erased then env else (held_needs_many env l tid mid; use env l Many mid) in
  if smult <> Erased then warn_use env l "match on" (Var tid);
  if smult = Erased then (env,sres,scode,Fun.id,tid,mid,disc,ctors) else
  let x, env = bind env ~word:true ~temporary:true None smult Dyn sres.ty ~rule:sres.term in
  (placed env x sres.place,res_of env x,V.CVar x,(fun body -> V.CLet ([x],scode,body)),tid,mid,disc,ctors)

and elab_match ?(demand = Fixed) ?(refute = false) ?(form = "match") ?res ?cells ?(skip = []) ?sink ?final tele env expect l args =
  match args with
  | m :: scrut :: ann :: branches ->
      let pos = pos_of expect in
      let smult = if res <> None then Erased else written env pos l "match" (mult_or env l m) in
      let env, sres, scode, swrap, tid, mid, disc, ctors = scrutinee ?res env l smult scrut in
      let extra = match cells with Some c -> c | None -> smult <> Erased && cells_allowed env mid in
      let branch_uses = ref env.uses and deep = ref [] in
      let deepen envb body flat = if deep_body envb body then deep := flat :: !deep in
      let shapes = shapes env l ctors in
      let tagged = tagged disc shapes in
      if pos <> Erased && smult <> Erased then held_needs_many env l tid mid;
      let env, ann_tele, atmatch = if refute then (env, [], false) else result_tele ~demand tele env expect l ann in
      let expect = match demand with Fixed -> expect | _ -> List.map (fun e -> e.mult) ann_tele in
      (* an at-match skips its runtime (A9): each branch must erase to nothing, dispatch and loads included *)
      let erasable bl code = let code = project_code (keeps ann_tele) code in
        if atmatch && pos <> Erased && not (erases_to_nothing (normalize code)) then error_in env bl "a branch of an at-match must erase to nothing, or to a reordering of variables; this one stores, allocates or calls";
        code in
      let sink expect = match sink with Some s -> s | None -> annotated env form ann ann_tele expect in
      let mults_of bl c = let phantom = marker env bl tid ctors c = Erased in List.map (fun e -> if phantom then Erased else field_under smult e.mult) (fst (ctor_type env bl c)) in
      let enter bl c names ats =
        let phantom = marker env bl tid ctors c = Erased in
        let tele, ret = ctor_type env bl c in
        let mults = mults_of bl c in
        let envb, fids = open_tele { env with run_pos = false } ~names:(names tele) ~ats:(ats tele) ~mults tele in
        (phantom, fids, envb, try Some (at bl (fun () -> refine envb sres c fids ret)) with Contradiction _ -> None)
      in
      let branch raw =
        let kind, pat, body =
          match raw with
          | List (_, [ a; (Atom _ as c) ]) when is_special env a Sp.Absurd -> (`Auto, c, [])
          | List (_, a :: pat :: body) when is_special env a Sp.Absurd -> (`Proof, pat, body)
          | List (_, pat :: body) -> (`Present, pat, body)
          | _ -> error (loc raw) "malformed branch%s" (help env (Sp.hints "branch"))
        in
        let bl = loc pat in
        let c, fs = match pat with Atom _ -> (pat, []) | List (_, c :: fs) -> (c, fs) | _ -> error bl "malformed pattern%s" (help env (Sp.hints "branch")) in
        let c = ctor_var env bl c in
        let extra = extra && marker env bl tid ctors c <> Erased in
        let fs, name = if kind = `Auto then (fs, if extra then Some (None, Reader.nowhere) else None) else pattern env ("a `" ^ form ^ "` branch") smult sres bl c (mults_of bl c) extra fs in
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
          | _, None -> error_in env bl "branch %s is refuted; write `(absurd %s)`" (qname env c) (name_of env c)
          | `Present, Some _ when refute -> error_in env bl "a branch of a refuting match is written `absurd`"
          | `Present, Some envb ->
              deepen envb body (if unreachable then None else Some c);
              let envb = { envb with usage_erased = envb.usage_erased || unreachable } in
              let expect = if unreachable then List.map (fun _ -> Erased) expect else expect in
              let envb, ress, code = elab_body ~tele:ann_tele ~sink:(sink expect) envb expect bl body in
              check_results envb bl body ann_tele ress;
              if not unreachable then branch_uses := join_uses !branch_uses envb.uses;
              `Present (bind_cell scode cell (if unreachable then code else erasable bl code))
          | `Proof, Some envb -> deepen envb body None; ignore (elab_refute envb bl body); `Absurd
        in
        (c, non_erased envb fids, unreachable, result, forced)
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
            let envb = { env with run_pos = false; usage_erased = env.usage_erased || reachable = [] } in
            let envb, cell, body = match body with
              | Atom (nl, n) :: (_ :: _ as body) when extra ->
                  let x, envb = bind envb ~word:true ~at:nl (name_or_anon n) smult Dyn sres.ty ~rule:sres.term in
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
      if pos <> Erased && ((not tagged) || smult = Erased) && List.length real + List.length (Option.to_list else_) > 1 then
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
      let env, result_ids = open_tele env ~word:false ~names:(anon ann_tele) ann_tele in
      (env, List.map (res_of env) result_ids, swrap (if pos = Erased then code else reconstruct env l ann_tele result_ids code))
  | _ -> error l "%s" (help env (Sp.misuse Sp.Match))

(* A match's or open-absurd's return annotation: a telescope of the position's size, or _ for the enclosing one. *)
and result_tele ?(demand = Fixed) tele env expect l ann =
  let atmatch, ann = match ann with List (_, [ a; (List _ as inner) ]) when is_special env a Sp.At -> (true, inner) | _ -> (false, ann) in
  let env, ann_tele =
    match (ann, tele) with
    | Atom (_, "_"), Some tele ->
        if List.exists (fun e -> has_meta env (sg_term e.sg)) tele then error l "the telescope `_` would reuse still has a `_` to infer";
        (env, tele)
    | Atom (_, "_"), None -> error l "no telescope to reuse for `_`"
    | List (_, ann), _ ->
        List.iter (function Atom (al, _) as a -> error al "expected a telescope or `_`, got %s" (tick (Reader.show a)) | _ -> ()) ann;
        let mults i el = function
          | Some m -> no_mult env "a match annotation's entries" el m
          | None -> (match List.nth_opt expect i with Some m -> Some m | None -> error l "match annotation has more than the %d entries the position needs" (List.length expect))
        in
        let env', _, ann_tele = elab_tele env ~places:true ~contextual:true ~mults ~holes:true ann in
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

(* An anonymous let at [mult] of a Matchable: the entry an open records (section 19). *)
and open_binding env l mult raw =
  let inner, r, code = elab_expr1 env mult raw in
  settle_res inner l r;
  (match canon inner r.ty with Matchable _ -> () | ty -> error_in env l "%s : %s is not a `Matchable`" (qshow inner r.term) (qshow inner ty));
  let value = if env.run_pos && mult <> Erased then List.hd (run_code inner code) else V.VToken in
  let state = if env.run_pos then Const value else match r.term with Var y -> (entry inner y).state | _ -> Dyn in
  let x, env' = bind inner ~at:l None mult state r.ty ~rule:r.term in
  (env', x, r.term, code)

and elab_body ?tele ?sink env expect l items =
  report_shadows ~env ();
  match items with
  | List (ll, h :: m :: scrut :: pat :: branches) :: (_ :: _ as rest) when is_special env h Sp.LetMatch && List.exists (real_branch env) branches ->
      elab_match ?sink ~form:"let-match" tele (read_special (pos_of expect) env h) expect ll (m :: scrut :: Atom (ll, "_") :: List (loc pat, pat :: rest) :: branches)
  | stmt :: (_ :: _ as rest) ->
      let env, wrap = elab_stmt (pos_of expect) env stmt in
      let env, ress, code = elab_body ?tele ?sink env expect l rest in
      (env, ress, wrap code)
  | items ->
      let env, _, final = elab_stmts (pos_of expect) env l items in
      elab_expr ?tele ?sink ~final:true env expect final

and deep_body env = function
  | [ List (_, h :: _) ] -> is_special env h Sp.Match || is_special env h Sp.CellMatch
  | [] | [ _ ] -> false
  | _ -> true

and real_branch env = function List (_, a :: _) -> not (is_special env a Sp.Absurd) | _ -> true

(* The statements before a body's final expression, and the code they wrap around what follows them. *)
and elab_stmts ?within spos env l = function
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
      let env, _, _ = elab_match ~refute:true ~res:(r, code) None env [ Erased ] l [ final; final; Atom (l, "_") ] in
      env

and open_contradicts env l e =
  let env', x, t, _ = open_binding env l Erased e in
  match open_adt env' x with
  | _ -> error_in env l "`open-absurd`: opening %s contradicts nothing" (qshow env' t)
  | exception Contradiction _ -> ()

and refine env scrut c fids ret =
  let env = match scrut.place, newtype_of env c, non_erased env fids with
    | Some p, Some _, [ x ] -> place env x p
    | _ -> env in
  let fvars = List.rev_map (fun x -> Var x) fids in
  merge_opens (unify_force (unify_force (forcing env) scrut.term (App (Var c, List.rev fvars))) scrut.ty (instantiate fvars ret))

and elab_stmt ?within spos env raw : Env.t * (V.code -> V.code) =
  let env, wrap = elab_stmt_unsettled ?within spos env raw in
  report_shadows ~env ();
  (env, wrap)

and elab_stmt_unsettled ?(within = "item of a body") spos env raw =
  match raw with
  | List (l, head :: args) -> (
      let env = if special_of env head <> None then read_special spos env head else env in
      match (special_of env head, args) with
      | Some Sp.Let, _ -> elab_let spos env l args
      | Some Sp.DefLvl, [ n ] ->
          let _, env = mint_level env ~at:(loc n) (name_or_anon (atom_or l n "a name")) in
          (env, Fun.id)
      | Some Sp.DefFns, _ -> elab_def_fns env l args
      | Some Sp.DefUnique, _ -> elab_def_fns ~unique:true env l args
      | Some Sp.DefAdts, _ -> elab_def_adts env args
      | Some Sp.ComptimeMatch, _ -> elab_comptime_match env l args
      | Some Sp.LetMatch, _ -> elab_let_match spos env l args
      | Some Sp.Unary, _ -> elab_unary spos env l args
      | Some Sp.DumpContext, _ -> dump_context env l Dump.Statement args
      | Some Sp.SlotSelf, [ a ] ->
          let x = var env (loc a) (atom_or (loc a) a "a variable") in
          if (entry env x).mult = Erased then error_in env (loc a) "`slot-self` needs a variable declared `many` or `unique`";
          check_type env (loc a) (type_of env x) Prelude.slot_term;
          ((try place env x (Var x) with Contradiction msg -> error_in env l "`slot-self`: %s contradicts the facts in force (%s)" (qname env x) (Lazy.force msg)), Fun.id)
      | Some Sp.OpenAtFn, [ e ] ->
          let env', p, _ = elab_expr1 env Erased e in
          settle_res env' l p;
          (match canon env' p.ty with
           | App (Var c, [ _; _ ]) when c = Prelude.atfn -> ()
           | ty -> error_in env l "%s : %s is not an `AtFn` proof" (qshow env' p.term) (qshow env' ty));
          let x, env' = bind env' ~at:l None Erased Dyn p.ty ~rule:p.term in
          (merge_opens (forcing (opens_add env' x)), Fun.id)
      | Some Sp.OpenAdt, [ m; e ] ->
          let mult = mult_or env l m in
          let env', x, t, code = open_binding env l mult e in
          let env' = try open_adt env' x with Contradiction msg -> error_in env l "`open-adt`: %s contradicts what is open (%s)" (qshow env' t) (Lazy.force msg) in
          (env', if env.run_pos || mult = Erased then Fun.id else fun rest -> V.CLet ([ x ], code, rest))
      | Some sp, _ when List.mem sp Sp.statements -> error l "%s" (help env (Sp.misuse sp))
      | _ -> not_a_statement within env raw)
  | _ -> not_a_statement within env raw

and not_a_statement within env raw =
  not_a env (if misplaced env raw = [] then Printf.sprintf "not a statement\nhint: every %s but the last must be a statement" (respell env within) else "not a statement") raw

and run_code env code = Eval.eval env.values code

(* Binders that all carry a type or an is clause are the telescope the right-hand side is expected to
   produce (SUGAR.md 6); the check of each binder against its value stays as it was. The right-hand side's
   statements are statements of the enclosing expression: their code wraps the let's own, and their entries
   stay in scope after it, anonymously (section 16). *)
and elab_let spos env l args =
  let bl, binder_raws, rhs =
    match args with
    | List (bl, bs) :: rhs when List.for_all (function List _ -> true | _ -> false) bs -> (bl, bs, rhs)
    | _ -> error l "%s" (help env (Sp.misuse Sp.Let))
  in
  let binders = List.concat_map (parse_entry env) binder_raws in
  let expect = List.map (fun b -> match b.s_mult with Some m -> m | None -> error_in env b.s_loc "`let` binder needs a multiplicity") binders in
  let env, tele =
    if binders <> [] && List.for_all (fun b -> b.s_sg <> None) binders then
      let env', _, t = elab_tele env ~holes:true ~written:false binder_raws in
      ({ env' with scope = env.scope }, Some t)
    else (env, None)
  in
  let after, wrap, final = elab_stmts ~within:"item of a `let`'s right-hand side" spos env l rhs in
  let sink = lazy { owner = respell env "the enclosing `let`"; noun = "value"; shown = List.map Reader.show binder_raws; anchors = [ (bl, respell env "the binders of the enclosing `let` are here") ] } in
  let inner, ress, code = elab_expr ?tele ~sink after expect final in
  let values = if env.run_pos && pos_of expect <> Erased then run_code inner code else [] in
  let raw i = snd (List.nth (result_sites env l [ final ] (List.length binders)) i) in
  let bind_one (env, ids, acc) (i, ((b, r), v)) =
    let env =
      match (tele, b.s_sg) with
      | Some t, _ -> solve_sg ?raw:(raw i) env b.s_loc (map_sg (instantiate acc) (List.nth t i).sg) r
      | None, Some s -> let env, sg = elab_sg env s in solve_sg ?raw:(raw i) env b.s_loc sg r
      | None, None -> env
    in
    settle_res env b.s_loc r;
    let state = if env.run_pos then Const v else match r.term with Var y -> (entry env y).state | _ -> Dyn in
    if b.s_place <> None then error_in env b.s_loc "`at` is allowed only on function telescope and match annotation entries";
    let x, env = bind env ~word:true ~at:b.s_loc (name_or_anon b.s_name) (Option.get b.s_mult) state r.ty ~rule:r.term in
    (placed env x r.place, x :: ids, r.term :: acc)
  in
  let env', ids, _ =
    List.fold_left bind_one (hide inner env, [], []) (List.mapi (fun i x -> (i, x)) (List.combine (List.combine binders ress) (spread expect values)))
  in
  let ids = non_erased env' (List.rev ids) in
  (env', if env.run_pos then Fun.id else fun rest -> wrap (if pos_of expect = Erased then rest else V.CLet (ids, code, rest)))

(* A match on a one-constructor type chooses nothing, so what it learns holds wherever the scrutinee does
   and its fields bind outward (section 16's reason for comptime-match, without a discriminant to verify). *)
(* Interns a literal once per program, its entries minted outside the scope (LITERALS.md): a numeral is a Const
   Nat beside an erased token typed by its spelling; a character is its code's Nat under the rule
   `is (MkChar (MkU8 n p))`, `p` a token of its bound, its proof its code's; a string is opaque. *)
and hoist env lit =
  let key = Literal.key lit in
  if List.mem_assoc key env.literals then env
  else
    let token env ty = bind env None Erased (Const V.VToken) ty in
    let frame, entry =
      match lit with
      | Literal.Numeral z ->
          let env, v = nat_value env z in
          let x, env = bind env None Many (Const v) (papp env "Nat" []) in
          let p, env = token env (papp env "Numeral" [ bin_term env z; Var x ]) in
          (env, (x, Some p))
      | Literal.Char c ->
          let env = hoist env (Literal.Numeral (Z.of_int c)) in
          let n, np = List.assoc (Z.to_string (Z.of_int c)) env.literals in
          let env, v = nat_value env (Z.of_int c) in
          let p, env = token env (papp env "Lt" [ Var n; Var (Option.get (prelude_id env "u8-modulus")) ]) in
          let x, env = bind env None Many (Const (pbuild env "MkChar" [ pbuild env "MkU8" [ v ] ])) (papp env "Char" []) ~rule:(papp env "MkChar" [ papp env "MkU8" [ Var n; Var p ] ]) in
          (env, (x, np))
      | Literal.Str s ->
          let env, v = str_value env s in
          let x, env = bind env None Many (Const v) (papp env "String" []) in
          (env, (x, None))
    in
    { frame with scope = env.scope; literals = (key, entry) :: frame.literals }

(* [unary] and [distinct] elaborate to calls on the prelude's Numeral lemmas, in the prelude's scope so
   user shadowing cannot reach them; the level context, and so [predates _], stays the caller's. *)
and elab_unary spos env l args =
  let a, rest = match args with a :: ([] | [ _ ] as rest) -> (a, rest) | _ -> error_in env l "`unary` takes one or two literals" in
  let za, _, sa = numeral_entry env l a in
  let lo =
    match rest with
    | [ b ] ->
        let zb, _, sb = numeral_entry env l b in
        if Z.geq zb za then error_in env l "`unary`: %s does not exceed %s" sa sb;
        zb
    | _ -> Z.zero
  in
  let k = Z.sub za lo in
  if Z.gt k (Z.of_int 4096) then error_in env l "`unary`: %s successors is beyond the limit" (Z.to_string k);
  let rec upto z acc = if Z.geq z za then List.rev acc else upto (Z.succ z) (z :: acc) in
  let env = List.fold_left (fun env z -> hoist env (Literal.Numeral z)) env (za :: upto lo []) in
  (* Fold the one-step proofs into a single Eq relating the literal to [floor] under k successors, so one
     let-match mints one rule and the literals walked over stay opaque. *)
  let floor, acc =
    if List.length args = 1 then ("(Zero)", "(numeral-zero 0 (numeral-of 0))")
    else (Z.to_string lo, Printf.sprintf "(Refl (Nat) %s)" (Z.to_string lo))
  in
  let step acc z =
    let n = Z.succ z in
    let below = Literal.succs (Z.to_int (Z.sub z lo)) floor in
    let stp =
      Printf.sprintf "(numeral-succ %s %s %s %s %s (numeral-of %s) (numeral-of %s))" (Literal.bin z)
        (Literal.bin n) (Z.to_string z) (Z.to_string n) (Literal.bin_succ z) (Z.to_string z) (Z.to_string n)
    in
    let congd = Printf.sprintf "(eq-cong-succ %s %s %s)" (Z.to_string z) below acc in
    Printf.sprintf "(eq-trans (Nat) %s (Succ %s) (Succ %s) %s %s)" (Z.to_string n) (Z.to_string z) below stp congd
  in
  let src = Printf.sprintf "(let-match erased %s (Refl _ _))" (List.fold_left step acc (upto lo [])) in
  in_prelude env (fun env -> elab_stmt spos env (List.hd (Reader.parse "<unary>" src)))

and elab_distinct env l a b =
  let za, xa, sa = numeral_entry env l a and zb, xb, sb = numeral_entry env l b in
  let refutes_nothing = respell env "so there is nothing to refute\nhint: `distinct` refutes a context whose facts equate two different literals, typically an `absurd` branch or function body" in
  if Z.equal za zb then error_in env l "`distinct`: %s is the same literal twice, %s" sa refutes_nothing;
  if not (equal (canon env (Var xa)) (canon env (Var xb))) then
    error_in env l "`distinct`: %s and %s do not canonicalize equally here, %s" sa sb refutes_nothing;
  let src =
    Printf.sprintf "(match erased (numeral-inj %s %s %s (numeral-of %s) (numeral-of %s)) (((False) f)) (absurd Refl))"
      (Literal.bin za) (Literal.bin zb) (Z.to_string za) (Z.to_string za) (Z.to_string zb)
  in
  let raw = match Reader.parse "<distinct>" src with [ r ] -> r | _ -> assert false in
  let env, (ress, code) =
    in_prelude env (fun env ->
        let env, ress, code = elab_expr env [ Erased ] raw in
        (env, (ress, code)))
  in
  (env, ress, code)

and elab_let_match spos env l args =
  match args with
  | m :: scrut :: List (pl, c :: fields) :: branches ->
      List.iter (fun b -> if real_branch env b then error_in env l "a `let-match` with a real branch besides its pattern must be a statement of a function, match branch or cell-match body") branches;
      let smult = written env spos l "let-match" (mult_or env l m) in
      let env, sres, scode, swrap, tid, mid, disc, ctors = scrutinee env l smult scrut in
      let c = ctor_var env pl c in
      if marker env pl tid ctors c = Erased && smult <> Erased then error pl "%s is phantom" (qname env c);
      let named = List.filter_map (function List (_, _ :: (Atom _ as b) :: _) | List (_, _ :: List (_, b :: _) :: _) -> Some (ctor_var env (loc b) b) | _ -> None) branches in
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
              let trial, fids = open_tele { env with run_pos = false } ~names:(anon tele) ~mults tele in
              Option.map (fun trial -> (other, trial)) (try Some (at l (fun () -> refine trial sres other fids ret)) with Contradiction _ -> None))
          ctors
      in
      if unrefuted <> [] then missing env l "let-match" sres unrefuted;
      if branches <> [] then ignore (elab_match ~refute:true ~res:(sres, scode) ~cells:(smult <> Erased && cells_allowed env mid) ~skip:[ c ] None env [ Erased ] l (m :: scrut :: Atom (l, "_") :: branches));
      let tele, ret = ctor_type env pl c in
      let mults = List.map (fun e -> field_under smult e.mult) tele in
      let fields, name = pattern env "a `let-match` pattern" smult sres pl c mults (smult <> Erased && cells_allowed env mid) fields in
      let names = field_names fields in
      let shapes = shapes env l ctors in
      let run = env.run_pos && smult <> Erased in
      let value = if run then Some (List.hd (run_code env (swrap scode))) else None in
      let env = match value,sres.term with Some v, Var x -> set_state env x (Const v) | _ -> env in
      let states = Option.map (fun v -> snd (const_fields env pl c mults v)) value in
      let env, fids = open_tele env ~names ~ats:(field_ats tele fields) ~mults ?states tele in
      let env = at l (fun () -> try refine env sres c fids ret with Contradiction msg -> error l "the scrutinee contradicts the facts in force (%s)" (Lazy.force msg)) in
      let env, cell = pattern_cell env pl smult sres c fids name in
      ( env,
        if smult = Erased || run then Fun.id
        else fun rest -> swrap (
          V.CMatch
            { scrut = scode; shape = match_shape env mid tid disc shapes;
              branches = [ (Option.get (discriminant shapes c), non_erased env fids, bind_cell scode cell rest) ]; default = None;
              live = Option.to_list (discriminant shapes c) }))
  | _ -> error l "%s" (help env (Sp.misuse Sp.LetMatch))

and elab_comptime_match env l args =
  match args with
  | [ m; x; List (pl, c :: fields) ] ->
      let smult = mult_or env l m in
      if smult = Erased then error_in env l "`comptime-match` takes `many` or `unique`, not `erased`";
      if not env.run_pos then error_in env l "`comptime-match` is a run-position statement (section 15)";
      let x, sharing =
        match x with
        | List (_, [ h; a ]) when special_of env h = Some Sp.Share ->
            let y = var env l (atom_or l a "a variable") in
            if (entry env y).mult <> Unique then error_in env l "`share` needs a unique value";
            if smult = Unique then error l "many value %s used at unique" (qname env y);
            (y, true)
        | _ -> (var env l (atom_or l x "a variable"), false)
      in
      let env = use env l ~sharing smult x in
      let value = match entry env x with { state = Const v; mult = (Many | Unique); _ } -> v | _ -> error_in env l "`comptime-match` needs a Const scrutinee that is `many` or `unique`" in
      let c = ctor_var env pl c in
      let tele, ret = ctor_type env pl c in
      let tid = match type_head env (type_of env x) with Some t -> t | None -> error l "scrutinee is not a datatype value" in
      let mid, disc, ctors = find_matchable env l tid in
      warn_use env l "match on" (Var tid);
      if adt_of env mid = None then error_in env l "the `Matchable` for %s is not Const, so `comptime-match` cannot consult it" (qname env tid);
      let env = use env l Many mid in
      if disc = Union then error_in env l "`comptime-match` needs an `enum`, not a `union`";
      if marker env pl tid ctors c = Erased then error_in env pl "`comptime-match`: %s is phantom, so no non-erased value is headed by it" (qname env c);
      let mults = List.map (fun e -> field_under smult e.mult) tele in
      let matched, states = const_fields env pl c mults value in
      if not matched then error_in env l "`comptime-match`: expected %s, got %s" (qname env c) (tick (show_value env l (type_of env x) value));
      let fields, name = pattern env "a `comptime-match` pattern" smult (res_of env x) pl c mults (smult <> Erased && cells_allowed env mid) fields in
      let names = field_names fields in
      let env, fids = open_tele env ~names ~ats:(field_ats tele fields) ~mults ~states tele in
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
        | Atom (al, "_") -> let x, env = mint_level env ~at:al None in (env, x)
        | _ -> level_var ~alt:" or `_`" env l lv
      in
      (* the header's marks: `at` before the name makes an at-function (A10), `at f` after it annotates a
         delegate to f (A11); a function marked `extern` and `at` has no implementation, its marks being a
         promise *)
      let header raw =
        match raw with
        | List (_, List (fl, m :: rest) :: body) -> (
            let mult = mult_or env fl m in
            let marks, rest = marks env [ Sp.Absurd; Sp.Extern; Sp.At ] rest in
            let delegates, rest = match rest with n :: a :: f :: rest when is_special env a Sp.At -> (Some f, n :: rest) | _ -> (None, rest) in
            match rest with
            | n :: colon :: sg when is_special env colon Sp.Colon ->
                let ps, rs = split_arrow env fl sg in
                let name = atom_or fl n "a function name" in
                let ty = elab_fn_type ~unique env (Var lvl) ps rs in
                let many_params = match ty with Fn (_, ps, _) | UniqueFn (_, ps, _) -> List.length (runtime ps) | _ -> 0 in
                let atfn = List.mem Sp.At marks and extern = List.mem Sp.Extern marks in
                if atfn && runtime (match ty with Fn (_, _, rs) | UniqueFn (_, _, rs) -> rs | _ -> []) <> [] then error_in env fl "an at-function's returns are erased or `at`";
                let impl = if extern && not atfn then Some (Ffi.claim_fn fl name many_params) else None in
                (fl, name, mult, List.mem Sp.Absurd marks, (impl, extern, atfn, delegates), ty, body)
            | _ -> error fl "malformed function header%s" (help env (Sp.hints "function-header")))
        | _ -> error (loc raw) "malformed function definition%s" (help env (Sp.hints "function-definition"))
      in
      let headers = List.map header fns in
      List.iter (fun (fl, _, m, _, _, _, _) -> if unique && m = Many then error_in env fl "`def-unique` requires `unique` or `erased`" else if not unique && m = Unique then error_in env fl "use `def-unique` to define a unique function") headers;
      let capture_uses = ref env.uses in
      let env, fids = List.fold_left_map (fun env (fl, name, mult, _, _, ty, _) -> let x, env = bind env ~word:true ~at:fl (name_or_anon name) mult Dyn ty in (env, x)) env headers in
      (* the `AtFn` proof is minted and opened before the bodies, so a call within the block to a function
         marked `at` is skipped (A10) *)
      let env = List.fold_left2 (fun env x (_, _, _, _, (_, _, atfn, _), ty, _) ->
        if not atfn then env else
        let p, env = witness env (proof_type Prelude.atfn [ ty; Var x ]) in
        merge_opens (forcing (opens_add env p))) env fids headers in
      let define x (fl, name, mult, absurd, (impl, extern, atfn, delegates), ty, body) =
        let params, rets = match ty with Fn (_, ps, rs) | UniqueFn (_, ps, rs) -> (ps, rs) | _ -> assert false in
        let envb = if unique then { env with entries = IntMap.add x { (entry env x) with mult = Erased } env.entries } else env in
        let envb, pids = open_tele envb params in
        let pvars = List.rev_map (fun x -> Var x) pids in
        (* a parameter written `at` is not passed: its word is its target's (A3) *)
        let renames body =
          let _, lets = List.fold_left2 (fun (ids, lets) (e : entry) x -> (Var x :: ids, match e.place with
            | Some p when e.mult <> Erased -> (x, location_var envb fl (instantiate ids p)) :: lets
            | _ -> lets)) ([], []) params pids in
          List.fold_left (fun body (x, y) -> V.CLet ([ x ], V.CVar y, body)) body lets in
        let subterms = List.filter_map (fun (e, x) -> if e.subterm then Some x else None) (List.combine params pids) in
        let envb = { envb with level = At lvl; subterms; enclosing = Some x; run_pos = false; in_extern = env.in_extern || extern; usage_erased = env.usage_erased || mult = Erased; captures = (if unique then env.captures else env.scope.ids @ env.captures) } in
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
        (match delegated with
         | Some (Var f) when f >= x -> error_in env fl "the function a `delegate` call names must be introduced before the function whose body it is"
         | Some (Var f) -> Hashtbl.replace V.aliases x (V.resolve f)
         | _ -> ());
        (match delegates, delegated with
         | None, _ -> ()
         | Some f, Some callee ->
             let f = named env (loc f) "a function name" f in
             if not (equal (canon env callee) (Var f)) then error_in env fl "%s is declared `at` %s but delegates to %s" (tick name) (qname env f) (qshow env callee)
         | Some f, None -> error_in env fl "%s is declared `at` %s but its body is not a `delegate` call" (tick name) (tick (Reader.show f)));
        (* an at-function's body erases to nothing and is never run through the proof; what remains is the
           dummy a first-class call without the proof reaches (A10) *)
        if atfn && mult <> Erased && not absurd && not (erases_to_nothing code) then error_in env fl "the body of at-function %s does not erase to nothing, or to a reordering of variables: it stores, allocates or calls" (tick name);
        let code = if atfn then V.CValues [] else code in
        ((x, { V.fname = name; params = runtime_ids params pids; body = code; impl }), Option.map (fun callee -> (x, ty, callee)) delegated)
      in
      let fns, proofs = List.split (List.map2 define fids headers) in
      let env = { env with uses = !capture_uses } in
      let env =
        List.fold_left
          (fun env -> function
            | Some (g, gty, callee) -> snd (witness env (proof_type Prelude.delegate [ sharing_of_fn env gty; gty; Var g; sharing_of_fn env (infer env l callee); infer env l callee; callee ]))
            | None -> env)
          env proofs
      in
      let fns = List.filter (fun (x, _) -> not (Hashtbl.mem V.aliases x)) fns in
      if env.run_pos then
        let values = Eval.close env.values fns in
        if fns <> [] then trace := Fns fns :: !trace;
        (List.fold_left (fun env x -> set_state env x (Const (IntMap.find (V.resolve x) values))) env fids, Fun.id)
      else
        let fns = List.filter (fun (x, _) -> (entry env x).mult <> Erased) fns in
        (env, if fns = [] then Fun.id else fun rest -> V.CLetRec (fns, rest))

(* Validates the tail/delegate marks in a body (section 9), returning the delegated callee if any. Lets that only
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
      | V.CApp (_, _, V.Same (cl, callee)) as c -> warn_in env cl [] "same-level call to %s is unmarked; mark it %s" (qshow env callee) (tick (speller env (if List.memq c in_tail then "tail" else "notail")))
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

and elab_def_adts env adts =
  let header raw =
    match raw with
    | List (_, List (al, n :: colon :: sg) :: d :: rest) when is_special env colon Sp.Colon -> (
        let ps, ret = split_arrow env al sg in
        match ret with
        | [ ty ] -> let ms, ctors = marks env [ Sp.NewtypeMark; Sp.Extern ] rest in (al, atom_or al n "a type constructor name", ps, ty, disc_of env al d, ms, ctors)
        | _ -> error al "a type constructor declares one return")
    | _ -> error_in env (loc raw) "malformed `def-adts` entry%s" (help env (Sp.hints "def-adts-entry"))
  in
  let headers = List.map header adts in
  let env, tids =
    List.fold_left_map
      (fun env (al, name, ps, ty, _, _, _) ->
        let x, env = bind env ~at:al (name_or_anon name) Erased (const env V.VToken) (elab_tyctor env al ps [ ty ]) in
        (env, x))
      env headers
  in
  let define (env, cids) tid (al, name, _, _, disc, ms, ctors) =
    let ctor env raw =
      match raw with
      | List (cl, m :: n :: colon :: rest) when is_special env colon Sp.Colon ->
          let mult = mult_or env cl m in
          if mult = Unique then error_in env cl "a constructor declaration cannot be `unique`";
          let name = atom_or cl n "a constructor name" in
          let env', tele, ret, ty = elab_valctor env cl rest in
          (match canon env' ret with App (Var t, _) when t = tid -> () | _ -> error cl "%s must return an application of %s" (tick name) (qname env tid));
          if mult = Erased && List.exists (fun e -> e.mult <> Erased) tele then warn_at cl [] "phantom constructor %s has a non-erased field" (tick name);
          let c, env = bind env ~at:cl (name_or_anon name) mult (if mult = Erased then const env V.VToken else Dyn) ty in
          (env, (mult, c))
      | _ -> error (loc raw) "malformed constructor%s" (help env (Sp.hints "constructor"))
    in
    let env, ctors = List.fold_left_map ctor env ctors in
    let ctors = List.map (fun (m, c) -> (m, Var c)) ctors in
    let shapes = shapes env al ctors in
    let adt = mint_adt ~newtype:(List.mem Sp.NewtypeMark ms) env name disc shapes in
    Ffi.note name adt;
    if List.mem Sp.Extern ms then adt.ext <- Some (Ffi.claim_type al name adt);
    let values = List.map (fun ct -> (ct.V.cid, V.VCtorFn ct)) adt.ctors in
    let env = if env.run_pos then List.fold_left (fun env (c, v) -> set_state env c (Const v)) env values else env in
    let mid, env = witness env ~mult:Many ~value:(V.VMatchable adt) (Matchable (disc, List.mem Sp.NewtypeMark ms, List.mem Sp.Extern ms, Var tid, ctors)) in
    let env = open_adt env mid in
    if List.mem Sp.NewtypeMark ms && wrappers disc shapes = [] then error al "%s is not of newtype shape (section 38)" (tick name);
    (env, cids @ values @ [ (mid, V.VMatchable adt) ])
  in
  let env, cids = List.fold_left2 define (env, []) tids headers in
  (env, if env.run_pos then Fun.id else fun rest -> V.CLet (List.map fst cids, V.CValues (List.map (fun (_, v) -> V.CConst v) cids), rest))

let rec literals = function
  | Atom (l, s) -> (match Literal.classify s with `Lit x -> [ (l, x) ] | `Bad msg -> error l "%s" msg | `Name -> [])
  | List (_, items) -> List.concat_map literals items

let hoist_at env (l, lit) =
  let what, ty = match lit with Literal.Numeral _ -> ("a numeral", "Nat") | Char _ -> ("a character literal", "Char") | Str _ -> ("a string literal", "String") in
  if prelude_id env ty = None then error l "%s needs the prelude's %s, which `--no-prelude` leaves out" what (tick ty);
  hoist env lit

let run_toplevel ?(consume = fun _ _ v -> print_endline (V.show v)) ?(path = "-") env items =
  let rec go env = function
    | [] -> env
    | List (l, Atom (_, ";!") :: words) :: rest -> go (at l (fun () -> pragma env l words)) rest
    | item :: rest -> (
        let env = List.fold_left hoist_at env (literals item) in
        at (loc item) (fun () ->
            if rest = [] && not (is_statement env item) then (
              if misplaced env item <> [] then not_a env "neither a statement nor an expression" item;
              let env, ress, code = elab_expr ~demand:Driver env [ Many ] item in
              settle_res env (loc item) (single (loc item) ress);
              let ty = (single (loc item) ress).ty and v = List.hd (run_code env code) in
              trace := Final (v, ty, path) :: !trace;
              consume env ty v;
              env)
            else go (fst (elab_stmt ~within:"top-level form" Many env item)) rest))
  in
  let env = Fun.protect ~finally:report_shadows (fun () -> go env items) in
  (match items with
   | item :: _ -> List.iter (fun r -> if not r.Reader.used then warn_at r.from [] "`;! suppress warn` for %s silenced nothing" (tick r.name)) (Option.value ~default:[] (Hashtbl.find_opt Reader.regions (loc item).file))
   | [] -> ());
  env
