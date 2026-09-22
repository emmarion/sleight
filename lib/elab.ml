open Term
open Reader
open Env
module V = Value
module Sp = Special

type entry = Term.entry = { name : string option; subterm : bool; mult : mult; sg : sg; place : term option }
type res = { term : term; ty : term; erasure : mult; place : term option }
type demand = Fixed | CallableHead | Driver

let location_var env l p =
  let readable x = (entry env x).mult <> Erased && ((entry env x).word || IntMap.mem x env.values) in
  match p with
  | Var x when readable x -> x
  | _ -> (match List.find_opt (fun x -> readable x && at_equal env p (Var x)) env.scope.ids with
      | Some x -> x
      | None -> error l "no caller word for at %s" (show env p))

let type_term = Prelude.type_term

(* Elaboration's third output channel, beside a program's own stdout and stderr and the message a refusal
   carries: a warning names something legal that the session reads as a mistake. Writing it through a hook is
   what lets the runner capture one, stderr being the process's own here rather than the world's. *)
let warn = ref prerr_string
let warn_at l fmt = Printf.ksprintf (fun m -> !warn (Printf.sprintf "%s: warning: %s\n" (Reader.where "-" l) m)) fmt

let single loc = function [ r ] -> r | rs -> error loc "expected one value, got %d" (List.length rs)
let pos_of expect = if expect <> [] && List.for_all (( = ) Erased) expect then Erased else if expect = [ Unique ] then Unique else Many
let atom = function Atom (_, n) -> Some n | List _ -> None
let atom_or loc raw what = match atom raw with Some n -> n | None -> error loc "expected %s, got %s" what (Reader.show raw)
let name_or_anon n = if n = "_" then None else Some n

(* A special form's head: a Const, non-erased entry of type (Special) holding one of its variants (section 4). *)
let rec special_of env raw =
  let value x = match entry env x with
    | { state = Const (V.VCtor (c, [||])); mult = (Many | Unique); _ } when equal (type_of env x) Prelude.special_term -> List.assoc_opt c.cid Prelude.specials
    | _ -> None in
  match raw with
  | Atom (_, n) -> Option.bind (lookup env n) value
  | List (_, [head; Atom (_, n)]) when special_of env head = Some Sp.Share -> Option.bind (lookup env n) value
  | _ -> None

let read_special pos env raw =
  match raw with
  | Atom (l,n) -> use env l Many (Option.get (lookup env n))
  | List (l,[h;Atom (_,n)]) when special_of env h = Some Sp.Share ->
      if pos = Erased then error l "share in an erased position";
      let x = Option.get (lookup env n) in
      if (entry env x).mult <> Unique then error l "share needs a unique value";
      use env l ~sharing:true Many x
  | _ -> env

let is_special env raw s = special_of env raw = Some s
let mult_of env raw = match special_of env raw with Some Sp.Erased -> Some Erased | Some Sp.Many -> Some Many | Some Sp.Unique -> Some Unique | _ -> None
let mult_or env loc raw = match mult_of env raw with Some m -> m | None -> error loc "expected a multiplicity, got %s" (Reader.show raw)
let is_statement env = function List (_, h :: _) -> List.exists (is_special env h) Sp.statements | _ -> false
let at loc f = try f () with Error (l, msg) when not (Reader.placed l) -> error loc "%s" msg
let var env loc n =
  match Literal.classify n with
  | `Name -> (match lookup env n with Some x -> x | None -> error loc "unbound name %s" n)
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
  let z =
    match Literal.classify name with
    | `Lit (Literal.Numeral z) -> z
    | `Lit (Literal.Char c) -> Z.of_int c
    | _ -> error loc "%s is not a numeral or character literal" name
  in
  match List.assoc_opt (Z.to_string z) env.literals with
  | Some (x, _) -> (z, x)
  | None -> error loc "literal %s is not in scope" (Z.to_string z)

(* An atom naming an entry, read through any alias rule the fact table holds for it (section 9). *)
let named env loc what raw =
  match canon env (Var (var env loc (atom_or loc raw what))) with Var x -> x | t -> error loc "%s is not %s" (show env t) what

let tyname env loc = named env loc "a type constructor"

(* Identity after canonicalization (section 5), solving any metas either side holds (Env.unify). *)
let solve what env loc actual expected =
  try unify env actual expected with Contradiction _ -> error loc "%s mismatch: expected %s, got %s" what (show env expected) (show env actual)

let check what env loc actual expected = ignore (solve what env loc actual expected)
let check_type = check "type" and check_equal = check "value"
let solve_sg env loc sg r = match sg with Ty ty -> solve "type" env loc r.ty ty | Is t -> solve "value" env loc r.term t
let check_sg env loc sg r = ignore (solve_sg env loc sg r)
let under pos m = if pos = Erased then Erased else m
let written pos l what m =
  if pos = Erased && m <> Erased then error l "%s in an erased position is written erased" what else m
let field_under pos m = if pos = Many && m = Unique then Many else under pos m
let wild = function Atom (_, "_") -> true | _ -> false

(* A boundary (SUGAR.md 6): a term reaching one with a `_` still open is refused. *)
let settle env loc t = if has_meta env t then error loc "cannot infer the _ in %s" (show env t)

let rec infer env loc t =
  match t with
  | Var x -> type_of env x
  | App (h, args) -> (
      match canon env (infer env loc h) with
      | TyCtor _ -> type_term
      | ValCtor (_, r) -> instantiate (List.rev args) r
      | ty -> error loc "%s has type %s and cannot be applied" (show env h) (show env ty))
  | Fn _ | UniqueFn _ | TyCtor _ | ValCtor _ | Matchable _ | Cell _ -> type_term
  | SlotHolds _ -> Prelude.slot_term
  | Bound _ -> error loc "internal: dangling binder"

let res_of env x = { term = Var x; ty = type_of env x; erasure = (entry env x).mult; place = Some (Var x) }
let settle_res env loc r = settle env loc r.term; settle env loc r.ty
let non_erased env ids = List.filter (fun x -> (entry env x).mult <> Erased) ids
let term_res env loc t = { term = t; ty = infer env loc t; erasure = Erased; place = None }

(* Opens [x], a Matchable entry (section 19): its constructors must be distinct after canonicalization,
   and it then merges with whatever open names one of them or its type constructor (Env.merge_opens). Failure is
   a Contradiction. *)
let open_adt env x =
  let rec dup = function [] -> None | c :: rest -> if List.mem c rest then Some c else dup rest in
  (match type_of env x with
  | Matchable (_, _, _, _, cs) -> Option.iter (fun c -> raise (Contradiction (show env c ^ " is listed twice"))) (dup (List.map snd cs))
  | _ -> ());
  merge_opens (forcing (opens_add env x))

(* The opened Matchable for a type, at most one (Env.merge_opens). *)
let matchables env tid =
  let of_type o = match o.Env.names with Var t :: _ when t = tid -> (match type_of env o.obj with Matchable (d, _, _, _, cs) -> Some (o.obj, d, cs) | _ -> None) | _ -> None in
  List.filter_map of_type env.opens.opened

let find_matchable env loc tid =
  match matchables env tid with [] -> error loc "%s has no Matchable open" (name_of env tid) | m :: _ -> m

let type_head env ty = match canon env ty with App (Var t, _) -> Some t | _ -> None

let held_needs_many env loc tid mid =
  if not (readable env mid) then
    error loc "the Matchable for %s is erased or out of scope, so a non-erased match cannot take a value of it apart" (name_of env tid)

let check_empty env loc ty =
  let empty = match type_head env ty with Some t when matchables env t <> [] -> (let _, _, cs = find_matchable env loc t in cs = []) | _ -> false in
  if not empty then error loc "%s is not an empty type" (show env ty)

let ctor_type env loc c =
  match canon env (type_of env c) with ValCtor (tele, ret) -> (tele, ret) | _ -> error loc "%s is not a value constructor" (name_of env c)

let tid_of env loc c = Option.get (type_head env (snd (ctor_type env loc c)))
let marker env loc tid ctors c =
  match List.find_opt (fun (_, c') -> c' = Var c) ctors with
  | Some (m, _) -> m
  | None -> error loc "%s is not a constructor of %s" (name_of env c) (name_of env tid)

(* A Matchable's constructors, each with its phantom marker and its number of non-erased fields (section 38). *)
let shapes env loc ctors =
  List.map (fun (m, c) -> match c with Var c -> (m, c, List.length (List.filter (fun e -> e.mult <> Erased) (fst (ctor_type env loc c)))) | _ -> assert false) ctors

let non_phantom shapes = List.filter_map (fun (m, c, n) -> if m = Many then Some (c, n) else None) shapes

(* A phantom constructor heads no runtime value (section 20 rule 2), so discriminants number the others only. *)
let discriminant shapes c = find_index (fun (c', _) -> c' = c) (non_phantom shapes)

let tagged disc shapes = disc = Enum && List.length (non_phantom shapes) > 1

let wrapper disc shapes =
  match List.filter (fun (m, _, n) -> m = Many && n = 1) shapes with
  | [ (_, w, _) ] when (not (tagged disc shapes)) && List.for_all (fun (m, c, n) -> m = Erased || c = w || n = 0) shapes -> Some w
  | _ -> None

let newtype_of env c =
  List.find_map (fun o -> if not (List.mem (Var c) o.Env.names) then None else match type_of env o.Env.obj with
    | Matchable (d, true, _, _, cs) when wrapper d (shapes env Reader.nowhere cs) = Some c -> Some o.obj
    | _ -> None) env.opens.opened

let ctor_of env loc c = match (entry env c).state with Const (V.VCtorFn ct) -> ct | _ -> error loc "%s is not a run-position constructor" (name_of env c)
let const env v = if env.run_pos then Const v else Dyn
let ctor_var env loc = named env loc "a constructor"
let proof_type ctor args = App (Var ctor, args)

let sharing_of_fn env t = match canon env t with UniqueFn _ -> Prelude.unique_term | Fn _ -> Prelude.shared_term | _ -> assert false
let sharing_mult env l t =
  let t = canon env t in
  if equal t Prelude.unique_term then Unique else if equal t Prelude.shared_term then Many
  else error l "coerce needs a canonical Unique or Shared side, got %s" (show env t)

let expect_proof env loc ctor p =
  match canon env (infer env loc p) with
  | App (Var c, args) when c = ctor -> args
  | ty -> error loc "expected a %s proof, got %s : %s" (name_of env ctor) (show env p) (show env ty)

let rec is_strict_subterm a b =
  match b with App (_, args) -> List.exists (fun x -> equal a x || is_strict_subterm a x) args | _ -> false

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
      | _ -> error l "malformed telescope entry %s" (Reader.show raw))
  | Atom (l, _) -> error l "expected a telescope entry, got %s" (Reader.show raw)

let split_arrow env loc items =
  let rec go acc = function
    | [] -> error loc "missing ->"
    | t :: rest when is_special env t Sp.Arrow -> (List.rev acc, rest)
    | t :: rest -> go (t :: acc) rest
  in
  go [] items

let no_mults loc = fun _ -> function None -> Some Erased | Some _ -> error loc "these entries carry no multiplicity"

(* Leading annotation tokens drawn from [allowed], in any order. *)
let marks env allowed items =
  let rec go acc = function
    | t :: rest when List.exists (is_special env t) allowed -> go (List.find (is_special env t) allowed :: acc) rest
    | rest -> (acc, rest)
  in
  go [] items

let fact_of env loc = function Ty t -> (t, None) | Is t -> (infer env loc t, Some t)

let anon tele = List.map (fun _ -> None) tele
let count_check l expect got = if List.length expect <> List.length got then error l "expected %d values, got %d" (List.length expect) (List.length got)
let ctor_result head mvars = [ { name = None; subterm = false; mult = Erased; sg = Is (App (head, List.rev mvars)); place = None } ]
let field_names env l c tele fields =
  if List.length fields <> List.length tele then error l "%s has %d fields" (name_of env c) (List.length tele);
  List.map (fun f -> name_or_anon (atom_or (loc f) f "a field name")) fields

(* [ids]: terms of the binders already in force, innermost first. Binds one fresh entry per item and returns their ids in order. *)
let open_tele env ?(word = true) ?names ?mults ?states ?(ids = []) ?meta tele =
  let nth l i default = match l with Some l -> List.nth l i | None -> default in
  let _, env, _, fresh =
    List.fold_left
      (fun (i, env, ids, fresh) e ->
        let ty, rule = fact_of env Reader.nowhere (map_sg (instantiate ids) e.sg) in
        let x, env = bind env ?meta ~word:(word && meta <> Some true) (nth names i e.name) (nth mults i e.mult) (nth states i Dyn) ty ?rule in
        let env = match Option.map (instantiate ids) e.place with
          | Some (SlotHolds p) when meta <> Some true -> at_merge env (Var x) p
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
  adt.ctors <- List.mapi (fun index (c, arity) -> { V.cname = name_of env c; cid = c; index; arity; adt }) (non_phantom shapes);
  adt

(* A match on an ADT the elaborator can see reads no Matchable at runtime (section 17); one on a held Matchable
   reads it as the shape the Matchable's type gives its values. *)
let match_shape env x tid disc shapes = match adt_of env x with Some adt -> V.Known adt | None -> V.Held (V.CVar x, mint_adt ~newtype:(match type_of env x with Matchable (_, n, _, _, _) -> n | _ -> false) env (name_of env tid) disc shapes)
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
  let a = mint_adt env (name_of env tid) disc shapes in
  let ct = { V.cname = name_of env c; cid = c; index = Option.value (discriminant shapes c) ~default:0;
    arity = List.length (List.filter (fun e -> e.mult <> Erased) params); adt = a } in
  (ct, params, ret)

let cells_allowed env mid = match type_of env mid with
  | Matchable (_, false, ext, _, _) -> not ext || env.in_extern
  | _ -> false

let split_cell_pattern _env l extra fields =
  if not extra then (fields, None) else match List.rev fields with
  | n :: fs -> (List.rev fs, Some (name_or_anon (atom_or l n "a cell binder")))
  | [] -> error l "a unique pattern needs its extra cell binder"

let pattern_cell env l mult scrut c fids name =
  match name with
  | None -> (env, None)
  | Some name ->
      let _, params, _ = cell_shape env l c in
      let slots = List.filter_map (fun (e,x) -> if e.mult = Erased then None else Some (SlotHolds (Var x))) (List.combine params fids) in
      let state = match scrut.term with Var x -> (entry env x).state | _ -> Dyn in
      let x, env = bind env ~word:true name mult state (Cell (Var c, slots)) in
      let env = match scrut.place with Some p -> at_merge env (Var x) p | None -> env in
      (env, Some x)

let bind_cell code cell body = match cell with None -> body | Some x -> V.CLet ([x],code,body)

let mint_level env name = bind env ~minted_level:true name Erased (const env V.VToken) Prelude.level_term

let rec elab_term ?expect env raw =
  match raw with
  | Atom (_, "_") -> let x, env = bind env ~meta:true None Erased Dyn type_term in (env, Var x)
  | Atom (l, n) -> (env, Var (var env l n))
  | List (l, []) -> error l "empty form"
  | List (l, head :: args) -> (
      match special_of env head with
      | Some sp -> elab_type_form env l sp args
      | None -> (
          let h = Var (var env l (atom_or l head "a constructor")) in
          match canon env (infer env l h) with
          | TyCtor tele | ValCtor (tele, _) -> let env, acc = elab_term_args env l ?expect tele h args in (env, App (h, List.rev acc))
          | ty -> error l "%s has type %s and cannot be applied in a type" (show env h) (show env ty)))

and elab_type_form env l sp args =
  match (sp, args) with
  | Sp.Cell, c :: slots ->
      let c = ctor_var env l c in
      let ct, _, _ = cell_shape env l c in
      if List.length slots <> ct.V.arity then error l "Cell needs %d slots" ct.arity;
      let env, slots = List.fold_left_map (fun env s -> let env, s = elab_term env s in check_type env l (infer env l s) Prelude.slot_term; (env, s)) env slots in
      (env, Cell (Var c, slots))
  | Sp.SlotVacant, [] -> (env, SlotHolds (Var Prelude.null))
  | Sp.SlotHolds, [ a ] ->
      let x = var env (loc a) (atom_or (loc a) a "a direct variable reference") in
      if (entry env x).mult = Erased then error (loc a) "SlotHolds needs a declared non-erased variable";
      if List.mem x env.signature then error (loc a) "SlotHolds cannot name a telescope binder; abstract over a Slot instead";
      (env, SlotHolds (Var x))
  | (Sp.Fn | Sp.UniqueFn), lv :: rest ->
      let env, lv = elab_term env lv in
      check_type env l (infer env l lv) Prelude.level_term;
      let ps, rs = split_arrow env l rest in
      (env, elab_fn_type ~unique:(sp = Sp.UniqueFn) env lv ps rs)
  | Sp.TyCtor, _ -> let ps, ret = split_arrow env l args in (env, elab_tyctor env l ps ret)
  | Sp.ValCtor, _ -> let _, _, _, t = elab_valctor env l args in (env, t)
  | Sp.Matchable, d :: rest ->
      let ms, rest = marks env [ Sp.NewtypeMark; Sp.Extern ] rest in
      let t, cs = match rest with t :: cs -> (t, cs) | _ -> error l "malformed Matchable" in
      let ctor = function
        | List (cl, [ m; c ]) -> let m = mult_or env cl m in
            if m = Unique then error cl "a Matchable constructor cannot be unique";
            (m, Var (ctor_var env cl c))
        | raw -> error (loc raw) "expected a constructor marker" in
      (env, Matchable (disc_of env l d, List.mem Sp.NewtypeMark ms, List.mem Sp.Extern ms, Var (tyname env l t), List.map ctor cs))
  | (Sp.Fn | Sp.UniqueFn | Sp.Matchable), _ -> error l "malformed %s" (Sp.name sp)
  | _ -> error l "%s cannot appear in a type" (Sp.name sp)

and elab_fn_type ?(unique = false) env lv ps rs =
  let env, ids, params = elab_tele env ~subterm:true ps in
  let _, _, rets = elab_tele env ~places:true ~ids:(List.rev ids) rs in
  if unique then UniqueFn (lv, params, rets) else Fn (lv, params, rets)

and elab_tyctor env l ps ret =
  let env', _, tele = elab_tele env ~mults:(no_mults l) ps in
  (match ret with [ r ] -> let env', r = elab_term env' r in check_equal env' l r type_term | _ -> error l "TyCtor returns Type");
  TyCtor tele

and elab_valctor env l items =
  let ps, ret = split_arrow env l items in
  let env', ids, tele = elab_tele env ps in
  let env', ret = match ret with [ r ] -> elab_type env' r | _ -> error l "a constructor returns one type" in
  settle env' l ret;
  (match canon env' ret with
  | App (Var t, _) when (not (List.mem t ids)) && (match type_of env' t with TyCtor _ -> true | _ -> false) -> ()
  | _ -> error l "a constructor returns an application of a type constructor in scope, not %s" (show env' ret));
  (env', tele, ret, ValCtor (tele, abstract (List.rev ids) ret))

and disc_of env l d = match special_of env d with Some Sp.Enum -> Enum | Some Sp.Union -> Union | _ -> error l "expected enum or union"

and elab_type env raw =
  let env, t = elab_term env raw in
  check_type env (loc raw) (infer env (loc raw) t) type_term;
  (env, t)

and elab_sg env = function
  | `Ty t -> let env, t = elab_type env t in (env, Ty t)
  | `Is t -> let env, t = elab_term env t in (env, Is t)

and level_var env l raw =
  let env, t = elab_term env raw in
  match canon env t with Var x when equal (type_of env x) Prelude.level_term -> (env, x) | t -> error l "%s is not a level" (show env t)

(* Elaborates source entries into a closed telescope, binding each name for the entries after it.
   [ids]: binders already in force, innermost first; [mults] maps an entry's index and declared multiplicity to its actual one. *)
and elab_tele env ?(places = false) ?(contextual = false) ?(subterm = false) ?(ids = []) ?(mults = fun _ m -> m) ?holes entries =
  let place_scope = env.scope.ids in
  let entries = List.concat_map (parse_entry env) entries in
  let _, env, ids, tele =
    List.fold_left
      (fun (i, env, ids, tele) e ->
        if e.s_subterm && not subterm then error e.s_loc "subterm is not allowed here";
        let mult = match mults i e.s_mult with Some m -> m | None -> error e.s_loc "entry %s needs a multiplicity" e.s_name in
        let env, sg = match e.s_sg with Some s -> elab_sg env s | None -> error e.s_loc "entry %s needs a type or an is clause" e.s_name in
        let ty, rule = fact_of env e.s_loc sg in
        let place = Option.map (fun raw ->
          if not places then error e.s_loc "at is allowed only on return and match annotation entries";
          if mult = Erased && not contextual then error e.s_loc "at needs a non-erased return";
          let x = var env (loc raw) (atom_or (loc raw) raw "a location variable") in
          if (entry env x).mult = Erased then error (loc raw) "at needs a non-erased variable";
          if not (List.mem x place_scope) then error (loc raw) "at must name an argument or a closed-over variable";
          SlotHolds (Var x)) e.s_place in
        let name = name_or_anon e.s_name in
        let x, env = at e.s_loc (fun () -> bind env ?holes name mult Dyn ty ?rule) in
        (i + 1, { env with signature = x :: env.signature }, x :: ids, { name; subterm = e.s_subterm; mult; sg = map_sg (abstract ids) sg; place = Option.map (abstract ids) place } :: tele))
      (0, env, ids, []) entries
  in
  (env, List.rev ids, List.rev tele)

(* Checks [args] against [tele] with [elab env mult arg expect]; returns the argument terms innermost first,
   and their code. A meta stands for each parameter (SUGAR.md 6): an argument written `_` is left to it, and
   is an error unless erased where it stands; any other argument is checked against its parameter and bound
   to its meta. [result] is the application's result telescope over the parameters' metas, unified with
   [expect] eagerly, where a `_` is present, before any argument is read, and again, reporting the mismatch,
   when a `_` would otherwise stay unsolved at the closing paren; every `_` is solved by then or refused. *)
and check_args env loc ?expect ?(result = fun _ -> []) ?(pos = Erased) ?(boundary = true) ?(bind_args = false) tele args elab =
  if List.length tele <> List.length args then error loc "expected %d arguments, got %d" (List.length tele) (List.length args);
  let env, metas = open_tele env ~meta:true ~names:(anon tele) ~mults:(List.map (fun _ -> Erased) tele) tele in
  let mvars = List.rev_map (fun x -> Var x) metas in
  let wilds = List.exists wild args in
  let against ~strict env = match expect with Some tele when wilds -> solve_tele ~strict env loc tele (result mvars) | _ -> env in
  let env = against ~strict:false env in
  let env, acc, codes, bindings =
    List.fold_left2
      (fun (env, acc, codes, bindings) (i, e, m) arg ->
        let sg = map_sg (instantiate acc) e.sg in
        if wild arg then (
          if under pos e.mult <> Erased then error (Reader.loc arg) "_ stands for an erased argument, and argument %d here is not erased" (i + 1);
          (env, Var m :: acc, codes, bindings))
        else
          let env, r, code = elab env e.mult arg (Some [ { e with sg } ]) in
          let env = solve_sg env (Reader.loc arg) sg r in
          let env, r, code, bindings =
            if bind_args && pos <> Erased && e.mult <> Erased then (
              match r.term, code with
              | Var _, V.CVar _ -> (env, r, code, bindings)
              | _ ->
                  let x, env = bind env ~holes:true ~word:true ~temporary:true None r.erasure Dyn r.ty ~rule:r.term in
                  let env = match r.place with Some p -> at_merge env (Var x) p | None -> env in
                  (env, { r with term = Var x; place = Some (Var x) }, V.CVar x, (x, code) :: bindings))
            else (env, r, code, bindings)
          in
          (solve "value" env (Reader.loc arg) r.term (Var m), r.term :: acc, (if e.mult <> Erased then code :: codes else codes), bindings))
      (env, [], [], []) (List.mapi (fun i (e, m) -> (i, e, m)) (List.combine tele metas)) args
  in
  let env = if boundary && List.exists (has_meta env) acc then against ~strict:true env else env in
  if boundary then List.iteri (fun i t -> if has_meta env t then error loc "argument %d is _ and cannot be inferred" (i + 1)) (List.rev acc);
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
and elab_term_args env loc ?expect tele ret args =
  let env, acc, _, _ =
    check_args env loc ?expect ~result:(ctor_result ret) ~boundary:false tele args (fun env _ a expect ->
        let env, t = elab_term ?expect env a in
        (env, term_res env (Reader.loc a) t, V.CErased))
  in
  (env, acc)

(* [ids] as in [open_tele]. *)
let check_results env loc ?(ids = []) tele ress =
  count_check loc tele ress;
  let env = List.fold_left2 (fun (env, acc) e r ->
    let env = solve_sg env loc (map_sg (instantiate acc) e.sg) r in
    (match Option.map (instantiate acc) e.place with
     | Some (SlotHolds p) when not env.usage_erased ->
         if not (Option.fold ~none:false ~some:(at_equal env p) r.place) then error loc "return does not satisfy at %s" (to_string (name_of env) p)
     | _ -> ());
    (env, r.term :: acc)) (env, ids) tele ress |> fst in
  List.iter (settle_res env loc) ress

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

let prove_subterm env l a b =
  if not (is_strict_subterm (canon env a) (canon env b)) then error l "%s is not a strict subterm of %s" (show env a) (show env b);
  mint env (proof_type Prelude.subterm [ infer env l a; a; infer env l b; b ])

let prove_predates env l x lvl =
  if not (entry env lvl).minted_level then error l "%s is not a level minted by def-lvl" (name_of env lvl);
  let x = match canon env (Var x) with Var y when x >= lvl -> y | _ -> x in
  if x >= lvl then error l "%s was not in scope when level %s was minted" (name_of env x) (name_of env lvl);
  mint env (proof_type Prelude.predates [ type_of env x; Var x; Var lvl ])

let demanded env demand mult ty =
  if mult = Erased then mult else
  match demand with
  | Fixed -> mult
  | CallableHead -> (match canon env ty with Cell _ | UniqueFn _ -> Unique | _ -> Many)
  | Driver -> if nullary env "IO" ty then Unique else Many

let rec elab_expr ?(demand = Fixed) ?(cc = V.Plain) ?tele env expect raw : Env.t * res list * V.code =
  let l = loc raw in
  let outer_erased = env.usage_erased in
  let env = { env with usage_erased = outer_erased || pos_of expect = Erased } in
  let env, ress, code = elab_form demand cc tele env expect raw in
  let ress = List.map (fun r -> { r with term = metaless env r.term; ty = metaless env r.ty }) ress in
  count_check l expect ress;
  List.iter2 (fun m r ->
    let m = demanded env demand m r.ty in
    if not outer_erased then (
    if m <> Erased && r.erasure = Erased then error l "erased value %s : %s used in a non-erased position" (show env r.term) (show env r.ty);
    if m = Unique && r.erasure = Many then error l "many value %s used at unique" (show env r.term);
    if m = Many && r.erasure = Unique then error l "unique value %s needs an explicit share" (show env r.term))) expect ress;
  ({ env with usage_erased = outer_erased }, ress, code)

and elab_expr1 ?demand ?cc ?tele env mult raw =
  let env, ress, code = elab_expr ?demand ?cc ?tele env [ mult ] raw in
  (env, List.hd ress, code)

and elab_erased env raw =
  let env, r, _ = elab_expr1 env Erased raw in
  settle_res env (loc raw) r;
  (env, r.term)

and elab_form demand cc expect_tele env expect raw =
  let pos = pos_of expect in
  let arg env m a tele = elab_expr1 ?tele env (under pos m) a in
  match raw with
  | Atom (l, n) ->
      let x = var env l n in
      (use env l (demanded env demand pos (type_of env x)) x, [ res_of env x ], if pos <> Erased then V.CVar x else V.CErased)
  | List (l, []) -> error l "empty form"
  | List (l, head :: args) -> (
      match special_of env head with
      | Some sp -> elab_special demand expect_tele (read_special pos env head) expect l sp args
      | None -> (
          let env, h, hcode, headwrap = elab_head env pos l head in
          let env, rs, code = match canon env h.ty with
          | TyCtor tele ->
              if pos <> Erased then error l "type constructor application in a non-erased position";
              let env, acc = elab_term_args env l ?expect:expect_tele tele h.term args in
              (env, [ { term = App (h.term, List.rev acc); ty = type_term; erasure = Erased; place = None } ], V.CErased)
          | ValCtor (tele, ret) ->
              if pos <> Erased && h.erasure = Erased then error l "erased constructor %s in a non-erased position" (show env h.term);
              let pos = demanded env demand pos ret in
              let env = match h.term with Var x -> use env l (under pos Many) x | _ -> env in
              let env, acc, codes, wrap = check_args env l ~bind_args:true ?expect:expect_tele ~result:(ctor_result h.term) ~pos ~boundary:false tele args (fun env _ a tele -> arg env (field_under pos (List.hd (Option.get tele)).mult) a tele) in
              let is_wrapper = newtype_of env (match canon env h.term with Var c -> c | _ -> -1) <> None in
              let code = if pos = Erased then V.CErased else if is_wrapper then List.hd codes else V.CApp (hcode, codes, V.Ctor) in
              let place = if is_wrapper && pos <> Erased then List.find_map (fun (e, a) -> if e.mult <> Erased then Some a else None) (List.combine tele (List.rev acc)) else None in
              (env, [ { term = App (h.term, List.rev acc); ty = instantiate acc ret; erasure = pos; place } ], wrap code)
          | Cell (c, slots) -> elab_cell_invoke env expect l h hcode c slots args
          | UniqueFn (lv, params, rets) -> elab_call ~unique:true cc env ?tele:expect_tele expect l h hcode lv params rets args arg
          | Fn (lv, params, rets) -> elab_call cc env ?tele:expect_tele expect l h hcode lv params rets args arg
          | ty -> error l "%s : %s is not applicable" (show env h.term) (show env ty) in
          (env, rs, headwrap code)))

and elab_head env pos l raw =
  match raw with
  | Atom (_,n) -> let x = var env l n in (env,res_of env x,V.CVar x,Fun.id)
  | _ ->
      let demand = if pos = Erased then Fixed else CallableHead in
      let env,r,code = elab_expr1 ~demand env (under pos Many) raw in
      let state = match r.term with Var x -> (entry env x).state | _ -> Dyn in
      let x,env = bind env ~word:true ~temporary:true None r.erasure state r.ty ~rule:r.term in
      let env = match r.place with Some p -> at_merge env (Var x) p | None -> env in
      (env,res_of env x,V.CVar x,fun body -> V.CLet ([x],code,body))

and elab_call ?(unique = false) cc env ?tele expect l callee hcode lv params rets args arg =
  let pos = pos_of expect in
  if pos <> Erased && callee.erasure = Erased then error l "erased function %s called in a non-erased position" (show env callee.term);
  if unique && pos <> Erased && callee.erasure = Many then error l "a shared UniqueFn is callable only erased";
  let env = match callee.term with Var x -> use env l (under pos (if unique then Unique else Many)) x | _ -> env in
  let annotation, args =
    let rec go i acc = function
      | List (_, [ k; p ]) :: rest when is_special env k Sp.Predates && i = 0 -> (Some (`Predates p), List.rev_append acc rest)
      | List (_, [ k; p ]) :: rest when is_special env k Sp.Subterm -> (Some (`Subterm (i, p)), List.rev_append acc rest)
      | a :: rest -> go (i + 1) (a :: acc) rest
      | [] -> (None, List.rev acc)
    in
    go 0 [] args
  in
  let env, acc, codes, wrap = check_args env l ~bind_args:true ?expect:tele ~result:(fun mvars -> instantiate_tele mvars rets) ~pos params args arg in
  let arg_terms = List.rev acc in
  let subterm_params = List.filter_map (fun (i, e) -> if e.subterm then Some i else None) (List.mapi (fun i e -> (i, e)) params) in
  let counterpart k = match List.nth_opt env.subterms k with Some x -> x | None -> error l "the enclosing function has no subterm parameter at position %d" k in
  let proof env prove = function Atom (_, "_") -> let env, p = prove env in (env, p.term) | p -> elab_erased env p in
  let same cur = equal (canon env lv) (canon env (Var cur)) in
  let annotation =
    let wild = Atom (l, "_") in
    let differs j pi = match List.nth_opt env.subterms j with Some x -> not (equal (canon env (List.nth arg_terms pi)) (canon env (Var x))) | None -> false in
    match (env.level, annotation) with
    | At cur, None when same cur -> (
        match List.find_opt (fun (j, pi) -> differs j pi) (List.mapi (fun j pi -> (j, pi)) subterm_params) with
        | Some (_, i) -> Some (`Subterm (i, wild))
        | None -> error l "same-level call to %s decreases no subterm argument" (show env callee.term))
    | At _, None -> Some (`Predates wild)
    | _ -> annotation
  in
  let env =
    match (env.level, annotation) with
    | Top, None -> env
    | Top, Some _ -> error l "the top level calls without proofs; drop the decrease annotation (section 24)"
    | At cur, Some (`Subterm (i, p)) when same cur -> (
        let k = match find_index (( = ) i) subterm_params with Some k -> k | None -> error l "argument %d is not a subterm parameter" i in
        List.iteri (fun j pi -> if j < k then check_equal env l (List.nth arg_terms pi) (Var (counterpart j))) subterm_params;
        let env, p = proof env (fun env -> prove_subterm env l (List.nth arg_terms i) (Var (counterpart k))) p in
        match expect_proof env l Prelude.subterm p with
        | [ _; a; _; b ] -> check_equal env l a (List.nth arg_terms i); check_equal env l b (Var (counterpart k)); env
        | _ -> assert false)
    | At cur, Some (`Predates p) when not (same cur) -> (
        let callee_level env = match canon env lv with Var m -> m | t -> error l "%s is not a variable" (show env t) in
        let env, p = proof env (fun env -> prove_predates env l (callee_level env) cur) p in
        match expect_proof env l Prelude.predates p with
        | [ _; x; l2 ] ->
            check_equal env l l2 (Var cur);
            if not (equal (canon env x) (canon env lv)) then
              error l "%s : %s does not relate the callee's level %s" (show env p) (show env (infer env l p)) (show env lv);
            env
        | _ -> assert false)
    | At cur, _ ->
        let kind, ann, other = if same cur then ("same", "subterm", "predates") else ("lower", "predates", "subterm") in
        error l "%s-level call to %s takes a (%s p) annotation, not (%s p)" kind (show env callee.term) ann other
  in
  let env, ids = open_tele env ~word:false ~names:(anon rets) ~mults:(List.map (fun e -> under pos e.mult) rets) ~ids:acc rets in
  count_check l expect ids;
  let code =
    if pos = Erased then V.CErased else
    let _, physical, returned = List.fold_left2 (fun (acc, physical, returned) (e : entry) x ->
      let place = Option.map (instantiate acc) e.place in
      (Var x :: acc, (if e.mult <> Erased && e.place = None then x :: physical else physical),
       (x, place) :: returned)) (acc, [], []) rets ids in
    let results = List.filter_map (fun (m, (x, place)) -> if m = Erased then None else
      Some (V.CVar (match place with Some (SlotHolds p) -> location_var env l p | None -> x | Some _ -> assert false)))
      (List.combine expect (List.rev returned)) in
    V.CLet (List.rev physical, V.CApp (hcode, codes, cc), V.CValues results)
  in
  (env, List.map (res_of env) ids, wrap code)

and elab_special demand tele env expect l sp args =
  let pos = pos_of expect in
  let m =
    if List.mem sp (Sp.CellMatch :: Sp.Values :: Sp.Match :: Sp.OpenAbsurd :: Sp.Tail :: Sp.Delegate :: Sp.statements) then pos
    else match expect with [ m ] -> m | _ -> error l "%s produces one value" (Sp.name sp)
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
          (env, Some [ { name = None; subterm = false; mult = Erased; place = None;
            sg = Ty (proof_type ctor [sa; Var a; Var x; sb; Var b; Var y]) } ]) in
    let env, p, _ = elab_expr1 ?tele env Erased raw in
    settle_res env l p;
    (env, expect_proof env l ctor p.term) in
  let erased (env, r) = (env, [ r ], V.CErased) in
  let mint env ty =
    let env = match expected_type env with Some want -> solve "type" env l ty want | None -> env in
    erased (mint env (metaless env ty)) in
  let side env raw =
    if wild raw then let x, env = bind env ~meta:true None Erased Dyn Prelude.sharing_term in (env, Var x)
    else let env, t = elab_term env raw in check_type env l (infer env l t) Prelude.sharing_term; (env, t) in
  let fetch what x found = match found with Some y -> erased (env, res_of env y) | None -> error l "%s has no %s" (name_of env x) what in
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
  | Sp.SlotVacant, [] ->
      (env, [ { term = SlotHolds (Var Prelude.null); ty = Prelude.slot_term; erasure = pos; place = None } ], if pos = Erased then V.CErased else V.CConst V.VToken)
  | Sp.SlotHolds, [ a ] ->
      let x = var env (loc a) (atom_or (loc a) a "a direct variable reference") in
      if (entry env x).mult = Erased then error (loc a) "SlotHolds needs a declared non-erased variable";
      if List.mem x env.signature then error (loc a) "SlotHolds cannot name a telescope binder; abstract over a Slot instead";
      (env, [ { term = SlotHolds (Var x); ty = Prelude.slot_term; erasure = pos; place = None } ], if pos = Erased then V.CErased else V.CVar x)
  | Sp.CellAlloc, [ raw ] ->
      let c, items = match raw with List (_, c :: ss) -> (c, Some ss) | Atom _ -> (raw, None) | _ -> error l "malformed cell-alloc" in
      let c = ctor_var env l c in
      let ct, _, _ = cell_shape env l c in
      let env, slots, writes, wrap = cell_items env pos l (List.init ct.V.arity (fun _ -> SlotHolds (Var Prelude.null)))
        (Option.value items ~default:(List.init ct.arity (fun _ -> Atom (l,"_")))) in
      let values = List.init ct.arity (fun i -> Option.value (List.assoc_opt i writes) ~default:(V.CConst V.VToken)) in
      let x, env = bind env None (under pos Unique) Dyn (Cell (Var c, slots)) in
      (env, [ { (res_of env x) with place = None } ], if pos = Erased then V.CErased else wrap (V.CCellAlloc (ct, values)))
  | Sp.CellWrite, [ u; List (_, c :: items) ] ->
      let env, r, input = elab_expr1 env (under pos Unique) u in
      let input_id = fresh () in
      let code = V.CVar input_id in
      let c = ctor_var env l c in
      let existing, slots = match canon env r.ty with Cell (Var c, ss) -> c, ss | _ -> error l "cell-write needs a Cell" in
      check_equal env l (Var c) (Var existing);
      let ct, _, _ = cell_shape env l c in
      let env, slots, writes, wrap = cell_items env pos l slots items in
      let x, env = bind env None (under pos Unique) Dyn (Cell (Var c, slots)) in
      let env = match r.place with Some p -> at_merge env (Var x) p | None -> env in
      (env, [ { (res_of env x) with place = r.place } ], if pos = Erased then V.CErased else V.CLet ([input_id], input, wrap (V.CCellWrite (ct, code, writes))))
  | Sp.CellMatch, _ -> elab_cell_match ~demand tele env expect l args
  | Sp.At, [ List (_, head :: args) ] ->
      let env, h, hcode, wrap = elab_head env pos l head in
      let env,rs,code = match canon env h.ty with
       | Cell (c, slots) -> elab_cell_invoke ~full:true env expect l h hcode c slots args
       | _ -> error l "at wraps a Cell invocation" in
      (env,rs,wrap code)
  | Sp.Share, [ a ] ->
      if pos = Erased then error l "share in an erased position";
      let env, r, code = match a with
        | Atom (al, n) ->
            let x = var env al n in
            if (entry env x).mult <> Unique then error al "share needs a unique value";
            (use env al ~sharing:true Many x, res_of env x, V.CVar x)
        | _ -> elab_expr1 env Unique a
      in
      (env, [ { r with erasure = Many } ], code)
  | Sp.Values, _ ->
      count_check l expect args;
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
  | Sp.Match, _ -> elab_match ~demand tele env expect l args
  | (Sp.Tail | Sp.Delegate), [ (List _ as call) ] ->
      if pos = Erased then error l "%s in an erased position" (Sp.name sp);
      let cc = if sp = Sp.Tail then V.Tail else V.Delegate in
      let env, ress, code = elab_expr ~demand ~cc ?tele env expect call in
      let rec has_call c = (match c with V.CApp (_, _, cc') -> cc' = cc | _ -> false) || List.exists has_call (V.subcodes c) in
      if not (has_call code) then error l "%s marks a function call, not %s" (Sp.name sp) (Reader.show call);
      (env, ress, code)
  | Sp.MatchableOf, [ t ] ->
      let x, _, _ = find_matchable env l (tyname env l t) in
      (env, [ res_of env x ], matchable_code env m x)
  | Sp.OpenAbsurd, [ e; ann ] ->
      let env', x, t, _ = open_binding env l Erased e in
      (match open_adt env' x with
      | _ -> error l "open-absurd: opening %s contradicts nothing" (show env' t)
      | exception Contradiction _ -> ());
      let env, ann_tele = result_tele ~demand tele env expect l ann in
      let env, ids = open_tele env ~word:false ~names:(anon ann_tele) ann_tele in
      (env, List.map (res_of env) ids, if pos = Erased then V.CErased else V.CAbsurd)
  | Sp.NumeralOf, [ e ] -> (
      let name = atom_or l e "a literal" in
      match Literal.classify name with
      | `Bad msg -> error l "%s" msg
      | `Name -> error l "numeral-of takes a literal, not %s" name
      | `Lit lit -> (
          match List.assoc_opt (Literal.key lit) env.literals with
          | Some (_, Some p) -> erased (env, res_of env p)
          | Some (_, None) -> error l "%s is a string literal, which carries no Numeral proof" name
          | None -> error l "literal %s is not in scope" name))
  | Sp.Distinct, [ a; b ] -> elab_distinct env l a b
  | Sp.LevelOf, [ f ] -> (
      let env, f = elab_term env f in
      settle env l f;
      match canon env (infer env l f) with
      | Fn (lv, _, _) | UniqueFn (lv, _, _) -> erased (env, { term = lv; ty = Prelude.level_term; erasure = Erased; place = None })
      | ty -> error l "level-of: %s : %s is not a function" (show env f) (show env ty))
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
  | Sp.Coerce, [ a; p ] -> (
      let env, p = proof env Prelude.coercible p in
      match p with
      | [ sa; _; a'; sb; b_ty; b ] ->
          let src = if pos = Erased then Erased else sharing_mult env l sa in
          let dst = if pos = Erased then Erased else sharing_mult env l sb in
          let env, a, code = elab_expr1 env src a in
          settle_res env l a;
          check_equal env l a.term a';
          let x, env = bind env None dst Dyn b_ty ~rule:b in
          let env = match a.place with Some p -> at_merge env (Var x) p | None -> env in
          (env, [ { (res_of env x) with place = a.place } ], code)
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
      if newtype_of env c = None then error l "%s has no opened newtype Matchable for its wrapping constructor" (name_of env c);
      let env, acc = elab_term_args env l params (Var c) args in
      List.iter (settle env l) acc;
      let e, f = List.find (fun (e, _) -> e.mult <> Erased) (List.combine params (List.rev acc)) in
      let src = if e.mult = Unique then s else Prelude.shared_term in
      mint env (proof_type Prelude.coercible [ src; infer env l f; f; s; instantiate acc ret; App (Var c, List.rev acc) ]))
  | Sp.CoercibleCtor, s :: c :: args ->
      let env, s = side env s in
      let env = match expected_sides env with Some (sa,_) -> solve "sharing" env l s sa | None -> env in
      let c = ctor_var env l c in
      let params, ret = ctor_type env l c in
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
        | _ -> error l "coercible-ctor: wrong number of arguments for %s" (name_of env c) in
      let env, src, tgt = go env [] [] params args in
      mint env (proof_type Prelude.coercible [ s; instantiate src ret; App (Var c, List.rev src); s; instantiate tgt ret; App (Var c, List.rev tgt) ])
  | Sp.CoercibleOf, [ d ] -> (
      let env, d = proof ?sides:(expected_sides env) env Prelude.delegate d in
      match d with
      | [ sg; gty; g; sf; fty; f ] -> mint env (proof_type Prelude.coercible [ sg; gty; g; sf; fty; f ])
      | _ -> assert false)
  | Sp.DelegateOf, [ g ] ->
      let g = named env l "a function name" g in
      let about x = (entry env x).name = None && (match type_of env x with App (Var c, [ _; _; Var g'; _; _; _ ]) -> c = Prelude.delegate && g' = g | _ -> false) in
      fetch "delegate proof in scope" g (List.find_opt about env.scope.ids)
  | sp, _ when List.mem sp Sp.statements -> error l "%s is a statement, not an expression" (Sp.name sp)
  | sp, _ -> error l "malformed %s form" (Sp.name sp)

and cell_items env pos l slots items =
  if List.length slots <> List.length items then error l "expected %d slot items" (List.length slots);
  let env, slots, writes, bindings = List.fold_left2 (fun (env, ss, ws, bs) (i, old) item ->
    if wild item then (env, old :: ss, ws, bs) else
    let env, r, code = elab_expr1 env (under pos Many) item in
    check_type env l r.ty Prelude.slot_term;
    settle_res env l r;
    let x = fresh () in
    (env, r.term :: ss, (i, V.CVar x) :: ws, (x, code) :: bs)) (env, [], [], []) (List.mapi (fun i s -> i,s) slots) items in
  (env, List.rev slots, List.rev writes, fun body -> List.fold_left (fun b (x,c) -> V.CLet ([x], c, b)) body bindings)

and elab_cell_invoke ?(full = false) env expect l h hcode ctor slots args =
  let pos = pos_of expect in
  let c = match canon env ctor with Var c -> c | _ -> error l "Cell constructor is not a variable" in
  let ct, params, ret = cell_shape env l c in
  let env = match h.term with Var x -> use env l (under pos Unique) x | _ -> env in
  if pos <> Erased && h.erasure <> Unique then error l "Cell invocation needs a unique cell";
  let rec marks mark args = match args with
    | List (_, [a]) :: rest when is_special env a Sp.At -> marks true rest
    | a :: rest -> (mark, a) :: marks false rest
    | [] -> if mark then error l "at must precede an argument" else [] in
  let marked = marks false args in
  let raw = List.map snd marked in
  let arg env m a tele = elab_expr1 ?tele env (field_under pos m) a in
  let env, acc, codes, wrap = check_args env l ~bind_args:true ~result:(ctor_result (Var c)) ~pos ~boundary:false params raw arg in
  let _, writes = List.fold_left2 (fun (i, writes) ((e : entry), t) (skip, _) ->
    if e.mult = Erased then (if skip then error l "at cannot mark an erased argument"; (i, writes)) else
    let same = equal (canon env (List.nth slots i)) (canon env (SlotHolds t)) in
    if (full || skip) && not same then error l "at argument %d is not in its slot's location class" (i+1);
    (i+1, if full || skip then writes else (i, List.nth codes i) :: writes)) (0, []) (List.combine params (List.rev acc)) marked in
  let code = if pos = Erased then V.CErased else if writes = [] then hcode else V.CCellWrite (ct, hcode, List.rev writes) in
  (env, [{term = App (Var c, List.rev acc); ty = instantiate acc ret; erasure = pos; place = h.place}], wrap code)

and elab_cell_match ?(demand = Fixed) tele env expect l args =
  match args with
  | m :: u :: ann :: List (pl, c :: names) :: body ->
      if pos_of expect = Erased then error l "cell-match in an erased position";
      let mode = mult_or env l m in
      let env, r, code = elab_expr1 env mode u in
      let c = ctor_var env pl c in
      let c', slots = match canon env r.ty with Cell (Var c, ss) -> c, ss | _ -> error l "cell-match needs a Cell" in
      check_equal env l (Var c) (Var c');
      let ct, _, _ = cell_shape env l c in
      let needed = ct.V.arity + if mode = Unique then 1 else 0 in
      if List.length names <> needed then error pl "cell-match needs %d binders" needed;
      let env, ann_tele = result_tele ~demand tele env expect l ann in
      let expect = match demand with Fixed -> expect | _ -> List.map (fun e -> e.mult) ann_tele in
      let sid, env = bind env ~word:true ~temporary:true None mode Dyn r.ty ~rule:r.term in
      let env = match r.place with Some p -> at_merge env (Var sid) p | None -> env in
      let envb, ids = List.fold_left_map (fun env n -> let x, env = bind env ~word:true (name_or_anon (atom_or pl n "a slot binder")) Many Dyn Prelude.slot_term in (env,x)) env (List.filteri (fun i _ -> i < ct.arity) names) in
      let envb = merge_opens (unify_force (forcing envb) (Cell (Var c,List.map (fun x -> Var x) ids)) (Cell (Var c,slots))) in
      let envb, back = if mode <> Unique then (envb, None) else
        let x, envb = bind envb ~word:true (name_or_anon (atom_or pl (List.nth names ct.arity) "a cell binder")) Unique Dyn r.ty ~rule:r.term in
        (at_merge envb (Var x) (Var sid), Some x) in
      let envb, rs, body = elab_body ~tele:ann_tele envb expect l body in
      check_results envb l ann_tele rs;
      let body = match back with None -> body | Some x -> V.CLet ([x], V.CVar sid, body) in
      let body = List.fold_right (fun (i,x) b -> V.CLet ([x], V.CCellRead (ct, i, V.CVar sid), b)) (List.mapi (fun i x -> i,x) ids) body in
      let env = {env with uses = envb.uses} in
      let env, result_ids = open_tele env ~word:false ~names:(anon ann_tele) ann_tele in
      (env, List.map (res_of env) result_ids, V.CLet ([sid], code, body))
  | _ -> error l "malformed cell-match"

and scrutinee env l smult scrut =
  let env, sres, scode = elab_expr1 env smult scrut in
  settle_res env l sres;
  let tid = match type_head env sres.ty with Some t -> t | None -> error l "cannot match on %s : %s" (show env sres.term) (show env sres.ty) in
  let mid, disc, ctors = find_matchable env l tid in
  let env = if smult = Erased then env else (held_needs_many env l tid mid; use env l Many mid) in
  if smult = Erased then (env,sres,scode,Fun.id,tid,mid,disc,ctors) else
  let x, env = bind env ~word:true ~temporary:true None smult Dyn sres.ty ~rule:sres.term in
  let env = match sres.place with Some p -> at_merge env (Var x) p | None -> env in
  (env,res_of env x,V.CVar x,(fun body -> V.CLet ([x],scode,body)),tid,mid,disc,ctors)

and elab_match ?(demand = Fixed) tele env expect l args =
  match args with
  | m :: scrut :: ann :: branches ->
      let pos = pos_of expect in
      let smult = written pos l "a match" (mult_or env l m) in
      let env, sres, scode, swrap, tid, mid, disc, ctors = scrutinee env l smult scrut in
      let extra = smult = Unique && cells_allowed env mid in
      let branch_uses = ref env.uses in
      let shapes = shapes env l ctors in
      let tagged = tagged disc shapes in
      if pos <> Erased && smult <> Erased then held_needs_many env l tid mid;
      let env, ann_tele = result_tele ~demand tele env expect l ann in
      let expect = match demand with Fixed -> expect | _ -> List.map (fun e -> e.mult) ann_tele in
      let enter bl c names =
        let phantom = marker env bl tid ctors c = Erased in
        let tele, ret = ctor_type env bl c in
        let mults = List.map (fun e -> if phantom then Erased else field_under smult e.mult) tele in
        let envb, fids = open_tele { env with run_pos = false } ~names:(names tele) ~mults tele in
        (phantom, fids, envb, try Some (at bl (fun () -> refine envb sres c fids ret)) with Contradiction _ -> None)
      in
      let branch raw =
        let kind, pat, body =
          match raw with
          | List (_, [ a; (Atom _ as c) ]) when is_special env a Sp.Absurd -> (`Auto, c, [])
          | List (_, a :: pat :: body) when is_special env a Sp.Absurd -> (`Proof, pat, body)
          | List (_, pat :: body) -> (`Present, pat, body)
          | _ -> error (loc raw) "malformed branch"
        in
        let bl = loc pat in
        let c, fs = match pat with Atom _ -> (pat, []) | List (_, c :: fs) -> (c, fs) | _ -> error bl "malformed pattern" in
        let c = ctor_var env bl c in
        let extra = extra && marker env bl tid ctors c <> Erased in
        let fs, name = if kind = `Auto then (fs, if extra then Some None else None) else split_cell_pattern env bl extra fs in
        let phantom, fids, envb, forced = enter bl c (fun tele -> if kind = `Auto then anon tele else field_names env bl c tele fs) in
        let forced, cell = match forced with
          | None -> (None,None)
          | Some e -> let e,x = pattern_cell e bl (if phantom then Erased else smult) sres c fids name in (Some e,x) in
        let unreachable = phantom && smult <> Erased in
        let result =
          match (kind, forced) with
          | `Auto, None -> `Absurd
          | `Auto, Some _ -> error bl "branch %s is not refuted" (name_of env c)
          | _, None -> error bl "branch %s is refuted; write (absurd %s)" (name_of env c) (name_of env c)
          | `Present, Some envb ->
              let envb = { envb with usage_erased = envb.usage_erased || unreachable } in
              let envb, ress, code = elab_body ~tele:ann_tele envb (if unreachable then List.map (fun _ -> Erased) expect else expect) bl body in
              check_results envb bl ann_tele ress;
              if not unreachable then branch_uses := join_uses !branch_uses envb.uses;
              `Present (bind_cell scode cell code)
          | `Proof, Some envb -> ignore (elab_absurd envb bl body); `Absurd
        in
        (c, non_erased envb fids, unreachable, result)
      in
      let elses, branches = List.partition (function List (_, a :: _) when is_special env a Sp.Else -> true | _ -> false) branches in
      let branches = List.map branch branches in
      List.iter
        (fun (_, c) ->
          match List.length (List.filter (fun (c', _, _, _) -> Var c' = c) branches) with
          | 0 | 1 -> ()
          | n -> error l "constructor %s has %d branches" (show env c) n)
        ctors;
      let covered =
        List.filter_map
          (fun (_, c) ->
            let c = match c with Var c -> c | _ -> assert false in
            if List.exists (fun (c', _, _, _) -> c' = c) branches then None
            else
              let phantom, _, _, forced = enter l c anon in
              if Option.is_none forced then None else Some (c, phantom && smult <> Erased))
          ctors
      in
      let reachable = List.filter_map (fun (c, unreachable) -> if unreachable then None else Some c) covered in
      let else_ =
        match elses with
        | [] ->
            (match covered with [] -> () | (c, _) :: _ -> error l "constructor %s has 0 branches" (name_of env c));
            None
        | [ List (el, _ :: body) ] ->
            if covered = [] then error el "else covers no constructor";
            let envb = { env with run_pos = false; usage_erased = env.usage_erased || reachable = [] } in
            let envb, cell, body = if not extra then (envb,None,body) else match body with
              | n :: body ->
                  let x, envb = bind envb ~word:true (name_or_anon (atom_or el n "a unique else binder")) smult Dyn sres.ty ~rule:sres.term in
                  let envb = match sres.place with Some p -> at_merge envb (Var x) p | None -> envb in
                  (envb,Some x,body)
              | [] -> error el "a unique else needs its binder and body" in
            let envb, ress, code = elab_body ~tele:ann_tele envb (if reachable = [] then List.map (fun _ -> Erased) expect else expect) el body in
            check_results envb el ann_tele ress;
            if reachable <> [] then branch_uses := join_uses !branch_uses envb.uses;
            if reachable = [] then None else Some (bind_cell scode cell code)
        | _ :: dup :: _ -> error (loc dup) "a match has at most one else branch"
        | _ -> error l "a match has at most one else branch"
      in
      let real =
        List.filter_map (fun (c, fids, unreachable, r) -> match r with `Present code when not unreachable -> Some (c, fids, code) | _ -> None) branches
      in
      if pos <> Erased && ((not tagged) || smult = Erased) && List.length real + List.length (Option.to_list else_) > 1 then
        error l "a match without a runtime discriminant can have only one real branch";
      let code =
        match (real, else_) with
        | _ when pos = Erased -> V.CErased
        | [], None -> V.CAbsurd
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
      (env, List.map (res_of env) result_ids, swrap code)
  | _ -> error l "malformed match"

(* A match's or open-absurd's return annotation: a telescope of the position's size, or _ for the enclosing one. *)
and result_tele ?(demand = Fixed) tele env expect l ann =
  let env, ann_tele =
    match (ann, tele) with
    | Atom (_, "_"), Some tele ->
        if List.exists (fun e -> has_meta env (sg_term e.sg)) tele then error l "the telescope _ would reuse still has a _ to infer";
        (env, tele)
    | Atom (_, "_"), None -> error l "no telescope to reuse for _"
    | List (_, ann), _ ->
        let mults i = function
          | Some _ -> error l "a match annotation carries no multiplicities"
          | None -> (match List.nth_opt expect i with Some m -> Some m | None -> error l "match annotation has more than the %d entries the position needs" (List.length expect))
        in
        let env', _, ann_tele = elab_tele env ~places:true ~contextual:true ~mults ~holes:true ann in
        let env = { env' with scope = env.scope } in
        let env = match tele with Some tele when List.length tele = List.length ann_tele -> solve_tele ~strict:true env l tele ann_tele | _ -> env in
        List.iter (fun e -> settle env l (sg_term e.sg)) ann_tele;
        (env, List.map (fun e -> { e with sg = map_sg (metaless env) e.sg }) ann_tele)
    | _ -> error l "malformed match annotation"
  in
  if List.length ann_tele <> List.length expect then error l "match annotation has %d entries, position needs %d" (List.length ann_tele) (List.length expect);
  let ann_tele = List.map (fun e ->
    let mult = match demand with
      | Fixed -> e.mult
      | _ -> demanded env demand e.mult (match e.sg with Ty t -> t | Is t -> infer env l t) in
    { e with mult }) ann_tele in
  (env, ann_tele)

(* An anonymous let at [mult] of a Matchable: the entry an open records (section 19). *)
and open_binding env l mult raw =
  let inner, r, code = elab_expr1 env mult raw in
  settle_res inner l r;
  (match canon inner r.ty with Matchable _ -> () | ty -> error l "%s : %s is not a Matchable" (show inner r.term) (show inner ty));
  let value = if env.run_pos && mult <> Erased then List.hd (run_code inner code) else V.VToken in
  let state = if env.run_pos then Const value else match r.term with Var y -> (entry inner y).state | _ -> Dyn in
  let x, env' = bind inner None mult state r.ty ~rule:r.term in
  (env', x, r.term, code)

and elab_body ?tele env expect l items =
  let env, wrap, final = elab_stmts (pos_of expect) env l items in
  let env, ress, code = elab_expr ?tele env expect final in
  (env, ress, wrap code)

(* The statements before a body's final expression, and the code they wrap around what follows them. *)
and elab_stmts spos env l = function
  | [] -> error l "a body needs a final expression"
  | [ final ] -> (env, Fun.id, final)
  | stmt :: rest ->
      let env, wrap = elab_stmt spos env stmt in
      let env, wrap', final = elab_stmts spos env l rest in
      (env, (fun code -> wrap (wrap' code)), final)

and elab_absurd env l body =
  let env, ress, _ = elab_body { env with usage_erased = true } [ Erased ] l body in
  settle_res env l (single l ress);
  check_empty env l (single l ress).ty;
  env

and refine env scrut c fids ret =
  let env = match scrut.place, newtype_of env c, non_erased env fids with
    | Some p, Some _, [ x ] -> at_merge env p (Var x)
    | _ -> env in
  let fvars = List.rev_map (fun x -> Var x) fids in
  merge_opens (unify_force (unify_force (forcing env) scrut.term (App (Var c, List.rev fvars))) scrut.ty (instantiate fvars ret))

and elab_stmt spos env raw : Env.t * (V.code -> V.code) =
  match raw with
  | List (l, head :: args) -> (
      let env = if special_of env head <> None then read_special spos env head else env in
      match (special_of env head, args) with
      | Some Sp.Let, _ -> elab_let spos env l args
      | Some Sp.DefLvl, [ n ] ->
          let _, env = mint_level env (name_or_anon (atom_or l n "a name")) in
          (env, Fun.id)
      | Some Sp.DefFns, _ -> elab_def_fns env l args
      | Some Sp.DefUnique, _ -> elab_def_fns ~unique:true env l args
      | Some Sp.DefAdts, _ -> elab_def_adts env args
      | Some Sp.ComptimeMatch, _ -> elab_comptime_match env l args
      | Some Sp.LetMatch, _ -> elab_let_match spos env l args
      | Some Sp.Unary, _ -> elab_unary spos env l args
      | Some Sp.OpenAdt, [ m; e ] ->
          let mult = mult_or env l m in
          let env', x, t, code = open_binding env l mult e in
          let env' = try open_adt env' x with Contradiction msg -> error l "open-adt: %s contradicts what is open (%s)" (show env' t) msg in
          (env', if env.run_pos || mult = Erased then Fun.id else fun rest -> V.CLet ([ x ], code, rest))
      | _ -> error l "%s is not a statement" (Reader.show raw))
  | _ -> error (loc raw) "%s is not a statement" (Reader.show raw)

and run_code env code = Eval.eval env.values code

(* Binders that all carry a type or an is clause are the telescope the right-hand side is expected to
   produce (SUGAR.md 6); the check of each binder against its value stays as it was. The right-hand side's
   statements are statements of the enclosing expression: their code wraps the let's own, and their entries
   stay in scope after it, anonymously (section 16). *)
and elab_let spos env l args =
  let binder_raws, rhs =
    match args with
    | List (_, bs) :: rhs when List.for_all (function List _ -> true | _ -> false) bs -> (bs, rhs)
    | _ -> error l "malformed let: expected (let (<binder> ...) <value> ...)"
  in
  let binders = List.concat_map (parse_entry env) binder_raws in
  let expect = List.map (fun b -> match b.s_mult with Some m -> m | None -> error b.s_loc "let binder needs a multiplicity") binders in
  let env, tele =
    if binders <> [] && List.for_all (fun b -> b.s_sg <> None) binders then
      let env', _, t = elab_tele env ~holes:true binder_raws in
      ({ env' with scope = env.scope }, Some t)
    else (env, None)
  in
  let after, wrap, final = elab_stmts spos env l rhs in
  let inner, ress, code = elab_expr ?tele after expect final in
  let values = if env.run_pos && pos_of expect <> Erased then run_code inner code else [] in
  let bind_one (env, ids, acc) (i, ((b, r), v)) =
    let env =
      match (tele, b.s_sg) with
      | Some t, _ -> solve_sg env b.s_loc (map_sg (instantiate acc) (List.nth t i).sg) r
      | None, Some s -> let env, sg = elab_sg env s in solve_sg env b.s_loc sg r
      | None, None -> env
    in
    settle_res env b.s_loc r;
    let state = if env.run_pos then Const v else match r.term with Var y -> (entry env y).state | _ -> Dyn in
    if b.s_place <> None then error b.s_loc "at is allowed only on return and match annotation entries";
    let x, env = bind env ~word:true (name_or_anon b.s_name) (Option.get b.s_mult) state r.ty ~rule:r.term in
    let env = match r.place with Some p -> at_merge env (Var x) p | None -> env in
    (env, x :: ids, r.term :: acc)
  in
  let env', ids, _ =
    List.fold_left bind_one (hide inner env, [], []) (List.mapi (fun i x -> (i, x)) (List.combine (List.combine binders ress) (spread expect values)))
  in
  let ids = non_erased env' (List.rev ids) in
  (env', if env.run_pos then Fun.id else fun rest -> wrap (if pos_of expect = Erased then rest else V.CLet (ids, code, rest)))

(* A match on a one-constructor type chooses nothing, so what it learns holds wherever the scrutinee does
   and its fields bind outward (section 16's reason for comptime-match, without a discriminant to verify). *)
(* Runs a literal's statements (Literal.source) in the prelude's scope, once per program. *)
and hoist env lit =
  let key = Literal.key lit in
  if List.mem_assoc key env.literals then env
  else
    let parts = match lit with Literal.Char c -> [ Literal.Numeral (Z.of_int c) ] | Literal.Str s -> Literal.chars s | Literal.Numeral _ -> [] in
    let env = List.fold_left hoist env parts in
    let frame = List.fold_left (fun env item -> fst (elab_stmt Many env item)) { env with scope = env.prelude } (Reader.parse "<literal>" (Literal.source lit)) in
    let entry =
      match (lit, frame.scope.ids) with
      | Literal.Numeral _, proof :: value :: _ -> (value, Some proof)
      | Literal.Char c, char :: _ -> (char, snd (List.assoc (Z.to_string (Z.of_int c)) env.literals))
      | Literal.Str _, str :: _ -> (str, None)
      | _ -> assert false
    in
    let facts = match lit with Literal.Str _ -> IntMap.add (fst entry) { (fact frame (fst entry)) with rule = None } frame.facts | _ -> frame.facts in
    { frame with scope = env.scope; facts; literals = (key, entry) :: frame.literals }

(* [unary] and [distinct] elaborate to calls on the prelude's Numeral lemmas, in the prelude's scope so
   user shadowing cannot reach them; the level context, and so [predates _], stays the caller's. *)
and elab_unary spos env l args =
  let za, _ = numeral_entry env l (List.hd args) in
  let lo =
    match args with
    | [ _ ] -> Z.zero
    | [ _; b ] ->
        let zb, _ = numeral_entry env l b in
        if Z.geq zb za then error l "unary: %s does not exceed %s" (Z.to_string za) (Z.to_string zb);
        zb
    | _ -> error l "unary takes one or two literals"
  in
  let k = Z.sub za lo in
  if Z.gt k (Z.of_int 4096) then error l "unary: %s successors is beyond the limit" (Z.to_string k);
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
  let za, xa = numeral_entry env l a and zb, xb = numeral_entry env l b in
  if Z.equal za zb then error l "distinct: %s is the same literal twice" (Z.to_string za);
  if not (equal (canon env (Var xa)) (canon env (Var xb))) then
    error l "distinct: %s and %s do not canonicalize equally here" (Z.to_string za) (Z.to_string zb);
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
  | [ m; scrut; List (pl, c :: fields) ] ->
      let smult = written spos l "a let-match" (mult_or env l m) in
      let env, sres, scode, swrap, tid, mid, disc, ctors = scrutinee env l smult scrut in
      let c = ctor_var env pl c in
      if marker env pl tid ctors c = Erased && smult <> Erased then error pl "%s is phantom" (name_of env c);
      (* Test each alternative before introducing the selected constructor's facts.
         Trial fields and refinements stay local, exactly as for omitted match branches. *)
      List.iter
        (fun (cmult, other) ->
          let other = match other with Var x -> x | _ -> assert false in
          if other <> c then (
            let tele, ret = ctor_type env l other in
            let mults = List.map (fun e -> if cmult = Erased then Erased else field_under smult e.mult) tele in
            let trial, fids = open_tele { env with run_pos = false } ~names:(anon tele) ~mults tele in
            let possible = try ignore (at l (fun () -> refine trial sres other fids ret)); true with Contradiction _ -> false in
            if possible then
              error l "constructor %s is not refuted, so %s needs an ordinary match" (name_of env other) (name_of env tid)))
        ctors;
      let tele, ret = ctor_type env pl c in
      let fields, name = split_cell_pattern env pl (smult = Unique && cells_allowed env mid) fields in
      let names = field_names env pl c tele fields in
      let mults = List.map (fun e -> field_under smult e.mult) tele in
      let shapes = shapes env l ctors in
      let run = env.run_pos && smult <> Erased in
      let value = if run then Some (List.hd (run_code env (swrap scode))) else None in
      let env = match value,sres.term with Some v, Var x -> set_state env x (Const v) | _ -> env in
      let states = Option.map (fun v -> snd (const_fields env pl c mults v)) value in
      let env, fids = open_tele env ~names ~mults ?states tele in
      let env = at l (fun () -> try refine env sres c fids ret with Contradiction msg -> error l "the scrutinee contradicts the facts in force (%s)" msg) in
      let env, cell = pattern_cell env pl smult sres c fids name in
      ( env,
        if smult = Erased || run then Fun.id
        else fun rest -> swrap (
          V.CMatch
            { scrut = scode; shape = match_shape env mid tid disc shapes;
              branches = [ (Option.get (discriminant shapes c), non_erased env fids, bind_cell scode cell rest) ]; default = None;
              live = Option.to_list (discriminant shapes c) }))
  | _ -> error l "malformed let-match: expected (let-match <multiplicity> x (C field ...))"

and elab_comptime_match env l args =
  match args with
  | [ m; x; List (pl, c :: fields) ] ->
      let smult = mult_or env l m in
      if smult = Erased then error l "comptime-match needs a non-erased multiplicity";
      if not env.run_pos then error l "comptime-match is a run-position statement (section 15)";
      let x, sharing =
        match x with
        | List (_, [ h; a ]) when special_of env h = Some Sp.Share ->
            let y = var env l (atom_or l a "a variable") in
            if (entry env y).mult <> Unique then error l "share needs a unique value";
            if smult = Unique then error l "many value %s used at unique" (name_of env y);
            (y, true)
        | _ -> (var env l (atom_or l x "a variable"), false)
      in
      let env = use env l ~sharing smult x in
      let value = match entry env x with { state = Const v; mult = (Many | Unique); _ } -> v | _ -> error l "comptime-match needs a Const, non-erased scrutinee" in
      let c = ctor_var env pl c in
      let tele, ret = ctor_type env pl c in
      let tid = match type_head env (type_of env x) with Some t -> t | None -> error l "scrutinee is not a datatype value" in
      let mid, disc, ctors = find_matchable env l tid in
      if adt_of env mid = None then error l "the Matchable for %s is not Const, so comptime-match cannot consult it" (name_of env tid);
      let env = use env l Many mid in
      if disc = Union then error l "comptime-match needs a non-erased discriminant";
      if marker env pl tid ctors c = Erased then error pl "comptime-match: %s is phantom, so no non-erased value is headed by it" (name_of env c);
      let mults = List.map (fun e -> field_under smult e.mult) tele in
      let matched, states = const_fields env pl c mults value in
      if not matched then error l "comptime-match: expected %s, got %s" (name_of env c) (show_value env l (type_of env x) value);
      let fields, name = split_cell_pattern env pl (smult = Unique && cells_allowed env mid) fields in
      let names = field_names env pl c tele fields in
      let env, fids = open_tele env ~names ~mults ~states tele in
      let env = at l (fun () -> try refine env (res_of env x) c fids ret with Contradiction msg -> error l "internal: the verified value contradicts the facts in force (%s)" msg) in
      let env, _ = pattern_cell env pl smult (res_of env x) c fids name in
      (env, Fun.id)
  | _ -> error l "malformed comptime-match: expected (comptime-match <multiplicity> x (C field ...))"

and elab_def_fns ?(unique = false) env l args =
  match args with
  | [] -> error l "def-fns needs a level"
  | lv :: fns ->
      if unique && List.length fns <> 1 then error l "def-unique defines exactly one function";
      let env, lvl =
        match lv with
        | Atom (_, "_") -> let x, env = mint_level env None in (env, x)
        | _ -> level_var env l lv
      in
      let header raw =
        match raw with
        | List (_, List (fl, m :: rest) :: body) -> (
            let mult = mult_or env fl m in
            let marks, rest = marks env [ Sp.Absurd; Sp.Extern ] rest in
            match rest with
            | n :: colon :: sg when is_special env colon Sp.Colon ->
                let ps, rs = split_arrow env fl sg in
                let name = atom_or fl n "a function name" in
                let ty = elab_fn_type ~unique env (Var lvl) ps rs in
                let many_params = match ty with Fn (_, ps, _) | UniqueFn (_, ps, _) -> List.length (List.filter (fun e -> e.mult <> Erased) ps) | _ -> 0 in
                let impl =
                  if List.mem Sp.Extern marks then Some (Ffi.claim_fn fl name many_params) else None
                in
                (fl, name, mult, List.mem Sp.Absurd marks, impl, ty, body)
            | _ -> error fl "malformed function header")
        | _ -> error (loc raw) "malformed function definition: expected ((<multiplicity> <name> : ... -> ...) <body> ...)"
      in
      let headers = List.map header fns in
      List.iter (fun (fl, _, m, _, _, _, _) -> if unique && m = Many then error fl "def-unique requires unique or erased" else if not unique && m = Unique then error fl "use def-unique to define a unique function") headers;
      let capture_uses = ref env.uses in
      let env, fids = List.fold_left_map (fun env (_, name, mult, _, _, ty, _) -> let x, env = bind env ~word:true (Some name) mult Dyn ty in (env, x)) env headers in
      let define x (fl, name, mult, absurd, impl, ty, body) =
        let params, rets = match ty with Fn (_, ps, rs) | UniqueFn (_, ps, rs) -> (ps, rs) | _ -> assert false in
        let envb = if unique then { env with entries = IntMap.add x { (entry env x) with mult = Erased } env.entries } else env in
        let envb, pids = open_tele envb params in
        let subterms = List.filter_map (fun (e, x) -> if e.subterm then Some x else None) (List.combine params pids) in
        let envb = { envb with level = At lvl; subterms; run_pos = false; in_extern = env.in_extern || impl <> None; usage_erased = env.usage_erased || mult = Erased; captures = (if unique then env.captures else env.scope.ids @ env.captures) } in
        let envb, code =
          if absurd then (elab_absurd envb fl body, V.CAbsurd)
          else
            let pvars = List.rev_map (fun x -> Var x) pids in
            let tele = instantiate_tele pvars rets in
            let envb, ress, code = elab_body ~tele envb (List.map (fun e -> under mult e.mult) rets) fl body in
            check_results envb fl ~ids:pvars rets ress;
            (envb, if mult = Erased then V.CErased else project_code (List.filter_map (fun e -> if e.mult = Erased then None else Some (e.place = None)) rets) code)
        in
        capture_uses := join_uses !capture_uses (IntMap.filter (fun x _ -> IntMap.mem x env.entries) envb.uses);
        let code, delegated = check_marks envb fl pids code in
        ((x, { V.fname = name; params = non_erased envb pids; body = code; impl }), Option.map (fun callee -> (x, ty, callee)) delegated)
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
      if env.run_pos then
        let values = Eval.close env.values fns in
        trace := Fns fns :: !trace;
        (List.fold_left (fun env (x, _) -> set_state env x (Const (IntMap.find x values))) env fns, Fun.id)
      else
        let fns = List.filter (fun (x, _) -> (entry env x).mult <> Erased) fns in
        (env, if fns = [] then Fun.id else fun rest -> V.CLetRec (fns, rest))

(* Validates the tail/delegate marks in a body (section 9), returning the delegated callee if any. Lets that only
   rename (all a coerce leaves), return exactly what they bind, or bind constants nothing mentions (a nested
   def-adts the body never reads) are first folded away, so a marked call stands in tail position in the code
   that runs. *)
and check_marks env l pids code =
  let non_erased = non_erased env in
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
  let code = norm [] code in
  let rec marked acc c = List.fold_left marked (match c with V.CApp (_, _, (V.Tail | V.Delegate)) -> c :: acc | _ -> acc) (V.subcodes c)
  in
  let rec tails ~direct = function
    | V.CApp (_, _, (V.Tail | V.Delegate)) as c -> [ c ]
    | V.CLet (_, _, rest) | V.CLetRec (_, rest) -> if direct then [] else tails ~direct rest
    | V.CMatch m -> if direct then [] else List.concat_map (tails ~direct) (List.map (fun (_, _, c) -> c) m.V.branches @ Option.to_list m.V.default)
    | _ -> []
  in
  ( code,
    match marked [] code with
    | [] -> None
    | marks ->
        let delegate = List.exists (function V.CApp (_, _, V.Delegate) -> true | _ -> false) marks in
        let ok = tails ~direct:delegate code in
        List.iter (fun c -> if not (List.memq c ok) then error l "a %s-marked call is not in tail position" (if delegate then "delegate" else "tail")) marks;
        if not delegate then None
        else
          match ok with
          | [ V.CApp (V.CVar f, args, _) ] ->
              if vars_of args <> non_erased pids then error l "a delegate call must pass the function's non-erased parameters straight through";
              Some (Var f)
          | _ -> error l "delegate needs exactly one call to a named function" )

and elab_def_adts env adts =
  let header raw =
    match raw with
    | List (_, List (al, n :: colon :: sg) :: d :: rest) when is_special env colon Sp.Colon -> (
        let ps, ret = split_arrow env al sg in
        match ret with
        | [ ty ] -> let ms, ctors = marks env [ Sp.NewtypeMark; Sp.Extern ] rest in (al, atom_or al n "a type constructor name", ps, ty, disc_of env al d, ms, ctors)
        | _ -> error al "a type constructor declares one return")
    | _ -> error (loc raw) "malformed def-adts entry: expected ((<name> : ... -> Type) enum ...)"
  in
  let headers = List.map header adts in
  let env, tids =
    List.fold_left_map
      (fun env (al, name, ps, ty, _, _, _) ->
        let x, env = bind env (Some name) Erased (const env V.VToken) (elab_tyctor env al ps [ ty ]) in
        (env, x))
      env headers
  in
  let define (env, cids) tid (al, name, _, _, disc, ms, ctors) =
    let ctor env raw =
      match raw with
      | List (cl, m :: n :: colon :: rest) when is_special env colon Sp.Colon ->
          let mult = mult_or env cl m in
          if mult = Unique then error cl "a constructor declaration cannot be unique";
          let name = atom_or cl n "a constructor name" in
          let env', tele, ret, ty = elab_valctor env cl rest in
          (match canon env' ret with App (Var t, _) when t = tid -> () | _ -> error cl "%s must return an application of %s" name (name_of env tid));
          if mult = Erased && List.exists (fun e -> e.mult <> Erased) tele then warn_at cl "phantom constructor %s has a non-erased field" name;
          let c, env = bind env (Some name) mult (if mult = Erased then const env V.VToken else Dyn) ty in
          (env, (mult, c))
      | _ -> error (loc raw) "malformed constructor"
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
    if List.mem Sp.NewtypeMark ms && wrapper disc shapes = None then error al "%s is not of newtype shape (section 38)" name;
    (env, cids @ values @ [ (mid, V.VMatchable adt) ])
  in
  let env, cids = List.fold_left2 define (env, []) tids headers in
  (env, if env.run_pos then Fun.id else fun rest -> V.CLet (List.map fst cids, V.CValues (List.map (fun (_, v) -> V.CConst v) cids), rest))

let rec literals = function
  | Atom (l, s) -> (match Literal.classify s with `Lit x -> [ x ] | `Bad msg -> error l "%s" msg | `Name -> [])
  | List (_, items) -> List.concat_map literals items

let run_toplevel ?(consume = fun _ _ v -> print_endline (V.show v)) ?(path = "-") env items =
  let rec go env = function
    | [] -> env
    | item :: rest -> (
        let env = List.fold_left hoist env (literals item) in
        at (loc item) (fun () ->
            if rest = [] && not (is_statement env item) then (
              let env, ress, code = elab_expr ~demand:Driver env [ Many ] item in
              settle_res env (loc item) (single (loc item) ress);
              let ty = (single (loc item) ress).ty and v = List.hd (run_code env code) in
              trace := Final (v, ty, path) :: !trace;
              consume env ty v;
              env)
            else (
              if not (is_statement env item) then error (loc item) "only the last top-level form may be an expression";
              go (fst (elab_stmt Many env item)) rest)))
  in
  go env items
