open Value

(* The prototype's fixed FFI (section 41): implementations by name for extern-marked prelude definitions, which are
   their models. Integers are zarith's. *)

let registered : (string, adt) Hashtbl.t = Hashtbl.create 8
let claimed : (string, unit) Hashtbl.t = Hashtbl.create 8

(* Every declared type by name, the first declaration winning, for an implementation that builds a plain type's
   values (nat-cmp's Cmp). *)
let adts : (string, adt) Hashtbl.t = Hashtbl.create 8
let note name adt = if not (Hashtbl.mem adts name) then Hashtbl.replace adts name adt
let reset () = Hashtbl.reset registered; Hashtbl.reset claimed; Hashtbl.reset adts

(* Each implementation may back one declaration per program. *)
let claim table loc name =
  match List.assoc_opt name table with
  | None -> Env.error loc "no extern implementation for %s" name
  | Some _ when Hashtbl.mem claimed name -> Env.error loc "the extern implementation of %s is already bound" name
  | Some impl -> Hashtbl.replace claimed name (); impl

(* The shape an implementation's view has (lib/ffi_core.ml), which its model must have too: whether tagged and
   the many-field arities of the non-phantom constructors in order, since the extracted program lays the view
   out as the model's own type. *)
let shapes = [ ("Nat", [ 0; 1 ]); ("String", [ 0; 2 ]); ("Rope", [ 0; 1; 2; 1 ]); ("Cmp", [ 0; 0; 0 ]); ("Half", [ 0; 1; 1 ]) ]
let arities = [ ("add", 2); ("sub", 2); ("mul", 2); ("div", 2); ("divmod", 2); ("nat-cmp", 2); ("nat-mod", 2); ("nat-halve", 1); ("trim", 1); ("append", 2); ("flatten", 1); ("str-cmp", 2); ("str-length", 1); ("str-split", 2); ("nat-str", 1) ]
let needs = [ ("nat-cmp", [ "Cmp" ]); ("str-cmp", [ "Cmp" ]); ("nat-halve", [ "Half" ]); ("flatten", [ "Rope" ]) ]

let spell ns = String.concat " " (List.map string_of_int ns)
let check_shape loc name adt =
  let ns = List.map (fun c -> c.arity) adt.ctors in
  match List.assoc_opt name shapes with
  | Some want when (not adt.tagged) || ns <> want ->
      Env.error loc "the extern implementation of %s has the tagged shape (%s), its declaration %s(%s)" name (spell want) (if adt.tagged then "" else "the untagged ") (spell ns)
  | _ -> ( try Ffi_templates.check name ns with Failure m -> Env.error loc "%s" m)

(* A function's model must take as many non-erased arguments as its implementation does, and the plain types
   the implementation builds or reads must be declared already in the implementation's shape. *)
let check_arity loc name n =
  (match List.assoc_opt name arities with
   | Some m when m <> n -> Env.error loc "the extern implementation of %s takes %d arguments, its model %d" name m n
   | _ -> ());
  List.iter
    (fun t -> match Hashtbl.find_opt adts t with Some adt -> check_shape loc t adt | None -> Env.error loc "the extern implementation of %s needs %s declared before it" name t)
    (Option.value (List.assoc_opt name needs) ~default:[])

let arity = Eval.Runtime "extern arity"
let z = function VExt (_, Int n) -> n | v -> raise (Eval.Runtime ("not an extern integer: " ^ show v))
let slice = function VExt (_, Slice (s, o, l)) -> (s, o, l) | v -> raise (Eval.Runtime ("not an extern string: " ^ show v))
let int name n = VExt (Hashtbl.find registered name, Int n)
let text sl = VExt (Hashtbl.find registered "String", Slice sl)

let plain name i args = construct (ctor_at (Hashtbl.find adts name) i) args

(* The interpreter's construction and matching of an extern type, through lib/ffi_core.ml's one-level view. *)
let bad name v = raise (Eval.Runtime (Printf.sprintf "not a %s: %s" name (show v)))
let des = function VCtor (c, fs) -> (c.index, fs) | v -> bad "constructor" v
let types : (string * (adt -> ext)) list =
  let nat adt n = VExt (adt, Int n) in
  List.map
    (fun (name, mk) -> (name, fun adt -> Hashtbl.replace registered name adt; mk adt))
    [ ( "Nat",
        fun adt ->
          { construct = (fun i args -> Ffi_core.nat_of ~z ~nat:(nat adt) (match (i, args) with 0, [] -> Zero | 1, [ p ] -> Succ p | _ -> raise arity));
            destruct = (fun v -> match Ffi_core.nat_view ~z ~nat:(nat adt) v with Zero -> (0, []) | Succ p -> (1, [ p ])) } );
      ( "Half",
        fun adt ->
          { construct = (fun i args -> Ffi_core.half_of ~z ~nat:(nat adt) (match (i, args) with 0, [] -> HZ | 1, [ m ] -> H1 m | 2, [ m ] -> H2 m | _ -> raise arity));
            destruct = (fun v -> match Ffi_core.half_view ~z ~nat:(int "Nat") v with HZ -> (0, []) | H1 m -> (1, [ m ]) | H2 m -> (2, [ m ])) } );
      ( "String",
        fun adt ->
          let str s = VExt (adt, Slice s) in
          { construct = (fun i args -> Ffi_core.str_of ~z ~slice ~str (match (i, args) with 0, [] -> SNil | 1, [ c; r ] -> SCons (c, r) | _ -> raise arity));
            destruct = (fun v -> match Ffi_core.str_view ~slice ~u8:(int "Nat") ~str v with SNil -> (0, []) | SCons (c, r) -> (1, [ c; r ])) } ) ]

let unary f = function [ a ] -> [ f a ] | _ -> raise arity
let binary f = function [ a; b ] -> [ f a b ] | _ -> raise arity
let nats name f = binary (fun a b -> int name (f (z a) (z b)))
let cmp get f = binary (fun a b -> plain "Cmp" (match f (get a) (get b) with Ffi_core.CLt -> 0 | CEq -> 1 | CGt -> 2) [])

let fns : (string * (value list -> value list)) list =
  [ ("add", nats "Nat" Ffi_core.add);
    ("sub", nats "Nat" Ffi_core.sub);
    ("mul", nats "Nat" Ffi_core.mul);
    ("div", nats "Nat" Ffi_core.div);
    ("divmod", function [ a; b ] -> let q, r = Ffi_core.divmod (z a) (z b) in [ int "Nat" q; int "Nat" r ] | _ -> raise arity);
    ("nat-cmp", cmp z Ffi_core.nat_cmp);
    ("str-cmp", cmp slice Ffi_core.str_cmp);
    ("str-length", unary (fun a -> int "Nat" (Ffi_core.str_length (slice a))));
    ("str-split", function [ a; b ] -> let x, y = Ffi_core.str_split (slice a) (z b) in [ text x; text y ] | _ -> raise arity);
    ("nat-str", unary (fun a -> text (Ffi_core.nat_str (z a))));
    ("nat-mod", nats "Nat" Ffi_core.nat_mod);
    ("nat-halve", unary (fun a -> int "Half" (Ffi_core.nat_halve (z a))));
    ("trim", unary (fun s -> text (Ffi_core.trim (slice s))));
    ("append", binary (fun a b -> text (Ffi_core.append (slice a) (slice b))));
    ("flatten", unary (Ffi_core.flatten ~slice ~z ~str:text ~rope:(fun v -> match des v with 0, [] -> REmpty | 1, [ s ] -> RStr s | 2, [ a; b ] -> RCat (a, b) | 3, [ c ] -> RChar c | _ -> bad "rope node" v))) ]
