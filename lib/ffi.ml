open Value

(* The prototype's fixed FFI (section 41): implementations by name for extern-marked prelude definitions, which are
   their models. Integers are zarith's. *)

let registered : (string, adt) Hashtbl.t = Hashtbl.create 8
let claimed : (string, Reader.loc) Hashtbl.t = Hashtbl.create 8

(* Every declared type by name, the first declaration winning, for an implementation that builds a plain type's
   values (nat-cmp's Cmp). *)
let adts : (string, adt) Hashtbl.t = Hashtbl.create 8
let note name adt = if not (Hashtbl.mem adts name) then Hashtbl.replace adts name adt
let reset () = Hashtbl.reset registered; Hashtbl.reset claimed; Hashtbl.reset adts

(* An implementation together with everything its declaration is checked against, so that one cannot be registered
   without its arity, the plain types it builds or reads, or the shape its view has. *)
type fn_spec = { takes : int; needs : string list; run : value list -> value list }
type ty_spec = { shape : int list; view : adt -> ext }

let arity = Eval.Runtime "extern arity"
let z = function VExt (_, Int n) -> n | v -> raise (Eval.Runtime ("not an extern integer: " ^ show v))
let slice = function VExt (_, Slice (s, o, l)) -> (s, o, l) | v -> raise (Eval.Runtime ("not an extern string: " ^ show v))
let array = function VExt (_, Array a) -> a | v -> raise (Eval.Runtime ("not an extern array: " ^ show v))
let int name n = VExt (Hashtbl.find registered name, Int n)
let text sl = VExt (Hashtbl.find registered "String", Slice sl)
let arr a = VExt (Hashtbl.find registered "Array", Array a)

let plain name i args = construct (ctor_at (Hashtbl.find adts name) i) args

(* The interpreter's construction and matching of an extern type, through lib/ffi_core.ml's one-level view. *)
let bad name v = raise (Eval.Runtime (Printf.sprintf "not a %s: %s" name (show v)))
let des = function VCtor (c, fs) -> (c.index, Array.to_list fs) | v -> bad "constructor" v
let view shape view = { shape; view }
let types : (string * ty_spec) list =
  let nat adt n = VExt (adt, Int n) in
  [ ( "Array",
      view [0; 2] (fun adt ->
        let wrap a = VExt (adt, Array a) in
        { construct = (fun i args -> Ffi_core.array_of ~array ~wrap (match i,args with 0,[] -> ANil | 1,[x;tl] -> ACons (x,tl) | _ -> raise arity));
          destruct = (fun v -> match Ffi_core.array_view ~array ~wrap v with ANil -> 0,[] | ACons(x,tl) -> 1,[x;tl]) }));
    ( "Nat",
      view [ 0; 1 ] (fun adt ->
          { construct = (fun i args -> Ffi_core.nat_of ~z ~nat:(nat adt) (match (i, args) with 0, [] -> Zero | 1, [ p ] -> Succ p | _ -> raise arity));
            destruct = (fun v -> match Ffi_core.nat_view ~z ~nat:(nat adt) v with Zero -> (0, []) | Succ p -> (1, [ p ])) }) );
    ( "Half",
      view [ 0; 1; 1 ] (fun adt ->
          { construct = (fun i args -> Ffi_core.half_of ~z ~nat:(nat adt) (match (i, args) with 0, [] -> HZ | 1, [ m ] -> H1 m | 2, [ m ] -> H2 m | _ -> raise arity));
            destruct = (fun v -> match Ffi_core.half_view ~z ~nat:(int "Nat") v with HZ -> (0, []) | H1 m -> (1, [ m ]) | H2 m -> (2, [ m ])) }) );
    ( "String",
      view [ 0; 2 ] (fun adt ->
          let str s = VExt (adt, Slice s) in
          { construct = (fun i args -> Ffi_core.str_of ~z ~slice ~str (match (i, args) with 0, [] -> SNil | 1, [ c; r ] -> SCons (c, r) | _ -> raise arity));
            destruct = (fun v -> match Ffi_core.str_view ~slice ~u8:(int "Nat") ~str v with SNil -> (0, []) | SCons (c, r) -> (1, [ c; r ])) }) ) ]

let unary f = function [ a ] -> [ f a ] | _ -> raise arity
let binary f = function [ a; b ] -> [ f a b ] | _ -> raise arity
let nats name f = binary (fun a b -> int name (f (z a) (z b)))
let quotient f = function [ a; b ] -> let q, r = f (z a) (z b) in [ int "Nat" q; int "Nat" r ] | _ -> raise arity
let tag name get f = binary (fun a b -> plain name (Obj.magic (f (get a) (get b)) : int) [])

let spec ?(needs = []) takes run = { takes; needs; run }
let swap = function [ a; i; x ] -> [ Ffi_core.array_swap (array a) (z i) x ] | _ -> raise arity
let place = function [ a; i; x ] -> Ffi_core.array_place (array a) (z i) x; [] | _ -> raise arity
let get = spec ~needs:["Array"] 2 (binary (fun a i -> Ffi_core.array_get (array a) (z i)))
let length = spec ~needs:["Array"] 1 (unary (fun a -> int "Nat" (Ffi_core.array_length (array a))))
let fns : (string * fn_spec) list =
  [ ("array-new", spec ~needs:["Array"] 1 (unary (fun n -> arr (Ffi_core.array_new ~blank:VToken (z n)))));
    ("array-make", spec ~needs:["Array"] 2 (binary (fun n x -> arr (Ffi_core.array_make (z n) x))));
    ("array-swap", spec ~needs:["Array"] 3 swap);
    ("array-swap-imm", spec ~needs:["Array"] 3 swap);
    ("array-pluck", spec ~needs:["Array"] 2 (binary (fun a i -> Ffi_core.array_pluck (array a) (z i))));
    ("array-get", get);
    ("array-get-many", get);
    ("array-place", spec ~needs:["Array"] 3 place);
    ("array-place-imm", spec ~needs:["Array"] 3 place);
    ("array-length", length);
    ("array-length-many", length);
    ("list-to-array", spec ~needs:["Array"; "List"] 1 (unary (fun l -> arr (Ffi_core.list_to_array ~list:(fun v -> match des v with 0, [] -> Nil | 1, [ x; rest ] -> Cons (x, rest) | _ -> bad "list node" v) l))));
    ("add", spec 2 (nats "Nat" Ffi_core.add));
    ("sub", spec 2 (nats "Nat" Ffi_core.sub));
    ("mul", spec 2 (nats "Nat" Ffi_core.mul));
    ("div", spec 2 (nats "Nat" Ffi_core.div));
    ("divmod", spec 2 (quotient Ffi_core.divmod));
    ("nat-cmp", spec ~needs:[ "Cmp" ] 2 (tag "Cmp" z Ffi_core.nat_cmp));
    ("lt-dec", spec ~needs:[ "Dec" ] 2 (tag "Dec" z Ffi_core.lt_dec));
    ("str-cmp", spec ~needs:[ "Cmp" ] 2 (tag "Cmp" slice Ffi_core.str_cmp));
    ("str-length", spec 1 (unary (fun a -> int "Nat" (Ffi_core.str_length (slice a)))));
    ("str-split", spec 2 (function [ a; b ] -> let x, y = Ffi_core.str_split (slice a) (z b) in [ text x; text y ] | _ -> raise arity));
    ("nat-str", spec 1 (unary (fun a -> text (Ffi_core.nat_str (z a)))));
    ("nat-mod", spec 2 (nats "Nat" Ffi_core.nat_mod));
    ("shl", spec 2 (nats "Nat" Ffi_core.shl));
    ("shr", spec 2 (nats "Nat" Ffi_core.shr));
    ("u62-add", spec 2 (nats "Nat" Ffi_core.u62_add));
    ("u62-sub", spec 2 (nats "Nat" Ffi_core.u62_sub));
    ("u62-mul", spec 2 (nats "Nat" Ffi_core.u62_mul));
    ("u62-div", spec 2 (nats "Nat" Ffi_core.u62_div));
    ("u62-mod", spec 2 (nats "Nat" Ffi_core.u62_mod));
    ("u62-divmod", spec 2 (quotient Ffi_core.u62_divmod));
    ("u62-shl", spec 2 (nats "Nat" Ffi_core.u62_shl));
    ("u62-shr", spec 2 (nats "Nat" Ffi_core.u62_shr));
    ("u62-cmp", spec ~needs:[ "Cmp" ] 2 (tag "Cmp" z Ffi_core.u62_cmp));
    ("u62-lt-dec", spec ~needs:[ "Dec" ] 2 (tag "Dec" z Ffi_core.u62_lt_dec));
    ("nat-halve", spec ~needs:[ "Half" ] 1 (unary (fun a -> int "Half" (Ffi_core.nat_halve (z a)))));
    ("trim", spec 1 (unary (fun s -> text (Ffi_core.trim (slice s)))));
    ("append", spec 2 (binary (fun a b -> text (Ffi_core.append (slice a) (slice b)))));
    ("flatten", spec ~needs:[ "Rope" ] 1 (unary (Ffi_core.flatten ~slice ~z ~str:text ~rope:(fun v -> match des v with 0, [] -> REmpty | 1, [ s ] -> RStr s | 2, [ a; b ] -> RCat (a, b) | 3, [ c ] -> RChar c | _ -> bad "rope node" v)))) ]

(* The shape an implementation's view has (lib/ffi_core.ml), which its model must have too: whether tagged and
   the non-erased-field arities of the non-phantom constructors in order, since the extracted program lays the view
   out as the model's own type. A plain type the implementations touch records its shape here instead. *)
let plain_shapes = [ ("Cmp", [ 0; 0; 0 ]); ("Dec", [ 0; 0 ]); ("Rope", [ 0; 1; 2; 1 ]); ("List", [ 0; 2 ]) ]
let spell ns = String.concat " " (List.map string_of_int ns)
let check_shape loc name adt =
  let ns = List.map (fun (c : ctor) -> c.arity) adt.ctors in
  let want =
    match List.assoc_opt name types with
    | Some t -> t.shape
    | None -> ( match List.assoc_opt name plain_shapes with Some s -> s | None -> Env.error loc "the FFI records no shape for %s" (Env.tick name))
  in
  if (not adt.tagged) || ns <> want then
    Env.error loc "the extern implementation of %s has the tagged shape (%s), its declaration %s(%s)" (Env.tick name) (spell want) (if adt.tagged then "" else "the untagged ") (spell ns);
  try Ffi_templates.check name ns with Failure m -> Env.error loc "%s" m

(* Each implementation may back one declaration per program. A function's model must take as many non-erased
   arguments as its implementation does, and the plain types the implementation builds or reads must be declared
   already, in the implementation's shape; both are checked before the binding, so a mismatched redeclaration of a
   name the prelude already bound still reports the mismatch. *)
let bind loc name =
  Option.iter
    (fun l -> Env.error_with loc [ (l, "the declaration that bound it") ] "the extern implementation of %s is already bound" (Env.tick name))
    (Hashtbl.find_opt claimed name);
  Hashtbl.replace claimed name loc

let claim_fn loc name n =
  match List.assoc_opt name fns with
  | None -> Env.error loc "no extern implementation for %s" (Env.tick name)
  | Some spec ->
      if spec.takes <> n then Env.error loc "the extern implementation of %s takes %d arguments, its model %d" (Env.tick name) spec.takes n;
      List.iter
        (fun t -> match Hashtbl.find_opt adts t with Some adt -> check_shape loc t adt | None -> Env.error loc "the extern implementation of %s needs %s declared before it" (Env.tick name) (Env.tick t))
        spec.needs;
      (try Ffi_templates.check_fn name n with Failure m -> Env.error loc "%s" m);
      bind loc name;
      spec.run

let claim_type loc name adt =
  match List.assoc_opt name types with
  | None -> Env.error loc "no extern implementation for %s" (Env.tick name)
  | Some spec -> check_shape loc name adt; bind loc name; Hashtbl.replace registered name adt; spec.view adt
