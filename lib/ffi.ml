open Value

(* The prototype's fixed FFI (section 42): implementations by name for extern-marked prelude definitions, which are
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
type fn_spec = { takes : int; needs : string list; decides : string option; run : value list -> value list }
type ty_spec = { shape : int list; view : adt -> ext }

let arity = Eval.Runtime "extern arity"
let z = function VWord n -> n | v -> raise (Eval.Runtime ("not an extern integer: " ^ show v))
let slice = function VExt (_, Slice (s, o, l)) -> (s, o, l) | v -> raise (Eval.Runtime ("not an extern string: " ^ show v))
let array = function VExt (_, Array a) -> a | v -> raise (Eval.Runtime ("not an extern array: " ^ show v))
let int n = VWord n
let text sl = VExt (Hashtbl.find registered "String", Slice sl)
let bytes = function VExt (_, Bytes b) -> b | v -> raise (Eval.Runtime ("not an extern byte buffer: " ^ show v))
let arr a = VExt (Hashtbl.find registered "Array", Array a)
let buf b = VExt (Hashtbl.find registered "Bytes", Bytes b)
let slots = function VExt (_, Slots t) -> t | v -> raise (Eval.Runtime ("not an extern slot table: " ^ show v))

let plain name i args = construct (ctor_at (Hashtbl.find adts name) i) args

let host v = let s, o, n = slice v in String.sub s o n
let pos = function Ffi_core.NoPos -> plain "Pos" 0 [] | MkPos (f, l, c) -> plain "Pos" 1 [ f; l; c ]
let list = function Ffi_core.Nil -> plain "List" 0 [] | Cons (x, r) -> plain "List" 1 [ x; r ]
let symbol = function Ffi_core.SName s -> plain "Symbol" 0 [ s ] | SGen (n, s) -> plain "Symbol" 1 [ n; s ]

(* The interpreter's construction and matching of an extern type, through lib/ffi_core.ml's one-level view. *)
let bad name v = raise (Eval.Runtime (Printf.sprintf "not a %s: %s" name (show v)))
let des name v = match dispatch None (Hashtbl.find adts name) v with Some r -> r | None -> bad "constructor" v
let unpos v = match des "Pos" v with 0, [] -> Ffi_core.NoPos | 1, [ f; l; c ] -> MkPos (f, l, c) | _ -> bad "Pos" v
let unlist v = match des "List" v with 0, [] -> Ffi_core.Nil | 1, [ x; r ] -> Cons (x, r) | _ -> bad "List" v
let unsymbol v = match des "Symbol" v with 0, [ s ] -> Ffi_core.SName s | 1, [ n; s ] -> SGen (n, s) | _ -> bad "Symbol" v
let view shape view = { shape; view }
let types : (string * ty_spec) list =
  let cons_view build view_ = view [0; 2] (fun adt ->
    { construct = (fun i args -> build adt (match i,args with 0,[] -> Ffi_core.ANil | 1,[x;tl] -> ACons (x,tl) | _ -> raise arity));
      destruct = (fun v -> match view_ adt v with Ffi_core.ANil -> 0,[] | ACons(x,tl) -> 1,[x;tl]) }) in
  let in_array adt a = VExt (adt, Array a) and in_bytes adt b = VExt (adt, Bytes b) in
  [ ("Array", cons_view (fun adt -> Ffi_core.array_of ~array ~wrap:(in_array adt)) (fun adt -> Ffi_core.array_view ~array ~wrap:(in_array adt)));
    ("Bytes", cons_view (fun adt -> Ffi_core.bytes_of ~z ~bytes ~wrap:(in_bytes adt)) (fun adt -> Ffi_core.bytes_view ~bytes ~u8:(int) ~wrap:(in_bytes adt)));
    ( "Slots",
      view [ 1 ] (fun adt ->
          { construct = (fun _ args -> match args with [ l ] -> Ffi_core.slots_of ~list:unlist ~wrap:(fun t -> VExt (adt, Slots t)) (MkSlots l) | _ -> raise arity);
            destruct = (fun v -> let (MkSlots l) = Ffi_core.slots_view ~slots ~list v in (0, [ l ])) }) );
    ( "Nat",
      view [ 0; 1 ] (fun _ ->
          { construct = (fun i args -> Ffi_core.nat_of ~z ~nat:int (match (i, args) with 0, [] -> Zero | 1, [ p ] -> Succ p | _ -> raise arity));
            destruct = (fun v -> match Ffi_core.nat_view ~z ~nat:int v with Zero -> (0, []) | Succ p -> (1, [ p ])) }) );
    ( "Half",
      view [ 0; 1; 1 ] (fun _ ->
          { construct = (fun i args -> Ffi_core.half_of ~z ~nat:int (match (i, args) with 0, [] -> HZ | 1, [ m ] -> H1 m | 2, [ m ] -> H2 m | _ -> raise arity));
            destruct = (fun v -> match Ffi_core.half_view ~z ~nat:int v with HZ -> (0, []) | H1 m -> (1, [ m ]) | H2 m -> (2, [ m ])) }) );
    ( "Raw",
      view [ 2; 1; 2; 2 ] (fun adt ->
          let get = function VExt (_, Raw r) -> r | v -> bad "Raw" v in
          { construct = (fun i args -> VExt (adt, Raw (Ffi_core.raw_of ~unhandle:(fun l -> function VHandle (x, r, m, v) -> Ffi_core.Handle (l, x, r, m, Obj.repr v) | v -> bad "Settled" v) ~unsymbol ~text:host ~z ~pos:unpos ~list:unlist ~raw:get (Ffi_core.raw_model i args))));
            destruct = (fun v -> Ffi_core.raw_fields (Ffi_core.raw_view ~handle:(fun (x, r, m, v) -> VHandle (x, r, m, Obj.obj v)) ~symbol ~get ~str:(fun s -> text (s, 0, String.length s)) ~nat:int ~pos ~list ~raw:(fun r -> VExt (adt, Raw r)) v)) }) );
    ( "String",
      view [ 0; 2 ] (fun adt ->
          let str s = VExt (adt, Slice s) in
          { construct = (fun i args -> Ffi_core.str_of ~z ~slice ~str (match (i, args) with 0, [] -> SNil | 1, [ c; r ] -> SCons (c, r) | _ -> raise arity));
            destruct = (fun v -> match Ffi_core.str_view ~slice ~u8:(int) ~str v with SNil -> (0, []) | SCons (c, r) -> (1, [ c; r ])) }) ) ]

let unary f = function [ a ] -> [ f a ] | _ -> raise arity
let binary f = function [ a; b ] -> [ f a b ] | _ -> raise arity
let nats f = binary (fun a b -> int (f (z a) (z b)))
let quotient f = function [ a; b ] -> let q, r = f (z a) (z b) in [ int q; int r ] | _ -> raise arity
let tag name get f = binary (fun a b -> plain name (Obj.magic (f (get a) (get b)) : int) [])

let spec ?(needs = []) ?decides takes run = { takes; needs; decides; run }
let decision name get f = spec ~needs:[ name ] ~decides:name 2 (tag name get f)
let swap = function [ a; i; x ] -> [ Ffi_core.array_swap (array a) (z i) x ] | _ -> raise arity
let place = function [ a; i; x ] -> Ffi_core.array_place (array a) (z i) x; [] | _ -> raise arity
let get = spec ~needs:["Array"] 2 (binary (fun a i -> Ffi_core.array_get (array a) (z i)))
let length = spec ~needs:["Array"] 1 (unary (fun a -> int (Ffi_core.array_length (array a))))
let bytes_get = spec ~needs:["Bytes"] 2 (binary (fun b i -> int (Ffi_core.bytes_get (bytes b) (z i))))
let bytes_length = spec ~needs:["Bytes"] 1 (unary (fun b -> int (Ffi_core.bytes_length (bytes b))))
let fns : (string * fn_spec) list =
  [ ("array-new", spec ~needs:["Array"] 1 (unary (fun n -> arr (Ffi_core.array_new ~blank:vacant (z n)))));
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
    ("array-length-dec", spec ~needs:[ "Array"; "Dec" ] ~decides:"Dec" 1 (unary (fun _ -> plain "Dec" 0 [])));
    ("array-length-dec-many", spec ~needs:[ "Array"; "Dec" ] ~decides:"Dec" 1 (unary (fun _ -> plain "Dec" 0 [])));
    ("list-to-array", spec ~needs:["Array"; "List"] 1 (unary (fun l -> arr (Ffi_core.list_to_array ~list:(fun v -> match des "List" v with 0, [] -> Nil | 1, [ x; rest ] -> Cons (x, rest) | _ -> bad "list node" v) l))));
    ("array-sub", spec ~needs:["Array"] 3 (function [ a; i; n ] -> [ arr (Ffi_core.array_sub (array a) (z i) (z n)) ] | _ -> raise arity));
    ("array-blit", spec ~needs:["Array"] 5 (function [ s; i; d; j; n ] -> Ffi_core.array_blit (array s) (z i) (array d) (z j) (z n); [] | _ -> raise arity));
    ("bytes-sub", spec ~needs:["Bytes"] 3 (function [ b; i; n ] -> [ buf (Ffi_core.bytes_sub (bytes b) (z i) (z n)) ] | _ -> raise arity));
    ("bytes-blit", spec ~needs:["Bytes"] 5 (function [ s; i; d; j; n ] -> Ffi_core.bytes_blit (bytes s) (z i) (bytes d) (z j) (z n); [] | _ -> raise arity));
    ("array-copy", spec ~needs:["Array"] 1 (unary (fun a -> arr (Ffi_core.array_copy (array a)))));
    ("bytes-copy", spec ~needs:["Bytes"] 1 (unary (fun b -> buf (Ffi_core.bytes_copy (bytes b)))));
    ("bytes-make", spec ~needs:["Bytes"] 2 (binary (fun n x -> buf (Ffi_core.bytes_make (z n) (z x)))));
    ("bytes-get", bytes_get);
    ("bytes-get-many", bytes_get);
    ("bytes-set", spec ~needs:["Bytes"] 3 (function [ b; i; x ] -> Ffi_core.bytes_set (bytes b) (z i) (z x); [] | _ -> raise arity));
    ("bytes-length", bytes_length);
    ("bytes-length-many", bytes_length);
    ("bytes-length-dec", spec ~needs:[ "Bytes"; "Dec" ] ~decides:"Dec" 1 (unary (fun _ -> plain "Dec" 0 [])));
    ("bytes-length-dec-many", spec ~needs:[ "Bytes"; "Dec" ] ~decides:"Dec" 1 (unary (fun _ -> plain "Dec" 0 [])));
    ("str-bytes-copy", spec ~needs:["Bytes"] 1 (unary (fun s -> buf (Ffi_core.str_bytes_copy (slice s)))));
    ("bytes-str", spec 1 (unary (fun b -> text (Ffi_core.bytes_str (bytes b)))));
    ("slots-new", spec ~needs:[ "Slots" ] 0 (fun _ -> [ VExt (Hashtbl.find registered "Slots", Slots (Ffi_core.slots_new ())) ]));
    ("slots-find", spec ~needs:[ "Slots"; "SlotFind" ] 2 (binary (fun t s -> match Ffi_core.slots_find (slots t) s with SlotFound i -> plain "SlotFind" 0 [ int (Z.of_int i) ] | SlotMissing -> plain "SlotFind" 1 [])));
    ("slots-intern", spec ~needs:[ "Slots"; "SlotIntern" ] 2 (binary (fun t s -> match Ffi_core.slots_intern (slots t) s with SlotExisting i -> plain "SlotIntern" 0 [ int (Z.of_int i) ] | SlotAdded i -> plain "SlotIntern" 1 [ int (Z.of_int i) ])));
    ("slots-length", spec ~needs:[ "Slots" ] 1 (unary (fun t -> int (Z.of_int (Ffi_core.slots_length (slots t))))));
    ("add", spec 2 (nats Ffi_core.add));
    ("sub", spec 2 (nats Ffi_core.sub));
    ("mul", spec 2 (nats Ffi_core.mul));
    ("div", spec 2 (nats Ffi_core.div));
    ("divmod", spec 2 (quotient Ffi_core.divmod));
    ("nat-cmp", decision "Cmp" z Ffi_core.nat_cmp);
    ("lt-dec", decision "Dec" z Ffi_core.lt_dec);
    ("nat-eq", decision "EqDec" z Ffi_core.nat_eq);
    ("bit-length", spec 1 (unary (fun a -> int (Ffi_core.bit_length (z a)))));
    ("bit-test", decision "Bit" z Ffi_core.bit_test);
    ("str-cmp", decision "Cmp" slice Ffi_core.str_cmp);
    ("str-eq", decision "EqDec" slice Ffi_core.str_eq);
    ("str-length", spec 1 (unary (fun a -> int (Ffi_core.str_length (slice a)))));
    ("str-get", spec 2 (binary (fun a i -> int (Ffi_core.str_get (slice a) (z i)))));
    ("str-split", spec 2 (function [ a; b ] -> let x, y = Ffi_core.str_split (slice a) (z b) in [ text x; text y ] | _ -> raise arity));
    ("nat-str", spec 1 (unary (fun a -> text (Ffi_core.nat_str (z a)))));
    ("str-nat", spec ~needs:[ "Maybe" ] 1 (unary (fun a -> match Ffi_core.str_nat (slice a) with Some n -> plain "Maybe" 1 [ int n ] | None -> plain "Maybe" 0 [])));
    ("nat-mod", spec 2 (nats Ffi_core.nat_mod));
    ("shl", spec 2 (nats Ffi_core.shl));
    ("shr", spec 2 (nats Ffi_core.shr));
    ("nat-and", spec 2 (nats Ffi_core.nat_and));
    ("nat-or", spec 2 (nats Ffi_core.nat_or));
    ("nat-xor", spec 2 (nats Ffi_core.nat_xor));
    ("u62-add", spec 2 (nats Ffi_core.u62_add));
    ("u62-sub", spec 2 (nats Ffi_core.u62_sub));
    ("u62-mul", spec 2 (nats Ffi_core.u62_mul));
    ("u62-div", spec 2 (nats Ffi_core.u62_div));
    ("u62-mod", spec 2 (nats Ffi_core.u62_mod));
    ("u62-divmod", spec 2 (quotient Ffi_core.u62_divmod));
    ("u62-shl", spec 2 (nats Ffi_core.u62_shl));
    ("u62-shr", spec 2 (nats Ffi_core.u62_shr));
    ("u62-and", spec 2 (nats Ffi_core.u62_and));
    ("u62-or", spec 2 (nats Ffi_core.u62_or));
    ("u62-xor", spec 2 (nats Ffi_core.u62_xor));
    ("u62-inc", spec 1 (unary (fun a -> int (Ffi_core.u62_inc (z a)))));
    ("u62-dec", spec 1 (unary (fun a -> int (Ffi_core.u62_dec (z a)))));
    ("u62-cmp", decision "Cmp" z Ffi_core.u62_cmp);
    ("u62-lt-dec", decision "Dec" z Ffi_core.u62_lt_dec);
    ("u62-eq", decision "EqDec" z Ffi_core.u62_eq);
    ("u62-bit-length", spec 1 (unary (fun a -> int (Ffi_core.u62_bit_length (z a)))));
    ("u62-bit-test", decision "Bit" z Ffi_core.u62_bit_test);
    ("nat-halve", spec ~needs:[ "Half" ] 1 (unary (fun a -> int (Ffi_core.nat_halve (z a)))));
    ("trim", spec 1 (unary (fun s -> text (Ffi_core.trim (slice s)))));
    ("append", spec 2 (binary (fun a b -> text (Ffi_core.append (slice a) (slice b)))));
    ("flatten", spec ~needs:[ "Rope" ] 1 (unary (Ffi_core.flatten ~slice ~z ~str:text ~rope:(fun v -> match des "Rope" v with 0, [] -> REmpty | 1, [ s ] -> RStr s | 2, [ a; b ] -> RCat (a, b) | 3, [ c ] -> RChar c | _ -> bad "rope node" v)))) ]

(* The shape an implementation's view has (lib/ffi_core.ml), which its model must have too: whether tagged and
   the non-erased-field arities of the non-phantom constructors in order, since the extracted program lays the view
   out as the model's own type. A plain type the implementations touch records its shape here instead. *)
let plain_shapes = [ ("SlotFind", [ 1; 0 ]); ("SlotIntern", [ 1; 1 ]); ("Cmp", [ 0; 0; 0 ]); ("Dec", [ 0; 0 ]); ("EqDec", [ 0; 0 ]); ("Bit", [ 0; 0 ]); ("Rope", [ 0; 1; 2; 1 ]); ("List", [ 0; 2 ]); ("Maybe", [ 0; 1 ]) ]
let spell ns = String.concat " " (List.map string_of_int ns)
let shape_of name = match List.assoc_opt name types with Some t -> t.shape | None -> List.assoc name plain_shapes
let check_shape loc name adt =
  let ns = List.map (fun (c : ctor) -> c.arity) adt.ctors in
  let want = try shape_of name with Not_found -> Env.error loc "the FFI records no shape for %s" (Env.tick name) in
  let tagged_want = List.length want > 1 in
  if (List.length ns > 1 && not adt.tagged) || ns <> want then
    Env.error loc "the extern implementation of %s has the %sshape (%s), its declaration %s(%s)" (Env.tick name) (if tagged_want then "tagged " else "") (spell want) (if tagged_want && not adt.tagged then "the untagged " else "") (spell ns);
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
      (try Ffi_templates.check_fn name n (Option.map shape_of spec.decides) with Failure m -> Env.error loc "%s" m);
      bind loc name;
      spec.run

let claim_type loc name adt =
  match List.assoc_opt name types with
  | None -> Env.error loc "no extern implementation for %s" (Env.tick name)
  | Some spec -> check_shape loc name adt; bind loc name; Hashtbl.replace registered name adt; spec.view adt

let result_adt name = Option.bind (List.assoc_opt name fns) (fun spec -> Option.bind spec.decides (Hashtbl.find_opt adts))
