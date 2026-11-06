open Term
module V = Value
module IntMap = V.IntMap

let sanitize s = String.map (fun c -> if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') then c else '_') s
let var x = if x < 0 then Printf.sprintf "l%d" (- x) else Printf.sprintf "v%d%s" x (match Hashtbl.find_opt Env.names x with Some (Src n) -> "_" ^ sanitize n | Some (Gen (g, n)) -> "_g" ^ Z.to_string g ^ "_" ^ sanitize n | None -> "")
let concat = String.concat
let params vs = if vs = [] then "()" else concat " " (List.map (fun v -> "(" ^ v ^ " : Obj.t)") vs)
let arrows n = concat " -> " (List.init (max n 1) (fun _ -> if n = 0 then "unit" else "Obj.t") @ [ "Obj.t" ])
let args es = if es = [] then "()" else concat " " es
let obj_tuple n = concat " * " (List.init n (fun _ -> "Obj.t"))
let tuple = function [] -> "(Obj.repr ())" | [ e ] -> e | es -> Printf.sprintf "(Obj.repr (%s))" (concat ", " es)
let untuple vs e body =
  match vs with
  | [] -> body
  | [ v ] -> Printf.sprintf "(let %s = %s in %s)" v e body
  | vs -> Printf.sprintf "(let (%s) = (Obj.obj %s : %s) in %s)" (concat ", " vs) e (obj_tuple (List.length vs)) body
let quote s = "\"" ^ String.escaped s ^ "\""
let quotes ss = "[" ^ String.concat "; " (List.map quote ss) ^ "]"
let z n = Printf.sprintf "(Z.of_string %s)" ("\"" ^ Z.to_string n ^ "\"")
let reading = function Ffi_core.MintedIs -> "Ffi_core.MintedIs" | MintedType -> "Ffi_core.MintedType"
let handle x r m = Printf.sprintf "(%d), %s, Ffi_core.%s" x (reading r) (String.capitalize_ascii (Term.mult_name m))
let handle_ty = "int * Ffi_core.reading * Ffi_core.mult * Obj.t"

let rec raw value r =
  let rec l = function
    | Ffi_core.At { file; line; col } -> Printf.sprintf "(Ffi_core.At { file = %s; line = %s; col = %s })" (quote file) (z line) (z col)
    | NoLoc -> "Ffi_core.NoLoc" | Unknown -> "Ffi_core.Unknown" | Framed (_, p) -> l p in
  match r with
  | Ffi_core.Atom (p, Src s) -> Printf.sprintf "(Ffi_core.Atom (%s, Ffi_core.Src %s))" (l p) (quote s)
  | Ffi_core.Atom (p, Gen (g, s)) -> Printf.sprintf "(Ffi_core.Atom (%s, Ffi_core.Gen (%s, %s)))" (l p) (z g) (quote s)
  | Ffi_core.Handle (p, x, r, m, v) -> Printf.sprintf "(Ffi_core.Handle (%s, %s, %s))" (l p) (handle x r m) (value (Obj.obj v))
  | Nat (p, n) -> Printf.sprintf "(Ffi_core.Nat (%s, %s))" (l p) (z n)
  | Char (p, c) -> Printf.sprintf "(Ffi_core.Char (%s, %d))" (l p) c
  | Str (p, s) -> Printf.sprintf "(Ffi_core.Str (%s, %s))" (l p) (quote s)
  | Wild p -> Printf.sprintf "(Ffi_core.Wild %s)" (l p)
  | List (p, xs) -> Printf.sprintf "(Ffi_core.List (%s, [ %s ]))" (l p) (concat "; " (List.map (raw value) xs))

(* An extern type's unwrap into its model's shape and the wrap back (lib/ffi_core.ml's views), over Obj.t. *)
let externs =
  let view name lower args args' = Printf.sprintf "let des_%s v = Obj.repr (Ffi_core.%s_view %s v)\nlet con_%s v = Ffi_core.%s_of %s (Obj.obj v)" name lower args name lower args' in
  [ ("Array", view "Array" "array" "~array:Obj.obj ~wrap:Obj.repr" "~array:Obj.obj ~wrap:Obj.repr");
    ("Slots", view "Slots" "slots" "~slots:Obj.obj ~list:Obj.repr" "~list:Obj.obj ~wrap:Obj.repr");
    ("Nat", view "Nat" "nat" "~z:Obj.obj ~nat:Obj.repr" "~z:Obj.obj ~nat:Obj.repr");
    ("Half", view "Half" "half" "~z:Obj.obj ~nat:Obj.repr" "~z:Obj.obj ~nat:Obj.repr");
    ("Bytes", view "Bytes" "bytes" "~bytes:Obj.obj ~u8:Obj.repr ~wrap:Obj.repr" "~z:Obj.obj ~bytes:Obj.obj ~wrap:Obj.repr");
    ("String", view "String" "str" "~slice:Obj.obj ~u8:Obj.repr ~str:Obj.repr" "~z:Obj.obj ~slice:Obj.obj ~str:Obj.repr");
    ( "Raw",
      "let des_Raw v = Obj.repr (Ffi_core.raw_view ~handle:Obj.repr ~symbol:Obj.repr ~get:Obj.obj ~str:(fun s -> Obj.repr ((s, 0, String.length s) : Ffi_core.slice)) ~nat:Obj.repr ~pos:Obj.repr ~list:Obj.repr ~raw:Obj.repr v)\n\
       let con_Raw v = Obj.repr (Ffi_core.raw_of ~unhandle:(fun l h -> let x, r, m, v = (Obj.obj h : int * Ffi_core.reading * Ffi_core.mult * Obj.t) in Ffi_core.Handle (l, x, r, m, v)) ~unsymbol:Obj.obj ~text:(fun v -> let (s, o, l) = (Obj.obj v : Ffi_core.slice) in String.sub s o l) ~z:Obj.obj ~pos:Obj.obj ~list:Obj.obj ~raw:Obj.obj (Obj.obj v))" ) ]

type shape = Ext of string | Tagged of int list | Untagged of int list | Union

let arities adt = List.map (fun c -> c.V.arity) adt.V.ctors
let plain_shape adt = if adt.V.ext <> None && !V.use_externs || adt.V.tagged then Tagged (arities adt) else if adt.V.newtype then Untagged (arities adt) else Union
let shape adt = if adt.V.ext <> None && !V.use_externs then Ext adt.tname else plain_shape adt

module IntSet = Set.Make (Int)
module FnTbl = Hashtbl.Make (struct type t = V.fn let equal = ( == ) let hash f = Hashtbl.hash (f.V.fname, f.V.params) end)

(* What a block's code needs from the frame it is defined in: a value it mentions, or the value of a function
   that is reached by name but whose closure must be passed in. *)
type key = KVal of id | KFn of id

(* A `def-fns` block. [heads] pairs each id the code calls with its number of arguments; [uses] and [binders],
   [consts] and [inner] cover the code of the blocks nested in it too, [inner] being their members. *)
type grp = {
  gid : int;
  members : (id * V.fn) list;
  mutable heads : (id * int) list;
  mutable uses : IntSet.t;
  mutable binders : IntSet.t;
  mutable consts : V.value list;
  mutable inner : IntSet.t;
  mutable caps : key list;
  mutable lifted : string list option;
  mutable factory : string option;
  mutable demand : IntSet.t;
  mutable held : IntSet.t;
  mutable deps : grp list;
  mutable needs : cell list;
  mutable insts : inst list;
  mutable adapter : int;
}

(* A value of the data array. [Blank]: a block allocated empty in pass 2 and filled in pass 4; [Leaf] built
   whole in pass 2; [Global] an entry of the globals table; [Member] a closure a factory call builds in pass 3;
   [Expr] built by its own expression in pass 3. *)
and cell = { vid : int; v : V.value; prod : prod; mutable slot : int }
and prod = Blank of int * int | Leaf | Global of int | Member of inst * int | Expr
and inst = { ig : grp; caps_of : V.value list; mutable cells : (int * cell) list; mutable base : int; mutable placed : int }

type cx = {
  env : Env.t;
  adts : V.adt list ref;
  shapes : int list list ref;
  narrows : ((int list * int list) * string) list ref;
  temps : int ref;
  actions : Buffer.t;
  shows : (term * string * string ref) list ref;
  words : Buffer.t;
  posts : (string * V.value) list ref;
  finals : (string * V.value) list ref;
  groups : grp list ref;
  by_member : (id, grp * int) Hashtbl.t;
  by_fn : (grp * int) FnTbl.t;
  cells : (int, (Obj.t * cell) list ref) Hashtbl.t;
  all_cells : cell list ref;
  globals : string list ref;
  global_keys : (Obj.t * int) list ref;
  work : [ `Lifted of grp | `Factory of grp | `Sub of V.value ] Queue.t;
  later : (unit -> string) list ref;
  analysed : bool ref;
  inst_tbl : (int, (V.venv Lazy.t * inst) list ref) Hashtbl.t;
}

(* An extern type's match and builds are its templates (lib/ffi_templates.txt) unless stripped, or where it
   has none, its runtime view; a template's temporaries are numbered per instantiation. *)
let templates = ref true
let reads = ref []
let writes = ref []
let output_bytes = ref None
let with_env = ref true
let with_exec = ref true
let template key = if !templates then Ffi_templates.find key else None
let stamp cx = incr cx.temps; !(cx.temps)
let use_adt cx a = if not (List.memq a !(cx.adts)) then cx.adts := a :: !(cx.adts)

let shape_index cx ns =
  let rec go i = function s :: rest -> if s = ns then i else go (i + 1) rest | [] -> cx.shapes := !(cx.shapes) @ [ ns ]; i in
  go 0 !(cx.shapes)
let type_name cx ns = "t" ^ string_of_int (shape_index cx ns)
let ctor_at cx ns i = Printf.sprintf "K%d_%d" (shape_index cx ns) i
let wide ns = List.length (List.filter (( <> ) 0) ns) > 244
let wide_ctor cx ns = Printf.sprintf "K%d_w" (shape_index cx ns)
let widest ns = List.fold_left max 0 ns

let field_names n = List.init n (fun i -> Printf.sprintf "f%d" i)
let fields c = field_names c.V.arity
let spaced parts = Printf.sprintf "\"(\" ^ %s ^ \")\"" (concat " ^ \" \" ^ " parts)
let pattern_at name fs = if fs = [] then name else Printf.sprintf "%s (%s)" name (concat ", " fs)
let field_binds fs = concat "; " (List.mapi (fun i f -> Printf.sprintf "f%d = %s" i f) fs)
let mutable_fields fs = "{ " ^ field_binds fs ^ " }"
let payload_fields n = concat "; " (List.init n (fun i -> Printf.sprintf "mutable f%d : Obj.t" i))
let mutable_payload n = "{ " ^ payload_fields n ^ " }"
let pattern ?(fill = "_") cx c fs =
  let ns = arities c.V.adt in
  if fs = [] then ctor_at cx ns c.index
  else if wide ns then
    let pad = List.init (widest ns - List.length fs) (fun _ -> fill) in
    Printf.sprintf "%s { d = %d; %s }" (wide_ctor cx ns) c.index (field_binds (fs @ pad))
  else ctor_at cx ns c.index ^ " " ^ mutable_fields fs
let narrow cx ns live =
  let key = (ns, live) in
  match List.assoc_opt key !(cx.narrows) with
  | Some name -> name
  | None ->
      let name = Printf.sprintf "%s_n%d" (type_name cx ns) (List.length !(cx.narrows)) in
      cx.narrows := (key, name) :: !(cx.narrows);
      name

let one_pattern cx n es =
  let k = ctor_at cx [n] 0 in
  if es = [] then k else k ^ " " ^ mutable_fields es

let one_block cx es = Printf.sprintf "(Obj.repr (%s))" (one_pattern cx (List.length es) es)

let bind_args cx es k =
  let n = stamp cx in
  let args = List.mapi (fun i e -> if Ffi_templates.is_name e then (e, None) else (Printf.sprintf "x%d_a%d" n i, Some e)) es in
  let binds = List.filter_map (fun (x, e) -> Option.map (fun e -> x ^ " = " ^ e) e) args in
  let text = k n (List.map fst args) in
  if binds = [] then text else Printf.sprintf "(let %s in %s)" (concat " and " binds) text

let fill_build cx ps es =
  bind_args cx es (fun n names -> "(" ^ Ffi_templates.fill ps ~scrut:(fun () -> assert false) ~temp:(Printf.sprintf "x%d_t%d" n) ~field:(fun _ _ -> assert false) ~body:(fun _ -> assert false) ~arg:(List.nth names) ^ ")")

let build cx c es =
  use_adt cx c.V.adt;
  match shape c.V.adt with
  | Ext name -> (
      match template (Ffi_templates.Build (name, c.index)) with
      | None -> Printf.sprintf "(con_%s (Obj.repr (%s)))" name (pattern cx c es)
      | Some ps -> fill_build cx ps es)
  | Tagged _ -> Printf.sprintf "(Obj.repr (%s))" (pattern ~fill:"(Obj.repr ())" cx c es)
  | Untagged _ -> tuple es
  | Union -> one_block cx es

let dummy n i j = Printf.sprintf "x%d_f%d_%d" n i j

let outcome_arms ?rebind cx a live arms default n =
  let live = List.sort_uniq compare live in
  let arm i = List.find_opt (fun (c, _, _) -> c.V.index = i) arms in
  let field i j = match arm i with Some (_, vs, _) -> List.nth vs j | None -> dummy n i j in
  let built i = let c = V.ctor_at a i in build cx c (List.init c.V.arity (field i)) in
  let at i b = match rebind with None -> b | Some x -> Printf.sprintf "(let %s = %s in %s)" x (built i) b in
  let defaulted = List.filter (fun i -> arm i = None && List.mem i live) (List.init (List.length a.V.ctors) Fun.id) in
  let dflt, thunk =
    match default with
    | Some d when List.length defaulted > 1 ->
        let arg i = if rebind = None then "()" else built i in
        ((fun i -> Printf.sprintf "(x%d_d %s)" n (arg i)), fun t -> Printf.sprintf "(let x%d_d %s = %s in %s)" n (Option.value rebind ~default:"()") d t)
    | Some d -> ((fun i -> at i d), Fun.id)
    | None -> ((fun _ -> "(absurd ())"), Fun.id)
  in
  let body i = match arm i with Some (_, _, b) -> at i b | None -> if List.mem i live then dflt i else "(absurd ())" in
  (body, field, thunk)

let fill_template ?arms cx fname ps es =
  bind_args cx es (fun n names ->
    let body, field, thunk =
      match (arms, Ffi.result_adt fname) with
      | Some k, _ -> k n
      | None, Some a -> outcome_arms cx a [] (List.map (fun c -> let fs = List.init c.V.arity (dummy n c.V.index) in (c, fs, build cx c fs)) a.V.ctors) None n
      | None, None -> ((fun _ -> assert false), (fun _ _ -> assert false), Fun.id) in
    thunk ("(" ^ Ffi_templates.fill ps ~scrut:(fun () -> assert false) ~temp:(Printf.sprintf "x%d_t%d" n) ~field ~body ~arg:(List.nth names) ^ ")"))

let field_match cx c target body =
  let ty, k, rest = match shape c.V.adt with
    | Tagged ns when wide ns -> (type_name cx ns, wide_ctor cx ns, " | _ -> absurd ()")
    | Tagged ns -> ((if List.length ns > 1 then "yes " ^ narrow cx ns [ c.V.index ] else type_name cx ns), ctor_at cx ns c.V.index, "")
    | Union -> let ns = [ c.V.arity ] in (type_name cx ns, ctor_at cx ns 0, "")
    | Untagged _ | Ext _ -> assert false in
  let r = Printf.sprintf "r%d" (stamp cx) in
  Printf.sprintf "(match (Obj.obj %s : %s) with %s %s -> %s%s)" target ty k r (body r) rest

let field_write cx c target stores =
  let imm, barred = List.partition (fun (_, m, _) -> m && !V.use_externs) stores in
  let offset = match shape c.V.adt with Tagged ns when wide ns -> 1 | _ -> 0 in
  let raw = List.map (fun (i, _, s) -> Printf.sprintf "Array.unsafe_set (Obj.obj %s : int array) %d (Obj.obj %s : int)" target (i + offset) s) imm in
  let barred = if barred = [] then [] else [ field_match cx c target (fun r -> concat "; " (List.map (fun (i, _, s) -> Printf.sprintf "%s.f%d <- %s" r i s) barred)) ] in
  concat "; " (barred @ raw)

let field_read cx c i target = field_match cx c target (fun r -> Printf.sprintf "%s.f%d" r i)

(* A fresh block holding [target]'s fields, [stores] in place of theirs (a `cell-write` or an invocation on a
   cell at `many`, section 37). *)
let field_copy cx c target stores =
  if c.V.arity = 0 then build cx c [] else
  let field r i f = match List.find_opt (fun (j, _, _) -> j = i) stores with Some (_, _, s) -> s | None -> r ^ "." ^ f in
  field_match cx c target (fun r -> build cx c (List.mapi (field r) (fields c)))

let cell_block cx c es =
  assert (List.exists (fun k -> k.V.cid = c.V.cid) c.V.adt.ctors);
  build cx c es

(* A match over [a]'s constructors: [arms] pair each constructor with its field names and body, [live] the
   discriminants that can occur, which narrows a tagged type so OCaml drops the others; an extern value is
   unwrapped one level first. *)
let dispatch cx a live scrut arms default =
  use_adt cx a;
  let cases pat = concat " " (List.map (fun (c, vs, body) -> Printf.sprintf "| %s -> %s" (pat c vs) body) arms) in
  let templated = match shape a with Ext name -> template (Ffi_templates.Match name) | _ -> None in
  let scrut = match shape a with Ext name when templated = None -> Printf.sprintf "(des_%s %s)" name scrut | _ -> scrut in
  match templated with
  | Some ps ->
      let n = stamp cx in
      let body, field, thunk = outcome_arms cx a live arms default n in
      let s, bind = if Ffi_templates.is_name scrut then (scrut, Fun.id) else (Printf.sprintf "x%d" n, fun t -> Printf.sprintf "(let x%d = %s in %s)" n scrut t) in
      bind (thunk ("(" ^ Ffi_templates.fill ps ~scrut:(fun () -> s) ~temp:(Printf.sprintf "x%d_t%d" n) ~field ~body ~arg:(fun _ -> assert false) ^ ")"))
  | None ->
  match plain_shape a with
  | Ext _ -> assert false
  | Tagged ns ->
      let live = List.sort_uniq compare live in
      let ty = if List.length live < List.length ns && not (wide ns) then "yes " ^ narrow cx ns live else type_name cx ns in
      let default = if wide ns && default = None then Some "(absurd ())" else default in
      let body = cases (pattern cx) ^ match default with Some d -> " | _ -> " ^ d | None -> "" in
      Printf.sprintf "(match (Obj.obj %s : %s) with %s)" scrut ty (if body = "" then "_ -> ." else body)
  | Untagged _ -> (match arms with [ (_, vs, body) ] -> untuple vs scrut body | [] -> Option.get default | _ -> assert false)
  | Union ->
      (match arms with
      | [ (_, vs, body) ] ->
          Printf.sprintf "(match (Obj.obj %s : %s) with %s -> %s)" scrut
            (type_name cx [List.length vs]) (one_pattern cx (List.length vs) vs) body
      | [] -> Option.value default ~default:"(absurd ())"
      | _ -> assert false)

(* ---- The blocks of code. Each `def-fns` block becomes a closed top-level function per member, its lifted copy,
   taking the block's captures before its parameters; a block needed as a value also gets a factory over its
   captures, which repeats the bodies under a local `let rec` and returns the members something needs as values. *)

let lifted m = var m ^ "_l"
let valued m = var m ^ "_v"
let maker g = "mk_" ^ var (fst (List.hd g.members))
let key_name = function KVal x -> var x | KFn m -> valued m
let typed n = "(" ^ n ^ " : Obj.t)"
let extern_body f = f.V.impl <> None && !V.use_externs
let own g = function KFn m -> List.mem_assoc m g.members | KVal _ -> false
let factory_caps g = List.filter (fun k -> not (own g k)) g.caps
let returned g = List.filter_map (fun (m, _) -> if IntSet.mem m g.demand || IntSet.mem m g.held then Some m else None) g.members
let emitted g = g.lifted <> None || g.factory <> None

let rec register cx ms =
  if !(cx.analysed) then failwith ("extraction met function " ^ (snd (List.hd ms)).V.fname ^ " after analysing the blocks");
  let g = { gid = List.length !(cx.groups); members = ms; heads = []; uses = IntSet.empty; binders = IntSet.empty; consts = []; inner = IntSet.empty; caps = []; lifted = None; factory = None; demand = IntSet.empty; held = IntSet.empty; deps = []; needs = []; insts = []; adapter = -1 } in
  List.iteri (fun i (x, f) -> Hashtbl.replace cx.by_member x (g, i); FnTbl.replace cx.by_fn f (g, i)) ms;
  cx.groups := g :: !(cx.groups);
  let bind ids = g.binders <- List.fold_left (fun s x -> IntSet.add x s) g.binders ids in
  let rec code c =
    match c with
    | V.CVar x -> g.uses <- IntSet.add (V.resolve x) g.uses
    | V.CConst v -> g.consts <- v :: g.consts
    | V.CApp (V.CVar x, args, _) -> g.heads <- (V.resolve x, List.length args) :: g.heads; List.iter code args
    | V.CLetRec (fns, rest) ->
        let h = group_at cx fns in
        g.inner <- List.fold_left (fun s (x, _) -> IntSet.add x s) (IntSet.union g.inner h.inner) h.members;
        List.iter (fun (_, f) -> fn f) fns;
        code rest
    | V.CLet (ids, _, _) -> bind ids; List.iter code (V.subcodes c)
    | V.CMatch m -> List.iter (fun (_, ids, _) -> bind ids) m.branches; List.iter code (V.subcodes c)
    | c -> List.iter code (V.subcodes c)
  and fn f = bind f.V.params; if not (extern_body f) then code f.V.body in
  List.iter (fun (_, f) -> fn f) ms;
  g

and group_at cx fns = match FnTbl.find_opt cx.by_fn (snd (List.hd fns)) with Some (g, _) -> g | None -> register cx fns

(* A closure's block, found by its code, or else by the closures sharing its environment. *)
let group_of cx cl =
  match FnTbl.find_opt cx.by_fn cl.V.fn with
  | Some r -> r
  | None -> (
      let peers = IntMap.fold (fun x v acc -> match v with V.VFn c when c.V.env == cl.V.env -> (x, c.V.fn) :: acc | _ -> acc) (Lazy.force cl.V.env) [] in
      if peers <> [] then ignore (register cx (List.rev peers));
      match FnTbl.find_opt cx.by_fn cl.V.fn with Some r -> r | None -> failwith ("extraction found no block for function " ^ cl.V.fn.fname))

let classify cx x =
  match Hashtbl.find_opt cx.by_member x with
  | Some gi -> `Member gi
  | None when x < 0 -> `Const (Hashtbl.find V.literal_values x)
  | None -> ( match IntMap.find_opt x cx.env.Env.values with Some v -> `Const v | None -> `Frame)

let immediate = function V.VWord n when Z.fits_int n -> Some (Z.to_int n) | V.VToken -> Some 0 | _ -> None
let imm_text n = Printf.sprintf "(Obj.repr (%d))" n
let ident = function
  | V.VCtor (_, vs) -> Obj.repr vs
  | V.VExt (_, Array a) -> Obj.repr a
  | V.VExt (_, Bytes b) -> Obj.repr b
  | V.VExt (_, Slots t) -> Obj.repr t
  | v -> Obj.repr v
let rec raw_values f = function Ffi_core.Handle (_, _, _, _, v) -> f (Obj.obj v) | List (_, rs) -> List.iter (raw_values f) rs | _ -> ()
let children f = function
  | V.VCtor (_, vs) -> Array.iter f vs
  | V.VTuple vs -> List.iter f vs
  | V.VHandle (_, _, _, v) -> f v
  | V.VExt (_, Array a) -> Array.iter f a
  | V.VExt (_, Slots t) -> Array.iter (fun k -> f (Obj.magic k)) (Ffi_core.slots_keys t)
  | V.VExt (_, Raw r) -> raw_values f r
  | _ -> ()
let bucket tbl k = let h = Hashtbl.hash k in match Hashtbl.find_opt tbl h with Some b -> b | None -> let b = ref [] in Hashtbl.add tbl h b; b

(* Every block the data or the code could reach is registered before the captures are worked out: the values
   the roots reach, each closure's whole environment as far as its code names it, and every block's constants. *)
let discover cx roots =
  let seen = Hashtbl.create 1024 and done_ = Hashtbl.create 64 and q = Queue.create () in
  let value v = if immediate v = None then let b = bucket seen (ident v) in if not (List.exists (fun k -> k == ident v) !b) then (b := ident v :: !b; Queue.add (`V v) q) in
  let refs g f = IntSet.iter f g.uses; List.iter (fun (x, _) -> f x) g.heads in
  List.iter value roots;
  let rec loop () =
    match Queue.take_opt q with
    | Some (`V (V.VFn cl)) ->
        let g, _ = group_of cx cl in
        let env = Lazy.force cl.V.env in
        refs g (fun x -> Option.iter value (IntMap.find_opt x env));
        loop ()
    | Some (`V v) -> children value v; loop ()
    | Some (`G g) ->
        List.iter value g.consts;
        refs g (fun x -> match classify cx x with `Const v -> value v | `Member _ | `Frame -> ());
        loop ()
    | None -> (
        match List.filter (fun g -> not (Hashtbl.mem done_ g.gid)) !(cx.groups) with
        | [] -> ()
        | gs -> List.iter (fun g -> Hashtbl.replace done_ g.gid (); Queue.add (`G g) q) gs; loop ())
  in
  loop ()

(* A block's captures: the frame values its code names, the captures of the blocks outside it that it calls, and
   the values of those it names as values, to a fixed point. A block whose captures are at most its own members'
   values captures nothing: its members are then their lifted copies. *)
let analyse cx =
  cx.analysed := true;
  let groups = List.rev !(cx.groups) in
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter
      (fun g ->
        let raw = ref [] in
        let add k = if not (List.mem k !raw) then raw := k :: !raw in
        let refer ~value x =
          if not (IntSet.mem x g.binders) then
            match classify cx x with
            | `Member (h, _) when not (IntSet.mem x g.inner) ->
                if value && h.caps <> [] then add (KFn x);
                if h != g then List.iter (function KVal y when IntSet.mem y g.binders -> () | KFn y when IntSet.mem y g.inner -> () | k -> add k) h.caps
            | `Frame -> add (KVal x)
            | `Member _ | `Const _ -> ()
        in
        IntSet.iter (refer ~value:true) g.uses;
        List.iter (fun (x, n) -> match classify cx x with `Member (h, i) -> refer ~value:(List.length (snd (List.nth h.members i)).V.params <> n) x | _ -> refer ~value:false x) g.heads;
        let caps = if List.for_all (own g) !raw then [] else List.sort compare !raw in
        if caps <> g.caps then (g.caps <- caps; changed := true))
      groups
  done

(* ---- The data: every value the roots reach, by identity, each a cell of the data array. *)

let use_global cx key text =
  match List.assq_opt key !(cx.global_keys) with
  | Some i -> i
  | None -> let i = List.length !(cx.globals) in cx.globals := text :: !(cx.globals); cx.global_keys := (key, i) :: !(cx.global_keys); i

let matchable_text cx adt =
  match shape adt with
  | Ext _ ->
      let arms = List.map (fun c -> let fs = fields c in (c, fs, "(Obj.repr (" ^ pattern cx c fs ^ "))")) adt.V.ctors in
      "(Obj.repr (fun held -> " ^ dispatch cx adt (List.init (List.length adt.V.ctors) Fun.id) "held" arms None ^ "))"
  | _ -> "m_plain"

let tag_of c = List.length (List.filter (fun k -> k.V.arity > 0 && k.V.index < c.V.index) c.V.adt.V.ctors)

let rec cell cx v =
  let k = ident v in
  let b = bucket cx.cells k in
  match List.assq_opt k !b with
  | Some c -> c
  | None ->
      let c = match v with V.VFn cl -> fn_cell cx cl | _ -> new_cell cx v (prod_of cx v) in
      b := (k, c) :: !b;
      c

and new_cell cx v prod =
  let c = { vid = List.length !(cx.all_cells); v; prod; slot = -1 } in
  cx.all_cells := c :: !(cx.all_cells);
  children (sub cx) v;
  c

and sub cx v = if immediate v = None then Queue.add (`Sub v) cx.work

and prod_of cx v =
  match v with
  | V.VCtor (c, vs) -> (
      use_adt cx c.adt;
      match shape c.adt with
      | Tagged ns when wide ns -> Blank (0, 1 + widest ns)
      | Tagged _ -> Blank (tag_of c, Array.length vs)
      | Union -> Blank (0, Array.length vs)
      | Ext _ | Untagged _ -> Expr)
  | V.VTuple vs -> Blank (0, List.length vs)
  | V.VHandle _ -> Blank (0, 4)
  | V.VExt (a, Array vs) -> use_adt cx a; Blank (0, Array.length vs)
  | V.VExt (a, (Slots _ | Slice _ | Bytes _)) -> use_adt cx a; Leaf
  | V.VExt (a, Raw _) -> use_adt cx a; Expr
  | V.VWord _ -> Leaf
  | V.VCtorFn c -> use_adt cx c.adt; Global (use_global cx (Obj.repr c) (var c.cid))
  | V.VMatchable a -> use_adt cx a; Global (use_global cx (Obj.repr a) (matchable_text cx a))
  | V.VToken | V.VFn _ -> assert false

(* A closure is a member of one run of its block: one for a block that captures nothing, else one per
   environment, which its factory rebuilds from the captured values. *)
and fn_cell cx cl =
  let g, i = group_of cx cl in
  let inst =
    if g.caps = [] then (
      match g.insts with
      | [ it ] -> it
      | _ ->
          let it = { ig = g; caps_of = []; cells = []; base = -1; placed = 0 } in
          g.insts <- [ it ];
          Queue.add (`Lifted g) cx.work;
          it)
    else
      let env = Lazy.force cl.V.env in
      let caps = List.map (fun k -> let x = match k with KVal x | KFn x -> x in match IntMap.find_opt x env with Some v -> v | None -> failwith ("extraction found no value captured for " ^ var x)) (factory_caps g) in
      let b = bucket cx.inst_tbl (g.gid, List.map (fun v -> Hashtbl.hash (ident v)) caps) in
      match List.find_opt (fun (e, it) -> e == cl.V.env && it.ig == g) !b with
      | Some (_, it) -> it
      | None ->
          let it = { ig = g; caps_of = caps; cells = []; base = -1; placed = 0 } in
          b := (cl.V.env, it) :: !b;
          g.insts <- it :: g.insts;
          Queue.add (`Factory g) cx.work;
          List.iter (sub cx) caps;
          it
  in
  g.held <- IntSet.add (fst (List.nth g.members i)) g.held;
  match List.assoc_opt i inst.cells with
  | Some c -> c
  | None -> let c = new_cell cx (V.VFn cl) (Member (inst, i)) in inst.cells <- (i, c) :: inst.cells; c

let find_cell cx v = match List.assq_opt (ident v) !(bucket cx.cells (ident v)) with Some c -> c | None -> failwith "extraction lost a value"

let later cx f = cx.later := f :: !(cx.later); Printf.sprintf "\001%d\002" (List.length !(cx.later) - 1)

(* ---- Code. [cur] is the block whose code is written, as its lifted copies or, under [fac], its factory; [sites]
   the blocks defined around the point written, each with the members wanted there as values. *)

type ectx = { cur : grp; fac : bool; sites : (grp * IntSet.t ref) list }

let need ctx g = if g != ctx.cur && not (List.memq g ctx.cur.deps) then ctx.cur.deps <- g :: ctx.cur.deps

let rec member_value cx ctx (g, i) =
  let m = fst (List.nth g.members i) in
  if ctx.fac && g == ctx.cur then Printf.sprintf "(Obj.repr %s)" (var m)
  else if g.caps = [] then (need ctx g; Queue.add (`Lifted g) cx.work; Printf.sprintf "(Obj.repr %s)" (lifted m))
  else
    match List.assq_opt g ctx.sites with
    | Some w -> w := IntSet.add m !w; valued m
    | None when List.mem (KFn m) ctx.cur.caps -> valued m
    | None -> failwith ("extraction lost the value of " ^ var m)

and key_value cx ctx = function KVal x -> var x | KFn m -> member_value cx ctx (Hashtbl.find cx.by_member m)

let const_member cx v =
  match v with V.VFn cl -> ( match FnTbl.find_opt cx.by_fn cl.V.fn with Some (g, i) when g.caps = [] -> Some (g, i) | _ -> None) | _ -> None

let const_value cx ctx v =
  match immediate v, v with
  | Some n, _ -> imm_text n
  | None, V.VCtorFn c -> use_adt cx c.adt; var c.cid
  | None, V.VMatchable a when (match shape a with Ext _ -> false | _ -> true) -> "m_plain"
  | None, _ -> (
      match const_member cx v with
      | Some gi -> member_value cx ctx gi
      | None ->
          let c = cell cx v in
          if not (List.memq c ctx.cur.needs) then ctx.cur.needs <- c :: ctx.cur.needs;
          Printf.sprintf "c_%d" c.vid)

let head cx f =
  let member (g, i) =
    let fn = snd (List.nth g.members i) in
    match (fn.V.impl, template (Ffi_templates.Fn fn.V.fname)) with
    | Some _, Some ps when !V.use_externs -> `Inline (fn.V.fname, ps)
    | _ -> `Known (g, i, List.length fn.V.params)
  in
  let const v = match v with V.VCtorFn c -> `Ctor c | _ -> ( match const_member cx v with Some gi -> member gi | None -> `Dyn) in
  match f with
  | V.CVar x -> ( match classify cx (V.resolve x) with `Member gi -> member gi | `Const v -> const v | `Frame -> `Dyn)
  | V.CConst v -> const v
  | _ -> `Dyn

let fn_body cx f code =
  match f.V.impl with
  | Some _ when !V.use_externs -> (
      match template (Ffi_templates.Fn f.fname) with
      | Some ps -> fill_template cx f.fname ps (List.map var f.params)
      | None ->
          let view label ctor =
            let a = (Program.ctor cx.env ctor).V.adt in
            let arms = List.map (fun c -> let fs = fields c in c,fs,"Ffi_core." ^ pattern_at c.V.cname fs) a.ctors in
            Printf.sprintf "~%s:(fun v -> %s) " label (dispatch cx a (List.init (List.length a.ctors) Fun.id) "v" arms None) in
          let extra = match f.fname with
            | "flatten" -> view "rope" "REmpty" ^ "~slice:Obj.obj ~z:Obj.obj ~str:Obj.repr "
            | "list-to-array" -> view "list" "Nil"
            | "array-new" -> "~blank:(Obj.repr ()) "
            | _ -> "" in
          let call = Printf.sprintf "Ffi_core.%s %s%s" (sanitize f.fname) extra (args (List.map (fun p -> "(Obj.obj " ^ var p ^ ")") f.params)) in
          "(Obj.repr (" ^ call ^ "))")
  | _ -> code f.V.body

let rec expr cx ctx code =
  let e = expr cx ctx in
  match code with
  | V.CVar x -> (
      let x = V.resolve x in
      match classify cx x with `Member gi -> member_value cx ctx gi | `Const v -> const_value cx ctx v | `Frame -> var x)
  | V.CConst v -> const_value cx ctx v
  | V.CErased -> "(Obj.repr ())"
  (* Each entry that is not a name is bound before the tuple is built: ocamlopt (4.14.1 here; the issue
     reports 5.x too) fails with `Selection.size_expr` when a call it inlines puts an unused one-field
     block inside a tuple's field, https://github.com/ocaml/ocaml/issues/15154. *)
  | V.CValues cs -> (match List.map e cs with [ x ] -> x | es -> bind_args cx es (fun _ -> tuple))
  | V.CApp (f, es, cc) -> (
      let es = List.map e es in
      match (cc, head cx f) with
      | V.Ctor, `Ctor c -> build cx c es
      | _, `Inline (fname, ps) -> fill_template cx fname ps es
      | _, `Known (g, i, n) when n = List.length es ->
          let m = fst (List.nth g.members i) in
          if ctx.fac && g == ctx.cur then Printf.sprintf "(%s %s)" (var m) (args es)
          else (
            need ctx g;
            Queue.add (`Lifted g) cx.work;
            Printf.sprintf "(%s %s)" (lifted m) (concat " " (List.map (key_value cx ctx) g.caps @ [ args es ])))
      | _ -> Printf.sprintf "((Obj.obj %s : %s) %s)" (e f) (arrows (List.length es)) (args es))
  | V.CLet ([ x ], (V.CApp (f, es, _) as rhs), (V.CMatch ({ scrut = V.CVar y; shape = V.Known a; _ } as m) as body)) when V.resolve y = x -> (
      match head cx f with
      | `Inline (fname, ps) when Ffi_templates.outcomes ps && List.memq a (Option.to_list (Ffi.result_adt fname)) ->
          let arms = List.map (fun (i, ids, body) -> (V.ctor_at a i, List.map var ids, e body)) m.branches in
          fill_template ~arms:(outcome_arms ~rebind:(var x) cx a m.live arms (Option.map e m.default)) cx fname ps (List.map e es)
      | _ -> bound cx ctx [ x ] rhs body)
  | V.CLet (ids, rhs, body) -> bound cx ctx ids rhs body
  | V.CLetRec (fns, rest) ->
      let g = group_at cx fns in
      let w = ref IntSet.empty in
      let body = expr cx { ctx with sites = (g, w) :: ctx.sites } rest in
      if IntSet.is_empty !w then body
      else (
        need ctx g;
        g.demand <- IntSet.union g.demand !w;
        Queue.add (`Factory g) cx.work;
        let wanted = !w in
        let caps = match factory_caps g with [] -> "()" | ks -> concat " " (List.map (key_value cx ctx) ks) in
        let name m = if IntSet.mem m wanted then valued m else "_" in
        let pat = later cx (fun () -> match returned g with [ m ] -> name m | ms -> "(" ^ concat ", " (List.map name ms) ^ ")") in
        Printf.sprintf "(let %s = %s %s in %s)" pat (maker g) caps body)
  | V.CMatch m ->
      let scrut = e m.scrut in
      let a, scrut =
        match m.shape with
        | V.Known a -> (a, scrut)
        | V.Held (code, a) -> (a, Printf.sprintf "((Obj.obj %s : Obj.t -> Obj.t) %s)" (e code) scrut)
      in
      dispatch cx a m.live scrut (List.map (fun (i, ids, body) -> (V.ctor_at a i, List.map var ids, e body)) m.branches) (Option.map e m.default)
  | V.CCellAlloc (c, ss) -> cell_block cx c (List.map e ss)
  | V.CCellRead (k, i, c) -> field_read cx k i (e c)
  | V.CCellCopy (k, c, ss) -> field_copy cx k (e c) (List.map (fun (i, m, s) -> i, m, e s) ss)
  | V.CCellWrite (k, c, ss) ->
      let name = Printf.sprintf "cell%d" (stamp cx) in
      let ss = List.map (fun (i, m, s) -> i, m, e s) ss in
      let stores = match field_write cx k name ss with "" -> "" | w -> w ^ "; " in
      Printf.sprintf "(let %s = %s in %s%s)" name (e c) stores name
  | V.CWorldDo c -> Printf.sprintf "(driver.Driver_core.perform world %s)" (e c)
  | V.CPrim (Special.SettledValue, [ h ]) -> Printf.sprintf "(let (_, _, _, v) = (Obj.obj %s : %s) in v)" (e h) handle_ty
  | V.CPrim (Special.SettledMult, [ h; er; m; u ]) ->
      Printf.sprintf "(match (Obj.obj %s : %s) with (_, _, Ffi_core.Erased, _) -> %s | (_, _, Ffi_core.Many, _) -> %s | _ -> %s)" (e h) handle_ty (e er) (e m) (e u)
  | V.CPrim (Special.SlotEq, [ a; b; none; some ]) -> Printf.sprintf "(if %s == %s then %s else %s)" (e a) (e b) (e some) (e none)
  | V.CPrim (Special.SettledErase, [ h ]) ->
      Printf.sprintf "(Obj.repr (let (x, r, _, _) = (Obj.obj %s : %s) in (x, r, Ffi_core.Erased, Obj.repr ())))" (e h) handle_ty
  | V.CPrim (Special.SettledType, [ h ]) ->
      Printf.sprintf "(Obj.repr (match (Obj.obj %s : %s) with (x, Ffi_core.MintedIs, _, _) -> (x, Ffi_core.MintedType, Ffi_core.Erased, Obj.repr ()) | _ -> (%s, Obj.repr ())))" (e h) handle_ty (handle !Term.type_entry MintedIs Erased)
  | V.CPrim (p, _) -> Printf.sprintf "(failwith %s)" (quote ("`" ^ Special.name p ^ "` reached with no macro world"))
  | V.CAbsurd -> "(absurd ())"

and bound cx ctx ids rhs body =
  if ids = [] then Printf.sprintf "(let _ = %s in %s)" (expr cx ctx rhs) (expr cx ctx body) else untuple (List.map var ids) (expr cx ctx rhs) (expr cx ctx body)

let emit_lifted cx g =
  if g.lifted = None then (
    let ctx = { cur = g; fac = false; sites = [] } in
    let caps = List.map (fun k -> typed (key_name k)) g.caps in
    g.lifted <- Some [];
    g.lifted <- Some (List.map (fun (m, f) -> Printf.sprintf "%s %s : Obj.t = %s" (lifted m) (concat " " (caps @ [ params (List.map var f.V.params) ])) (fn_body cx f (expr cx ctx))) g.members))

let emit_factory cx g =
  if g.factory = None then (
    let ctx = { cur = g; fac = true; sites = [] } in
    let ps = match factory_caps g with [] -> "()" | ks -> concat " " (List.map (fun k -> typed (key_name k)) ks) in
    g.factory <- Some "";
    let defs = List.map (fun (m, f) -> Printf.sprintf "%s %s : Obj.t = %s" (var m) (params (List.map var f.V.params)) (fn_body cx f (expr cx ctx))) g.members in
    let ret = later cx (fun () -> match returned g with [ m ] -> "Obj.repr " ^ var m | ms -> "(" ^ concat ", " (List.map (fun m -> "Obj.repr " ^ var m) ms) ^ ")") in
    g.factory <- Some (Printf.sprintf "%s %s =\n  let rec %s in\n  %s" (maker g) ps (concat "\n  and " defs) ret))

let run cx =
  let rec loop () =
    match Queue.take_opt cx.work with
    | Some (`Lifted g) -> emit_lifted cx g; loop ()
    | Some (`Factory g) -> emit_factory cx g; loop ()
    | Some (`Sub v) -> ignore (cell cx v); loop ()
    | None -> ()
  in
  loop ()

(* ---- The program's data array, built in four passes around the code: pass 2 allocates every block blank and
   builds every leaf, pass 3 runs the code's definitions in order, interleaved with the closures their factories
   build, and pass 4 fills the blocks. A fixed loop reads each pass from a string: a token is an operation letter
   with its numbers, and a value is a slot or, after an "i", an immediate. *)

let runtime = {|let rt_data : Ffi_core.word array ref = ref [||]
let rt_next = ref 0
let rt_get k : Obj.t = Obj.magic (Array.unsafe_get !rt_data k)
let rt_push (v : Obj.t) = Array.unsafe_set !rt_data !rt_next (Obj.magic v : Ffi_core.word); incr rt_next
let rt_globals : Obj.t array ref = ref [||]
let rt_adapters : (Obj.t array -> Obj.t array) array ref = ref [||]
let rt_src = ref ""
let rt_pos = ref 0
let rt_num () =
  let s = !rt_src in
  let neg = s.[!rt_pos] = '-' in
  if neg then incr rt_pos;
  let n = ref 0 in
  while !rt_pos < String.length s && s.[!rt_pos] >= '0' && s.[!rt_pos] <= '9' do n := 10 * !n + Char.code s.[!rt_pos] - 48; incr rt_pos done;
  incr rt_pos;
  if neg then - !n else !n
let rt_ref () = if (!rt_src).[!rt_pos] = 'i' then (incr rt_pos; Obj.repr (rt_num ())) else rt_get (rt_num ())
let rt_text () = let n = rt_num () in let t = String.sub !rt_src !rt_pos n in rt_pos := !rt_pos + n + 1; t
let rt_run s =
  rt_src := s;
  rt_pos := 0;
  while !rt_pos < String.length s do
    let op = s.[!rt_pos] in
    incr rt_pos;
    match op with
    | 'b' -> let t = rt_num () in rt_push (Obj.new_block t (rt_num ()))
    | 't' -> ignore (rt_num ()); rt_push (Obj.repr (Ffi_core.slots_new ()))
    | 's' -> let t = rt_text () in rt_push (Obj.repr ((t, 0, String.length t) : Ffi_core.slice))
    | 'y' -> rt_push (Obj.repr (Bytes.of_string (rt_text ())))
    | 'z' -> rt_push (Obj.repr (Z.of_string (rt_text ())))
    | 'g' -> rt_push (!rt_globals).(rt_num ())
    | 'c' ->
        let a = rt_num () in
        let caps = Array.make (rt_num ()) (Obj.repr 0) in
        for i = 0 to Array.length caps - 1 do caps.(i) <- rt_ref () done;
        Array.iter rt_push ((!rt_adapters).(a) caps)
    | 'f' -> let b = rt_get (rt_num ()) in for i = 0 to rt_num () - 1 do Obj.set_field b i (rt_ref ()) done
    | 'k' -> let t = rt_get (rt_num ()) in for _ = 1 to rt_num () do ignore (Ffi_core.slots_add (Obj.obj t) (rt_ref ())) done
    | _ -> failwith "malformed data"
  done|}

(* The emitted blocks in strongly connected components of their references by name, callee first. *)
let components groups =
  let index = Hashtbl.create 64 and low = Hashtbl.create 64 and on = Hashtbl.create 64 in
  let stack = ref [] and counter = ref 0 and comps = ref [] in
  let get t g = Hashtbl.find t g.gid in
  let rec strong g =
    Hashtbl.replace index g.gid !counter;
    Hashtbl.replace low g.gid !counter;
    incr counter;
    stack := g :: !stack;
    Hashtbl.replace on g.gid ();
    List.iter
      (fun h ->
        if emitted h then
          if not (Hashtbl.mem index h.gid) then (strong h; Hashtbl.replace low g.gid (min (get low g) (get low h)))
          else if Hashtbl.mem on h.gid then Hashtbl.replace low g.gid (min (get low g) (get index h)))
      g.deps;
    if get low g = get index g then
      let rec pop acc = match !stack with h :: rest -> stack := rest; Hashtbl.remove on h.gid; if h == g then h :: acc else pop (h :: acc) | [] -> acc in
      comps := pop [] :: !comps
  in
  List.iter (fun g -> if not (Hashtbl.mem index g.gid) then strong g) groups;
  Array.of_list (List.rev !comps)

let rec index_of x = function y :: rest -> if y = x then 0 else 1 + index_of x rest | [] -> raise Not_found

let assemble cx =
  let comps = components (List.filter emitted (List.rev !(cx.groups))) in
  let comp_of = Hashtbl.create 64 in
  Array.iteri (fun k gs -> List.iter (fun g -> Hashtbl.replace comp_of g.gid k) gs) comps;
  let order = ref [] and cstate = Array.make (Array.length comps) 0 and estate = Hashtbl.create 16 in
  let cycle () = failwith "extraction found a cycle among the definitions and the closures they need" in
  let rec comp k =
    match cstate.(k) with
    | 2 -> ()
    | 1 -> cycle ()
    | _ ->
        cstate.(k) <- 1;
        List.iter (fun g -> List.iter (fun h -> if emitted h then let j = Hashtbl.find comp_of h.gid in if j <> k then comp j) g.deps; List.iter prod g.needs) comps.(k);
        cstate.(k) <- 2;
        order := `Comp k :: !order
  and inst it =
    match it.placed with
    | 2 -> ()
    | 1 -> cycle ()
    | _ -> it.placed <- 1; comp (Hashtbl.find comp_of it.ig.gid); List.iter value it.caps_of; it.placed <- 2; order := `Inst it :: !order
  and expr_cell c =
    match Hashtbl.find_opt estate c.vid with
    | Some 2 -> ()
    | Some _ -> cycle ()
    | None -> Hashtbl.replace estate c.vid 1; children value c.v; Hashtbl.replace estate c.vid 2; order := `Expr c :: !order
  and value v = if immediate v = None then prod (find_cell cx v)
  and prod c = match c.prod with Member (it, _) -> inst it | Expr -> expr_cell c | Blank _ | Leaf | Global _ -> () in
  Array.iteri (fun k _ -> comp k) comps;
  let cells = List.rev !(cx.all_cells) in
  List.iter prod cells;
  let order = List.rev !order in
  let next = ref 0 in
  let take () = let k = !next in incr next; k in
  List.iter (fun c -> match c.prod with Blank _ | Leaf | Global _ -> c.slot <- take () | Member _ | Expr -> ()) cells;
  List.iter
    (function
      | `Inst it ->
          it.base <- !next;
          let ret = returned it.ig in
          next := !next + List.length ret;
          List.iter (fun (i, c) -> let m = fst (List.nth it.ig.members i) in c.slot <- it.base + index_of m ret) it.cells
      | `Expr c -> c.slot <- take ()
      | `Comp _ -> ())
    order;
  let tok v = match immediate v with Some n -> "i" ^ string_of_int n | None -> string_of_int (find_cell cx v).slot in
  let toks vs = concat "" (List.map (fun v -> tok v ^ " ") vs) in
  let data_expr v = match immediate v with Some n -> imm_text n | None -> Printf.sprintf "(rt_get %d)" (find_cell cx v).slot in
  let text t = Printf.sprintf "%d:%s " (String.length t) t in
  let pass2 = Buffer.create 4096 and pass4 = Buffer.create 4096 in
  let fill c ts = Printf.bprintf pass4 "f%d %d %s" c.slot (List.length ts) (concat "" (List.map (fun t -> t ^ " ") ts)) in
  List.iter
    (fun c ->
      match (c.prod, c.v) with
      | Blank (t, n), v -> (
          Printf.bprintf pass2 "b%d.%d " t n;
          match v with
          | V.VCtor (k, vs) -> fill c ((match shape k.adt with Tagged ns when wide ns -> [ "i" ^ string_of_int k.index ] | _ -> []) @ List.map tok (Array.to_list vs))
          | V.VTuple vs -> fill c (List.map tok vs)
          | V.VExt (_, Array a) -> fill c (List.map tok (Array.to_list a))
          | V.VHandle (x, r, m, v) ->
              let r = match r with Ffi_core.MintedIs -> 0 | MintedType -> 1 and m = match m with Erased -> 0 | Many -> 1 | Unique -> 2 in
              fill c [ "i" ^ string_of_int x; "i" ^ string_of_int r; "i" ^ string_of_int m; tok v ]
          | _ -> assert false)
      | Global i, _ -> Printf.bprintf pass2 "g%d " i
      | Leaf, V.VExt (_, Slots t) ->
          Buffer.add_string pass2 "t0 ";
          let ks = Array.to_list (Ffi_core.slots_keys t) in
          Printf.bprintf pass4 "k%d %d %s" c.slot (List.length ks) (toks (List.map Obj.magic ks))
      | Leaf, V.VExt (_, Slice (s, o, l)) -> Buffer.add_string pass2 ("s" ^ text (String.sub s o l))
      | Leaf, V.VExt (_, Bytes b) -> Buffer.add_string pass2 ("y" ^ text (Bytes.to_string b))
      | Leaf, V.VWord n -> Buffer.add_string pass2 ("z" ^ text (Z.to_string n))
      | Leaf, _ -> assert false
      | (Member _ | Expr), _ -> ())
    cells;
  let out = Buffer.create 65536 and seg = Buffer.create 1024 and adapters = ref 0 in
  let flush () = if Buffer.length seg > 0 then (Printf.bprintf out "let () = rt_run %s\n" (quote (Buffer.contents seg)); Buffer.clear seg) in
  let comp_text gs =
    let defs = List.concat_map (fun g -> Option.value g.lifted ~default:[] @ Option.to_list g.factory) gs in
    let names = List.concat_map (fun g -> (if g.lifted <> None then List.map (fun (m, _) -> lifted m) g.members else []) @ if g.factory <> None then [ maker g ] else []) gs in
    let needs = List.fold_left (fun acc g -> List.fold_left (fun acc c -> if List.memq c acc then acc else c :: acc) acc g.needs) [] gs in
    let defs = "let rec " ^ concat "\nand " defs in
    if needs = [] then defs ^ "\n"
    else
      let names = concat ", " names in
      Printf.sprintf "let %s =\n  let %s in\n  %s in\n  %s\n" names (concat " and " (List.map (fun c -> Printf.sprintf "c_%d = rt_get %d" c.vid c.slot) needs)) defs names
  in
  let adapter g =
    g.adapter <- !adapters;
    incr adapters;
    let ret = returned g in
    if g.caps = [] then Printf.sprintf "let () = (!rt_adapters).(%d) <- (fun _ -> [| %s |])\n" g.adapter (concat "; " (List.map (fun m -> "Obj.repr " ^ lifted m) ret))
    else
      let vs = List.map valued ret in
      let caps = match factory_caps g with [] -> "()" | ks -> concat " " (List.mapi (fun i _ -> Printf.sprintf "c.(%d)" i) ks) in
      Printf.sprintf "let () = (!rt_adapters).(%d) <- (fun c -> let %s = %s %s in [| %s |])\n" g.adapter (match vs with [ v ] -> v | _ -> "(" ^ concat ", " vs ^ ")") (maker g) caps (concat "; " vs)
  in
  List.iter
    (function
      | `Comp k ->
          flush ();
          Buffer.add_string out (comp_text comps.(k));
          List.iter (fun g -> if g.insts <> [] then Buffer.add_string out (adapter g)) comps.(k)
      | `Inst it -> Printf.bprintf seg "c%d %d %s" it.ig.adapter (List.length it.caps_of) (toks it.caps_of)
      | `Expr c ->
          flush ();
          let e = match c.v with V.VExt (_, Raw r) -> "Obj.repr " ^ raw data_expr r | V.VCtor (k, vs) -> build cx k (List.map data_expr (Array.to_list vs)) | _ -> assert false in
          Printf.bprintf out "let () = rt_push (%s)\n" e)
    order;
  flush ();
  concat ""
    [ Printf.sprintf "let () = rt_data := Array.make %d (Obj.magic 0 : Ffi_core.word); rt_adapters := Array.make %d (fun _ -> [||])\n" !next !adapters;
      Printf.sprintf "let () = rt_globals := [| %s |]\n" (concat "; " (List.rev !(cx.globals)));
      Printf.sprintf "let () = rt_run %s\n" (quote (Buffer.contents pass2));
      Buffer.contents out;
      Printf.sprintf "let () = rt_run %s\n" (quote (Buffer.contents pass4));
      concat "" (List.rev_map (fun (name, v) -> Printf.sprintf "let %s = %s\n" name (data_expr v)) !(cx.finals));
      concat "" (List.rev_map (fun (name, v) -> Printf.sprintf "let () = %s := %s\n" name (data_expr v)) !(cx.posts));
      "let () = rt_data := [||]; rt_globals := [||]; rt_adapters := [||]\n" ]

let subst cx s =
  let thunks = Array.of_list (List.rev !(cx.later)) in
  let b = Buffer.create (String.length s) in
  let rec go i =
    if i < String.length s then
      if s.[i] = '\001' then (
        let j = String.index_from s i '\002' in
        Buffer.add_string b (thunks.(int_of_string (String.sub s (i + 1) (j - i - 1))) ());
        go (j + 1))
      else (Buffer.add_char b s.[i]; go (i + 1))
  in
  go 0;
  Buffer.contents b

let new_cx env =
  { env; adts = ref []; shapes = ref []; narrows = ref []; temps = ref 0; actions = Buffer.create 1024; shows = ref []; words = Buffer.create 256; posts = ref []; finals = ref [];
    groups = ref []; by_member = Hashtbl.create 256; by_fn = FnTbl.create 256; cells = Hashtbl.create 4096; all_cells = ref []; globals = ref []; global_keys = ref [];
    work = Queue.create (); later = ref []; analysed = ref false; inst_tbl = Hashtbl.create 64 }

(* A value the program's top level reads after the data is built, by a name bound then. *)
let root cx v =
  match immediate v with
  | Some n -> imm_text n
  | None -> let name = Printf.sprintf "final_%d" (List.length !(cx.finals)) in cx.finals := (name, v) :: !(cx.finals); name

let all a = List.init (List.length a.V.ctors) Fun.id

(* The type of each shape met, the extern types' unwraps and wraps, and every constructor as its builder. *)
let types cx =
  let builder c =
    let fs = fields c in
    Printf.sprintf "let %s : Obj.t = %s" (var c.V.cid) (Printf.sprintf "(Obj.repr (fun %s : Obj.t -> %s))" (params fs) (build cx c fs))
  in
  let extern a = match shape a with Ext name -> Some (List.assoc name externs) | _ -> None in
  let builders = List.concat_map (fun a -> List.map builder a.V.ctors) !(cx.adts) in
  let narrow ((ns, live), name) =
    let decl i n =
      let idx = if List.mem i live then "yes" else "no" in
      if n = 0 then Printf.sprintf "%s : %s %s" (ctor_at cx ns i) idx name else Printf.sprintf "%s : %s -> %s %s" (ctor_at cx ns i) (mutable_payload n) idx name
    in
    Printf.sprintf "type _ %s = %s" name (concat " | " (List.mapi decl ns))
  in
  let decl ns =
    let ctor i n = if n = 0 then Some (ctor_at cx ns i) else if wide ns then None else Some (ctor_at cx ns i ^ " of " ^ mutable_payload n) in
    let shared = if wide ns then [ Printf.sprintf "%s of { d : int; %s }" (wide_ctor cx ns) (payload_fields (widest ns)) ] else [] in
    Printf.sprintf "%s = %s" (type_name cx ns) (concat " | " (List.filter_map Fun.id (List.mapi ctor ns) @ shared)) in
  concat "\n"
    (List.rev_map narrow !(cx.narrows)
    @ [ (match !(cx.shapes) with [] -> "" | shapes -> "type " ^ concat "\nand " (List.map decl shapes)) ]
    @ List.filter_map extern !(cx.adts)
    @ builders)

(* A Nat as a Z.t: its own integer under the FFI, else the Peano chain counted down one constructor at a time. *)
let nat_z cx =
  let a = (Program.ctor cx.env "Zero").V.adt in
  match shape a with
  | Ext _ -> "(fun (v : Obj.t) -> (Obj.obj v : Z.t))"
  | _ ->
      let arms = [ (Program.ctor cx.env "Zero", [], "n"); (Program.ctor cx.env "Succ", [ "p" ], "(go (Z.succ n) p)") ] in
      Printf.sprintf "(let rec go n (v : Obj.t) = %s in go Z.zero)" (dispatch cx a (all a) "v" arms None)

(* The printer for a literal type, which prints the literal its value reads back from (Literal.spell): a Char and
   a U8 are their Nat (section 33), so neither is unwrapped first. *)
let literal_show cx ty =
  let named name = match (ty, Env.lookup { cx.env with Env.scope = cx.env.Env.prelude } (Reader.Src name)) with App (Var t, []), Some p -> t = p | _ -> false in
  let string_body () =
    let a = (Program.ctor cx.env "SNil").V.adt in
    match shape a with
    | Ext _ -> "(let (s, o, l) = (Obj.obj v : Ffi_core.slice) in Ffi_core.lit_string (String.sub s o l))"
    | _ ->
        let cons = Printf.sprintf "(Buffer.add_char b (Char.chr (Z.to_int (%s c))); go r)" (nat_z cx) in
        let arms = [ (Program.ctor cx.env "SNil", [], "()"); (Program.ctor cx.env "SCons", [ "c"; "r" ], cons) ] in
        Printf.sprintf "(let b = Buffer.create 16 in let rec go (v : Obj.t) = %s in go v; Ffi_core.lit_string (Buffer.contents b))" (dispatch cx a (all a) "v" arms None)
  in
  if named "Nat" then Some (Printf.sprintf "(Z.to_string (%s v))" (nat_z cx))
  else if named "Char" then Some (Printf.sprintf "(Ffi_core.lit_char (Z.to_int (%s v)))" (nat_z cx))
  else if named "String" then Some (string_body ())
  else None

let rec show cx env ty =
  let ty = Env.canon env ty in
  let key = map_vars (fun _ t -> match t with Var x when not (IntMap.mem x cx.env.entries) -> Var (-1) | t -> t) 0 ty in
  match List.find_opt (fun (k, _, _) -> equal k key) !(cx.shows) with
  | Some (_, name, _) -> name
  | None ->
      let name = Printf.sprintf "show_%d" (List.length !(cx.shows)) and body = ref "" in
      cx.shows := (key, name, body) :: !(cx.shows);
      let named tid = try Elab.listed_ctors env Reader.nowhere tid with Env.Error _ -> [] in
      let adt_of tid = match named tid with (_, ct) :: _ -> use_adt cx ct.V.adt; Some ct.V.adt | [] -> None in
      (* one arm: the constructor's name over its fields, an erased one printing as `_` and taking no binder
         (section 45). The shared Ffi_core.show_app joins them, so `$` reads the same here as in the
         interpreter rather than being decided again. *)
      let branch tid a c =
        match Elab.listed_entry (named tid) c with None -> None | Some cid ->
        try
          let tele, ret = Elab.ctor_type env Reader.nowhere cid in
          let env', fids = Elab.open_tele env tele in
          let env' = Env.merge_opens (Env.unify_force (Env.forcing env') (instantiate (List.rev_map (fun x -> Var x) fids) ret) ty) in
          let rec args i acc = function
            | [] -> []
            | ((_ : entry), x) :: rest when (Env.entry env' x).mult = Erased -> "\"_\"" :: args i ("\"_\"" :: acc) rest
            | (e, x) :: rest ->
                let word, i = match e.place with
                  | Some (SlotOf (Bound k)) -> (List.nth acc k, i)
                  | Some p ->
                      ((match (Env.entry env (Elab.location_var env Reader.nowhere p)).state with
                        | Settled v ->
                            let name = Printf.sprintf "word_%d" (stamp cx) in
                            Buffer.add_string cx.words (Printf.sprintf "let %s : Obj.t ref = ref (Obj.repr ())\n" name);
                            cx.posts := (name, v) :: !(cx.posts);
                            "!" ^ name
                        | Hypothetical -> "(Obj.repr ())"), i)
                  | None -> (Printf.sprintf "f%d" i, i + 1) in
                Printf.sprintf "%s %s" (show cx env' (Env.type_of env' x)) word :: args i (word :: acc) rest
          in
          let text = Printf.sprintf "(Ffi_core.show_app %s [ %s ])" (quote c.V.cname) (concat "; " (args 0 [] (List.combine tele fids))) in
          ignore a;
          Some (c, fields c, text)
        with Env.Contradiction _ | Env.Error _ | Not_found -> None
      in
      (body :=
         match literal_show cx ty with
         | Some text -> text
         | None -> (
         match ty with
         | Cell _ -> "\"_\""
         | t when equal t Prelude.slot_term -> "\"_\""
         | App (Var tid, _) -> (
             match adt_of tid with
             | None -> "\"_\""
             | Some a ->
                 (* the tag where there is one, else the sole non-phantom constructor; a union with several has
                    no way to choose and prints `_` (section 45) *)
                 let arms = if a.V.tagged then List.filter_map (branch tid a) a.V.ctors
                            else match a.V.ctors with [ c ] -> Option.to_list (branch tid a c) | _ -> [] in
                 if arms = [] then "\"_\""
                 else dispatch cx a (List.map (fun (c, _, _) -> c.V.index) arms) "v" arms (Some "\"_\""))
         | _ -> "\"_\""));
      name

(* The driver's operations on the prelude's values, each direct (lib/driver_core.ml); a String held as the
   FFI's slice converts to and from the host's string directly. *)
let host_conversions =
  "~str_of_host:(fun s -> Obj.repr ((s, 0, String.length s) : Ffi_core.slice)) ~str_to_slice:(fun v -> (Obj.obj v : Ffi_core.slice)) "
let nat_conversion = "~nat_to_z:(fun v -> (Obj.obj v : Z.t)) ~nat_of_z:Obj.repr "
let apply_ocaml =
  "(fun (k : Obj.t) xs -> if xs = [] then (Obj.obj k : unit -> Obj.t) () else List.fold_left (fun f (x : Obj.t) -> (Obj.obj f : Obj.t -> Obj.t) x) k xs)"
let driver cx =
  let c = Program.ctor cx.env in
  let lam fs body = Printf.sprintf "(fun %s -> %s)" (params fs) body in
  let make n = let fs = fields (c n) in if fs = [] then build cx (c n) [] else lam fs (build cx (c n) fs) in
  let un n arm = let a = (c n).adt in lam [ "v" ] (dispatch cx a (all a) "v" (List.map (fun ct -> let fs = fields ct in (ct, fs, arm ct fs)) a.V.ctors) None) in
  let option n = un n (fun ct fs -> if ct.V.cname = n then Printf.sprintf "(Some (%s))" (concat ", " fs) else "None") in
  let field n = un n (fun _ fs -> List.hd fs) in
  let variant ct fs = Printf.sprintf "(Driver_core.%s%s)" ct.V.cname (if fs = [] then "" else " (" ^ concat ", " fs ^ ")") in
  let ops =
    [ ("zero", make "Zero"); ("succ", make "Succ"); ("pred", option "Succ");
      ("u8", make "MkU8"); ("un_u8", field "MkU8"); ("char", make "MkChar"); ("un_char", field "MkChar");
      ("snil", make "SNil"); ("scons", make "SCons"); ("un_str", option "SCons"); ("un_list", option "Cons"); ("un_pair", un "MkPair" (fun _ fs -> Printf.sprintf "(%s)" (concat ", " fs))); ("un_some", option "Some");
      ("some", make "Some"); ("none", make "None"); ("ok", make "Ok"); ("fail", make "Fail"); ("unit", make "MkUnit");
      ("cons", make "Cons"); ("nil", make "Nil"); ("pair", make "MkPair");
      ("is_file", make "IsFile"); ("is_dir", make "IsDir"); ("is_other", make "IsOther"); ("missing", make "Missing");
      ("changed", make "Changed"); ("unchanged", make "Unchanged"); ("mk_usage", "(Obj.repr " ^ make "MkUsage" ^ ")"); ("mk_exited", "(Obj.repr " ^ make "MkExited" ^ ")");
      ("un_job", un "MkExecJob" (fun _ fs -> Printf.sprintf "(%s)" (concat ", " fs))); ("exec_results", make "MkExecResults");
      ("request", un "WriteOut" variant); ("step", un "Exit" variant);
      ("is_start", un "Start" (fun ct _ -> string_of_bool (ct.V.cname = "Start")));
      ("apply", apply_ocaml) ]
  in
  let host = (match shape (c "SNil").V.adt with Ext "String" -> host_conversions | _ -> "")
             ^ (match shape (c "Zero").V.adt with Ext "Nat" -> nat_conversion | _ -> "") in
  Printf.sprintf "let driver = Driver_core.make %s{ %s }\n" host (concat "; " (List.map (fun (k, v) -> "Driver_core." ^ k ^ " = " ^ v) ops))
  ^ Printf.sprintf {|let flush_to oc s o l = output_substring oc s o l; flush oc
let world = { Driver_core.read_rest = (fun () -> In_channel.input_all stdin); read_line = (fun () -> In_channel.input_line stdin); out = flush_to stdout; err = flush_to stderr; args = List.tl (Array.to_list Sys.argv); env = Sys.getenv_opt; envs = Driver_core.host_envs; cwd = Sys.getcwd; exit; print = print_endline; exec = true; fence = ref Driver_core.unconfined; limit = ref None; used = ref 0 }
let world = Driver_core.start %s %s %s %b %b world
let print_final = Driver_core.print world
let run_program = driver.run_program world
let run_main = driver.run_main world
|} (quotes !reads) (quotes !writes) (match !output_bytes with Some b -> "(Some " ^ quote b ^ ")" | None -> "None") !with_env !with_exec

let item cx = function
  | Env.Fns _ -> ()
  | Env.Final (v, ty, path) ->
      let text =
        match (v, Program.final cx.env ty) with
        (* a bare constructor prints `_`, as the type-directed printer gives it (section 45) *)
        | V.VCtorFn _, Program.Plain -> "print_final \"_\""
        | _, kind -> (
            let e = root cx v in
            match kind with
            | Program.Main -> Printf.sprintf "run_main %s" e
            | Program -> Printf.sprintf "exit (run_program %s)" e
            | Thunk t -> Printf.sprintf "print_final (%s ((Obj.obj %s : unit -> Obj.t) ()))" (show cx cx.env t) e
            | Plain -> Printf.sprintf "print_final (%s %s)" (show cx cx.env ty) e)
      in
      Buffer.add_string cx.actions (Printf.sprintf "let () = source := %s; %s\n" (quote path) text)
  | Env.Native (i, v, a) ->
      let arms = List.map (fun c -> (c, [], Printf.sprintf "print_int %d" c.V.index)) a.V.ctors in
      Buffer.add_string cx.actions (Printf.sprintf "let () = if Sys.argv.(1) = \"%d\" then let v = (Obj.obj %s : unit -> Obj.t) () in %s\n" i (root cx v) (dispatch cx a (all a) "v" arms None))

(* Only what the final values reach is written out: the trace's blocks are registered so that a closure finds
   its code, but none is emitted unless something reaches it. *)
let emit env items =
  let cx = new_cx env in
  List.iter (function Env.Fns fs -> ignore (group_at cx fs) | Env.Final _ | Env.Native _ -> ()) items;
  List.iter (item cx) items;
  let driver = if Program.prelude_opt env "Exit" = None then "let print_final = print_endline" else driver cx in
  let shows = List.rev_map (fun (_, name, body) -> Printf.sprintf "%s (v : Obj.t) : string = %s" name !body) !(cx.shows) in
  let roots = List.map snd (!(cx.finals) @ !(cx.posts)) in
  discover cx roots;
  analyse cx;
  List.iter (sub cx) roots;
  run cx;
  let data = assemble cx in
  let types = types cx in
  subst cx
    (concat "\n"
       [ "[@@@warning \"-a\"]";
         "module Ffi_core = struct\n" ^ Ffi_core_source.source ^ "\nend";
         "module Driver_core = struct\n" ^ Driver_core_source.source ^ "\nend";
         "let source = ref \"-\"\nlet absurd () = prerr_endline (!source ^ \": runtime error: absurd code reached\"); exit 1";
         "type yes = Yes_ and no = No_\nlet m_plain : Obj.t = Obj.repr (fun (v : Obj.t) : Obj.t -> v)";
         types;
         runtime;
         driver;
         Buffer.contents cx.words;
         (if shows = [] then "" else "let rec " ^ concat "\nand " shows);
         data;
         Buffer.contents cx.actions ])

(* A native-compute compiles its functions once, beside the run-position functions so far, runs each by its
   index, as many at once as the host has processors, and answers the discriminant each run prints. *)
let () =
  Elab.native := fun env fs ->
    let ml = emit env (List.filter (function Env.Fns _ -> true | _ -> false) (List.rev !Env.trace) @ List.mapi (fun i (v, a) -> Env.Native (i, v, a)) fs) in
    let dir = Filename.temp_file "sleight" ".native" in
    let file = Filename.concat dir in
    let exited what = function
      | Ok (0, out, _) -> Ok out
      | Ok (code, out, err) -> Stdlib.Error (Printf.sprintf "%s exited with code %d\n%s%s" what code out err)
      | Stdlib.Error m -> Stdlib.Error m in
    let answer r = Result.bind (exited "the compiled function" r) (fun out -> Option.to_result ~none:("the compiled function printed " ^ out) (int_of_string_opt out)) in
    let run () =
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      Program.write_file (file "main.ml") ml;
      Result.map
        (fun _ -> List.map answer (Program.exec_all (Lazy.force Program.processors) (List.mapi (fun i _ -> (file "main", [ string_of_int i ], Program.host_envs (), None, "")) fs)))
        (exited "ocamlfind" (Program.compile false dir (file "main"))) in
    let result = try run () with (Unix.Unix_error _ | Sys_error _) as e -> Stdlib.Error (Driver_core.explain e) in
    (try Array.iter (fun f -> Sys.remove (file f)) (Sys.readdir dir); Sys.rmdir dir with Sys_error _ -> ());
    result
