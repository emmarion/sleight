open Term

module IntMap = Map.Make (Int)

type cc = Plain | Tail | Delegate | Ctor

(* An ADT's runtime shape: [tagged] when it is an enum with more than one non-phantom constructor (section 38);
   [ext] when the FFI implements it (section 41), its values then being [VExt] payloads. *)
type adt = { tname : string; tagged : bool; mutable ctors : ctor list; mutable ext : ext option }
and ctor = { cname : string; cid : id; index : int; arity : int; adt : adt }
and ext = { construct : int -> value list -> value; destruct : value -> int * value list }

and value =
  | VCtor of ctor * value list
  | VTuple of value list
  | VExt of adt * payload
  | VCtorFn of ctor
  | VFn of closure
  | VToken

and payload = Int of Z.t | Slice of Ffi_core.slice

and fn = { fname : string; params : id list; body : code; impl : (value list -> value list) option }
and closure = { fn : fn; env : venv Lazy.t }
and venv = value IntMap.t

and code =
  | CVar of id
  | CConst of value
  | CErased
  | CValues of code list
  | CApp of code * code list * cc
  | CLet of id list * code * code
  | CLetRec of (id * fn) list * code
  | CMatch of code * (code * id list * code) list
  | CAbsurd

(* Extern implementations run unless stripped (section 41's invariant). *)
let use_externs = ref true

(* An untagged value is its many fields: one of them bare, none the token. *)
let tuple = function [ v ] -> v | [] -> VToken | vs -> VTuple vs
let untuple n v = match (n, v) with 1, v -> [ v ] | 0, _ -> [] | _, VTuple vs -> vs | _ -> assert false

let construct c args =
  match c.adt.ext with
  | Some e when !use_externs -> e.construct c.index args
  | _ -> if c.adt.tagged then VCtor (c, args) else tuple args

(* The constructor index and many fields of a value of [c]'s type. *)
let destruct c v =
  match (c.adt.ext, v) with
  | Some e, VExt _ -> e.destruct v
  | _ when c.adt.tagged -> (match v with VCtor (c', fs) -> (c'.index, fs) | _ -> assert false)
  | _ -> (c.index, untuple c.arity v)

let rec show = function
  | VCtor (c, fields) -> "(" ^ String.concat " " (c.cname :: List.map show fields) ^ ")"
  | VTuple vs -> "(" ^ String.concat " " (List.map show vs) ^ ")"
  | VExt (adt, _) as v ->
      let i, fs = (Option.get adt.ext).destruct v in
      if adt.tagged then show (VCtor (List.nth adt.ctors i, fs)) else show (tuple fs)
  | VCtorFn c -> "<constructor " ^ c.cname ^ ">"
  | VFn cl -> "<function " ^ cl.fn.fname ^ ">"
  | VToken -> "_"
