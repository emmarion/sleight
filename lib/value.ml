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
  | VMatchable of adt
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
  | CMatch of matching
  | CAbsurd

(* What a match compiles to: the Matchable saying how to take the scrutinee apart, whether its type carries a
   discriminant, and one branch per real constructor keyed by that constructor's discriminant (section 38). *)
and matching = { matchable : code; scrut : code; tags : bool; branches : (int * id list * code) list }

let map_code f = function
  | CValues cs -> CValues (List.map f cs)
  | CApp (g, args, cc) -> CApp (f g, List.map f args, cc)
  | CLet (ids, rhs, rest) -> CLet (ids, f rhs, f rest)
  | CLetRec (fns, rest) -> CLetRec (fns, f rest)
  | CMatch m -> CMatch { m with matchable = f m.matchable; scrut = f m.scrut; branches = List.map (fun (i, ids, b) -> (i, ids, f b)) m.branches }
  | (CVar _ | CConst _ | CErased | CAbsurd) as c -> c

let subcodes = function
  | CValues cs -> cs
  | CApp (g, args, _) -> g :: args
  | CLet (_, rhs, rest) -> [ rhs; rest ]
  | CLetRec (_, rest) -> [ rest ]
  | CMatch m -> m.matchable :: m.scrut :: List.map (fun (_, _, b) -> b) m.branches
  | CVar _ | CConst _ | CErased | CAbsurd -> []

(* Extern implementations run unless stripped (section 41's invariant). *)
let use_externs = ref true

(* An untagged value is its many fields: one of them bare, none the token. *)
let tuple = function [ v ] -> v | [] -> VToken | vs -> VTuple vs
let untuple n v = match (n, v) with 1, v -> [ v ] | 0, _ -> [] | _, VTuple vs -> vs | _ -> assert false

let construct c args =
  match c.adt.ext with
  | Some e when !use_externs -> e.construct c.index args
  | _ -> if c.adt.tagged then VCtor (c, args) else tuple args

(* [ctors] holds the non-phantom constructors, so a constructor sits at its own discriminant. *)
let ctor_at adt i = List.nth adt.ctors i

(* The discriminant and many fields of a value, read through the FFI where its type has one (section 41) and
   off the tag otherwise; [None] where the type carries no discriminant and the value is its fields as they
   stand, which the caller's one branch takes apart by its own arity. *)
let dispatch adt tagged v =
  match (adt.ext, v) with
  | Some e, VExt _ -> Some (e.destruct v)
  | _ when not tagged -> None
  | _ -> (match v with VCtor (c, fs) -> Some (c.index, fs) | _ -> assert false)

let destruct c v = match dispatch c.adt c.adt.tagged v with Some r -> r | None -> (c.index, untuple c.arity v)

let rec show = function
  | VCtor (c, fields) -> "(" ^ String.concat " " (c.cname :: List.map show fields) ^ ")"
  | VTuple vs -> "(" ^ String.concat " " (List.map show vs) ^ ")"
  | VExt (adt, _) as v ->
      let i, fs = (Option.get adt.ext).destruct v in
      if adt.tagged then show (VCtor (ctor_at adt i, fs)) else show (tuple fs)
  | VCtorFn c -> "<constructor " ^ c.cname ^ ">"
  | VMatchable adt -> "<matchable " ^ adt.tname ^ ">"
  | VFn cl -> "<function " ^ cl.fn.fname ^ ">"
  | VToken -> "_"
