open Term

module IntMap = Map.Make (Int)

type repr = Tagged | Field of int | Unspecified

type ctor_info = { cname : string; adt : id; fields : mult list; phantom : bool; repr : repr }

let ctors : (id, ctor_info) Hashtbl.t = Hashtbl.create 64

type cc = Plain | Tail | Delegate

type value =
  | VCtor of id * value list
  | VCtorFn of id
  | VFn of closure
  | VToken

and closure = { fname : string; params : id list; body : code; env : venv Lazy.t }
and venv = value IntMap.t

and code =
  | CVar of id
  | CErased
  | CValues of code list
  | CApp of code * code list * cc
  | CLet of id list * code * code
  | CLetRec of (id * (string * id list * code)) list * code
  | CMatch of code * (code * id list * code) list
  | CAbsurd

(* Const entries' stored values (section 34), looked up by entry id from running code. *)
let consts : (id, value) Hashtbl.t = Hashtbl.create 64

let rec show = function
  | VCtor (c, []) -> "(" ^ (Hashtbl.find ctors c).cname ^ ")"
  | VCtor (c, fields) -> "(" ^ String.concat " " ((Hashtbl.find ctors c).cname :: List.map show fields) ^ ")"
  | VCtorFn c -> "<constructor " ^ (Hashtbl.find ctors c).cname ^ ">"
  | VFn cl -> "<function " ^ cl.fname ^ ">"
  | VToken -> "_"
