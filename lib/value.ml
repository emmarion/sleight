open Term

module IntMap = Map.Make (Int)

type cc = Plain | Tail | Delegate

(* [tagged]: the constructor's type is an enum with more than one non-phantom constructor, so its values carry a tag. *)
type ctor = { cname : string; cid : id; tagged : bool }

type value =
  | VCtor of ctor * value list
  | VTuple of value list
  | VCtorFn of ctor
  | VFn of closure
  | VToken

and closure = { fname : string; params : id list; body : code; env : venv Lazy.t }
and venv = value IntMap.t

and code =
  | CVar of id
  | CConst of value
  | CErased
  | CValues of code list
  | CApp of code * code list * cc
  | CLet of id list * code * code
  | CLetRec of (id * (string * id list * code)) list * code
  | CMatch of code * bool * (code * id list * code) list
  | CAbsurd

(* An untagged value is its many fields: one of them bare, none the token. *)
let tuple = function [ v ] -> v | [] -> VToken | vs -> VTuple vs
let untuple n v = match (n, v) with 1, v -> [ v ] | 0, _ -> [] | _, VTuple vs -> vs | _ -> assert false

let rec show = function
  | VCtor (c, fields) -> "(" ^ String.concat " " (c.cname :: List.map show fields) ^ ")"
  | VTuple vs -> "(" ^ String.concat " " (List.map show vs) ^ ")"
  | VCtorFn c -> "<constructor " ^ c.cname ^ ">"
  | VFn cl -> "<function " ^ cl.fname ^ ">"
  | VToken -> "_"
