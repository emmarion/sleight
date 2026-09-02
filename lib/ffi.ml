open Value

(* The prototype's fixed FFI (section 41): extern implementations by name, consulted where a def-adts or def-fns is
   marked extern. Integers are zarith's. Each extern-marked definition in Builtin.source is the model these stand in for. *)

let registered : (string, adt) Hashtbl.t = Hashtbl.create 8
let z = function VExt (_, n) -> n | v -> raise (Eval.Runtime ("not an extern integer: " ^ show v))
let int name n = VExt (Hashtbl.find registered name, n)

(* A Peano-declared type held as an integer: constructor 0 is zero, constructor 1 the successor. *)
let peano adt =
  { construct = (fun i args -> match (i, args) with 0, [] -> VExt (adt, Z.zero) | 1, [ n ] -> VExt (adt, Z.succ (z n)) | _ -> assert false);
    destruct = (fun v -> let n = z v in if Z.equal n Z.zero then (0, []) else (1, [ VExt (adt, Z.pred n) ])) }

let modulus = Z.of_int 256

(* A bounded Nat with one constructor, whose runtime field is a Nat. *)
let bounded adt =
  { construct = (fun _ args -> match args with [ n ] -> VExt (adt, z n) | _ -> assert false);
    destruct = (fun v -> (0, [ int "Nat" (z v) ])) }

let types : (string * (adt -> ext)) list =
  List.map (fun (name, mk) -> (name, fun adt -> Hashtbl.replace registered name adt; mk adt)) [ ("Nat", peano); ("U8", bounded) ]

let unary name f = function [ a ] -> [ int name (f (z a)) ] | _ -> raise (Eval.Runtime "extern arity")
let binary name f = function [ a; b ] -> [ int name (f (z a) (z b)) ] | _ -> raise (Eval.Runtime "extern arity")

let fns : (string * (value list -> value list)) list =
  [ ("nat-add", binary "Nat" Z.add);
    ("u8-add", binary "U8" (fun a b -> Z.rem (Z.add a b) modulus));
    ("nat-to-u8", unary "U8" (fun n -> Z.rem n modulus));
    ("u8-to-nat", unary "Nat" Fun.id) ]
