open Value

(* The prototype's fixed FFI (section 41): extern implementations by name, consulted where a def-adts or def-fns is
   marked extern. Integers are zarith's. Each extern-marked definition in Builtin.source is the model these stand in for. *)

let registered : (string, adt) Hashtbl.t = Hashtbl.create 8
let claimed : (string, unit) Hashtbl.t = Hashtbl.create 8
let reset () = Hashtbl.reset registered; Hashtbl.reset claimed

(* Each implementation may back one declaration per program. *)
let claim table name =
  match List.assoc_opt name table with
  | None -> None
  | Some impl -> if Hashtbl.mem claimed name then Some (Error ()) else (Hashtbl.replace claimed name (); Some (Ok impl))

let z = function VExt (_, Int n) -> n | v -> raise (Eval.Runtime ("not an extern integer: " ^ show v))
let slice = function VExt (_, Slice (s, o, l)) -> (s, o, l) | v -> raise (Eval.Runtime ("not an extern string: " ^ show v))
let int name n = VExt (Hashtbl.find registered name, Int n)
let text sl = VExt (Hashtbl.find registered "String", Slice sl)
let str s = text (s, 0, String.length s)

let ext (construct, destruct) = { construct; destruct }

let types : (string * (adt -> ext)) list =
  List.map
    (fun (name, mk) -> (name, fun adt -> Hashtbl.replace registered name adt; ext (mk adt)))
    [ ("Nat", fun adt -> Ffi_core.peano ~z ~nat:(fun n -> VExt (adt, Int n)));
      ("U8", fun adt -> Ffi_core.bounded ~z ~nat:(int "Nat") ~u8:(fun n -> VExt (adt, Int n)));
      ("Bin", fun adt -> Ffi_core.bijective ~z ~bin:(fun n -> VExt (adt, Int n)));
      ("String", fun adt -> Ffi_core.text ~z ~slice ~u8:(int "U8") ~str:(fun s -> VExt (adt, Slice s))) ]

let unary name f = function [ a ] -> [ int name (f (z a)) ] | _ -> raise (Eval.Runtime "extern arity")
let binary name f = function [ a; b ] -> [ int name (f (z a) (z b)) ] | _ -> raise (Eval.Runtime "extern arity")

let fns : (string * (value list -> value list)) list =
  [ ("nat-add", binary "Nat" Ffi_core.nat_add);
    ("u8-add", binary "U8" Ffi_core.u8_add);
    ("nat-to-u8", unary "U8" Ffi_core.nat_to_u8);
    ("u8-to-nat", unary "Nat" Ffi_core.u8_to_nat);
    ("bin-to-nat", unary "Nat" Ffi_core.bin_to_nat);
    ("trim", function [ s ] -> [ text (Ffi_core.trim (slice s)) ] | _ -> raise (Eval.Runtime "extern arity")) ]
