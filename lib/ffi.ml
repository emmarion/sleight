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
let str s = VExt (Hashtbl.find registered "String", Slice (s, 0, String.length s))

(* A Peano-declared type held as an integer: constructor 0 is zero, constructor 1 the successor. *)
let peano adt =
  { construct = (fun i args -> match (i, args) with 0, [] -> VExt (adt, Int Z.zero) | 1, [ n ] -> VExt (adt, Int (Z.succ (z n))) | _ -> assert false);
    destruct = (fun v -> let n = z v in if Z.equal n Z.zero then (0, []) else (1, [ VExt (adt, Int (Z.pred n)) ])) }

(* Bijective base 2 held as an integer: constructor 1 is 2b+1, constructor 2 is 2b+2, so every integer has one spelling. *)
let bijective adt =
  let digit d b = VExt (adt, Int (Z.add (Z.shift_left (z b) 1) (Z.of_int d))) in
  { construct = (fun i args -> match (i, args) with 0, [] -> VExt (adt, Int Z.zero) | (1 | 2), [ b ] -> digit i b | _ -> assert false);
    destruct =
      (fun v ->
        let n = z v in
        if Z.equal n Z.zero then (0, [])
        else let d = if Z.is_odd n then 1 else 2 in (d, [ VExt (adt, Int (Z.shift_right (Z.sub n (Z.of_int d)) 1)) ])) }

let modulus = Z.of_int 256

(* A bounded Nat with one constructor, whose runtime field is a Nat. *)
let bounded adt =
  { construct = (fun _ args -> match args with [ n ] -> VExt (adt, Int (z n)) | _ -> assert false);
    destruct = (fun v -> (0, [ int "Nat" (z v) ])) }

(* A cons list of Char held as a slice of a byte string: destructing yields the tail slice over the same buffer. *)
let text adt =
  { construct =
      (fun i args ->
        match (i, args) with
        | 0, [] -> VExt (adt, Slice ("", 0, 0))
        | 1, [ c; rest ] -> let s, o, l = slice rest in VExt (adt, Slice (String.make 1 (Char.chr (Z.to_int (z c))) ^ String.sub s o l, 0, l + 1))
        | _ -> assert false);
    destruct = (fun v -> let s, o, l = slice v in if l = 0 then (0, []) else (1, [ int "U8" (Z.of_int (Char.code s.[o])); VExt (adt, Slice (s, o + 1, l - 1)) ])) }

let types : (string * (adt -> ext)) list =
  List.map
    (fun (name, mk) -> (name, fun adt -> Hashtbl.replace registered name adt; mk adt))
    [ ("Nat", peano); ("U8", bounded); ("Bin", bijective); ("String", text) ]

let unary name f = function [ a ] -> [ int name (f (z a)) ] | _ -> raise (Eval.Runtime "extern arity")
let binary name f = function [ a; b ] -> [ int name (f (z a) (z b)) ] | _ -> raise (Eval.Runtime "extern arity")

let fns : (string * (value list -> value list)) list =
  [ ("nat-add", binary "Nat" Z.add);
    ("u8-add", binary "U8" (fun a b -> Z.rem (Z.add a b) modulus));
    ("nat-to-u8", unary "U8" (fun n -> Z.rem n modulus));
    ("u8-to-nat", unary "Nat" Fun.id);
    ("bin-to-nat", unary "Nat" Fun.id);
    ("trim", function [ s ] -> let b, o, l = slice s in [ str (String.sub b o l) ] | _ -> raise (Eval.Runtime "extern arity")) ]
