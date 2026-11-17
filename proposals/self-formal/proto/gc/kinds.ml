(* Read with ocamlfind ocamlopt -dcmm -c kinds.ml: which stores get caml_modify. *)
type t = K of { mutable f0 : Obj.t; mutable f1 : Obj.t }
let int_cast_on_array (a : Obj.t array) i (x : Obj.t) = Array.unsafe_set (Obj.obj (Obj.repr a) : int array) i (Obj.obj x : int)
let int_cast_on_cell (c : Obj.t) (x : Obj.t) = Array.unsafe_set (Obj.obj c : int array) 1 (Obj.obj x : int)
let obj_array (a : Obj.t array) i x = Array.unsafe_set a i x
type word = ..
let word_array (a : word array) i x = Array.unsafe_set a i x
let record_field (c : t) x = match c with K r -> r.f1 <- x
