(* The tree-walking interpreter's array-blit-imm (lib/ffi.ml, blit_imm) calls Ffi_core.array_blit_imm on a
   [Value.value array], whose elements, a Nat's [VWord] included, are blocks. This makes the same call: a
   young [VWord] source blitted into an old destination, then a minor collection. *)
open Sleight
module V = Value

let blit_imm s i d j n = Ffi_core.array_blit_imm s (Z.of_int i) d (Z.of_int j) (Z.of_int n)
let dst = Array.make 1000 (V.VWord Z.zero)

let[@inline never] fill k = blit_imm (Array.init 8 (fun i -> V.VWord (Z.of_int (k + i)))) 0 dst 0 8

let () =
  Gc.full_major ();
  let bad = ref 0 and trials = 10_000 in
  for k = 1 to trials do
    Gc.minor ();
    fill k;
    Gc.minor ();
    ignore (Sys.opaque_identity (Array.init 4096 (fun i -> ref (-i))));
    for i = 0 to 7 do
      match dst.(i) with V.VWord z when Obj.is_int (Obj.repr z) && Z.equal z (Z.of_int (k + i)) -> () | _ -> incr bad
    done;
    Array.fill dst 0 8 (V.VWord Z.zero)
  done;
  Printf.printf "%d of %d elements read back wrong after a blit_imm of young VWords into an old array\n" !bad (8 * trials)
