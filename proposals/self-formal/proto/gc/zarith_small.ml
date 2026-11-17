(* Is every Z.t in [0, 2^62) an immediate however it is computed, and 2^62 not? Results of big
   intermediates, string parsing, shifts, division, gcd, and Sleight's own Nat operations. *)
let p62 = Z.shift_left Z.one 62
let big = Z.pow (Z.of_int 3) 200
let below = [
  Z.sub p62 Z.one; Z.pred p62; Z.sub (Z.add big (Z.of_int 5)) big; Z.div (Z.mul big (Z.of_int 7)) big;
  Z.rem big (Z.of_int 1_000_003); Z.shift_right big 270; Z.shift_right (Z.shift_left (Z.of_int 12345) 100) 100;
  Z.of_string "4611686018427387903"; Z.of_string "0"; Z.div (Z.gcd big (Z.mul big (Z.of_int 4))) big;
  Z.logand big (Z.of_int 0xFFFF); Z.sqrt (Z.mul (Z.sub p62 Z.one) (Z.sub p62 Z.one)); Z.of_int64 4611686018427387903L;
  Z.of_float 4.0e18; Z.neg (Z.neg (Z.of_int 99)); Z.abs (Z.of_int (-7)); Z.sub (Z.mul p62 p62) (Z.mul p62 p62) ]
let () =
  List.iteri (fun i z -> if Z.lt z p62 && Z.geq z Z.zero && not (Obj.is_int (Obj.repr z)) then Printf.printf "case %d boxed\n" i) below;
  let rng = Random.State.make [| 7 |] in
  let boxed = ref 0 in
  for _ = 1 to 1_000_000 do
    let a = Z.add big (Z.of_int (Random.State.bits rng)) in
    let z = Z.rem a (Z.shift_left Z.one (1 + Random.State.int rng 62)) in
    if not (Obj.is_int (Obj.repr z)) then incr boxed
  done;
  Printf.printf "2^62 immediate: %b; 2^62-1 immediate: %b; random reductions below 2^62 boxed: %d of 1000000\n"
    (Obj.is_int (Obj.repr p62)) (Obj.is_int (Obj.repr (Z.pred p62))) !boxed
