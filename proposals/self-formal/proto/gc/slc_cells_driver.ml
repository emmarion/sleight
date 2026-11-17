(* Appended to slc's output for tests/cell_imm.sl in place of its final line; build_slc_cells.sh fills in
   SWAP_IN, WRITE_IN and FRESH_IN with the emitted names. Drives the emitted (imm o n) stores on cells kept
   old, beside pointer-holding blocks, under minor, major and compacting collections. *)
let swap_in = SWAP_IN and write_in = WRITE_IN and fresh_in = FRESH_IN
let n = 512
let rng = ref 0x1234567
let rand k = rng := (!rng * 1103515245 + 12345) land 0x3FFFFFFF; !rng mod k
let u62 v = to_any (Z.of_int v)
let cells = Array.init n (fun i -> fresh_in (u62 i))
let shadow = Array.init n (fun i -> (i, i))
let boxes = Array.init n (fun i -> ref (string_of_int i))
let box_keys = Array.init n (fun i -> i)
let field c i : int = Z.to_int (Obj.obj (Obj.field c i))
let verify () =
  Array.iteri (fun i c -> let a, b = shadow.(i) in
    if field c 0 <> a || field c 1 <> b || !(boxes.(i)) <> string_of_int box_keys.(i) then failwith (Printf.sprintf "cell %d" i)) cells
let () =
  let iters = try int_of_string Sys.argv.(1) with _ -> 2_000_000 in
  let junk = ref [] in
  for it = 1 to iters do
    let i = rand n and z = rand 1_000_000_000 in
    (match rand 4 with
     | 0 -> ignore (swap_in cells.(i) (u62 z)); let _, b = shadow.(i) in shadow.(i) <- (b, z)
     | 1 -> ignore (write_in cells.(i) (u62 z)); let _, b = shadow.(i) in shadow.(i) <- (z, b)
     | 2 -> cells.(i) <- fresh_in (u62 z); shadow.(i) <- (z, z)
     | _ -> boxes.(i) := string_of_int it; box_keys.(i) <- it);
    junk := ref it :: (if it mod 997 = 0 then [] else !junk);
    if it mod 50_000 = 0 then (ignore (Gc.major_slice 0); verify ());
    if it mod 400_000 = 0 then (Gc.full_major (); verify ());
    if it mod 1_000_000 = 0 then (Gc.compact (); verify ())
  done;
  Gc.full_major (); Gc.compact (); verify ();
  let s = Gc.quick_stat () in
  Printf.printf "ok iters=%d minor=%d major=%d compactions=%d\n" iters s.minor_collections s.major_collections s.compactions
