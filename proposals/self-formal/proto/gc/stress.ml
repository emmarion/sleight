(* Positive stress: barrier-free immediate-over-immediate stores through Sleight's own Ffi_core
   (array_swap_imm, array_place_imm, array_blit_imm) and through the emitted (imm o n) store shape,
   into old blocks that also hold pointers, under minor, major, and compacting collections. *)
module F = Sleight.Ffi_core

type node = { key : int; payload : string }

let node k = { key = k; payload = String.make (8 + (k land 15)) (Char.chr (65 + (k land 25))) }

let check_node k (n : node) =
  n.key = k && String.length n.payload = 8 + (k land 15)
  && String.for_all (fun c -> c = Char.chr (65 + (k land 25))) n.payload

type cell = K of { mutable p : Obj.t; mutable a : Obj.t; mutable b : Obj.t }

let iters = try int_of_string Sys.argv.(1) with _ -> 2_000_000
let narrays = 48
let len i = if i mod 3 = 0 then 600 else 40
let half i = len i / 2
let rng = ref 0x2545F491
let rand n = rng := (!rng * 1103515245 + 12345) land 0x3FFFFFFF; !rng mod n

(* Indices [0, half) hold node pointers, [half, len) hold ints; shadow tracks both. *)
let arrays = Array.init narrays (fun i -> Array.init (len i) (fun j -> if j < half i then Obj.repr (node (i * 1000 + j)) else Obj.repr j))
let keys = Array.init narrays (fun i -> Array.init (len i) (fun j -> if j < half i then i * 1000 + j else j))
let cells = Array.init 256 (fun i -> K { p = Obj.repr (node i); a = Obj.repr 0; b = Obj.repr 0 })
let cell_keys = Array.init 256 (fun i -> (i, 0, 0))

let emitted_store cell k v = Array.unsafe_set (Obj.obj cell : int array) k (Obj.obj v : int)

let verify () =
  Array.iteri (fun i a ->
    Array.iteri (fun j w ->
      let k = keys.(i).(j) in
      if j < half i then (if Obj.is_int w || not (check_node k (Obj.obj w)) then failwith (Printf.sprintf "node %d.%d" i j))
      else if not (Obj.is_int w) || (Obj.obj w : int) <> k then failwith (Printf.sprintf "imm %d.%d" i j)) a) arrays;
  Array.iteri (fun i (K c) ->
    let p, a, b = cell_keys.(i) in
    if not (check_node p (Obj.obj c.p)) || (Obj.obj c.a : int) <> a || (Obj.obj c.b : int) <> b then failwith (Printf.sprintf "cell %d" i)) cells

let garbage = ref []

let () =
  Gc.full_major ();
  let swaps = ref 0 in
  for it = 1 to iters do
    let i = rand narrays in
    let a = arrays.(i) and h = half i in
    (match rand 8 with
     | 0 | 1 | 2 ->
       let j = h + rand h and v = rand 1_000_000_000 in
       let old : int = F.array_swap_imm a (Z.of_int j) (Z.of_int v) |> Obj.repr |> Obj.obj in
       if old <> keys.(i).(j) then failwith "swap old";
       keys.(i).(j) <- v; incr swaps
     | 3 ->
       let j = h + rand h and v = rand 1_000_000_000 in
       F.array_place_imm a (Z.of_int j) (Z.of_int v); keys.(i).(j) <- v
     | 4 ->
       let i2 = rand narrays in
       let n = 1 + rand (min h (half i2)) in
       let src_j = half i2 + rand (half i2 - n + 1) and dst_j = h + rand (h - n + 1) in
       F.array_blit_imm arrays.(i2) (Z.of_int src_j) a (Z.of_int dst_j) (Z.of_int n);
       Array.blit keys.(i2) src_j keys.(i) dst_j n
     | 5 ->
       let j = rand h and k = it in
       a.(j) <- Obj.repr (node k); keys.(i).(j) <- k
     | 6 ->
       let c = rand 256 in
       let va = rand 1_000_000 and vb = rand 1_000_000 in
       emitted_store (Obj.repr cells.(c)) 1 (Obj.repr va);
       emitted_store (Obj.repr cells.(c)) 2 (Obj.repr vb);
       let p, _, _ = cell_keys.(c) in cell_keys.(c) <- (p, va, vb)
     | _ ->
       let c = rand 256 in
       let (K r) = cells.(c) in
       r.p <- Obj.repr (node (it + 7)); let _, va, vb = cell_keys.(c) in cell_keys.(c) <- (it + 7, va, vb));
    garbage := node it :: (if it mod 1000 = 0 then [] else !garbage);
    if it mod 50_000 = 0 then (ignore (Gc.major_slice 0); verify ());
    if it mod 400_000 = 0 then (Gc.full_major (); verify ());
    if it mod 1_000_000 = 0 then (Gc.compact (); verify ())
  done;
  Gc.full_major (); Gc.compact (); verify ();
  let s = Gc.quick_stat () in
  Printf.printf "ok iters=%d swaps=%d minor=%d major=%d compactions=%d\n" iters !swaps s.minor_collections s.major_collections s.compactions
