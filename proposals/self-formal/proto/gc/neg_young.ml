(* Negative control (a): a young pointer stored into an old block through an [int array] cast, so no
   remembered-set entry is made. Argument "barrier" uses an [Obj.t array] store instead (caml_modify). *)
type node = { key : int; check : int }

let barrier = Array.length Sys.argv > 1 && Sys.argv.(1) = "barrier"
let old = Array.make 1000 (Obj.repr 0)

let[@inline never] put k =
  let n = Obj.repr { key = k; check = k * 7 + 1 } in
  if barrier then Array.unsafe_set old 0 n else Array.unsafe_set (Obj.obj (Obj.repr old) : int array) 0 (Obj.obj n : int)

let () =
  Gc.full_major ();
  let bad = ref 0 and trials = 10_000 in
  for k = 1 to trials do
    put k;
    Gc.minor ();
    ignore (Sys.opaque_identity (Array.init 4096 (fun i -> { key = -i; check = -i })));
    let w = old.(0) in
    if Obj.is_int w then incr bad
    else (let n : node = Obj.obj w in if n.key <> k || n.check <> k * 7 + 1 then incr bad);
    Array.unsafe_set old 0 (Obj.repr 0)
  done;
  Printf.printf "%s: %d of %d trials read a corrupted node\n" (if barrier then "barrier" else "no barrier") !bad trials
