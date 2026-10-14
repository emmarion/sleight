let () =
  let n = 1 lsl 20 in
  let a = Array.make n 0 in
  let s = ref 42 in
  for j = 0 to n - 1 do
    s := (!s * 1103515245 + 12345) mod (1 lsl 30);
    a.(n - 1 - j) <- !s
  done;
  let w0 = Gc.minor_words () in
  let t0 = Unix.gettimeofday () in
  heapsort a;
  let t1 = Unix.gettimeofday () in
  let w1 = Gc.minor_words () in
  let sum = ref Z.zero in
  Array.iteri (fun i x -> sum := Z.add !sum (Z.mul (Z.of_int (i + 1)) (Z.of_int x))) a;
  Printf.printf "ms %.3f checksum %s minor-words %.0f\n" ((t1 -. t0) *. 1e3) (Z.to_string !sum) (w1 -. w0)
