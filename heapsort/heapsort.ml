let sift (a : int array) m i =
  let rec go i =
    let l = 2 * i + 1 in
    if l < m then begin
      let c = if l + 1 < m && a.(l) <= a.(l + 1) then l + 1 else l in
      if a.(c) > a.(i) then begin
        let t = a.(i) in
        a.(i) <- a.(c);
        a.(c) <- t;
        go c
      end
    end
  in
  go i

let heapsort a =
  let n = Array.length a in
  for k = n / 2 - 1 downto 0 do sift a n k done;
  for m = n downto 2 do
    let t = a.(0) in
    a.(0) <- a.(m - 1);
    a.(m - 1) <- t;
    sift a (m - 1) 0
  done

let gen n =
  let s = ref 0x9E3779B97F4A7C15L in
  Array.init n (fun _ ->
    let open Int64 in
    s := logxor !s (shift_left !s 13);
    s := logxor !s (shift_right_logical !s 7);
    s := logxor !s (shift_left !s 17);
    to_int (shift_right_logical !s 1))

let () =
  let n = 1 lsl 20 in
  for _ = 1 to 5 do
    let a = gen n in
    let t0 = Sys.time () in
    heapsort a;
    let t1 = Sys.time () in
    Printf.printf "%.1f ms  min %d median %d max %d\n" ((t1 -. t0) *. 1e3) a.(0) a.(n / 2) a.(n - 1)
  done
