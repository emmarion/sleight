open X_c1sim10c
let qi = function A->0|B->1|C->2|D->3|E->4|F->5
let si = function S0->0|S1->1
let side b l = Buffer.add_string b (string_of_int (List.length l));
  List.iter (fun (s, n) -> Buffer.add_char b ' '; Buffer.add_string b (string_of_int (si s)); Buffer.add_char b ' '; Buffer.add_string b (Z.to_string n)) l;
  Buffer.add_char b '\n'
let txt (((q, ll), s), rr) = let b = Buffer.create 100000 in
  Buffer.add_string b (Printf.sprintf "%d %d\n" (qi q) (si s)); side b ll; side b rr; Buffer.contents b
let rec dropn n l = if n = 0 then l else dropn (n - 1) (List.tl l)
let rec taken n l = if n = 0 then [] else List.hd l :: taken (n - 1) (List.tl l)
let req (s1, n1) (s2, n2) = s1 = s2 && Z.equal n1 n2
let sdiff o n =
  let lo = List.length o and ln = List.length n in
  let k = min lo ln in
  let rec go a b i last = match a, b with
    | x :: a', y :: b' -> if a == b then last else go a' b' (i + 1) (if req x y then last else i + 1)
    | _ -> last in
  let m = go (dropn (lo - k) o) (dropn (ln - k) n) 0 0 in
  let common = k - m in
  let b = Buffer.create 64 in
  Buffer.add_string b (string_of_int (lo - common)); Buffer.add_char b ' '; side b (taken (ln - common) n); Buffer.contents b
let diff (((_, l0), _), r0) (((q, l1), s), r1) = Printf.sprintf "2 %d %d\n%s%s" (qi q) (si s) (sdiff l0 l1) (sdiff r0 r1)
let writef f s = let oc = open_out f in output_string oc s; close_out oc
let z = Z.of_int
let reg p = let dg = phiONW2 p (Z.sub (Z.mul (z 2) (lpF p)) (z 2)) in rle_cells (S0 :: flat (enc dg) @ tc T2)
let mk ll rr = (((C, ll), S1), rr)
let out = Buffer.create 1000000
let cur = ref None
let emit c i c' =
  (match !cur with None -> Buffer.add_string out (txt c) | Some c0 -> Buffer.add_string out ("4 0 " ^ String.sub (diff c0 c) 2 (String.length (diff c0 c) - 2)));
  Buffer.add_string out (Printf.sprintf "4 %d " i ^ String.sub (diff c c') 2 (String.length (diff c c') - 2)); cur := Some c'
let nb = ref 0 and nr = ref 0
let () =
  let tailR = [(S1, z 7); (S0, z 3); (S1, z 2)] in
  for p = 3 to 7 do
    let p1 = p - 1 in
    let u = uoN2 p and kt = kturnF2 p1 and tn = tN2 p1 and u1 = uoN2 p1 in
    List.iter (fun d ->
      let e' = Z.sub (Z.neg tn) (z d) in
      let e' = if Z.is_even e' then e' else Z.pred e' in
      if Z.leq Z.zero (Z.add e' u1) then begin
        let g = Z.add (Z.add e' u) kt in
        let st0 = Z.add (Z.add (Z.mul (z 4) e') (Z.neg (pw2 p1))) (cAN2 p1) in
        let h = Z.add (Z.sub (kdF2 p1) st0) (z 5) in
        if Z.sign g > 0 && Z.sign h > 0 then begin
          let c = mk [(S0, z 2); (S1, z 5); (S0, z 1); (S1, z 1)] (reg p @ (S0, g) :: (S1, z 6) :: (S0, h) :: tailR) in
          match try_beven2 c with Some (c', _) -> incr nb; emit c 8 c' | None -> () end end) [0; 2; 10; 101]
  done;
  for p = 1 to 6 do
    let up = uoN p and c1 = c1F p in
    for k = 0 to 400 do
      let f = Z.sub (z 2) (z (2 * k)) in
      let g = Z.sub (Z.sub f c1) (Z.neg up) in
      if Z.sign g > 0 then
        List.iter (fun h0 -> List.iter (fun h1 ->
          let c = mk [(S0, z 2); (S1, z 2); (S0, z 1); (S1, z 1)] (reg p @ (S0, g) :: (S1, z 6) :: (S0, z h0) :: (S1, z 6) :: (S0, Z.of_string h1) :: tailR) in
          match try_reent c with Some (c', _) -> incr nr; emit c 7 c' | None -> ()) ["5"; "1000"; "100000000000000000000000000000000"]) [4; 5; 8; 21; 100]
    done
  done;
  Buffer.add_string out "0\n";
  print_string (Buffer.contents out);
  Printf.eprintf "beven %d reent %d\n" !nb !nr
