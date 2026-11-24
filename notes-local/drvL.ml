open X_c1sim10c
let names = [| "BIGJC"; "BIGJ"; "RET"; "VDESC"; "WALKN"; "CHILD"; "BCOVF"; "REENT"; "BEVEN"; "CHAIN"; "DEATH"; "AEND"; "L0"; "AX";
               "FRAME"; "TRAIN"; "TRAING"; "FDESC"; "CONTACT"; "CONTACT0"; "ITER"; "IDENT"; "SWEEP3"; "ABSORB"; "RESUME1"; "VDESC2" |]
let nm i = if i >= 0 && i < Array.length names then names.(i) else "M9"
let qi = function A->0|B->1|C->2|D->3|E->4|F->5
let si = function S0->0|S1->1
let side b l = Buffer.add_string b (string_of_int (List.length l));
  List.iter (fun (s, n) -> Buffer.add_char b ' '; Buffer.add_string b (string_of_int (si s)); Buffer.add_char b ' '; Buffer.add_string b (Z.to_string n)) l;
  Buffer.add_char b '\n'
let txt (((q, ll), s), rr) = let b = Buffer.create 100000 in
  Buffer.add_string b (Printf.sprintf "%d %d\n" (qi q) (si s)); side b ll; side b rr; Buffer.contents b
let lm_parts (((q, ll), s), rr) = match q, s with
  | C, S1 -> (match left_split ll, parse7 rr with
     | Some (n, l0), Some (dg, t) -> let x = enc dg in
       (match strip (rle_cells (S0 :: flat x @ tc t)) rr with Some r' -> Some (n, l0, dg, x, t, r') | None -> None)
     | _ -> None)
  | _ -> None
let mac (((q, ll), s), _) = match q, ll, s with
  | C, (S1, p) :: _, S1 when Z.sign p > 0 -> "WIPE" | C, (S0, p) :: _, S0 when Z.sign p > 0 -> "CHAINW" | _ -> "STEP"
let rest c = if walk_move c <> None then "WALK" else if is_wc c then mac c else if shift c <> None then "SHIFT" else mac c
let m9class c = match lm_parts c with
  | Some (n, l0, dg, x, t, r') ->
    if try_jump9 n l0 dg x t r' <> None then "JUMP" else if try_round n l0 x t r' <> None then "ROUND"
    else if try_sweep n l0 x t r' <> None then "SWEEP" else rest c
  | None -> rest c
let m9code c = match m9class c with "STEP" -> 0 | "CHAINW" -> 1 | "WIPE" -> 2 | "ROUND" -> 3 | "JUMP" -> 4 | "SWEEP" -> 5 | "WALK" -> 6 | _ -> 7
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
let () = match Sys.argv.(1) with
  | "trace" ->
    let n = int_of_string Sys.argv.(2) and dir = Sys.argv.(3) in
    let cks = List.map int_of_string (Array.to_list (Array.sub Sys.argv 4 (Array.length Sys.argv - 4))) in
    let tr = open_out (dir ^ "/trace.txt") in
    let c = ref rc0 in
    if List.mem 0 cks then writef (Printf.sprintf "%s/c_%d.txt" dir 0) (txt !c);
    for m = 1 to n do
      let ta = Unix.gettimeofday () in
      let r = moveC10 !c in
      let dt = Unix.gettimeofday () -. ta in
      let cls = match r with None -> failwith "stuck" | Some (i, _) -> if nm i = "M9" then "M9:" ^ m9class !c else nm i in
      (match r with Some (_, (c', _)) -> c := c' | None -> ());
      Printf.fprintf tr "%d %s %.6f\n" m cls dt;
      if List.mem m cks then (flush tr; writef (Printf.sprintf "%s/c_%d.txt" dir m) (txt !c))
    done; close_out tr
  | "hints" ->
    let a = int_of_string Sys.argv.(2) and b = int_of_string Sys.argv.(3) and out = Sys.argv.(4) and all = Sys.argv.(5) = "all" in
    let c = ref rc0 in
    for _ = 1 to a do (match moveC10 !c with Some (_, (c', _)) -> c := c' | None -> failwith "stuck") done;
    let oc = open_out out in
    output_string oc (txt !c);
    let t9 = ref 0.0 and n9 = ref 0 in
    for _ = a + 1 to b do
      let c0 = !c in
      let r = match moveC10 c0 with Some r -> r | None -> failwith "stuck" in
      let (i, (c1, _)) = r in
      let cls = if nm i = "M9" then m9code c0 else -1 in
      if cls >= 0 then begin
        let ta = Unix.gettimeofday () in ignore (move9 c0); t9 := !t9 +. (Unix.gettimeofday () -. ta); incr n9 end;
      if cls >= 0 && cls < 6 && not all then
        let (((q, ll), s), rr) = c1 in
        let fr = function [] -> "2 0" | (b, n) :: _ -> Printf.sprintf "%d %s" (si b) (Z.to_string n) in
        Printf.fprintf oc "1 %d %d %d %s %s\n" cls (qi q) (si s) (fr ll) (fr rr)
      else output_string oc (diff c0 c1);
      c := c1
    done;
    output_string oc "0\n"; close_out oc;
    writef (out ^ ".end") (txt !c);
    Printf.printf "move9 alone: %d moves %.3f s\n" !n9 !t9
  | "hm" ->
    let a = int_of_string Sys.argv.(2) and b = int_of_string Sys.argv.(3) and out = Sys.argv.(4) in
    let mine = List.map int_of_string (String.split_on_char ',' Sys.argv.(5)) in
    let c = ref rc0 in
    for _ = 1 to a do (match moveC10 !c with Some (_, (c', _)) -> c := c' | None -> failwith "stuck") done;
    let oc = open_out out in
    output_string oc (txt !c);
    for _ = a + 1 to b do
      let c0 = !c in
      let (i, (c1, _)) = match moveC10 c0 with Some r -> r | None -> failwith "stuck" in
      let cls = if nm i = "M9" then m9code c0 else -1 in
      if cls >= 0 && cls < 6 then begin
        let (((q, ll), s), rr) = c1 in
        let fr = function [] -> "2 0" | (b, n) :: _ -> Printf.sprintf "%d %s" (si b) (Z.to_string n) in
        Printf.fprintf oc "1 %d %d %d %s %s\n" cls (qi q) (si s) (fr ll) (fr rr) end
      else begin
        let d = diff c0 c1 in
        if List.mem i mine then Printf.fprintf oc "3 %d %s" i (String.sub d 2 (String.length d - 2))
        else output_string oc d end;
      c := c1
    done;
    output_string oc "0\n"; close_out oc;
    writef (out ^ ".end") (txt !c)
  | "frames" ->
    let dir = Sys.argv.(2) in
    List.iteri (fun i e -> writef (Printf.sprintf "%s/fin%d.txt" dir i) (txt (((e.fq, e.fL), e.fs), e.fR @ [(S0, e.fcap)]));
      writef (Printf.sprintf "%s/fout%d.txt" dir i) (txt e.fout)) tbl1;
    writef (dir ^ "/axin.txt") (txt (((C, lL0), S1), aXloc @ [(S0, aXcap)]));
    writef (dir ^ "/axout.txt") (txt aXout);
    writef (dir ^ "/preA.txt") (txt (((C, lL0), S1), preA));
    writef (dir ^ "/preB.txt") (txt (((C, lL0), S1), preB));
    writef (dir ^ "/l0aout.txt") (txt (((C, lL0), S1), outAO (Z.add nWN (Z.of_int 4)) []));
    writef (dir ^ "/nums.txt") (Printf.sprintf "%s %s %s\n" (Z.to_string nBN) (Z.to_string nWN) (Z.to_string aXcap))
  | "sim9" ->
    let n = int_of_string Sys.argv.(2) in
    let c = ref rc0 in
    let ta = Unix.gettimeofday () in
    (try for _ = 1 to n do (match move9 !c with Some (c', _) -> c := c' | None -> raise Exit) done with Exit -> ());
    Printf.eprintf "sim9 %d moves %.3f s\n" n (Unix.gettimeofday () -. ta);
    print_string (txt !c)
  | _ -> prerr_endline "usage"
