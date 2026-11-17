(* Negative control (b): during marking, the only reference to a white old block [x] is moved from a
   block [b] whose scan has not reached it into an already-black block [a], and b's slot is overwritten by an
   immediate. Without barrier the overwrite does not darken [x]. Argument "barrier" does both stores with
   caml_modify. Argument "imm" is the positive case: in the same window it makes only barrier-free
   immediate-over-immediate stores, across [a] and [b], leaving [x] in place. A weak pointer reports whether the collector freed [x] while [a] still points at it. *)
(* 4.14 blackens a block when its scan starts and keeps the unscanned rest on the mark stack, so a
   black [b] with a white [x] in its last slot is the window. *)
let mode = if Array.length Sys.argv > 1 then Sys.argv.(1) else "nobarrier"
let barrier = mode = "barrier"

(* Header colour bits 8-9 (4.14: white 0, gray 1, blue 2, black 3), read through the header word as an int. *)
let colour (o : Obj.t) = (Array.unsafe_get (Obj.obj o : int array) (-1) lsr 7) land 3

let store (arr : Obj.t array) i (v : Obj.t) =
  if barrier then Array.unsafe_set arr i v else Array.unsafe_set (Obj.obj (Obj.repr arr) : int array) i (Obj.obj v : int)

type state = { mutable a : Obj.t array; mutable b : Obj.t array; w : Obj.t Weak.t }

let st = { a = [||]; b = [||]; w = Weak.create 1 }
let blen = 4_000_000

let[@inline never] setup () =
  st.a <- Array.make 300 (Obj.repr 0);
  st.b <- Array.make blen (Obj.repr 0);
  let x = Bytes.make 4096 'x' in
  Array.unsafe_set st.b (blen - 1) (Obj.repr x);
  Weak.set st.w 0 (Some (Obj.repr x))

let[@inline never] move () =
  if mode = "imm" then
    for i = 0 to blen - 2 do store st.b i (Obj.repr (i + 1)); if i < 300 then store st.a i (Obj.repr i) done
  else begin
    let x = st.b.(blen - 1) in
    store st.a 1 x;
    store st.b (blen - 1) (Obj.repr 0)
  end

let trial () =
  setup ();
  Gc.full_major ();
  let rec step n =
    if n = 0 then `Missed
    else begin
      ignore (Gc.major_slice 2000);
      let ca = colour (Obj.repr st.a) and cx = colour st.b.(blen - 1) in
      if ca = 3 && cx = 0 then (move (); `Moved) else if cx <> 0 then `Missed else step (n - 1)
    end in
  let r = step 10_000 in
  Gc.full_major ();
  Gc.full_major ();
  match r with
  | `Missed -> `Missed
  | `Moved -> if Weak.check st.w 0 && (mode <> "imm" || Bytes.get (Obj.obj st.b.(blen - 1)) 4095 = 'x') then `Kept else `Freed

let () =
  let moved = ref 0 and freed = ref 0 and missed = ref 0 in
  for _ = 1 to 20 do
    match trial () with `Missed -> incr missed | `Kept -> incr moved | `Freed -> incr moved; incr freed
  done;
  Printf.printf "%s: window hit %d, missed %d; x freed while still referenced in %d\n"
    mode !moved !missed !freed
