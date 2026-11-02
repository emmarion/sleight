(* A conventional-OCaml port of the runtime half of fourcolor/red: C-reducibility of the 633 configurations.
   Colours are ints 0..3, leaf counts are ints, bit stacks are lists. *)

type step = SR of int | SY | SH | SU
type ctree = CNode of ctree * ctree * ctree | CLeaf of int | CEmpty
type gtree = GNode of gtree * gtree * gtree * gtree | GL0 | GL1 | GL2 | GL3 | GL01 | GL12 | GL13 | GL23 | GEmpty
type gsym = GPush | GSkip | GPop0 | GPop1
type bstack = BS0 | BP0 of bstack | BP1 of bstack
type 'a rx = RNil | RCons of bstack * 'a * 'a rx
type gset = GSG of gtree | GSOne
type es = ESStart | ESTail of int array | ESEven | ESOdd

exception Fail

let perm a b c = [| 0; a; b; c |]
let p123 = perm 1 2 3 and p132 = perm 1 3 2 and p231 = perm 2 3 1 and p312 = perm 3 1 2
let addc a b = a lxor b
let rec imem (x : int) = function [] -> false | y :: r -> x = y || imem x r

(* lists *)
let rec take n l = if n = 0 then [] else match l with [] -> [] | x :: r -> x :: take (n - 1) r
let rec drop n l = if n = 0 then l else match l with [] -> [] | _ :: r -> drop (n - 1) r
let rot k l = if k <= List.length l then drop k l @ take k l else l
let rec setnth l i y = match l with [] -> raise Fail | x :: r -> if i = 0 then y :: r else x :: setnth r (i - 1) y
let nth l i = match List.nth_opt l i with Some x -> x | None -> raise Fail
let insert xs c x = let v = nth xs c in setnth xs c x @ [ v ]
let rec last = function [ a ] -> a | _ :: r -> last r | [] -> raise Fail

(* ctrees *)
let cempty = function CEmpty -> true | _ -> false
let gempty = function GEmpty -> true | _ -> false
let ccons t1 t2 t3 = if cempty t1 && cempty t2 && cempty t3 then CEmpty else CNode (t1, t2, t3)
let rec cunion tl tr =
  match tr, tl with
  | CEmpty, _ -> tl
  | CLeaf _, CEmpty -> tr
  | CLeaf _, CLeaf _ -> CLeaf 1
  | CNode _, CEmpty -> tr
  | CNode (r1, r2, r3), CNode (l1, l2, l3) -> ccons (cunion l1 r1) (cunion l2 r2) (cunion l3 r3)
  | _ -> assert false
let rec crot left t =
  match t with
  | CNode (t1, t2, t3) ->
    let a1 = crot left t1 and a2 = crot left t2 and a3 = crot left t3 in
    if left then ccons a3 a1 a2 else ccons a2 a3 a1
  | _ -> t
let cunion_rot tl tr = cunion (crot true tl) (crot false tr)
let rec cunion_rotlr tl tr =
  match tr, tl with
  | CLeaf _, CLeaf _ -> CLeaf 1
  | CNode (r1, r2, r3), CNode (l1, l2, l3) -> ccons (cunion_rotlr l3 r2) (cunion_rotlr l1 r3) (cunion_rotlr l2 r1)
  | _ -> cunion_rot tl tr
let sel t e = match t with CNode (t1, t2, t3) -> (match e with 1 -> t1 | 2 -> t2 | 3 -> t3 | _ -> CEmpty) | _ -> CEmpty
let rec sub t = function [] -> (match t with CLeaf n -> n | _ -> 0) | e :: r -> sub (sel t e) r

(* gtrees *)
let gbits = function
  | GL0 -> (true, false, false, false) | GL1 -> (false, true, false, false) | GL2 -> (false, false, true, false)
  | GL3 -> (false, false, false, true) | GL01 -> (true, true, false, false) | GL12 -> (false, true, true, false)
  | GL13 -> (false, true, false, true) | GL23 -> (false, false, true, true) | _ -> (false, false, false, false)
let pick4 s (a, b, c, d) = match s with GPush -> a | GSkip -> b | GPop0 -> c | GPop1 -> d
let glive g = not (gempty g)

(* ctree restriction by a list of (bstack, gtree) *)
let rgcons bs t acc = if gempty t then acc else RCons (bs, t, acc)
let ctr_split rl =
  let rec go r1 r2 r3 = function
    | RNil -> (r1, r2, r3)
    | RCons (bs, GNode (t0, t1, t2, t3), rest) -> (
      let r1 = rgcons bs t1 r1 in
      match bs with
      | BS0 -> go r1 (rgcons (BP0 bs) t0 r2) (rgcons (BP1 bs) t0 r3) rest
      | BP0 b -> go r1 (rgcons (BP0 bs) t0 (rgcons b t2 r2)) (rgcons (BP1 bs) t0 (rgcons b t3 r3)) rest
      | BP1 b -> go r1 (rgcons (BP0 bs) t0 (rgcons b t3 r2)) (rgcons (BP1 bs) t0 (rgcons b t2 r3)) rest)
    | RCons (_, _, rest) -> go r1 r2 r3 rest
  in
  go RNil RNil RNil rl
let decr_if b lf = if not b then lf else match lf with CLeaf n -> if n = 1 then CEmpty else CLeaf (n - 1) | t -> t
let rec ctr_decr l1 l2 l3 = function
  | RNil -> (l1, l2, l3)
  | RCons (bs, g, rest) -> (
    let (b0, b1, b2, b3) = gbits g in
    let l1 = decr_if b1 l1 in
    match bs with
    | BS0 -> ctr_decr l1 (decr_if b0 l2) (decr_if b0 l3) rest
    | BP0 _ -> ctr_decr l1 (decr_if b0 (decr_if b2 l2)) (decr_if b0 (decr_if b3 l3)) rest
    | BP1 _ -> ctr_decr l1 (decr_if b0 (decr_if b3 l2)) (decr_if b0 (decr_if b2 l3)) rest)
let ife t l = if cempty l then t else CEmpty
(* returns (keep, gone); h = height - 1 *)
let rec crestrict h t rl =
  match t with
  | CEmpty -> (CEmpty, CEmpty)
  | _ when (match rl with RNil -> true | _ -> false) -> (t, CEmpty)
  | CNode (l1, l2, l3) when h = 0 ->
    let m1, m2, m3 = ctr_decr l1 l2 l3 rl in
    ((if m1 == l1 && m2 == l2 && m3 == l3 then t else ccons m1 m2 m3), ccons (ife l1 m1) (ife l2 m2) (ife l3 m3))
  | CNode (t1, t2, t3) ->
    let r1, r2, r3 = ctr_split rl in
    let a1, b1 = crestrict (h - 1) t1 r1 and a2, b2 = crestrict (h - 1) t2 r2 and a3, b3 = crestrict (h - 1) t3 r3 in
    ((if a1 == t1 && a2 == t2 && a3 == t3 then t else ccons a1 a2 a3), ccons b1 b2 b3)
  | CLeaf _ -> assert false

(* gtree restriction by a list of (bstack, ctree) *)
let gtr_split w0 w1 w2 w3 rl =
  let rx w bs t acc = if w && not (cempty t) then RCons (bs, t, acc) else acc in
  let rec go r0 r1 r2 r3 = function
    | RNil -> (r0, r1, r2, r3)
    | RCons (bs, CNode (t1, t2, t3), rest) -> (
      let r0 = rx w0 (BP0 bs) t2 (rx w0 (BP1 bs) t3 r0) and r1 = rx w1 bs t1 r1 in
      match bs with
      | BS0 -> go r0 r1 r2 r3 rest
      | BP0 b -> go r0 r1 (rx w2 b t2 r2) (rx w3 b t3 r3) rest
      | BP1 b -> go r0 r1 (rx w2 b t3 r2) (rx w3 b t2 r3) rest)
    | RCons (_, _, rest) -> go r0 r1 r2 r3 rest
  in
  go RNil RNil RNil RNil rl
let is_leaf = function CLeaf _ -> true | _ -> false
let sym_hit s bs t =
  match t with
  | CNode (t1, t2, t3) -> (
    match s, bs with
    | GPush, _ -> is_leaf t2 || is_leaf t3
    | GSkip, _ -> is_leaf t1
    | (GPop0 | GPop1), BS0 -> false
    | GPop0, BP0 _ | GPop1, BP1 _ -> is_leaf t2
    | GPop0, BP1 _ | GPop1, BP0 _ -> is_leaf t3)
  | _ -> false
let rec gmatch s = function RNil -> false | RCons (bs, t, rest) -> sym_hit s bs t || gmatch s rest
let gleaf_restrict t rl =
  let one s = if gmatch s rl then (t, GEmpty) else (GEmpty, t) in
  let two s1 l1 s2 l2 =
    match gmatch s1 rl, gmatch s2 rl with
    | true, true -> (t, GEmpty)
    | true, false -> (l1, l2)
    | false, true -> (l2, l1)
    | false, false -> (GEmpty, t)
  in
  match t with
  | GL0 -> one GPush | GL1 -> one GSkip | GL2 -> one GPop0 | GL3 -> one GPop1
  | GL01 -> two GPush GL0 GSkip GL1
  | GL12 -> two GSkip GL1 GPop0 GL2
  | GL13 -> two GSkip GL1 GPop1 GL3
  | GL23 -> two GPop0 GL2 GPop1 GL3
  | _ -> (GEmpty, t)
let all_empty a b c d = gempty a && gempty b && gempty c && gempty d
let rec grestrict t rl =
  if (match rl with RNil -> true | _ -> false) then (GEmpty, t)
  else
    match t with
    | GNode (t0, t1, t2, t3) ->
      let r0, r1, r2, r3 = gtr_split (glive t0) (glive t1) (glive t2) (glive t3) rl in
      let a0, b0 = grestrict t0 r0 and a1, b1 = grestrict t1 r1 and a2, b2 = grestrict t2 r2 and a3, b3 = grestrict t3 r3 in
      if all_empty a0 a1 a2 a3 then (GEmpty, if b0 == t0 && b1 == t1 && b2 == t2 && b3 == t3 then t else GNode (b0, b1, b2, b3))
      else if all_empty b0 b1 b2 b3 then (GNode (a0, a1, a2, a3), GEmpty)
      else (GNode (a0, a1, a2, a3), if b0 == t0 && b1 == t1 && b2 == t2 && b3 == t3 then t else GNode (b0, b1, b2, b3))
    | GEmpty -> (GEmpty, GEmpty)
    | _ -> gleaf_restrict t rl

(* the Kempe closure, over mutable copies of ctu and gtu restricted in place *)
type utree = UEmpty | UBot of { mutable l1 : ctree; mutable l2 : ctree; mutable l3 : ctree } | UNode of { mutable u1 : utree; mutable u2 : utree; mutable u3 : utree }
type ugtree = UGEmpty | UGLeaf of { mutable g : gtree } | UGNode of { mutable x0 : ugtree; mutable x1 : ugtree; mutable x2 : ugtree; mutable x3 : ugtree }
let rec ut_of h t =
  match t with
  | CNode (t1, t2, t3) -> if h = 0 then UBot { l1 = t1; l2 = t2; l3 = t3 } else UNode { u1 = ut_of (h - 1) t1; u2 = ut_of (h - 1) t2; u3 = ut_of (h - 1) t3 }
  | _ -> UEmpty
let rec ct_of = function
  | UEmpty -> CEmpty
  | UBot b -> CNode (b.l1, b.l2, b.l3)
  | UNode n -> CNode (ct_of n.u1, ct_of n.u2, ct_of n.u3)
let rec ug_of = function
  | GNode (t0, t1, t2, t3) -> UGNode { x0 = ug_of t0; x1 = ug_of t1; x2 = ug_of t2; x3 = ug_of t3 }
  | GEmpty -> UGEmpty
  | g -> UGLeaf { g }
let uempty = function UEmpty -> true | _ -> false
let ugempty = function UGEmpty -> true | UGLeaf { g = GEmpty } -> true | _ -> false
(* returns (keep, gone); keep is u, updated in place, or UEmpty *)
let rec crestrict_u h u rl =
  match u, rl with
  | UEmpty, _ -> (UEmpty, CEmpty)
  | _, RNil -> (u, CEmpty)
  | UBot b, _ ->
    let m1, m2, m3 = ctr_decr b.l1 b.l2 b.l3 rl in
    let gone = ccons (ife b.l1 m1) (ife b.l2 m2) (ife b.l3 m3) in
    if cempty m1 && cempty m2 && cempty m3 then (UEmpty, gone)
    else (b.l1 <- m1; b.l2 <- m2; b.l3 <- m3; (u, gone))
  | UNode n, _ ->
    let r1, r2, r3 = ctr_split rl in
    let k1, b1 = crestrict_u (h - 1) n.u1 r1 in
    let k2, b2 = crestrict_u (h - 1) n.u2 r2 in
    let k3, b3 = crestrict_u (h - 1) n.u3 r3 in
    let gone = ccons b1 b2 b3 in
    if uempty k1 && uempty k2 && uempty k3 then (UEmpty, gone)
    else (
      if k1 != n.u1 then n.u1 <- k1;
      if k2 != n.u2 then n.u2 <- k2;
      if k3 != n.u3 then n.u3 <- k3;
      (u, gone))
let uglive = function UGEmpty -> false | UGLeaf { g } -> glive g | UGNode _ -> true
(* returns (hit, miss); miss is u, updated in place, or UGEmpty *)
let rec grestrict_u u rl =
  match u, rl with
  | UGEmpty, _ -> (GEmpty, UGEmpty)
  | _, RNil -> (GEmpty, u)
  | UGLeaf l, _ -> let a, b = grestrict l.g rl in l.g <- b; (a, u)
  | UGNode n, _ ->
    let r0, r1, r2, r3 = gtr_split (uglive n.x0) (uglive n.x1) (uglive n.x2) (uglive n.x3) rl in
    let a0, z0 = grestrict_u n.x0 r0 in
    let a1, z1 = grestrict_u n.x1 r1 in
    let a2, z2 = grestrict_u n.x2 r2 in
    let a3, z3 = grestrict_u n.x3 r3 in
    n.x0 <- z0; n.x1 <- z1; n.x2 <- z2; n.x3 <- z3;
    if all_empty a0 a1 a2 a3 then (GEmpty, u)
    else if ugempty z0 && ugempty z1 && ugempty z2 && ugempty z3 then (GNode (a0, a1, a2, a3), UGEmpty)
    else (GNode (a0, a1, a2, a3), u)
let rec gt_of = function
  | UGEmpty -> GEmpty
  | UGLeaf { g } -> g
  | UGNode n -> GNode (gt_of n.x0, gt_of n.x1, gt_of n.x2, gt_of n.x3)
let kempe_tree h ctu ctr gtu =
  let step (u, gtr, gu) =
    if uempty u || gempty gtr then `Done (u, gtr, gu)
    else if ugempty gu then `Done (UEmpty, GEmpty, UGEmpty)
    else
      let keep, gone = crestrict_u h u (RCons (BS0, gtr, RNil)) in
      `Go (keep, cunion_rotlr gone gone, gu)
  in
  let rec ktc d (u, ctr, gu) =
    if d = 0 then
      let hit, miss = grestrict_u gu (RCons (BS0, ctr, RNil)) in
      (u, hit, miss)
    else
      let s1 = ktc (d - 1) (u, ctr, gu) in
      let s2 = match step s1 with `Done s -> s | `Go x -> ktc (d - 1) x in
      match step s2 with `Done s -> s | `Go x -> ktc (d - 1) x
  in
  let u, _, _ = ktc (h + 2) (ut_of h ctu, ctr, ug_of gtu) in
  ct_of u

(* the initial trees *)
let gtree_full h =
  let mk push skip prev =
    let a0, b0 = push and a1, b1 = skip in
    let a2, b2 = match prev with None -> (GEmpty, GEmpty) | Some p -> p in
    (GNode (a0, b1, a2, b2), GNode (b0, a1, b2, a2))
  in
  let vac = (GEmpty, GEmpty) in
  let head = function [] -> vac | e :: _ -> e in
  let rec gstep prev = function [] -> [ mk vac vac prev ] | e :: rest -> mk (head rest) e prev :: gstep (Some e) rest in
  let rec grow k = if k = 0 then [ (GL0, GL01); (GL12, GL13); (GL23, GL23) ] else gstep None (grow (k - 1)) in
  snd (head (grow h))
let gsel gs s =
  match gs with
  | GSOne -> GSG GEmpty
  | GSG (GNode (t0, t1, t2, t3)) -> GSG (match s with GPush -> t0 | GSkip -> t1 | GPop0 -> t2 | GPop1 -> t3)
  | GSG g -> if pick4 s (gbits g) then GSOne else GSG GEmpty
let rscons bs gs acc = match gs with GSG GEmpty -> acc | _ -> RCons (bs, gs, acc)
let psplit e ps =
  let rec go acc = function
    | RNil -> acc
    | RCons (bs, gs, rest) ->
      go
        (match e with
        | 1 -> rscons bs (gsel gs GSkip) acc
        | 2 | 3 ->
          let g1 = gsel gs GPush in
          let c =
            match bs, e with
            | BS0, _ -> acc
            | BP0 b, 2 | BP1 b, 3 -> rscons b (gsel gs GPop0) acc
            | (BP0 b | BP1 b), _ -> rscons b (gsel gs GPop1) acc
          in
          rscons (if e = 3 then BP1 bs else BP0 bs) g1 c
        | _ -> acc)
        rest
  in
  go RNil ps
let esstep st c =
  match st with
  | ESStart -> (match c with 0 -> ESEven | 1 -> ESTail p123 | 2 -> ESTail p312 | _ -> ESTail p231)
  | ESTail g -> (match g.(c) with 2 -> ESEven | 3 -> ESOdd | _ -> st)
  | _ -> st
let leaf n = if n = 0 then CEmpty else CLeaf n
let pcnt3 ps =
  let i b = if b then 1 else 0 in
  let rec go n1 n2 n3 = function
    | RNil -> (n1, n2, n3)
    | RCons (bs, gs, rest) -> (
      let (b0, b1, b2, b3) = match gs with GSOne -> (false, false, false, false) | GSG g -> gbits g in
      match bs with
      | BS0 -> go (n1 + i b1) (n2 + i b0) (n3 + i b0) rest
      | BP0 _ -> go (n1 + i b1) (n2 + i b0 + i b2) (n3 + i b0 + i b3) rest
      | BP1 _ -> go (n1 + i b1) (n2 + i b0 + i b3) (n3 + i b0 + i b2) rest)
  in
  go 0 0 0 ps
let rec ones = function RNil -> 0 | RCons (_, GSOne, r) -> 1 + ones r | RCons (_, _, r) -> ones r
let rec ct_build k ps st =
  if (match ps, st with RNil, _ | _, ESOdd -> true | _ -> false) then CEmpty
  else if k = 0 then leaf (ones ps)
  else if k = 1 then
    let n1, n2, n3 = pcnt3 ps in
    let last e n = if (match esstep st e with ESOdd -> true | _ -> false) then CEmpty else leaf n in
    ccons (last 1 n1) (last 2 n2) (last 3 n3)
  else
    let sub e = ct_build (k - 1) (psplit e ps) (esstep st e) in
    ccons (sub 1) (sub 2) (sub 3)
let ctree_full h gtu = ct_build (h + 1) (RCons (BS0, GSG gtu, RNil)) ESStart

(* the ring colourings of a configuration *)
let ct_cons_e c t = match c with 1 -> ccons t CEmpty CEmpty | 2 -> ccons CEmpty t CEmpty | 3 -> ccons CEmpty CEmpty t | _ -> CEmpty
let rec cfcbr2 g = function [] -> CLeaf 1 | e :: rest -> ct_cons_e g.(e) (cfcbr2 g rest)
let rec cfcbr1 g = function
  | [] -> CLeaf 1
  | e :: rest -> (
    match g.(e) with
    | 0 -> CEmpty
    | 1 -> ct_cons_e 1 (cfcbr1 g rest)
    | 2 -> ct_cons_e 2 (cfcbr2 g rest)
    | _ -> ct_cons_e 2 (cfcbr2 (perm p132.(g.(1)) p132.(g.(2)) p132.(g.(3))) rest))
let cpbranch = function
  | _ :: e1 :: rest -> cfcbr1 (match e1 with 1 -> p123 | 2 -> p312 | 3 -> p231 | _ -> raise Fail) rest
  | _ -> raise Fail
let rec cpcol cp et =
  match cp with
  | [] -> cpbranch et
  | SR k :: rest -> cpcol rest (rot k et)
  | SY :: rest -> (
    match et with
    | [] -> CEmpty
    | e1 :: r1 ->
      let e2 = p231.(e1) and e3 = p312.(e1) in
      cunion (cpcol rest (e2 :: e3 :: r1)) (cpcol rest (e3 :: e2 :: r1)))
  | SH :: rest -> (
    match et with
    | e1 :: e2 :: r2 ->
      if addc e1 e2 = 0 then
        let g1 = p231.(e1) and g2 = p312.(e1) in
        cunion (cpcol rest (g1 :: g1 :: r2)) (cpcol rest (g2 :: g2 :: r2))
      else cpcol rest (e2 :: e1 :: r2)
    | _ -> CEmpty)
  | SU :: _ -> raise Fail
let rec cpcolor0 = function
  | SR _ :: rest -> cpcolor0 rest
  | SY :: rest -> cpcol rest [ 1; 2; 3 ]
  | cp -> cpcol cp [ 1; 1 ]
let cpcolor cp =
  let t0 = cpcolor0 (List.rev cp) in
  ccons t0 (crot true t0) (crot false t0)

(* the configuration map *)
let rec cpmap = function
  | [] -> (2, [ 1; 0 ], [ 0; 1 ], [ 1; 0 ])
  | s :: rest -> (
    let d, e, f, r = cpmap rest in
    let ecpu d e f r =
      let c = nth e (last r) in
      (e @ [ d + 1; d ], insert (f @ [ d ]) c (d + 1), (d + 1) :: d :: r)
    in
    let ecpn d e f r =
      match r with
      | a1 :: p1 -> (
        let x0 = match p1 with [] -> a1 | x :: _ -> x in
        let ex = nth e x0 in
        let z = nth f ex in
        let ea = nth e a1 and ez = nth e z in
        let e2 = e @ [ d + 1; d ] and f2 = insert (insert f ea d) ez (d + 1) in
        if z = a1 then (e2, f2, [ d ]) else match p1 with _ :: _ :: q -> (e2, f2, a1 :: d :: q) | _ -> raise Fail)
      | [] -> raise Fail
    in
    match s with
    | SR k -> (d, e, f, rot k r)
    | SY ->
      let e1, f1, r1 = ecpu d e f r in
      let e2, f2, r2 = ecpn (d + 2) e1 f1 r1 in
      (d + 4, e2, f2, r2)
    | SH ->
      let e1, f1, r1 = ecpu d e f r in
      let e2, f2, r2 = ecpn (d + 2) e1 f1 r1 in
      let e3, f3, r3 = ecpn (d + 4) e2 f2 r2 in
      (d + 6, e3, f3, r3)
    | SU -> raise Fail)
let rec ctrenum = function
  | [] -> []
  | SR _ :: rest -> ctrenum rest
  | SY :: rest -> (match rest with [] -> [] | _ -> let _, _, _, r = cpmap rest in List.hd r :: ctrenum rest)
  | SH :: rest -> (
    let d, _, _, r = cpmap rest in
    match r with a :: p1 -> (d + 2) :: a :: (match p1 with [] -> a | x :: _ -> x) :: ctrenum rest | [] -> raise Fail)
  | SU :: _ -> raise Fail

(* the contract search *)
let all_cols = [ 0; 1; 2; 3 ]
let permt g l = List.map (fun c -> g.(c)) l
let rec eventail = function [] -> true | (0 | 1) :: r -> eventail r | 2 :: _ -> true | _ -> false
let etrace et =
  let b = match et with [] | 0 :: _ -> true | 1 :: l -> eventail l | 2 :: l -> eventail (permt p312 l) | _ :: l -> eventail (permt p231 l) in
  if b then et else permt p132 et
let rec dfs look ie rp us d et =
  match rp with
  | [] -> (match et with [] -> false | _ :: et1 -> look (etrace et1) = 0)
  | s :: rest -> (
    let k = match s with SU -> Some (`U, d + 2) | SY -> Some (`Y, d + 4) | SH -> Some (`H, d + 6) | SR _ -> None in
    match k, s with
    | None, SR k -> dfs look ie rest all_cols d (rot k et)
    | None, _ -> false
    | Some (k, d2), _ -> (
      match us with
      | [] -> true
      | u :: us1 ->
        dfs look ie rp us1 d et
        &&
        let cand =
          match k, et with
          | `U, _ -> Some ([ (d + 1, u) ], u :: u :: et)
          | `Y, e1 :: et1 -> let v = addc u e1 in Some ([ (d + 1, u); (d + 2, v) ], u :: v :: et1)
          | `H, e1 :: e2 :: et2 ->
            let v = addc u e1 in
            let w = addc v e2 in
            Some ([ (d + 1, u); (d + 2, v); (d + 4, w) ], u :: w :: et2)
          | _ -> None
        in
        match cand with
        | None -> true
        | Some (cks, o) ->
          let flag (x, u) = if imem x ie then u = 0 else u <> 0 in
          (not (List.for_all flag cks)) || dfs look ie rest all_cols d2 o))


(* the flat engine: a trace c_0..c_h is the base-3 number of its digits c_i - 1, most significant first, and so is a prefix;
   per-prefix data for level k (prefixes of k digits) of a trie is stored at offs.(k) + prefix *)
let gb b i = Char.code (Bytes.unsafe_get b i)
let sb b i v = Bytes.unsafe_set b i (Char.unsafe_chr v)
type buf = { mutable a : int array; mutable n : int }
let newbuf () = { a = Array.make 1024 0; n = 0 }
let bpush b x =
  if b.n = Array.length b.a then (let a = Array.make (2 * b.n) 0 in Array.blit b.a 0 a 0 b.n; b.a <- a);
  Array.unsafe_set b.a b.n x; b.n <- b.n + 1
let offs = Array.init 17 (fun k -> let p = ref 1 in for _ = 1 to k do p := 3 * !p done; (!p - 1) / 2)
let rec ctree_iter f k p = function
  | CNode (a, b, c) -> ctree_iter f (k + 1) (3 * p) a; ctree_iter f (k + 1) (3 * p + 1) b; ctree_iter f (k + 1) (3 * p + 2) c
  | CLeaf n -> f k p n
  | CEmpty -> ()
(* flat gtree, one word per node: bits 0-3 its part of gu (leaf: the symbols; internal: 1 if nonempty), bits 4-7 its part of gtr
   likewise, bits 8-11 the children present (internal) or all its symbols (leaf), bits 12- the first child; children are contiguous.
   Symbol bits: 1 Push, 2 Skip, 4 Pop0, 8 Pop1.  A bit stack is an int with a sentinel 1 above its bits. *)
let rank = Array.init 64 (fun i -> let m = i lsr 2 in let r = ref 0 in for j = 0 to (i land 3) - 1 do if m land (1 lsl j) <> 0 then incr r done; !r)
external get16 : Bytes.t -> int -> int = "%caml_bytes_get16u"
external set16 : Bytes.t -> int -> int -> unit = "%caml_bytes_set16u"
let child w s = (w lsr 12) + Array.unsafe_get rank (((w lsr 6) land 60) + s)
let in_gu w = w land 15 <> 0
let in_gtr w = w land 0xF0 <> 0
(* ul: levels 0..h, the number of live children of each trace prefix; uc: the 16-bit count of each trace;
   rot: digit-rotation tables (by 1 and by 2) for the low lo-digit part and the high part of a trace *)
type eng = { h : int; nodes0 : int array; ul0 : Bytes.t; uc0 : Bytes.t; lo : int; rot : int array array }
let hits = newbuf () and gone = newbuf () and celems = newbuf ()
(* the digits a leaf's symbol set m matches, given the top of the bit stack (0 empty, 1 + bit): as 2-bit counts per digit
   (sdig), and as the subset of m matching a trace of a 3-bit set x of digits (ghit) *)
let digits m top = List.concat_map (fun (s, ds) -> if m land (1 lsl s) <> 0 then List.map (fun d -> (s, d)) ds else [])
  [ (0, [ 1; 2 ]); (1, [ 0 ]); (2, if top = 0 then [] else [ top ]); (3, if top = 0 then [] else [ 3 - top ]) ]
let sdig = Array.init 64 (fun i -> List.fold_left (fun a (_, d) -> a + (1 lsl (2 * d))) 0 (digits (i lsr 2) (i land 3)))
let ghit = Array.init 512 (fun i -> List.fold_left (fun a (s, d) -> if (i land 7) land (1 lsl d) <> 0 then a lor (1 lsl s) else a) 0 (digits (i lsr 5) ((i lsr 3) land 3)))
let top bs = if bs > 1 then 1 + (bs land 1) else 0
let rec kill_up ul k p = if k > 0 then (let p' = p / 3 in let j = offs.(k - 1) + p' in let c = gb ul j - 1 in sb ul j c; if c = 0 then kill_up ul (k - 1) p')
let died ul h t = bpush gone t; kill_up ul (h + 1) t
let dec uc ul h t c = let n = get16 uc (2 * t) in if n > 0 then (let n' = if n > c then n - c else 0 in set16 uc (2 * t) n'; if n' = 0 then died ul h t)
(* S at a leaf: decrement u by the chromograms of gtr ending in leaf word w, at trace prefix p *)
let sleaf uc ul h p w bs =
  let x = Array.unsafe_get sdig (((w lsr 2) land 60) + top bs) and q = 3 * p in
  if x land 3 <> 0 then dec uc ul h q (x land 3);
  if x land 12 <> 0 then dec uc ul h (q + 1) ((x lsr 2) land 3);
  if x land 48 <> 0 then dec uc ul h (q + 2) (x lsr 4)
(* the walks go down the gtree once, carrying at depth k the trace prefixes p consistent with the chromogram prefix, with their
   bit stacks: lp.(k).(i), lb.(k).(i) for i < ln.(k); there are at most 2^k, a prefix determining its stack *)
let lp = Array.init 17 (fun k -> Array.make (1 lsl k) 0) and lb = Array.init 17 (fun k -> Array.make (1 lsl k) 0) and ln = Array.make 17 0
(* the pairs of depth k+1 for symbol s, keeping prefixes whose entry in the level-(k+1) array a is nonzero; returns their number *)
let extend a k s =
  let sp = lp.(k) and sbs = lb.(k) and dp = lp.(k + 1) and db = lb.(k + 1) and o = offs.(k + 1) and n = ln.(k) in
  let j = ref 0 in
  (match s with
  | 0 ->
    for i = 0 to n - 1 do
      let q = 3 * Array.unsafe_get sp i and bs = 2 * Array.unsafe_get sbs i in
      if gb a (o + q + 1) <> 0 then (Array.unsafe_set dp !j (q + 1); Array.unsafe_set db !j bs; incr j);
      if gb a (o + q + 2) <> 0 then (Array.unsafe_set dp !j (q + 2); Array.unsafe_set db !j (bs + 1); incr j)
    done
  | 1 ->
    for i = 0 to n - 1 do
      let q = 3 * Array.unsafe_get sp i in
      if gb a (o + q) <> 0 then (Array.unsafe_set dp !j q; Array.unsafe_set db !j (Array.unsafe_get sbs i); incr j)
    done
  | _ ->
    let flip = s - 2 in
    for i = 0 to n - 1 do
      let bs = Array.unsafe_get sbs i in
      if bs > 1 then (
        let q = (3 * Array.unsafe_get sp i) + 1 + (bs land 1 lxor flip) in
        if gb a (o + q) <> 0 then (Array.unsafe_set dp !j q; Array.unsafe_set db !j (bs lsr 1); incr j))
    done);
  ln.(k + 1) <- !j;
  !j
(* the trace prefix and bit stack of a pair (q = 3p, bs) extended by symbol s (for s = 0, Push, the colour-3 extension is the
   colour-2 one plus 1, both ways); prefix -1 when s pops an empty stack *)
let extp q bs s = if s = 0 then q + 1 else if s = 1 then q else if bs > 1 then q + 1 + (bs land 1 lxor (s - 2)) else -1
let extb bs s = if s = 0 then 2 * bs else if s = 1 then bs else bs lsr 1
(* S: decrement u by the chromograms of gtr below node g at depth k; leaves below depth k > 0 are done from their parent *)
let sleaves ul uc h k s wc =
  let o = offs.(h) in
  for i = 0 to ln.(k) - 1 do
    let q = 3 * Array.unsafe_get lp.(k) i and bs = Array.unsafe_get lb.(k) i in
    let p = extp q bs s and bs = extb bs s in
    if p >= 0 && gb ul (o + p) > 0 then sleaf uc ul h p wc bs;
    if s = 0 && gb ul (o + p + 1) > 0 then sleaf uc ul h (p + 1) wc (bs + 1)
  done
let rec swalk nodes ul uc h k g =
  let w = Array.unsafe_get nodes g in
  if k = h then for i = 0 to ln.(k) - 1 do sleaf uc ul h lp.(k).(i) w lb.(k).(i) done
  else
    for s = 0 to 3 do
      if (w lsr (8 + s)) land 1 <> 0 then (
        let gc = child w s in
        let wc = Array.unsafe_get nodes gc in
        if in_gtr wc then if k + 1 = h then sleaves ul uc h k s wc else if extend ul k s > 0 then swalk nodes ul uc h (k + 1) gc)
    done
let mark nodes g m = let w = Array.unsafe_get nodes g in if w land 0xF0 = 0 then bpush hits g; Array.unsafe_set nodes g (w lor (m lsl 4))
(* G: mark as gtr the chromograms of gu below node g at depth k that match a trace of ctr; returns whether any did *)
let ghits ca o m p bs = Array.unsafe_get ghit ((((m lsl 2) + top bs) lsl 3) + gb ca (o + p))
let gleaves nodes ca h k s gc =
  let o = offs.(h) and m = Array.unsafe_get nodes gc land 15 in
  let r = ref 0 and i = ref 0 in
  while !r <> m && !i < ln.(k) do
    let q = 3 * Array.unsafe_get lp.(k) !i and bs = Array.unsafe_get lb.(k) !i in
    let p = extp q bs s and bs = extb bs s in
    if p >= 0 then r := !r lor ghits ca o m p bs;
    if s = 0 then r := !r lor ghits ca o m (p + 1) (bs + 1);
    incr i
  done;
  !r <> 0 && (mark nodes gc !r; true)
let rec gwalk nodes ca h k g =
  let w = Array.unsafe_get nodes g in
  if k = h then (
    let m = w land 15 in
    let r = ref 0 in
    for i = 0 to ln.(k) - 1 do r := !r lor ghits ca offs.(h) m lp.(k).(i) lb.(k).(i) done;
    !r <> 0 && (mark nodes g !r; true))
  else (
    let any = ref false in
    for s = 0 to 3 do
      if (w lsr (8 + s)) land 1 <> 0 then (
        let gc = child w s in
        if in_gu (Array.unsafe_get nodes gc) && if k + 1 = h then gleaves nodes ca h k s gc else extend ca k s > 0 && gwalk nodes ca h (k + 1) gc then any := true)
    done;
    !any && (mark nodes g 1; true))
let start a = lp.(0).(0) <- 0; lb.(0).(0) <- 1; ln.(0) <- 1; gb a 0 <> 0
(* remove gtr from gu, recomputing membership along gtr *)
let rec upd nodes h k g =
  let w = nodes.(g) in
  let m =
    if k = h then w land lnot (w lsr 4) land 15
    else (
      let any = ref 0 in
      for s = 0 to 3 do
        if (w lsr (8 + s)) land 1 <> 0 then (let gc = child w s in let wc = nodes.(gc) in if (if in_gtr wc then upd nodes h (k + 1) gc else in_gu wc) then any := 1)
      done;
      !any)
  in
  nodes.(g) <- w land lnot 15 lor m;
  m <> 0
(* ctr: ca holds levels 0..h, level h as the 3-bit set of member digits, the others as nonzero flags *)
let ctr_path ca h v p = let rec up k p = if k > 0 then (let j = offs.(k - 1) + (p / 3) in if gb ca j <> v then (sb ca j v; up (k - 1) (p / 3))) in up h p
let cadd ca h t =
  let i = offs.(h) + (t / 3) and b = 1 lsl (t mod 3) in
  let x = gb ca i in
  if x land b = 0 then (sb ca i (x lor b); bpush celems t; if x = 0 then ctr_path ca h 1 (t / 3))
let cclear ca h = for i = 0 to celems.n - 1 do let p = celems.a.(i) / 3 in sb ca (offs.(h) + p) 0; ctr_path ca h 0 p done; celems.n <- 0

let make_eng h =
  let g = gtree_full h in
  let rec cnt = function GNode (a, b, c, d) -> 1 + cnt a + cnt b + cnt c + cnt d | GEmpty -> 0 | _ -> 1 in
  let nodes = Array.make (cnt g) 0 and next = ref 1 in
  let rec fill id k = function
    | GNode (t0, t1, t2, t3) ->
      assert (k < h);
      let ch = List.filter (fun (_, t) -> not (gempty t)) [ (0, t0); (1, t1); (2, t2); (3, t3) ] in
      assert (ch <> []);
      let b = !next in
      next := b + List.length ch;
      nodes.(id) <- (b lsl 12) lor (List.fold_left (fun m (s, _) -> m lor (1 lsl s)) 0 ch lsl 8) lor 1;
      List.iteri (fun i (_, t) -> fill (b + i) (k + 1) t) ch
    | GEmpty -> assert false
    | l ->
      assert (k = h);
      let a, b, c, d = gbits l in
      let m = (if a then 1 else 0) lor (if b then 2 else 0) lor (if c then 4 else 0) lor if d then 8 else 0 in
      nodes.(id) <- (m lsl 8) lor m
  in
  fill 0 0 g;
  let n3 = offs.(h + 2) - offs.(h + 1) in
  let cnts = Array.make n3 0 and ev = Bytes.make offs.(h + 2) '\001' in
  (* es: 3 at the root, then the first digit until the digit first changes; then 4 if it changed to the cyclic successor, else 5 (odd) *)
  let es = Bytes.make offs.(h + 2) '\003' in
  for k = 0 to h do
    for p = 0 to offs.(k + 1) - offs.(k) - 1 do
      let e = gb es (offs.(k) + p) in
      for d = 0 to 2 do
        let e' = if e = 3 then d else if e = 4 || e = d then e else if d = (e + 1) mod 3 then 4 else 5 in
        sb es (offs.(k + 1) + (3 * p) + d) e';
        if e' = 5 then sb ev (offs.(k + 1) + (3 * p) + d) 0
      done
    done
  done;
  let rec count k g =
    let w = nodes.(g) in
    if k = h then
      for i = 0 to ln.(k) - 1 do
        let x = sdig.(((w lsr 6) land 60) + top lb.(k).(i)) and q = 3 * lp.(k).(i) in
        for d = 0 to 2 do let t = q + d in if gb ev (offs.(h + 1) + t) <> 0 then cnts.(t) <- cnts.(t) + ((x lsr (2 * d)) land 3) done
      done
    else for s = 0 to 3 do if (w lsr (8 + s)) land 1 <> 0 && extend ev k s > 0 then count (k + 1) (child w s) done
  in
  ignore (start ev);
  count 0 0;
  let ul = Bytes.make offs.(h + 1) '\000' and uc = Bytes.make (2 * n3) '\000' in
  let rec live k p = if k > 0 then (let j = offs.(k - 1) + (p / 3) in sb ul j (gb ul j + 1); if gb ul j = 1 then live (k - 1) (p / 3)) in
  Array.iteri (fun t c -> if c > 0 then (assert (c < 65536); set16 uc (2 * t) c; live (h + 1) t)) cnts;
  let lo = (h + 1) / 2 in
  let pw n = offs.(n + 1) - offs.(n) in
  let tab r n = Array.init (pw n) (fun t -> let rec go t k acc mul = if k = 0 then acc else go (t / 3) (k - 1) (acc + ((t mod 3 + r) mod 3 * mul)) (3 * mul) in go t n 0 1) in
  { h; nodes0 = nodes; ul0 = ul; uc0 = uc; lo = pw lo; rot = [| tab 1 lo; tab 1 (h + 1 - lo); tab 2 lo; tab 2 (h + 1 - lo) |] }

(* returns the remaining trace counts, or None when the Kempe tree is empty by exhaustion of gu *)
let kempe_flat e ctr0 =
  let h = e.h in
  let nodes = Array.copy e.nodes0 and ul = Bytes.copy e.ul0 and uc = Bytes.copy e.uc0 and ca = Bytes.make offs.(h + 1) '\000' in
  hits.n <- 0; celems.n <- 0;
  let killed = ref false in
  let rot r t = (e.rot.(r + 1).(t / e.lo) * e.lo) + e.rot.(r).(t mod e.lo) in
  let g_round () =
    for i = 0 to hits.n - 1 do let g = hits.a.(i) in nodes.(g) <- nodes.(g) land lnot 0xF0 done;
    hits.n <- 0;
    if in_gu nodes.(0) && start ca && gwalk nodes ca h 0 0 then ignore (upd nodes h 0 0)
  in
  let s_round () =
    gone.n <- 0;
    if start ul then swalk nodes ul uc h 0 0;
    cclear ca h;
    for i = 0 to gone.n - 1 do let t = gone.a.(i) in cadd ca h (rot 0 t); cadd ca h (rot 2 t) done
  in
  let finished () = !killed || gb ul 0 = 0 || (not (in_gtr nodes.(0))) || ((not (in_gu nodes.(0))) && (killed := true; true)) in
  let rec ktc d =
    if d = 0 then g_round ()
    else (
      ktc (d - 1);
      if not (finished ()) then (s_round (); ktc (d - 1));
      if not (finished ()) then (s_round (); ktc (d - 1)))
  in
  ctree_iter (fun k p _ -> assert (k = h + 1); cadd ca h p) 0 0 ctr0;
  ktc (h + 2);
  if !killed || gb ul 0 = 0 then None else Some uc
let flat_look h = function
  | None -> fun _ -> 0
  | Some uc ->
    let rec go k p = function [] -> if k = h + 1 then get16 uc (2 * p) else 0 | c :: r -> if c < 1 || c > 3 || k > h then 0 else go (k + 1) ((3 * p) + c - 1) r in
    go 0 0
let flat_list = function
  | None -> []
  | Some uc -> List.filter (fun (_, c) -> c > 0) (List.init (Bytes.length uc / 2) (fun t -> (t, get16 uc (2 * t))))
let tree_list t = let l = ref [] in ctree_iter (fun _ p c -> l := (p, c) :: !l) 0 0 t; List.sort compare !l
(* one configuration *)
let tcache = Hashtbl.create 8
let fcache = Hashtbl.create 8
let cached c h mk = match Hashtbl.find_opt c h with Some x -> x | None -> let x = mk h in Hashtbl.replace c h x; x
let kt_empty = ref false
let setup ?(drop_contract = false) ?(shift = 0) (cci, cp) =
  let _, e, _, r = cpmap cp in
  let xs = ctrenum cp in
  let n = List.length xs in
  let cci = List.map (fun i -> (i + shift) mod n) cci in
  let cc = if drop_contract then [] else List.filteri (fun i _ -> imem i cci) xs in
  let ie = List.concat_map (fun y -> [ y; nth e y ]) cc in
  let h = List.length r - 2 in
  if h < 0 then raise Fail;
  (h, ie)
let finish look ie cp = List.for_all (function SR _ | SY | SH -> true | SU -> false) cp && dfs look ie (SU :: List.rev cp) all_cols 0 []
let kt_tree h cp =
  let ctu, gtu = cached tcache h (fun h -> let g = gtree_full h in (ctree_full h g, g)) in
  kempe_tree h ctu (cpcolor cp) gtu
let kt_flat h cp = kempe_flat (cached fcache h make_eng) (cpcolor cp)
let reducible ?drop_contract ?shift ((_, cp) as c) =
  let h, ie = setup ?drop_contract ?shift c in
  let kt = kt_flat h cp in
  kt_empty := kt = None;
  finish (flat_look h kt) ie cp
let reducible_tree ((_, cp) as c) =
  let h, ie = setup c in
  let kt = kt_tree h cp in
  finish (fun l -> sub kt l) ie cp
(* decoding *)
let decode bytes =
  let rec nums = function 0 :: r -> ([], r) | n :: r -> let ns, r2 = nums r in ((n - 1) :: ns, r2) | [] -> raise Fail in
  let rec steps = function
    | 0 :: r -> ([], r)
    | n :: r -> let ps, r2 = steps r in ((match n with 1 -> SH | 2 -> SY | _ -> SR (n - 3)) :: ps, r2)
    | [] -> raise Fail
  in
  match bytes with
  | (0 | 1) :: r -> let cci, r1 = nums r in let cp, r2 = steps r1 in if r2 <> [] then raise Fail; (cci, cp)
  | _ -> raise Fail


let () =
  let ic = open_in Sys.argv.(1) in
  let ints l = List.map int_of_string (String.split_on_char ' ' (String.trim l)) in
  let sizes = ints (input_line ic) in
  let cfgs = ref [] in
  (try while true do cfgs := decode (ints (input_line ic)) :: !cfgs done with End_of_file -> ());
  let cfgs = Array.of_list (List.rev !cfgs) in
  let mode = if Array.length Sys.argv > 2 then Sys.argv.(2) else "pieces" in
  let ring (_, cp) = let _, _, _, r = cpmap cp in List.length r in
  match mode with
  | "pieces" ->
    let i = ref 0 and ok = ref 0 and total = ref 0.0 in
    let piece n =
      Hashtbl.reset fcache;
      let t0 = Sys.time () in
      for _ = 1 to n do if reducible cfgs.(!i) then incr ok; incr i done;
      let dt = Sys.time () -. t0 in
      total := !total +. dt;
      Printf.printf "piece %d configs %.3fs\n%!" n dt
    in
    List.iter piece sizes;
    piece (Array.length cfgs - !i);
    Printf.printf "reducible %d of %d, total CPU %.2fs\n" !ok (Array.length cfgs) !total
  | "mutate" ->
    let nonempty = ref 0 and fails = ref 0 and fails_empty = ref 0 in
    Array.iter
      (fun c ->
        let r = reducible ~shift:1 c in
        if not !kt_empty then (incr nonempty; if not r then incr fails) else if not r then incr fails_empty)
      cfgs;
    Printf.printf "kt nonempty in %d configs; with each contract shifted by one edge, %d of those fail; %d with empty kt fail\n" !nonempty !fails !fails_empty
  | "range" ->
    let a = int_of_string Sys.argv.(3) and n = int_of_string Sys.argv.(4) in
    for i = a to a + n - 1 do if not (reducible cfgs.(i)) then print_endline "FAIL" done
  | "check" ->
    let a = int_of_string Sys.argv.(3) and n = int_of_string Sys.argv.(4) in
    let bad = ref 0 in
    for i = a to a + n - 1 do
      let _, cp = cfgs.(i) in
      let h, _ = setup cfgs.(i) in
      let lt = tree_list (kt_tree h cp) and lf = flat_list (kt_flat h cp) in
      let r1 = reducible_tree cfgs.(i) and r2 = reducible cfgs.(i) in
      let ok = lt = lf && r1 = r2 in
      if not ok then incr bad;
      Printf.printf "config %d ring %d kt traces %d sum %d reducible %b/%b %s\n%!" i (ring cfgs.(i)) (List.length lt)
        (List.fold_left (fun s (_, c) -> s + c) 0 lt) r1 r2 (if ok then "SAME" else "DIFFER")
    done;
    Printf.printf "checked %d, differ %d\n" n !bad
  | "one" ->
    let i = int_of_string Sys.argv.(3) in
    let _, cp = cfgs.(i) in
    let h, _ = setup cfgs.(i) in
    let t0 = Sys.time () in
    let e = cached fcache h make_eng in
    let t1 = Sys.time () in
    let kt = kt_flat h cp in
    let t2 = Sys.time () in
    Printf.printf "config %d ring %d init %.3fs kempe %.3fs kt traces %d reducible %b\n" i (h + 2) (t1 -. t0) (t2 -. t1)
      (List.length (flat_list kt)) (ignore e; reducible cfgs.(i))
  | "init" ->
    for h = 0 to int_of_string Sys.argv.(3) do
      let e = make_eng h in
      let fl = flat_list (Some e.uc0) and tl = tree_list (ctree_full h (gtree_full h)) in
      Printf.printf "h %d traces %d %s\n%!" h (List.length fl) (if fl = tl then "SAME" else "DIFFER")
    done
  | _ -> ()
