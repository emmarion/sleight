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
let rec dfs kt ie rp us d et =
  match rp with
  | [] -> (match et with [] -> false | _ :: et1 -> sub kt (etrace et1) = 0)
  | s :: rest -> (
    let k = match s with SU -> Some (`U, d + 2) | SY -> Some (`Y, d + 4) | SH -> Some (`H, d + 6) | SR _ -> None in
    match k, s with
    | None, SR k -> dfs kt ie rest all_cols d (rot k et)
    | None, _ -> false
    | Some (k, d2), _ -> (
      match us with
      | [] -> true
      | u :: us1 ->
        dfs kt ie rp us1 d et
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
          (not (List.for_all flag cks)) || dfs kt ie rest all_cols d2 o))

(* one configuration *)
let cache = Hashtbl.create 8
let kt_empty = ref false
let reducible ?(drop_contract = false) ?(shift = 0) (cci, cp) =
  let _, e, _, r = cpmap cp in
  let xs = ctrenum cp in
  let n = List.length xs in
  let cci = List.map (fun i -> (i + shift) mod n) cci in
  let cc = if drop_contract then [] else List.filteri (fun i _ -> imem i cci) xs in
  let ie = List.concat_map (fun y -> [ y; nth e y ]) cc in
  let h = List.length r - 2 in
  if h < 0 then raise Fail;
  let ctu, gtu =
    match Hashtbl.find_opt cache h with
    | Some x -> x
    | None ->
      let gtu = gtree_full h in
      let x = (ctree_full h gtu, gtu) in
      Hashtbl.replace cache h x;
      x
  in
  let kt = kempe_tree h ctu (cpcolor cp) gtu in
  kt_empty := cempty kt;
  List.for_all (function SR _ | SY | SH -> true | SU -> false) cp && dfs kt ie (SU :: List.rev cp) all_cols 0 []

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
  match mode with
  | "pieces" ->
    let i = ref 0 and ok = ref 0 and total = ref 0.0 in
    let piece n =
      Hashtbl.reset cache;
      let t0 = Sys.time () in
      for _ = 1 to n do if reducible cfgs.(!i) then incr ok; incr i done;
      let dt = Sys.time () -. t0 in
      total := !total +. dt;
      Printf.printf "piece %d configs %.3fs\n%!" n dt
    in
    List.iter piece sizes;
    piece (Array.length cfgs - !i);
    Printf.printf "reducible %d of %d, total CPU %.2fs\n" !ok (Array.length cfgs) !total
  | "nocontract" ->
    let n = ref 0 and nonempty = ref 0 and bad = ref 0 in
    Array.iter
      (fun ((cci, _) as c) ->
        let r = reducible ~drop_contract:true c in
        if cci <> [] then (incr nonempty; if r then incr bad);
        if r then incr n)
      cfgs;
    Printf.printf "without contracts: %d reducible; %d with a contract, of which %d pass without it\n" !n !nonempty !bad
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
  | "one" ->
    let i = int_of_string Sys.argv.(3) in
    let cci, cp = cfgs.(i) in
    let _, _, _, r = cpmap cp in
    let h = List.length r - 2 in
    let t0 = Sys.time () in
    let gtu = gtree_full h in
    let ctu = ctree_full h gtu in
    let t1 = Sys.time () in
    let ctr = cpcolor cp in
    let kt = kempe_tree h ctu ctr gtu in
    let t2 = Sys.time () in
    let ok = reducible (cci, cp) in
    let rec size = function CNode (a, b, c) -> 1 + size a + size b + size c | _ -> 1 in
    Printf.printf "config %d ring %d init %.3fs kempe %.3fs sizes ctu %d ctr %d kt %d reducible %b\n" i (h + 2) (t1 -. t0) (t2 -. t1)
      (size ctu) (size ctr) (size kt) ok
  | _ -> ()
