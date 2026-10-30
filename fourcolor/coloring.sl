; Colourings of hypermaps, after the parts of Gonthier's coloring.v that need no Kempe chains: a four-colouring makes a
; map bridgeless, and the four-colourings of the dual and the mirror.

; ks gives the two ends of each bond of g different colours.
(def-adts $ (Proper : ((List (Nat)) ks) ((List (Bond)) g) -> Type)
  enum
  (many ProperNil : (erased (List (Nat)) ks) -> (Proper ks (Nil (Bond))))
  (many ProperCons : (erased (List (Nat)) ks) (erased (List (Bond)) g) (erased (Nat) x y l1 l2) (erased (Nth (Nat) ks x l1) p1)
      (erased (Nth (Nat) ks y l2) p2) (erased (Apart (Nat) Lt l1 l2) ne) (erased (Proper ks g) rest) -> (Proper ks (Cons (Bond) (MkBond x y) g))))

(def-fns _ $ (erased proper-of : (erased (List (Nat)) X Y LX LY ks) (erased (List (Bond)) g) (subterm erased (Zip X Y g) z)
    (erased (Respects ks X LX) rx) (erased (Respects ks Y LY) ry) (erased (Differ LX LY) df) -> (erased (Proper ks g) r))
  (let-match erased z (ZipCons X1 Y1 g1 x y z1) ((ZipNil) (ProperNil ks)))
  (let-match erased rx (RespCons _ _ LX1 _ l1 p1 rx1))
  (let-match erased ry (RespCons _ _ LY1 _ l2 p2 ry1))
  (let-match erased df (DifferCons _ _ _ _ ne df1))
  (ProperCons ks g1 x y l1 l2 p1 p2 ne (proper-of X1 Y1 LX1 LY1 ks g1 z1 rx1 ry1 df1)))

(def-fns _ $ (erased differ-of : (erased (List (Nat)) X Y LX LY ks) (erased (List (Bond)) g) (subterm erased (Zip X Y g) z)
    (erased (Proper ks g) pr) (erased (Respects ks X LX) rx) (erased (Respects ks Y LY) ry) -> (erased (Differ LX LY) r))
  (let-match erased z (ZipCons X1 Y1 g1 x y z1) ((ZipNil) (let-match erased rx (RespNil _)) (let-match erased ry (RespNil _)) (DifferNil)))
  (let-match erased pr (ProperCons _ _ _ _ m1 m2 q1 q2 ne pr1))
  (let-match erased rx (RespCons _ _ LX1 _ l1 p1 rx1))
  (let-match erased ry (RespCons _ _ LY1 _ l2 p2 ry1))
  (let-match erased (nth-fn _ ks x l1 m1 p1 q1) (Refl _ _))
  (let-match erased (nth-fn _ ks y l2 m2 p2 q2) (Refl _ _))
  (DifferCons LX1 LY1 l1 l2 ne (differ-of X1 Y1 LX1 LY1 ks g1 z1 pr1 rx1 ry1)))

(def-fns _ $ (erased proper-adj : (erased (List (Nat)) ks) (erased (List (Bond)) g) (erased (Nat) x y l1 l2) (subterm erased (Adj g x y) a)
    (erased (Proper ks g) pr) (erased (Nth (Nat) ks x l1) p1) (erased (Nth (Nat) ks y l2) p2) -> (erased (Apart (Nat) Lt l1 l2) r))
  (match erased a _
    ((AdjFwd _ _ _)
      (let-match erased pr (ProperCons _ _ _ _ m1 m2 q1 q2 ne _))
      (let-match erased (nth-fn _ ks x l1 m1 p1 q1) (Refl _ _))
      (let-match erased (nth-fn _ ks y l2 m2 p2 q2) (Refl _ _))
      ne)
    ((AdjBwd _ _ _)
      (let-match erased pr (ProperCons _ _ _ _ m1 m2 q1 q2 ne _))
      (let-match erased (nth-fn _ ks y l2 m1 p2 q1) (Refl _ _))
      (let-match erased (nth-fn _ ks x l1 m2 p1 q2) (Refl _ _))
      (apart-sym l2 l1 ne))
    ((AdjThere g1 _ _ _ a1)
      (let-match erased pr (ProperCons _ _ _ _ _ _ _ _ _ pr1))
      (proper-adj ks g1 x y l1 l2 a1 pr1 p1 p2))))

; The bonds of the inverse q of p are those of p reversed.
(def-fns _ $ (erased proper-inv : (erased (Nat) d) (erased (List (Nat)) ks p q) (erased (List (Bond)) gp gq) (subterm erased (Fun q gq) fq)
    (erased (Perm d q p) pm) (erased (Graph d p gp) gr) (erased (Proper ks gp) pr) (erased (Length (Nat) ks d) lk) -> (erased (Proper ks gq) r))
  (let-match erased fq (FunCons _ g1 x y py f1) ((FunNil _) (ProperNil ks)))
  (let ((erased lx) (erased ly)) (values (nth-lt-length _ q x d y py (perm-length d q p pm)) (perm-val d x y q p pm py)))
  (let ((erased l1) (erased p1)) (nth-exists _ ks d x lk lx))
  (let ((erased l2) (erased p2)) (nth-exists _ ks d y lk ly))
  (ProperCons ks g1 x y l1 l2 p1 p2 (apart-sym l2 l1 (proper-adj ks gp y x l2 l1 (graph-adj d y x p gp gr (perm-inv d x y q p pm py)) pr p2 p1))
    (proper-inv d ks p q gp g1 f1 pm gr pr lk)))

(def-fns _ $ (erased allsep-proper : (erased (List (Nat)) ks) (erased (List (Bond)) g h) (subterm erased (Proper ks g) pr) (erased (Const ks h) cl)
    -> (erased (AllSep h g) r))
  (let-match erased pr (ProperCons _ g1 x y l1 l2 p1 p2 ne pr1) ((ProperNil _) (AllSepNil h)))
  (AllSepCons h g1 x y (MkSep h x y ks l1 l2 cl p1 p2 ne) (allsep-proper ks g1 h pr1 cl)))

(def-fns _ $ (erased differ-sym : (erased (List (Nat)) xs ys) (subterm erased (Differ xs ys) df) -> (erased (Differ ys xs) r))
  (let-match erased df (DifferCons xs1 ys1 x y ne df1) ((DifferNil) (DifferNil)))
  (DifferCons ys1 xs1 y x (apart-sym x y ne) (differ-sym xs1 ys1 df1)))

; A labelling constant along p is constant along its inverse q.
(def-fns _ $ (erased resp-inv : (erased (Nat) d) (erased (List (Nat)) ks p q) (erased (Perm d p q) pm) (erased (Respects ks p ks) rp)
    (erased (Length (Nat) ks d) lk) -> (erased (Respects ks q ks) r))
  (let ((erased gp) (erased grp)) (perm-graph d p q pm))
  (let ((erased gq) (erased grq)) (perm-graph d q p (perm-sym d p q pm)))
  (graph-resp d q ks gq grq (const-inv d ks p q gp gq (graph-fun d q gq grq) (perm-sym d p q pm) grp (resp-const d ks p gp (graph-fun d p gp grp) rp lk)) lk))

; The edges of a four-colouring are proper.
(def-fns _ $ (erased coloring-proper : (erased (Nat) d) (erased (List (Nat)) e f ks ids) (erased (List (Bond)) ge) (erased (FourColoring e f ks) c)
    (erased (Graph d e ge) gr) (erased (Iota d ids) io) (erased (Length (Nat) ks d) lk) -> (erased (Proper ks ge) r))
  (let-match erased c (MkFourColoring _ _ _ ke rf re df u))
  (proper-of ids e ks ke ks ge (graph-zip d e ids ge gr io) (respects-id-right d ids ks io lk) re (differ-sym ke ks df)))

(def-fns _ $ (erased proper-coloring : (erased (Nat) d) (erased (List (Nat)) e f ks ids) (erased (List (Bond)) ge) (erased (Proper ks ge) pr)
    (erased (Graph d e ge) gr) (erased (Iota d ids) io) (erased (Respects ks f ks) rf) (erased (Under ks 4) u) (erased (Length (Nat) ks d) lk)
    (erased (Under e d) ue) -> (erased (FourColoring e f ks) r))
  (let ((erased ke) (erased re)) (respects-exists ks e d ue lk))
  (MkFourColoring e f ks ke rf re
    (differ-sym ks ke (differ-of ids e ks ke ks ge (graph-zip d e ids ge gr io) pr (respects-id-right d ids ks io lk) re)) u))

; A four-colourable map is bridgeless (colorable_bridgeless).
(def-fns _ $ (erased colorable-bridgeless : (erased (Nat) d) (erased (List (Nat)) e n f ks) (erased (Hypermap d e n f) h) (erased (FourColoring e f ks) c)
    -> (erased (Bridgeless d e n f) r))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (let ((erased ids) (erased io)) (iota-exists d))
  (let-match erased c (MkFourColoring _ _ _ ke rf re df u))
  (let ((erased lk)) (respects-length ks f ks d rf (perm-length d f fi pf)))
  (let ((erased ge) (erased gre)) (perm-graph d e nf pe))
  (let ((erased gf) (erased grf)) (perm-graph d f fi pf))
  (MkBridgeless d e n f ge gf gre grf
    (allsep-proper ks ge gf (coloring-proper d e f ks ids ge c gre io lk) (resp-const d ks f gf (graph-fun d f gf grf) rf lk))))

; A four-colouring with edge e and face f is one with edge and face inverted: with e and n, this is coloring_dual.
(def-fns _ $ (erased coloring-inv : (erased (Nat) d) (erased (List (Nat)) e f ei fi ks) (erased (Perm d e ei) pe) (erased (Perm d f fi) pf)
    (erased (FourColoring e f ks) c) -> (erased (FourColoring ei fi ks) r))
  (let ((erased ids) (erased io)) (iota-exists d))
  (let-match erased c (MkFourColoring _ _ _ ke rf re df u))
  (let ((erased lk)) (respects-length ks f ks d rf (perm-length d f fi pf)))
  (let ((erased ge) (erased gre)) (perm-graph d e ei pe))
  (let ((erased gei) (erased grei)) (perm-graph d ei e (perm-sym d e ei pe)))
  (proper-coloring d ei fi ks ids gei
    (proper-inv d ks e ei ge gei (graph-fun d ei gei grei) (perm-sym d e ei pe) gre (coloring-proper d e f ks ids ge c gre io lk) lk)
    grei io (resp-inv d ks f fi pf rf lk) u lk (perm-under d ei e (perm-sym d e ei pe))))

; Each edge x-(e x) gives the mirror edge (f (e x))-(f x), whose ends have the colours of x and e x.
(def-fns _ $ (erased proper-mirror : (erased (Nat) d) (erased (List (Nat)) e n f fe fn ks ids) (erased (List (Bond)) ge gfn) (subterm erased (Fun e ge) fg)
    (erased (Respects f e fe) cfe) (erased (Respects n fe ids) ke) (erased (Respects f n fn) rfn) (erased (Respects ks f ks) rf) (erased (Iota d ids) io)
    (erased (Graph d fn gfn) grfn) (erased (Proper ks gfn) pr) (erased (Length (Nat) e d) le) (erased (Length (Nat) f d) lf)
    (erased (Length (Nat) ks d) lk) (erased (Under e d) ue) -> (erased (Proper ks ge) r))
  (let-match erased fg (FunCons _ g1 x y px f1) ((FunNil _) (ProperNil ks)))
  (let ((erased lx) (erased ly)) (values (nth-lt-length _ e x d y px le) (under-nth e x y d ue px)))
  (let ((erased z) (erased pz)) (nth-exists _ f d y lf ly))
  (let ((erased w) (erased pw)) (nth-exists _ f d x lf lx))
  (let ((erased pzx)) (respects-nth n fe ids x z x ke (respects-at f e fe x y z cfe px pz) (iota-nth d x ids io lx)))
  (let ((erased kx) (erased pkx)) (nth-exists _ ks d x lk lx))
  (let ((erased ky) (erased pky)) (nth-exists _ ks d y lk ly))
  (ProperCons ks g1 x y kx ky pkx pky
    (apart-sym ky kx (proper-adj ks gfn z w ky kx (graph-adj d z w fn gfn grfn (respects-at f n fn z x w rfn pzx pw)) pr
      (respects-nth ks f ks y z ky rf pz pky) (respects-nth ks f ks x w kx rf pw pkx)))
    (proper-mirror d e n f fe fn ks ids g1 gfn f1 cfe ke rfn rf io grfn pr le lf lk ue)))

; A four-colouring of the mirror (edge f . n, face f inverted) is one of the map (coloring_mirror).
(def-fns _ $ (erased coloring-mirror : (erased (Nat) d) (erased (List (Nat)) e n f fn fi ks) (erased (Hypermap d e n f) h) (erased (Respects f n fn) rfn)
    (erased (Perm d f fi) pf) (erased (FourColoring fn fi ks) c) -> (erased (FourColoring e f ks) r))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased nf) (erased pe)) (hyper-perm d e n f h))
  (let-match erased h (MkHypermap _ _ _ _ ids fe en nf2 io cfe ke cen kn cnf kf))
  (let-match erased c (MkFourColoring _ _ _ kfn rfi rfn2 dfn u))
  (let ((erased lk)) (respects-length ks fi ks d rfi (perm-length d fi f (perm-sym d f fi pf))))
  (let ((erased rf)) (resp-inv d ks fi f (perm-sym d f fi pf) rfi lk))
  (let ((erased gfn) (erased grfn)) (graph-exists d fn (respects-length f n fn d rfn ln)))
  (let ((erased ge) (erased gre)) (graph-exists d e le))
  (let ((erased ue)) (perm-under d e nf pe))
  (proper-coloring d e f ks ids ge
    (proper-mirror d e n f fe fn ks ids ge gfn (graph-fun d e ge gre) cfe ke rfn rf io grfn (coloring-proper d fn fi ks ids gfn c grfn io lk) le lf lk ue)
    gre io rf u lk ue))

(def-fns _ $ (erased repeat-under : (erased (Nat) m c b) (erased (List (Nat)) ks) (subterm erased (Repeat (Nat) m c ks) rp) (erased (Lt c b) l)
    -> (erased (Under ks b) r))
  (let-match erased rp (RepeatCons _ m1 _ ks1 rp1) ((RepeatNil _ _) (UnderNil b)))
  (UnderCons ks1 c b l (repeat-under m1 c b ks1 rp1 l)))

; A cubic map is precubic.
(def-fns _ $ (erased cubic-precubic : (erased (Nat) d) (erased (List (Nat)) n) (erased (AllOrder d n (Succ (Succ (Succ (Zero))))) cu)
    -> (erased (Precubic d n) r))
  (let-match erased cu (MkAllOrder _ _ _ ks ol rk))
  (MkPrecubic d n ks ol (repeat-under d _ _ ks rk (LtS _ _ $ LtS _ _ $ LtS _ _ $ LtZ _))))
