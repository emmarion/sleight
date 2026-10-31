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
  (graph-resp d q ks gq grq
    (const-inv d ks p q gp gq (graph-fun d q gq grq) (perm-sym d p q pm) grp (resp-const d ks p gp (graph-fun d p gp grp) rp lk)) lk))

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
(def-fns _ $ (erased colorable-bridgeless : (erased (Nat) d) (erased (List (Nat)) e n f ks) (erased (Hypermap d e n f) h)
    (erased (FourColoring e f ks) c)
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
(def-fns _ $ (erased proper-mirror : (erased (Nat) d) (erased (List (Nat)) e n f fe fn ks ids) (erased (List (Bond)) ge gfn)
    (subterm erased (Fun e ge) fg)
    (erased (Respects f e fe) cfe) (erased (Respects n fe ids) ke) (erased (Respects f n fn) rfn) (erased (Respects ks f ks) rf)
    (erased (Iota d ids) io)
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
(def-fns _ $ (erased coloring-mirror : (erased (Nat) d) (erased (List (Nat)) e n f fn fi ks) (erased (Hypermap d e n f) h)
    (erased (Respects f n fn) rfn)
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
    (proper-mirror d e n f fe fn ks ids ge gfn (graph-fun d e ge gre) cfe ke rfn rf io grfn (coloring-proper d fn fi ks ids gfn c grfn io lk) le lf lk
      ue)
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

(def-fns _ $ (erased join-length-inv : (erased (List (Nat)) pre rest ks) (erased (Nat) i r k) (subterm erased (Join pre rest ks) j)
    (erased (Length (Nat) pre i) lp) (erased (Length (Nat) ks k) lk) (erased (Add i r k) a) -> (erased (Length (Nat) rest r) res))
  (let-match erased j (JoinCons pre1 _ ks1 x j1)
    ((JoinNil _) (let-match erased lp (LengthNil _)) (let-match erased a (AddZero _)) lk))
  (let-match erased lp (LengthCons _ _ _ i1x lp1))
  (let-match erased lk (LengthCons _ _ _ k1 lk1))
  (let-match erased a (AddSucc _ _ _ a1))
  (join-length-inv pre1 rest ks1 i1x r k1 j1 lp1 lk1 a1))

(def-fns _ $ (erased join-snoc : (erased (List (Nat)) pre rest ks pre2) (erased (Nat) c) (subterm erased (Join pre (Cons (Nat) c rest) ks) j)
    (erased (Snoc (Nat) pre c pre2) s) -> (erased (Join pre2 rest ks) r))
  (let-match erased j (JoinCons pre1 _ ks1 x j1)
    ((JoinNil _) (let-match erased s (SnocNil _ _)) (JoinCons (Nil _) rest rest c (JoinNil rest))))
  (let-match erased s (SnocCons _ _ _ _ pre3 s1))
  (JoinCons pre3 rest ks1 x (join-snoc pre1 rest ks1 pre3 c j1 s1)))

(def-fns _ $ (erased join-nil-r : (erased (List (Nat)) pre ks) (subterm erased (Join pre (Nil (Nat)) ks) j) -> (erased (Eq (List (Nat)) ks pre) e))
  (let-match erased j (JoinCons pre1 _ ks1 x j1) ((JoinNil _) (Refl _ ks)))
  (let-match erased (join-nil-r pre1 ks1 j1) (Refl _ _))
  (Refl _ ks))

(def-fns _ $ (erased under-snoc-add : (erased (List (Nat)) pre pre2) (erased (Nat) c b) (subterm erased (Snoc (Nat) pre c pre2) s)
    (erased (Under pre b) u)
    (erased (Lt c b) l) -> (erased (Under pre2 b) r))
  (let-match erased s (SnocCons _ x _ pre1 pre3 s1) ((SnocNil _ _) (UnderCons (Nil _) c b l (UnderNil b))))
  (let-match erased u (UnderCons _ _ _ lx u1))
  (UnderCons pre3 x b lx (under-snoc-add pre1 pre3 c b s1 u1 l)))

; xs and ys agree at some position.
(def-adts $ (SameAt : ((List (Nat)) xs ys) -> Type)
  enum
  (many MkSameAt : (erased (List (Nat)) xs ys) (erased (Nat) j x) (erased (Nth (Nat) xs j x) px) (erased (Nth (Nat) ys j x) py) -> (SameAt xs ys)))

(def-fns _ $ (erased differ-dec : (erased (List (Nat)) xs ys) (erased (Nat) k) (subterm erased (Length (Nat) xs k) lx) (erased (Length (Nat) ys k) ly)
    -> (erased (Or (Differ xs ys) (SameAt xs ys)) r))
  (let-match erased lx (LengthCons _ x xs1 k1 lx1) ((LengthNil _) (let-match erased ly (LengthNil _)) (OrL _ _ (DifferNil))))
  (let-match erased ly (LengthCons _ y ys1 _ ly1))
  (let-match erased (nat-eq x y) (Unequal _ _ _ _ ne)
    ((Equal _ _ _) (OrR _ _ (MkSameAt xs ys (Zero) x (NthHere _ x xs1) (NthHere _ x ys1)))))
  (let-match erased (differ-dec xs1 ys1 k1 lx1 ly1) (OrR _ _ sa) ((OrL _ _ df) (OrL _ _ (DifferCons xs1 ys1 x y ne df))))
  (let-match erased sa (MkSameAt _ _ j z px py))
  (OrR _ _ (MkSameAt xs ys (Succ j) z (NthThere _ x xs1 j z px) (NthThere _ y ys1 j z py))))

; Why no four-colouring of (e, f) on d darts extends pre and gives the darts of r the colours lc: on a full pre, one of the
; three checks fails; otherwise each colour of the next dart fails.
(def-adts $ (NoExt : ((Nat) d) ((List (Nat)) e f r lc pre) -> Type)
  enum
  (many NEFace : (erased (Nat) d) (erased (List (Nat)) e f r lc pre X) (erased (Length (Nat) pre d) lp) (erased (Respects pre f X) rX)
      (erased (NeAt X pre) ne) -> (NoExt d e f r lc pre))
  (many NERing : (erased (Nat) d) (erased (List (Nat)) e f r lc pre R) (erased (Length (Nat) pre d) lp) (erased (Respects pre r R) rR)
      (erased (NeAt R lc) ne) -> (NoExt d e f r lc pre))
  (many NEEdge : (erased (Nat) d) (erased (List (Nat)) e f r lc pre ke) (erased (Length (Nat) pre d) lp) (erased (Respects pre e ke) rke)
      (erased (SameAt ke pre) sa) -> (NoExt d e f r lc pre))
  (many NEStep : (erased (Nat) d i m) (erased (List (Nat)) e f r lc pre p0 p1 p2 p3) (erased (Length (Nat) pre i) lp) (erased (Add i (Succ m) d) a)
      (erased (Snoc (Nat) pre (Zero) p0) s0) (erased (Snoc (Nat) pre (Succ (Zero)) p1) s1) (erased (Snoc (Nat) pre (Succ (Succ (Zero))) p2) s2)
      (erased (Snoc (Nat) pre (Succ (Succ (Succ (Zero)))) p3) s3) (erased (NoExt d e f r lc p0) n0) (erased (NoExt d e f r lc p1) n1)
      (erased (NoExt d e f r lc p2) n2) (erased (NoExt d e f r lc p3) n3) -> (NoExt d e f r lc pre)))

; The search for a four-colouring of (e, f) on d darts extending pre that gives the darts of r the colours lc: one is found, or
; none extends pre.
(def-adts $ (Search : ((Nat) d) ((List (Nat)) e f r lc pre) -> Type)
  enum
  (many Found : (erased (Nat) d) (erased (List (Nat)) e f r lc pre ks) (erased (FourColoring e f ks) c) (erased (Respects ks r lc) rl)
      -> (Search d e f r lc pre))
  (many NotFound : (erased (Nat) d) (erased (List (Nat)) e f r lc pre) (erased (NoExt d e f r lc pre) ne) -> (Search d e f r lc pre)))

(def-fns _ $ (erased join-all : (erased (List (Nat)) pre rest ks) (erased (Nat) d) (erased (Join pre rest ks) j) (erased (Length (Nat) pre d) lp)
    (erased (Length (Nat) ks d) l) -> (erased (Eq (List (Nat)) ks pre) e))
  (let-match erased (join-length-inv pre rest ks d (Zero) d j lp l (add-zero-right d)) (LengthNil _))
  (join-nil-r pre ks j))

(def-fns _ $ (erased absurd neat-irrefl : (erased (List (Nat)) xs) (erased (NeAt xs xs) ne) -> (erased (False) f))
  (let-match erased ne (MkNeAt _ _ j a b pa pb ab))
  (let-match erased (nth-fn _ xs j a b pa pb) (Refl _ _))
  (apart-irrefl a ab))

(def-fns _ $ (erased noext-sound : (erased (Nat) d) (erased (List (Nat)) e f r lc pre ks rest) (subterm erased (NoExt d e f r lc pre) ne)
    (erased (Join pre rest ks) j) (erased (Length (Nat) ks d) l) (erased (FourColoring e f ks) c) (erased (Respects ks r lc) rl) -> (erased (False) res))
  (match erased ne _
    ((NEFace _ _ _ _ _ _ X lp rX nq)
      (let-match erased (join-all pre rest ks d j lp l) (Refl _ _))
      (let-match erased c (MkFourColoring _ _ _ ke2 rf re df u))
      (let-match erased (respects-fn pre f X pre rX rf) (Refl _ _))
      (neat-irrefl X nq))
    ((NERing _ _ _ _ _ _ R lp rR nq)
      (let-match erased (join-all pre rest ks d j lp l) (Refl _ _))
      (let-match erased (respects-fn pre r R lc rR rl) (Refl _ _))
      (neat-irrefl R nq))
    ((NEEdge _ _ _ _ _ _ ke lp rke sa)
      (let-match erased (join-all pre rest ks d j lp l) (Refl _ _))
      (let-match erased c (MkFourColoring _ _ _ ke2 rf re df u))
      (let-match erased (respects-fn pre e ke ke2 rke re) (Refl _ _))
      (let-match erased sa (MkSameAt _ _ j2 x px py))
      (apart-irrefl x (differ-nth ke pre j2 x x df px py)))
    ((NEStep _ i m1 _ _ _ _ _ p0 p1 p2 p3 lp a s0 s1 s2 s3 n0 n1 n2 n3)
      (let-match erased (unary-4) (Refl _ _))
      (let-match erased (join-length-inv pre rest ks i (Succ m1) d j lp l a) (LengthCons _ c0 rest1 _ _))
      (let-match erased c (MkFourColoring _ _ _ _ _ _ _ u))
      (let ((erased lc0)) (under-nth ks i c0 4 u (join-nth-r pre rest ks i (Zero) i c0 j lp (add-zero-right i) (NthHere _ c0 rest1))))
      (let ((erased q) (erased sq)) (snoc-exists _ pre c0))
      (let ((erased jq)) (join-snoc pre rest1 ks q c0 j sq))
      (let-match erased lc0 (LtS _ _ l1)
        ((LtZ _) (let-match erased (snoc-fn _ pre q p0 c0 sq s0) (Refl _ _)) (noext-sound d e f r lc p0 ks rest1 n0 jq l c rl)))
      (let-match erased l1 (LtS _ _ l2)
        ((LtZ _) (let-match erased (snoc-fn _ pre q p1 c0 sq s1) (Refl _ _)) (noext-sound d e f r lc p1 ks rest1 n1 jq l c rl)))
      (let-match erased l2 (LtS _ _ l3)
        ((LtZ _) (let-match erased (snoc-fn _ pre q p2 c0 sq s2) (Refl _ _)) (noext-sound d e f r lc p2 ks rest1 n2 jq l c rl)))
      (let-match erased l3 (LtZ _) (absurd (LtS _ _ l4) l4))
      (let-match erased (snoc-fn _ pre q p3 c0 sq s3) (Refl _ _))
      (noext-sound d e f r lc p3 ks rest1 n3 jq l c rl))))

; A list of d colours is checked: f-invariance by comparing it with its composite with f, the edges by comparing it with
; its composite with e, and the ring by comparing its composite with r with lc.
(def-fns _ $ (erased search-full : (erased (Nat) d k) (erased (List (Nat)) e f r lc pre) (erased (Under e d) ue) (erased (Under f d) uf)
    (erased (Under r d) ur) (erased (Length (Nat) e d) le) (erased (Length (Nat) f d) lf) (erased (Length (Nat) r k) lr) (erased (Length (Nat) lc k) llc)
    (erased (Length (Nat) pre d) lp) (erased (Under pre 4) up) -> (erased (Search d e f r lc pre) res))
  (let ((erased X) (erased rX)) (respects-exists pre f d uf lp))
  (let ((erased ke) (erased rke)) (respects-exists pre e d ue lp))
  (let ((erased R) (erased rR)) (respects-exists pre r d ur lp))
  (let-match erased (list-dec X pre d (respects-length pre f X d rX lf) lp) (OrL _ _ eq)
    ((OrR _ _ ne) (NotFound d e f r lc pre (NEFace d e f r lc pre X lp rX ne))))
  (let-match erased eq (Refl _ _))
  (let-match erased (list-dec R lc k (respects-length pre r R k rR lr) llc) (OrL _ _ eqr)
    ((OrR _ _ ne) (NotFound d e f r lc pre (NERing d e f r lc pre R lp rR ne))))
  (let-match erased eqr (Refl _ _))
  (let-match erased (differ-dec ke pre d (respects-length pre e ke d rke le) lp) (OrR _ _ sa)
    ((OrL _ _ df) (Found d e f r lc pre pre (MkFourColoring e f pre ke rX rke df up) rR)))
  (NotFound d e f r lc pre (NEEdge d e f r lc pre ke lp rke sa)))

; The search tries each colour below 4 for the next dart.
(def-fns _ $ (erased search : (erased (Nat) d k) (erased (List (Nat)) e f r lc) (erased (Under e d) ue) (erased (Under f d) uf) (erased (Under r d) ur)
    (erased (Length (Nat) e d) le) (erased (Length (Nat) f d) lf) (erased (Length (Nat) r k) lr) (erased (Length (Nat) lc k) llc)
    (subterm erased (Nat) m) (erased (List (Nat)) pre) (erased (Nat) i) (erased (Length (Nat) pre i) lp) (erased (Add i m d) a) (erased (Under pre 4) up)
    -> (erased (Search d e f r lc pre) res))
  (let-match erased (unary-4) (Refl _ _))
  (let-match erased m (Succ m1)
    ((Zero) (let-match erased (add-fn i (Zero) d i a (add-zero-right i)) (Refl _ _)) (search-full d k e f r lc pre ue uf ur le lf lr llc lp up)))
  (let ((erased a1)) (add-succ-left i m1 d a))
  (let ((erased p0) (erased s0)) (snoc-exists _ pre (Zero)))
  (let ((erased p1) (erased s1)) (snoc-exists _ pre (Succ (Zero))))
  (let ((erased p2) (erased s2)) (snoc-exists _ pre (Succ (Succ (Zero)))))
  (let ((erased p3) (erased s3)) (snoc-exists _ pre (Succ (Succ (Succ (Zero))))))
  (let-match erased (search d k e f r lc ue uf ur le lf lr llc m1 p0 (Succ i) (snoc-length _ pre p0 _ i s0 lp) a1 (under-snoc-add pre p0 _ 4 s0 up (LtZ _)))
    (NotFound _ _ _ _ _ _ n0) ((Found _ _ _ _ _ _ ks c rl) (Found d e f r lc pre ks c rl)))
  (let-match erased (search d k e f r lc ue uf ur le lf lr llc m1 p1 (Succ i) (snoc-length _ pre p1 _ i s1 lp) a1
      (under-snoc-add pre p1 _ 4 s1 up (LtS _ _ $ LtZ _)))
    (NotFound _ _ _ _ _ _ n1) ((Found _ _ _ _ _ _ ks c rl) (Found d e f r lc pre ks c rl)))
  (let-match erased (search d k e f r lc ue uf ur le lf lr llc m1 p2 (Succ i) (snoc-length _ pre p2 _ i s2 lp) a1
      (under-snoc-add pre p2 _ 4 s2 up (LtS _ _ $ LtS _ _ $ LtZ _)))
    (NotFound _ _ _ _ _ _ n2) ((Found _ _ _ _ _ _ ks c rl) (Found d e f r lc pre ks c rl)))
  (let-match erased (search d k e f r lc ue uf ur le lf lr llc m1 p3 (Succ i) (snoc-length _ pre p3 _ i s3 lp) a1
      (under-snoc-add pre p3 _ 4 s3 up (LtS _ _ $ LtS _ _ $ LtS _ _ $ LtZ _)))
    (NotFound _ _ _ _ _ _ n3) ((Found _ _ _ _ _ _ ks c rl) (Found d e f r lc pre ks c rl)))
  (NotFound d e f r lc pre (NEStep d i m1 e f r lc pre p0 p1 p2 p3 lp a s0 s1 s2 s3 n0 n1 n2 n3)))

; A map has a four-colouring that gives the darts of r the colours lc, or none.
(def-fns _ $ (erased search-ring : (erased (Nat) d k) (erased (List (Nat)) e n f r lc) (erased (Hypermap d e n f) h) (erased (Under r d) ur)
    (erased (Length (Nat) r k) lr) (erased (Length (Nat) lc k) llc) -> (erased (Search d e f r lc (Nil (Nat))) res))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (search d k e f r lc (perm-under d e nf pe) (perm-under d f fi pf) ur le lf lr llc d (Nil _) (Zero) (LengthNil _) (AddZero d) (UnderNil 4)))

; A map has a four-colouring, or none (decide_colorable).
(def-adts $ (ColorDec : ((List (Nat)) e f) -> Type)
  enum
  (many Colorable : (erased (List (Nat)) e f ks) (erased (FourColoring e f ks) c) -> (ColorDec e f))
  (many Uncolorable : (erased (List (Nat)) e f) (erased (Level) L)
      (erased (Fn L (erased (List (Nat)) ks) (erased (FourColoring e f ks) c) -> (erased (False) r)) no) -> (ColorDec e f)))

(def-fns _ $ (erased decide-colorable : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) -> (erased (ColorDec e f) r))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let-match erased (search-ring d (Zero) e n f (Nil _) (Nil _) h (UnderNil d) (LengthNil _) (LengthNil _))
    (NotFound _ _ _ _ _ _ ne) ((Found _ _ _ _ _ _ ks c _) (Colorable e f ks c)))
  (def-fns _ $ (erased never : (erased (List (Nat)) ks) (erased (FourColoring e f ks) c) -> (erased (False) r))
    (let-match erased c (MkFourColoring _ _ _ _ rf _ _ _))
    (noext-sound d e f (Nil _) (Nil _) (Nil _) ks ks ne (JoinNil ks) (respects-length ks f ks d rf lf) c (RespNil ks)))
  (Uncolorable e f (level-of never) never))
