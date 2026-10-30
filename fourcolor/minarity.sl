; min_arity of birkhoff.v with minimality as data, through its spoke ring, and from it birkhoff3.sl's MinArity and embed.sl's
; BirkGeo. Load after birkhoff3.sl, in the chain PLAN.md gives.

(def-fns _ $ (erased order-at : (erased (Nat) d x) (erased (List (Nat)) p q) (erased (HPerm d p q) pm) (erased (Lt x d) lx)
    -> (erased (Nat) k) (erased (Order p x k) o))
  (let ((erased y) (erased py) (erased ly)) (perm-nth d x p q pm lx))
  (let ((erased xs) (erased w)) (cycle d x y p q pm py lx))
  (let ((erased ys) (erased w2)) (walk-to p xs y x w))
  (let ((erased k) (erased l)) (length-exists _ ys))
  (values (Succ k) (MkOrder p ys x y k py w2 l)))

(def-fns _ $ (erased orders-on : (erased (Nat) d) (erased (List (Nat)) p q xs) (erased (HPerm d p q) pm) (subterm erased (Under xs d) u)
    -> (erased (List (Nat)) ks) (erased (Orders p xs ks) os))
  (let-match erased u (UnderCons xs1 x _ lx u1) ((UnderNil _) (values (Nil _) (OrdNil p))))
  (let ((erased k) (erased o)) (order-at d x p q pm lx))
  (let ((erased ks) (erased os)) (orders-on d p q xs1 pm u1))
  (values (Cons _ k ks) (OrdCons p xs1 ks x k o os)))

; Every dart has an order under a permutation.
(def-fns _ $ (erased order-list : (erased (Nat) d) (erased (List (Nat)) p q) (erased (HPerm d p q) pm) -> (erased (List (Nat)) ks) (erased (OrderList d p ks) ol))
  (let ((erased ids) (erased io)) (iota-exists d))
  (let ((erased ks) (erased os)) (orders-on d p q ids pm (perm-under d ids ids (perm-id d ids io))))
  (values ks (MkOrderList d p ids ks io os)))

; A planar bridgeless plain cubic map, with fe = face . edge, undone by node, and a labelling lab of its faces.
(def-adts $ (Spk : ((Nat) d) ((List (Nat)) e n f fe lab) -> Type)
  enum
  (many MkSpk : (erased (Nat) d) (erased (List (Nat)) e n f fe lab ids) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) gen)
      (erased (Bridgeless d e n f) bl) (erased (AllOrder d e (Succ (Succ (Zero)))) pl) (erased (AllOrder d n (Succ (Succ (Succ (Zero))))) cu)
      (erased (Respects f e fe) rfe) (erased (Respects n fe ids) kfe) (erased (Iota d ids) io) (erased (Under fe d) ufe) (erased (Length (Nat) fe d) lfe)
      (erased (FaceLab d f lab) fl) (erased (Respects lab f lab) rl) -> (Spk d e n f fe lab)))

(def-fns _ $ (erased spk-make : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) gen)
    (erased (Bridgeless d e n f) bl) (erased (AllOrder d e (Succ (Succ (Zero)))) pl) (erased (AllOrder d n (Succ (Succ (Succ (Zero))))) cu)
    -> (erased (List (Nat)) fe lab) (erased (Spk d e n f fe lab) c))
  (let ((erased h2)) h)
  (let-match erased h2 (MkHypermap _ _ _ _ ids fe en nf io cfe ke cen kn cnf kf))
  (let ((erased nf2) (erased ni) (erased fi) (erased rnf) (erased pme) (erased pmn) (erased pmf)) (hyper-core d e n f h))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased lab) (erased fl)) (facelab-exists d f fi pmf))
  (let ((erased fl2)) fl)
  (let-match erased fl2 (MkFaceLab _ k _ fi2 _ ids2 rs gf pf gr io2 ro cl ll))
  (values fe lab (MkSpk d e n f fe lab ids h gen bl pl cu cfe ke io (respects-under-vals f e fe d cfe (perm-under d f fi pmf))
    (respects-length f e fe d cfe le) fl (graph-resp d f lab gf gr cl ll))))

(def-fns _ $ (erased fe-node : (erased (Nat) d u s) (erased (List (Nat)) e n f fe lab) (erased (Spk d e n f fe lab) c) (erased (Nth (Nat) fe u s) ps)
    -> (erased (Nth (Nat) n s u) r))
  (let-match erased c (MkSpk _ _ _ _ _ _ ids h gen bl pl cu rfe kfe io ufe lfe fl rl))
  (respects-nth n fe ids u s u kfe ps (iota-nth d u ids io (nth-lt-length _ fe u d s ps lfe))))

(def-fns _ $ (erased fe-split : (erased (Nat) d u s) (erased (List (Nat)) e n f fe lab) (erased (Spk d e n f fe lab) c) (erased (Nth (Nat) fe u s) ps)
    -> (erased (Nat) eu) (erased (Nth (Nat) e u eu) pe) (erased (Nth (Nat) f eu s) pf))
  (let-match erased c (MkSpk _ _ _ _ _ _ ids h gen bl pl cu rfe kfe io ufe lfe fl rl))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pme) (erased pmn) (erased pmf)) (hyper-core d e n f h))
  (let ((erased eu) (erased pe) (erased leu)) (perm-nth d u e nf pme (nth-lt-length _ fe u d s ps lfe)))
  (let ((erased s2) (erased pf) (erased _)) (perm-nth d eu f fi pmf leu))
  (let-match erased (nth-fn _ fe u s s2 ps (respects-at f e fe u eu s2 rfe pe pf)) (Refl _ _))
  (values eu pe pf))

; n (f v) = e v.
(def-fns _ $ (erased node-face : (erased (Nat) d v u) (erased (List (Nat)) e n f fe lab) (erased (Spk d e n f fe lab) c) (erased (Nth (Nat) f v u) pf)
    -> (erased (Nat) ev) (erased (Nth (Nat) e v ev) pe) (erased (Nth (Nat) n u ev) pn))
  (let-match erased c (MkSpk _ _ _ _ _ _ ids h gen bl pl cu rfe kfe io ufe lfe fl rl))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pme) (erased pmn) (erased pmf)) (hyper-core d e n f h))
  (let ((erased lv)) (pre-lt d v u f fi pmf pf))
  (let ((erased w) (erased pw) (erased lw)) (perm-nth d v nf e (perm-sym d e nf pme) lv))
  (let ((erased pew) (erased _)) (plain-eq d w v e pl lw (perm-inv d v w nf e (perm-sym d e nf pme) pw)))
  (values w pew (respects-nth n f nf v u w rnf pf pw)))

; n (e u) = fe (f u).
(def-fns _ $ (erased node-edge : (erased (Nat) d u eu w sw) (erased (List (Nat)) e n f fe lab) (erased (Spk d e n f fe lab) c) (erased (Nth (Nat) f u w) pf)
    (erased (Nth (Nat) e u eu) pe) (erased (Nth (Nat) fe w sw) ps) -> (erased (Nth (Nat) n eu sw) r))
  (let-match erased c (MkSpk _ _ _ _ _ _ ids h gen bl pl cu rfe kfe io ufe lfe fl rl))
  (let ((erased ev) (erased pev) (erased pnw)) (node-face d u w e n f fe lab c pf))
  (let-match erased (nth-fn _ e u eu ev pe pev) (Refl _ _))
  (let ((erased z) (erased pz) (erased pzs) (erased _) (erased _)) (cubic-eq d sw w n cu (under-nth fe w sw d ufe ps) (fe-node d w sw e n f fe lab c ps)))
  (let-match erased (nth-fn _ n w z eu pz pnw) (Refl _ _))
  pzs)

; The spoke of the face image of v, one face step after the edge image of the spoke of v, is reached along f: the step of
; the spoke ring.
(def-fns _ $ (erased spoke-step : (erased (Nat) d v u su sv esu) (erased (List (Nat)) e n f fe lab) (erased (Spk d e n f fe lab) c)
    (erased (Nth (Nat) f v u) pf) (erased (Nth (Nat) fe u su) psu) (erased (Nth (Nat) fe v sv) psv) (erased (Nth (Nat) e su esu) pe)
    -> (erased (SomePath f (Nil (Nat)) esu sv) r))
  (let-match erased c (MkSpk _ _ _ _ _ _ ids h gen bl pl cu rfe kfe io ufe lfe fl rl))
  (let ((erased ev) (erased pev) (erased pnu)) (node-face d v u e n f fe lab c pf))
  (let ((erased z) (erased pz) (erased pzs) (erased _) (erased _)) (cubic-eq d su u n cu (under-nth fe u su d ufe psu) (fe-node d u su e n f fe lab c psu)))
  (let-match erased (nth-fn _ n u z ev pz pnu) (Refl _ _))
  (let ((erased ev2) (erased pev2) (erased pfv)) (fe-split d v sv e n f fe lab c psv))
  (let-match erased (nth-fn _ e v ev ev2 pev pev2) (Refl _ _))
  (some-cat f esu ev sv (some-step f esu ev (hyper-third d esu su ev e n f h pe pzs)) (some-step f ev sv pfv)))

(let ((erased five)) (Succ (Succ (Succ (Succ (Succ (Zero)))))))

; What the steps of min_arity take: a map as min_arity has it, and BirkhoffChecks.
(def-adts $ (MinCx : ((Level) B) ((Nat) d) ((List (Nat)) e n f fe lab) -> Type)
  enum
  (many MkMinCx : (erased (Level) B) (erased (Nat) d) (erased (List (Nat)) e n f fe lab) (erased (Predates (Level) (level-of birk-glue) B) pb)
      (erased (BirkhoffChecks) bks) (erased (Spk d e n f fe lab) c) (erased (Connected d e n f) cn) (erased (NoColoring e f) nc) -> (MinCx B d e n f fe lab)))

(def-fns _ $ (erased cx-ring : (erased (Level) B) (erased (Nat) d x0 k) (erased (List (Nat)) e n f fe lab p) (erased (MinCx B d e n f fe lab) m)
    (erased (Ring e f x0 p) rg) (erased (Length (Nat) (Cons (Nat) x0 p) k) lr) (erased (Lt k five) l5) (erased (NonTrivial d e n f (Cons (Nat) x0 p) (Zero)) nt)
    -> (erased (Reduces B d e n f) r))
  (unary 6)
  (let-match erased m (MkMinCx _ _ _ _ _ _ _ pb bks c cn nc))
  (let-match erased c (MkSpk _ _ _ _ _ _ ids h gen bl pl cu rfe kfe io ufe lfe fl rl))
  (birkhoff-reduces B pb d x0 k (Zero) e n f p bks h gen bl pl cu cn nc rg lr (lt-weaken k five l5) (BMLow k l5) nt))

(def-fns _ $ (erased cx-dd : (erased (Level) B) (erased (Nat) d u u2 eu eu2 l l2) (erased (List (Nat)) e n f fe lab) (erased (MinCx B d e n f fe lab) m)
    (erased (Nth (Nat) e u eu) pe) (erased (Nth (Nat) e u2 eu2) pe2) (erased (Nth (Nat) lab u l) pl1) (erased (Nth (Nat) lab u2 l) pl2)
    (erased (Nth (Nat) lab eu l2) pm1) (erased (Nth (Nat) lab eu2 l2) pm2) (erased (Apart (Nat) Lt u u2) ne) -> (erased (Reduces B d e n f) r))
  (let-match erased m (MkMinCx _ _ _ _ _ _ _ pb bks c cn nc))
  (let-match erased c (MkSpk _ _ _ _ _ _ ids h gen bl pl cu rfe kfe io ufe lfe fl rl))
  (double-dart B pb d u u2 eu eu2 e n f bks h gen bl pl cu cn nc pe pe2 (facelab-same d u u2 l f lab fl pl1 pl2) (facelab-same d eu eu2 l2 f lab fl pm1 pm2) ne))

; Every dart of xs has the label l.
(def-adts $ (LabAll : ((List (Nat)) lab) ((Nat) l) ((List (Nat)) xs) -> Type)
  enum
  (many LabNil : (erased (List (Nat)) lab) (erased (Nat) l) -> (LabAll lab l (Nil (Nat))))
  (many LabCons : (erased (List (Nat)) lab xs) (erased (Nat) l x) (erased (Nth (Nat) lab x l) px) (erased (LabAll lab l xs) rest) -> (LabAll lab l (Cons (Nat) x xs))))

(def-fns _ $ (erased laball-in : (erased (Nat) l u) (erased (List (Nat)) lab xs) (subterm erased (LabAll lab l xs) al) (erased (In u xs) iu) -> (erased (Nth (Nat) lab u l) r))
  (let-match erased al (LabCons _ xs1 _ x px al1) (absurd (LabNil _ _) iu))
  (match erased iu _ ((InHere _ _) px) ((InThere _ _ _ iu1) (laball-in l u lab xs1 al1 iu1))))

(def-fns _ $ (erased walk-laball : (erased (Nat) a b l) (erased (List (Nat)) p lab s xs) (subterm erased (Path p s a b xs) w) (erased (Respects lab p lab) rf)
    (erased (Nth (Nat) lab a l) pl) -> (erased (LabAll lab l xs) r))
  (let-match erased w (PathStep _ _ xs1 _ a1 _ pa _ w1) ((PathHere _ _ _) (LabNil lab l)))
  (LabCons lab xs1 l a pl (walk-laball a1 b l p lab s xs1 w1 rf (respects-nth lab p lab a a1 l rf pa pl))))

(def-fns _ $ (erased path-under : (erased (Nat) d a b) (erased (List (Nat)) p q s xs) (erased (HPerm d p q) pm) (subterm erased (Path p s a b xs) w) (erased (Lt a d) la)
    -> (erased (Under xs d) u))
  (let-match erased w (PathStep _ _ xs1 _ a1 _ pa _ w1) ((PathHere _ _ _) (UnderNil d)))
  (UnderCons xs1 a d la (path-under d a1 b p q s xs1 pm w1 (perm-val d a a1 p q pm pa))))

; z :: ys, with c z the start of a walk along c to z, is closed under the inverse q of c.
(def-fns _ $ (erased cyc-inv : (erased (Nat) d z z2 t u) (erased (List (Nat)) c q s ys) (erased (HPerm d c q) pm) (erased (Path c s z2 z ys) cy)
    (erased (Nth (Nat) c z z2) pz) (erased (In t (Cons (Nat) z ys)) it) (erased (Nth (Nat) q t u) pt) -> (erased (In u (Cons (Nat) z ys)) r))
  (let-match erased (nat-eq t z2) (Unequal _ _ _ _ ne)
    ((Equal _ _ _) (let-match erased (nth-fn _ q z2 u z pt (perm-inv d z z2 c q pm pz)) (Refl _ _)) (InHere u ys)))
  (let ((erased v) (erased iv) (erased pv)) (path-prev c s ys z2 z t cy it ne))
  (let-match erased (nth-fn _ q t u v pt (perm-inv d v t c q pm pv)) (Refl _ _))
  (InThere u z ys iv))

(def-fns _ $ (erased walk-cyc-inv : (erased (Nat) d z z2 a b) (erased (List (Nat)) c q s s2 ys xs) (erased (HPerm d c q) pm) (erased (Path c s z2 z ys) cy)
    (erased (Nth (Nat) c z z2) pz) (subterm erased (Path q s2 a b xs) w) (erased (In a (Cons (Nat) z ys)) ia)
    -> (erased (Sub xs (Cons (Nat) z ys)) sb) (erased (In b (Cons (Nat) z ys)) ib))
  (let-match erased w (PathStep _ _ xs1 _ a1 _ pa _ w1) ((PathHere _ _ _) (values (HSubNil _) ia)))
  (let ((erased sb1) (erased ib1)) (walk-cyc-inv d z z2 a1 b c q s s2 ys xs1 pm cy pz w1 (cyc-inv d z z2 a a1 c q s ys pm cy pz ia pa)))
  (values (HSubCons a xs1 _ ia sb1) ib1))

(def-fns _ $ (erased spoke-apart : (erased (Nat) d u s l l2) (erased (List (Nat)) e n f fe lab) (erased (Spk d e n f fe lab) c) (erased (Nth (Nat) fe u s) ps)
    (erased (Nth (Nat) lab u l) pu) (erased (Nth (Nat) lab s l2) pl) -> (erased (Apart (Nat) Lt l l2) r))
  (let-match erased (nat-eq l l2) (Unequal _ _ _ _ ne)
    (absurd (Equal _ _ _)
      (let-match erased c (MkSpk _ _ _ _ _ _ ids h gen bl pl0 cu rfe kfe io ufe lfe fl rl))
      (let ((erased eu) (erased pe) (erased pf)) (fe-split d u s e n f fe lab c ps))
      (let-match erased (facelab-same d u eu l f lab fl pu (respects-at lab f lab eu s l rl pf pl)) (MkSomePath _ _ ws _ _ wp))
      (bridgeless-face d u eu e n f (Nil _) ws bl pe wp)))
  ne)

; No spoke of a dart of label l has the label l.
(def-fns _ $ (erased spokes-off : (erased (Nat) d lx) (erased (List (Nat)) e n f fe lab Vs Rs ls) (erased (Spk d e n f fe lab) c)
    (subterm erased (Respects fe Vs Rs) rv) (erased (Respects lab Rs ls) rl) (erased (LabAll lab lx Vs) al) -> (erased (NotIn lx ls) r))
  (let-match erased rv (RespCons _ Vs1 Rs1 u s pus rv1) ((RespNil _) (let-match erased rl (RespNil _)) (NotInNil lx)))
  (let-match erased rl (RespCons _ _ ls1 _ l pl rl1))
  (let-match erased al (LabCons _ _ _ _ plu al1))
  (NotInCons lx l ls1 (spoke-apart d u s lx l e n f fe lab c pus plu pl) (spokes-off d lx e n f fe lab Vs1 Rs1 ls1 c rv1 rl1 al1)))

; The spokes of distinct darts of one face lie on distinct faces, or the map reduces (double-dart).
(def-fns _ $ (erased spokes-simple : (erased (Level) B) (erased (Nat) d lx) (erased (List (Nat)) e n f fe lab Vs Rs ls) (erased (MinCx B d e n f fe lab) m)
    (subterm erased (Respects fe Vs Rs) rv) (erased (Respects lab Rs ls) rl) (erased (Distinct Vs) dv) (erased (LabAll lab lx Vs) al)
    -> (erased (HOr (Distinct ls) (Reduces B d e n f)) r))
  (let-match erased rv (RespCons _ Vs1 Rs1 u s pus rv1) ((RespNil _) (let-match erased rl (RespNil _)) (OrL _ _ (DistNil))))
  (let-match erased rl (RespCons _ _ ls1 _ l pl rl1))
  (let-match erased dv (DistCons _ _ ou dv1))
  (let-match erased al (LabCons _ _ _ _ plu al1))
  (let-match erased (spokes-simple B d lx e n f fe lab Vs1 Rs1 ls1 m rv1 rl1 dv1 al1) (OrL _ _ dl1) ((OrR _ _ r) (OrR _ _ r)))
  (match erased (in-dec l ls1) _
    ((OrR _ _ o) (OrL _ _ (DistCons l ls1 o dl1)))
    ((OrL _ _ il)
      (let-match erased m (MkMinCx _ _ _ _ _ _ _ pb bks c cn nc))
      (let-match erased c (MkSpk _ _ _ _ _ _ ids h gen bl pl0 cu rfe kfe io ufe lfe fl rlf))
      (let ((erased s2) (erased is2) (erased ps2)) (respects-in lab Rs1 ls1 l rl1 il))
      (let ((erased u2) (erased iu2) (erased pu2)) (respects-in fe Vs1 Rs1 s2 rv1 is2))
      (let ((erased eu) (erased pe) (erased pf)) (fe-split d u s e n f fe lab c pus))
      (let ((erased eu2) (erased pe2) (erased pf2)) (fe-split d u2 s2 e n f fe lab c pu2))
      (OrR _ _ (cx-dd B d u u2 eu eu2 lx l e n f fe lab m pe pe2 plu (laball-in lx u2 lab Vs1 al1 iu2)
        (respects-at lab f lab eu s l rlf pf pl) (respects-at lab f lab eu2 s2 l rlf pf2 ps2) (notin-in u u2 Vs1 ou iu2))))))
