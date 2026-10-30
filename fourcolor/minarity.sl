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

; Spokes along a walk of fi from a, the fi image of c, form a ring path from the spoke of c to the spoke of the last dart z left.
(def-fns _ $ (erased spoke-rpath : (erased (Nat) d c a b sc) (erased (List (Nat)) e n f fe lab fi S ws Q) (erased (Spk d e n f fe lab) cb) (erased (HPerm d f fi) pmf)
    (subterm erased (Path fi S a b ws) w) (erased (Nth (Nat) fi c a) pc) (erased (Nth (Nat) fe c sc) psc) (erased (Respects fe ws Q) rq)
    -> (erased (Nat) z sz) (erased (Nth (Nat) fi z b) pz) (erased (Nth (Nat) fe z sz) psz) (erased (RPath e f sc Q sz) rp))
  (let-match erased w (PathStep _ _ ws1 _ a1 _ pa _ w1) ((PathHere _ _ _) (let-match erased rq (RespNil _)) (values c sc pc psc (RPNil e f sc))))
  (let-match erased rq (RespCons _ _ Q1 _ sa psa rq1))
  (let ((erased z) (erased sz) (erased pz) (erased psz) (erased rp1)) (spoke-rpath d a a1 b sa e n f fe lab fi S ws1 Q1 cb pmf w1 pa psa rq1))
  (let ((erased cb2)) cb)
  (let-match erased cb2 (MkSpk _ _ _ _ _ _ ids h gen bl pl cu rfe kfe io ufe lfe fl rl))
  (let ((erased nf) (erased ni) (erased fi2) (erased rnf) (erased pme) (erased pmn) (erased pmf2)) (hyper-core d e n f h))
  (let ((erased esc) (erased pesc) (erased _)) (perm-nth d sc e nf pme (under-nth fe c sc d ufe psc)))
  (values z sz pz psz (RPCons e f Q1 sc esc sa sz pesc (spoke-step d a c sc sa esc e n f fe lab cb (perm-inv d c a fi f (perm-sym d f fi pmf) pc) psc psa pesc) rp1)))

; The spoke ring sx :: Q of the face of x, read along fi from x as the spokes of V = x :: ys, with the labels ls of its faces,
; lx that of the face of x, and m < 5 darts.
(def-adts $ (SRg : ((Nat) d) ((List (Nat)) e n f fe lab) ((Nat) x sx) ((List (Nat)) Q) ((Nat) lx) ((List (Nat)) ls) -> Type)
  enum
  (many MkSRg : (erased (Nat) d x a sx lx m) (erased (List (Nat)) e n f fe lab fi ys Q ls) (erased (Spk d e n f fe lab) c)
      (erased (HPerm d f fi) pmf) (erased (Nth (Nat) fi x a) pa) (erased (Path fi (Cons (Nat) x (Nil (Nat))) a x ys) w)
      (erased (Respects fe (Cons (Nat) x ys) (Cons (Nat) sx Q)) rv) (erased (Ring e f sx Q) rg) (erased (Nth (Nat) lab x lx) plx)
      (erased (LabAll lab lx (Cons (Nat) x ys)) al) (erased (Respects lab (Cons (Nat) sx Q) ls) rls) (erased (Distinct (Cons (Nat) lx ls)) dl)
      (erased (Length (Nat) (Cons (Nat) sx Q) m) lm) (erased (Lt m five) l5) -> (SRg d e n f fe lab x sx Q lx ls)))

; The spoke ring of a face of k darts, k < 5 (scycle_spoke_ring and size_spoke_ring), or a reduction from double-dart.
(def-fns _ $ (erased ring-build : (erased (Level) B) (erased (Nat) d x k) (erased (List (Nat)) e n f fe lab) (erased (MinCx B d e n f fe lab) m)
    (erased (Order f x k) o) (erased (Lt k five) lk)
    -> (erased (Nat) sx lx) (erased (List (Nat)) Q ls) (erased (HOr (SRg d e n f fe lab x sx Q lx ls) (Reduces B d e n f)) r))
  (let-match erased m (MkMinCx _ _ _ _ _ _ _ pb bks c cn nc))
  (let ((erased c2)) c)
  (let-match erased c2 (MkSpk _ _ _ _ _ _ ids h gen bl pl cu rfe kfe io ufe lfe fl rl))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pme) (erased pmn) (erased pmf)) (hyper-core d e n f h))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased ll)) (respects-length lab f lab d rl lf))
  (let ((erased pfi)) (perm-sym d f fi pmf))
  (let-match erased o (MkOrder _ xs _ y k1 py wf lxs))
  (let ((erased lx)) (pre-lt d x y f fi pmf py))
  (let ((erased a) (erased pa) (erased la)) (perm-nth d x fi f pfi lx))
  (let ((erased ws) (erased w0)) (cycle d x a fi f pfi pa lx))
  (let ((erased ys) (erased w)) (walk-to fi ws a x w0))
  (let ((erased sx) (erased psx)) (nth-exists _ fe d x lfe lx))
  (let ((erased Q) (erased rq)) (respects-exists fe ys d (path-under d a x fi f _ ys pfi w la) lfe))
  (let ((erased z) (erased sz) (erased pz) (erased psz) (erased rp)) (spoke-rpath d x a x sx e n f fe lab fi _ ys Q c pmf w pa psx rq))
  (let ((erased esz) (erased pesz) (erased _)) (perm-nth d sz e nf pme (under-nth fe z sz d ufe psz)))
  (let ((erased sp)) (spoke-step d x z sz sx esz e n f fe lab c (perm-inv d z x fi f pfi pz) psz psx pesz))
  (let ((erased rv)) (RespCons fe ys Q x sx psx rq))
  (let ((erased lxl) (erased plx)) (nth-exists _ lab d x ll lx))
  (let ((erased ls) (erased rls)) (respects-exists lab _ d (respects-under-vals fe _ _ d rv ufe) ll))
  (let ((erased rfi)) (resp-inv d lab f fi pmf rl ll))
  (let ((erased al)) (LabCons lab ys lxl x plx (walk-laball a x lxl fi lab _ ys w rfi (respects-nth lab fi lab x a lxl rfi pa plx))))
  (let ((erased dv)) (DistCons x ys (path-avoid fi _ ys a x x w (InHere x _)) (walk-distinct fi (Nil _) ys a x w)))
  (let-match erased (spokes-simple B d lxl e n f fe lab _ _ ls m rv rls dv al) (OrL _ _ dls) ((OrR _ _ r) (values x x (Nil _) (Nil _) (OrR _ _ r))))
  (let ((erased rg)) (MkRing e f Q sx sz esz rp pesz sp (MkSimple f _ lab ls rl rls dls)))
  (let ((erased mv) (erased lv)) (length-exists _ (Cons _ x ys)))
  (let ((erased sb) (erased _)) (walk-cyc-inv d x y a x f fi _ _ xs ys pmf wf py w (cyc-inv d x y x a f fi _ xs pmf wf py (InHere x xs) pa)))
  (let ((erased le5)) (pigeonhole (Cons _ x ys) (Cons _ x xs) mv k dv (HSubCons x ys _ (InHere x xs) sb) lv (LengthCons _ x xs k1 lxs)))
  (values sx lxl Q ls (OrL _ _ (MkSRg d x a sx lxl mv e n f fe lab fi ys Q ls c pmf pa w rv rg plx al rls
    (DistCons lxl ls (spokes-off d lxl e n f fe lab _ _ ls c rv rls al) dls) (respects-length fe _ _ mv rv lv) (lt-ls mv (Succ k) five le5 (LtS k five lk))))))

; A dart of the spoke ring is the spoke of a dart of the face.
(def-fns _ $ (erased sr-in : (erased (Nat) d x sx lx s) (erased (List (Nat)) e n f fe lab Q ls) (erased (SRg d e n f fe lab x sx Q lx ls) sr) (erased (In s (Cons (Nat) sx Q)) is)
    -> (erased (Nat) u) (erased (Nth (Nat) fe u s) pu) (erased (Nth (Nat) lab u lx) plu))
  (let-match erased sr (MkSRg _ _ a _ _ m _ _ _ _ _ fi ys _ _ c pmf pa w rv rg plx al rls dl lm l5))
  (let ((erased u) (erased iu) (erased pu)) (respects-in fe _ _ s rv is))
  (values u pu (laball-in lx u lab _ al iu)))

; The spoke of each dart of the face is on the spoke ring (mem_spoke_ring).
(def-fns _ $ (erased sr-hit : (erased (Nat) d x sx lx w) (erased (List (Nat)) e n f fe lab Q ls) (erased (SRg d e n f fe lab x sx Q lx ls) sr) (erased (Nth (Nat) lab w lx) pw)
    -> (erased (Nat) s) (erased (Nth (Nat) fe w s) ps) (erased (In s (Cons (Nat) sx Q)) is))
  (let-match erased sr (MkSRg _ _ a _ _ m _ _ _ _ _ fi ys _ _ c pmf pa w0 rv rg plx al rls dl lm l5))
  (let-match erased c (MkSpk _ _ _ _ _ _ ids h gen bl pl cu rfe kfe io ufe lfe fl rl))
  (let-match erased (facelab-same d x w lx f lab fl plx pw) (MkSomePath _ _ xs _ _ wf))
  (let ((erased sb) (erased iw)) (walk-cyc-inv d x a x w fi f _ _ ys xs (perm-sym d f fi pmf) w0 pa wf (InHere x ys)))
  (let ((erased s) (erased ps) (erased is)) (respects-val fe _ _ w rv iw))
  (values s ps is))

(def-fns _ $ (erased absurd kernel-fband : (erased (Nat) y z) (erased (List (Nat)) f r) (erased (Kernel f r y) k) (erased (SomePath f (Nil (Nat)) y z) sp)
    (erased (In z r) iz) -> (erased (False) fl))
  (let-match erased k (MkKernel _ _ lab ls _ l rf rp px out))
  (let-match erased sp (MkSomePath _ _ ws _ _ w))
  (apart-irrefl l (notin-in l l ls out (in-map lab r ls z l iz rp (path-label f lab (Nil _) ws y z l w rf px)))))

(def-fns _ $ (erased absurd kernel-dp : (erased (Nat) s y) (erased (List (Nat)) n f r) (erased (DPath n f r s y) dp) (erased (In s r) is) (erased (Kernel f r y) ky)
    -> (erased (False) fl))
  (match erased dp _
    (absurd (DPNil _ _ _ _) (apart-irrefl s (notin-in s s r (kernel-off f r s ky) is)))
    (absurd (DPNode _ _ _ _ _ _ out _ _) (apart-irrefl s (notin-in s s r out is)))
    (absurd (DPFace _ _ _ _ _ _ out _ _) (apart-irrefl s (notin-in s s r out is)))))

(def-fns _ $ (erased dp-on : (erased (Nat) d x sx lx w y) (erased (List (Nat)) e n f fe lab Q ls) (erased (SRg d e n f fe lab x sx Q lx ls) sr)
    (subterm erased (DPath n f (Cons (Nat) sx Q) w y) dp) (erased (Nth (Nat) lab w lx) pw) (erased (Kernel f (Cons (Nat) sx Q) y) ky) -> (erased (Nth (Nat) lab y lx) r))
  (let ((erased sr2)) sr)
  (let-match erased sr2 (MkSRg _ _ a _ _ m _ _ _ _ _ fi ys _ _ c pmf pa w0 rv rg plx al rls dl lm l5))
  (let-match erased c (MkSpk _ _ _ _ _ _ ids h gen bl pl cu rfe kfe io ufe lfe fl rl))
  (let ((erased nf) (erased ni) (erased fi2) (erased rnf) (erased pme) (erased pmn) (erased pmf2)) (hyper-core d e n f h))
  (match erased dp _
    ((DPNil _ _ _ _) pw)
    ((DPFace _ _ _ _ w1 _ out pf dp1) (dp-on d x sx lx w1 y e n f fe lab Q ls sr dp1 (respects-nth lab f lab w w1 lx rl pf pw) ky))
    (absurd (DPNode _ _ _ _ w1 _ out pn dp1)
      (let ((erased s) (erased ps) (erased is)) (sr-hit d x sx lx w e n f fe lab Q ls sr pw))
      (let-match erased (perm-inj d w1 s w n ni pmn pn (fe-node d w s e n f fe lab c ps)) (Refl _ _))
      (kernel-dp s y n f _ dp1 is ky))))

; diskF_spoke_ring, the direction min_arity's colouring uses: a dart of diskN of the spoke ring on none of its faces is on the face.
(def-fns _ $ (erased disk-on : (erased (Nat) d x sx lx y) (erased (List (Nat)) e n f fe lab Q ls) (erased (SRg d e n f fe lab x sx Q lx ls) sr)
    (erased (DiskN n f (Cons (Nat) sx Q) y) dn) (erased (Kernel f (Cons (Nat) sx Q) y) ky) -> (erased (Nth (Nat) lab y lx) r))
  (let ((erased sr2)) sr)
  (let-match erased sr2 (MkSRg _ _ a _ _ m _ _ _ _ _ fi ys _ _ c pmf pa w0 rv rg plx al rls dl lm l5))
  (let-match erased c (MkSpk _ _ _ _ _ _ ids h gen bl pl cu rfe kfe io ufe lfe fl rl))
  (let ((erased nf) (erased ni) (erased fi2) (erased rnf) (erased pme) (erased pmn) (erased pmf2)) (hyper-core d e n f h))
  (let-match erased dn (MkDiskN _ _ _ _ y0 y2 iy0 pn dp))
  (let ((erased u) (erased pu) (erased plu)) (sr-in d x sx lx y0 e n f fe lab Q ls sr iy0))
  (let ((erased lu)) (nth-lt-length _ fe u d y0 pu lfe))
  (let ((erased z) (erased pnu) (erased pnz) (erased _) (erased _)) (cubic-eq d y0 u n cu (under-nth fe u y0 d ufe pu) (fe-node d u y0 e n f fe lab c pu)))
  (let-match erased (perm-inj d y2 z y0 n ni pmn pn pnz) (Refl _ _))
  (let ((erased v) (erased pv) (erased _)) (perm-nth d u fi2 f (perm-sym d f fi2 pmf2) lu))
  (let ((erased pfv)) (perm-inv d u v fi2 f (perm-sym d f fi2 pmf2) pv))
  (let ((erased ev) (erased pev) (erased pnev)) (node-face d v u e n f fe lab c pfv))
  (let-match erased (nth-fn _ n u z ev pnu pnev) (Refl _ _))
  (let ((erased sv) (erased psv) (erased isv)) (sr-hit d x sx lx v e n f fe lab Q ls sr (respects-at lab f lab v u lx rl pfv plu)))
  (let ((erased ev2) (erased pev2) (erased pfz)) (fe-split d v sv e n f fe lab c psv))
  (let-match erased (nth-fn _ e v ev ev2 pev pev2) (Refl _ _))
  (match erased dp (((Nth (Nat) lab y lx) r))
    ((DPNode _ _ _ _ w1 _ out pn2 dp1)
      (let-match erased (perm-inj d w1 u z n ni pmn pn2 pnu) (Refl _ _))
      (dp-on d x sx lx u y e n f fe lab Q ls sr dp1 plu ky))
    (absurd (DPNil _ _ _ _) (kernel-fband z sv f _ ky (some-step f z sv pfz) isv))
    (absurd (DPFace _ _ _ _ w1 _ out pf dp1)
      (let-match erased (nth-fn _ f z w1 sv pf pfz) (Refl _ _))
      (kernel-dp sv y n f _ dp1 isv ky))))

; The other direction of diskF_spoke_ring, at x.
(def-fns _ $ (erased sr-diskf : (erased (Nat) d x sx lx) (erased (List (Nat)) e n f fe lab Q ls) (erased (SRg d e n f fe lab x sx Q lx ls) sr)
    -> (erased (DiskF n f (Cons (Nat) sx Q) x) r))
  (let-match erased sr (MkSRg _ _ a _ _ m _ _ _ _ _ fi ys _ _ c pmf pa w rv rg plx al rls dl lm l5))
  (let-match erased c (MkSpk _ _ _ _ _ _ ids h gen bl pl cu rfe kfe io ufe lfe fl rl))
  (let ((erased nf) (erased ni) (erased fi2) (erased rnf) (erased pme) (erased pmn) (erased pmf2)) (hyper-core d e n f h))
  (let-match erased rv (RespCons _ _ _ _ _ psx _))
  (let-match erased dl (DistCons _ _ ol _))
  (MkDiskF n f _ x (disk-node d sx x n ni f _ pmn (disk-ring d sx n ni f _ pmn (InHere sx Q) (under-nth fe x sx d ufe psx)) (fe-node d x sx e n f fe lab c psx))
    (MkKernel f _ lab ls x lx rl rls plx ol)))

; Every dart is on the face of x or on a face of its spoke ring, or the map reduces: a dart on neither is in diskFC of the spoke
; ring (disk-on), which is then nontrivial for 0.
(def-fns _ $ (erased cover : (erased (Level) B) (erased (Nat) d x sx lx y l) (erased (List (Nat)) e n f fe lab Q ls) (erased (MinCx B d e n f fe lab) m)
    (erased (SRg d e n f fe lab x sx Q lx ls) sr) (erased (Nth (Nat) lab y l) pl) -> (erased (HOr (In l (Cons (Nat) lx ls)) (Reduces B d e n f)) r))
  (let ((erased sr2)) sr)
  (let-match erased sr2 (MkSRg _ _ a _ _ k _ _ _ _ _ fi ys _ _ c pmf pa w rv rg plx al rls dl lm l5))
  (let-match erased c (MkSpk _ _ _ _ _ _ ids h gen bl pl0 cu rfe kfe io ufe lfe fl rl))
  (let ((erased nf) (erased ni) (erased fi2) (erased rnf) (erased pme) (erased pmn) (erased pmf2)) (hyper-core d e n f h))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased ly)) (nth-lt-length _ lab y d l pl (respects-length lab f lab d rl lf)))
  (let ((erased gf) (erased grf)) (perm-graph d f fi2 pmf2))
  (let ((erased ur)) (ring-under d sx e n f Q h rg))
  (match erased (band-dec d y f fi2 _ gf pmf2 grf ur ly) _
    ((OrL _ _ fb)
      (let-match erased fb (MkFband _ _ _ z iz sp))
      (OrL _ _ (InThere l lx ls (in-map lab _ ls z l iz rls (facelab-path d y z l f lab fl sp pl)))))
    ((OrR _ _ ky)
      (let ((erased hd) (erased zs) (erased ds)) (ds-exists d e n f _ h ur))
      (let ((erased ids2) (erased io2) (erased sp)) (ds-split d e n _ hd zs ds))
      (match erased (split-cover hd ids2 hd zs y sp (iota-in d y ids2 io2 ly)) _
        ((OrL _ _ ih)
          (let-match erased (nth-fn _ lab y l lx pl (disk-on d x sx lx y e n f fe lab Q ls sr (ds-in d y sx e n f Q hd zs h gen rg ur ds ih) ky)) (Refl _ _))
          (OrL _ _ (InHere l ls)))
        ((OrR _ _ iz)
          (OrR _ _ (cx-ring B d sx k e n f fe lab Q m rg lm l5
            (nontrivial0 d sx x y e n f Q hd zs h gen rg ds (sr-diskf d x sx lx e n f fe lab Q ls sr) iz ky))))))))

; The colours of min_arity, by the position of a face in lx :: ls: 0 for the face of x, then 1, 3, 2 and 3 around the ring.
(let ((erased col5)) (Cons (Nat) (Zero) $ Cons (Nat) (Succ (Zero)) $ Cons (Nat) (Succ (Succ (Succ (Zero)))) $ Cons (Nat) (Succ (Succ (Zero)))
  $ Cons (Nat) (Succ (Succ (Succ (Zero)))) $ Nil (Nat)))

(def-fns _ $ (erased col5-len : -> (erased (Length (Nat) col5 five) r))
  (LengthCons _ _ _ _ $ LengthCons _ _ _ _ $ LengthCons _ _ _ _ $ LengthCons _ _ _ _ $ LengthCons _ _ _ _ $ LengthNil _))

(def-adts $ (Find : ((List (Nat)) L) ((Nat) l) -> Type)
  enum
  (many FHit : (erased (List (Nat)) L) (erased (Nat) l j) (erased (Nth (Nat) L j l) p) -> (Find L l))
  (many FMiss : (erased (List (Nat)) L) (erased (Nat) l) (erased (NotIn l L) o) -> (Find L l)))

(def-fns _ $ (erased find-in : (erased (Nat) l) (subterm erased (List (Nat)) L) -> (erased (Find L l) r))
  (let-match erased L (Cons _ l0 L1) ((Nil _) (FMiss _ l (NotInNil l))))
  (let-match erased (nat-eq l l0) (Unequal _ _ _ _ ne) ((Equal _ _ _) (FHit _ l (Zero) (NthHere _ l L1))))
  (match erased (find-in l L1) _
    ((FHit _ _ j p) (FHit _ l (Succ j) (NthThere _ l0 L1 j l p)))
    ((FMiss _ _ o) (FMiss _ l (NotInCons l l0 L1 ne o)))))

; c is the colour of a face of label l: col5 at the position of l in L, or 0 off L.
(def-adts $ (TabAt : ((List (Nat)) L) ((Nat) l c) -> Type)
  enum
  (many TAHit : (erased (List (Nat)) L) (erased (Nat) l j c) (erased (Nth (Nat) L j l) p) (erased (Nth (Nat) col5 j c) q) -> (TabAt L l c))
  (many TAMiss : (erased (List (Nat)) L) (erased (Nat) l) (erased (NotIn l L) o) -> (TabAt L l (Zero))))

(def-adts $ (Tab : ((List (Nat)) L xs ks) -> Type)
  enum
  (many TabNil : (erased (List (Nat)) L) -> (Tab L (Nil (Nat)) (Nil (Nat))))
  (many TabCons : (erased (List (Nat)) L xs ks) (erased (Nat) l c) (erased (TabAt L l c) t) (erased (Tab L xs ks) rest)
      -> (Tab L (Cons (Nat) l xs) (Cons (Nat) c ks))))

(def-fns _ $ (erased tab-exists : (erased (List (Nat)) L) (erased (Nat) m) (erased (Length (Nat) L m) lL) (erased (Lt m (Succ five)) lm) (subterm erased (List (Nat)) xs)
    -> (erased (List (Nat)) ks) (erased (Tab L xs ks) t))
  (let-match erased xs (Cons _ l xs1) ((Nil _) (values (Nil _) (TabNil L))))
  (let ((erased ks1) (erased t1)) (tab-exists L m lL lm xs1))
  (match erased (find-in l L) _
    ((FHit _ _ j p)
      (let ((erased c) (erased q)) (nth-exists _ col5 five j (col5-len) (lt-ls j m five (nth-lt-length _ L j m l p lL) lm)))
      (values (Cons _ c ks1) (TabCons L xs1 ks1 l c (TAHit L l j c p q) t1)))
    ((FMiss _ _ o) (values (Cons _ (Zero) ks1) (TabCons L xs1 ks1 l (Zero) (TAMiss L l o) t1)))))

(def-fns _ $ (erased tab-nth : (erased (List (Nat)) L xs ks) (erased (Nat) i l) (subterm erased (Tab L xs ks) t) (erased (Nth (Nat) xs i l) p)
    -> (erased (Nat) c) (erased (Nth (Nat) ks i c) pc) (erased (TabAt L l c) ta))
  (let-match erased t (TabCons _ xs1 ks1 l0 c0 ta0 t1) (absurd (TabNil _) p))
  (match erased p _
    ((NthHere _ _ _) (values c0 (NthHere _ c0 ks1) ta0))
    ((NthThere _ _ _ i1 _ p1)
      (let ((erased c) (erased pc) (erased ta)) (tab-nth L xs1 ks1 i1 l t1 p1))
      (values c (NthThere _ c0 ks1 i1 c pc) ta))))

(def-fns _ $ (erased tab-length : (erased (List (Nat)) L xs ks) (erased (Nat) k) (subterm erased (Tab L xs ks) t) (erased (Length (Nat) xs k) l)
    -> (erased (Length (Nat) ks k) r))
  (let-match erased t (TabCons _ xs1 ks1 l0 c0 ta0 t1) ((TabNil _) (let-match erased l (LengthNil _)) (LengthNil _)))
  (let-match erased l (LengthCons _ _ _ k1 l1))
  (LengthCons _ c0 ks1 k1 (tab-length L xs1 ks1 k1 t1 l1)))

(def-fns _ $ (erased tab-under : (erased (List (Nat)) L xs ks) (subterm erased (Tab L xs ks) t) -> (erased (Under ks 4) r))
  (unary 4)
  (let-match erased t (TabCons _ xs1 ks1 l0 c0 ta0 t1) ((TabNil _) (UnderNil 4)))
  (let ((erased u5)) (UnderCons _ _ _ (LtZ _) $ UnderCons _ _ _ (LtS _ _ $ LtZ _) $ UnderCons _ _ _ (LtS _ _ $ LtS _ _ $ LtS _ _ $ LtZ _)
    $ UnderCons _ _ _ (LtS _ _ $ LtS _ _ $ LtZ _) $ UnderCons _ _ _ (LtS _ _ $ LtS _ _ $ LtS _ _ $ LtZ _) $ UnderNil 4))
  (UnderCons ks1 c0 4 (match erased ta0 (((Lt c0 4) r)) ((TAHit _ _ j _ _ q) (under-nth col5 j c0 4 u5 q)) ((TAMiss _ _ _) (LtZ _)))
    (tab-under L xs1 ks1 t1)))

(def-fns _ $ (erased tabat-fn : (erased (List (Nat)) L) (erased (Nat) l c c2) (erased (Distinct L) dl) (erased (TabAt L l c) t1) (erased (TabAt L l c2) t2)
    -> (erased (Eq (Nat) c c2) r))
  (match erased t1 _
    ((TAHit _ _ j _ p q)
      (match erased t2 _
        ((TAHit _ _ j2 _ p2 q2) (let-match erased (distinct-nth L j j2 l dl p p2) (Refl _ _)) (nth-fn _ col5 j c c2 q q2))
        (absurd (TAMiss _ _ o) (apart-irrefl l (notin-in l l L o (nth-in L j l p))))))
    ((TAMiss _ _ o)
      (match erased t2 _
        (absurd (TAHit _ _ j2 _ p2 q2) (apart-irrefl l (notin-in l l L o (nth-in L j2 l p2))))
        ((TAMiss _ _ _) (Refl _ c))))))
