; Sums of a list g of numbers, one per dart: at a list of darts, along a face, and over the faces of a hypermap, where
; they add up to the sum over all darts (the partition of the darts into faces that dscore_roots of discharge.v uses).
; Load after dscore.sl.

; s is the sum of g at the darts xs.
(def-adts $ (SumAt : ((List (Nat)) g xs) ((Nat) s) -> Type)
  enum
  (many SANil : (erased (List (Nat)) g) -> (SumAt g (Nil (Nat)) (Zero)))
  (many SACons : (erased (List (Nat)) g xs) (erased (Nat) x c s1 s) (erased (Nth (Nat) g x c) p) (erased (SumAt g xs s1) rest)
      (erased (Add c s1 s) a) -> (SumAt g (Cons (Nat) x xs) s)))

; Every dart of xs is in ys.
(def-adts $ (Incl : ((List (Nat)) xs ys) -> Type)
  enum
  (many InclNil : (erased (List (Nat)) ys) -> (Incl (Nil (Nat)) ys))
  (many InclCons : (erased (Nat) x) (erased (List (Nat)) xs ys) (erased (In x ys) p) (erased (Incl xs ys) rest) -> (Incl (Cons (Nat) x xs) ys)))

(def-fns _ $ (erased incl-in : (erased (List (Nat)) xs ys) (erased (Nat) u) (subterm erased (Incl xs ys) i) (erased (In u xs) p) -> (erased (In u ys) r))
  (let-match erased i (InclCons x xs1 _ px i1) (absurd (InclNil _) p))
  (let-match erased p (InThere _ _ _ p1) ((InHere _ _) px))
  (incl-in xs1 ys u i1 p1))

(def-fns _ $ (erased incl-weak : (erased (List (Nat)) xs ys) (erased (Nat) y) (subterm erased (Incl xs ys) i) -> (erased (Incl xs (Cons (Nat) y ys)) r))
  (let-match erased i (InclCons x xs1 _ px i1) ((InclNil _) (InclNil _)))
  (InclCons x xs1 _ (InThere x y ys px) (incl-weak xs1 ys y i1)))

(def-fns _ $ (erased incl-refl : (subterm erased (List (Nat)) xs) -> (erased (Incl xs xs) r))
  (let-match erased xs (Cons _ x xs1) ((Nil _) (InclNil _)))
  (InclCons x xs1 xs (InHere x xs1) (incl-weak xs1 xs1 x (incl-refl xs1))))

(def-fns _ $ (erased incl-trans : (erased (List (Nat)) a b c) (subterm erased (Incl a b) i) (erased (Incl b c) j) -> (erased (Incl a c) r))
  (let-match erased i (InclCons x a1 _ px i1) ((InclNil _) (InclNil c)))
  (InclCons x a1 c (incl-in b c x j px) (incl-trans a1 b c i1 j)))

(def-fns _ $ (erased remove-incl : (erased (Nat) x) (erased (List (Nat)) ys ys1) (subterm erased (Remove x ys ys1) rm) -> (erased (Incl ys1 ys) r))
  (let-match erased rm (RmThere _ y ys2 ys3 rm1) ((RmHere _ _) (incl-weak ys1 ys1 x (incl-refl ys1))))
  (InclCons y ys3 ys (InHere y ys2) (incl-weak ys3 ys2 y (remove-incl x ys2 ys3 rm1))))

(def-fns _ $ (erased remove-notin : (erased (Nat) x) (erased (List (Nat)) ys ys1) (subterm erased (Remove x ys ys1) rm) (erased (Distinct ys) dy)
    -> (erased (NotIn x ys1) r))
  (let-match erased rm (RmThere _ y ys2 ys3 rm1) ((RmHere _ _) (let-match erased dy (DistCons _ _ ny _)) ny))
  (let-match erased dy (DistCons _ _ ny dy1))
  (NotInCons x y ys3 (apart-sym y x (notin-in y x ys2 ny (remove-src x ys2 ys3 rm1))) (remove-notin x ys2 ys3 rm1 dy1)))

(def-fns _ $ (erased incl-drop : (erased (List (Nat)) a b) (erased (Nat) x) (subterm erased (Incl a (Cons (Nat) x b)) i) (erased (NotIn x a) nx)
    -> (erased (Incl a b) r))
  (let-match erased i (InclCons u a1 _ pu i1) ((InclNil _) (InclNil b)))
  (let-match erased nx (NotInCons _ _ _ ne nx1))
  (let-match erased pu (InThere _ _ _ pu1) (absurd (InHere _ _) (apart-irrefl x ne)))
  (InclCons u a1 b pu1 (incl-drop a1 b x i1 nx1)))

(def-fns _ $ (erased incl-remove : (erased (List (Nat)) a ys ys1) (erased (Nat) x) (subterm erased (Incl a ys) i) (erased (NotIn x a) nx)
    (erased (Remove x ys ys1) rm) -> (erased (Incl a ys1) r))
  (let-match erased i (InclCons u a1 _ pu i1) ((InclNil _) (InclNil ys1)))
  (let-match erased nx (NotInCons _ _ _ ne nx1))
  (InclCons u a1 ys1 (remove-keep x u ys ys1 rm pu (apart-sym x u ne)) (incl-remove a1 ys ys1 x i1 nx1 rm)))

(def-fns _ $ (erased sumat-remove : (erased (List (Nat)) g ys ys1) (erased (Nat) x c s1 s) (subterm erased (Remove x ys ys1) rm)
    (erased (Nth (Nat) g x c) p) (erased (SumAt g ys1 s1) k) (erased (Add c s1 s) a) -> (erased (SumAt g ys s) r))
  (let-match erased rm (RmThere _ y ys2 ys3 rm1) ((RmHere _ _) (SACons g ys1 x c s1 s p k a)))
  (let-match erased k (SACons _ _ _ cy t1 _ py k1 ay))
  (let ((erased z) (erased r1) (erased r2)) (plus-lcomm c cy t1 s1 s ay a))
  (SACons g ys2 y cy z s py (sumat-remove g ys2 ys3 x c t1 z rm1 p k1 r1) r2))

; Two duplicate-free lists of the same darts have the same sum.
(def-fns _ $ (erased perm-sum : (erased (List (Nat)) g xs ys) (erased (Nat) s) (subterm erased (SumAt g xs s) k) (erased (Distinct xs) dx)
    (erased (Distinct ys) dy) (erased (Incl xs ys) i1) (erased (Incl ys xs) i2) -> (erased (SumAt g ys s) r))
  (match erased k _
    ((SANil _) (match erased ys _ ((Nil _) (SANil g)) (absurd (Cons _ y ys1) (let-match erased i2 (InclCons _ _ _ iy _)) iy)))
    ((SACons _ xs1 x c s1 _ p k1 a)
      (let-match erased dx (DistCons _ _ nx dx1))
      (let-match erased i1 (InclCons _ _ _ ix i11))
      (let ((erased ys1) (erased rm)) (remove-exists x ys ix))
      (sumat-remove g ys ys1 x c s1 s rm p
        (perm-sum g xs1 ys1 s1 k1 dx1 (remove-distinct x ys ys1 rm dy) (incl-remove xs1 ys ys1 x i11 nx rm)
          (incl-drop ys1 xs1 x (incl-trans ys1 ys xs (remove-incl x ys ys1 rm) i2) (remove-notin x ys ys1 rm dy)))
        a))))

(def-fns _ $ (erased sumat-fn : (erased (List (Nat)) g xs) (erased (Nat) s t) (subterm erased (SumAt g xs s) k) (erased (SumAt g xs t) l)
    -> (erased (Eq (Nat) s t) e))
  (let-match erased k (SACons _ xs1 x c s1 _ p k1 a) ((SANil _) (let-match erased l (SANil _)) (Refl _ s)))
  (let-match erased l (SACons _ _ _ c2 t1 _ p2 l1 a2))
  (let-match erased (nth-fn _ g x c c2 p p2) (Refl _ _))
  (let-match erased (sumat-fn g xs1 s1 t1 k1 l1) (Refl _ _))
  (add-fn c s1 s t a a2))

(def-fns _ $ (erased sumat-app : (erased (List (Nat)) g a b c) (erased (Nat) s) (subterm erased (AppN a b c) ap) (erased (SumAt g c s) k)
    -> (erased (Nat) s1 s2) (erased (SumAt g a s1) k1) (erased (SumAt g b s2) k2) (erased (Add s1 s2 s) e))
  (let-match erased ap (AppCons a1 _ c1 x ap1) ((AppNil _) (values (Zero) s (SANil g) k (AddZero s))))
  (let-match erased k (SACons _ _ _ cx t _ px k3 ax))
  (let ((erased s1) (erased s2) (erased k1) (erased k2) (erased e)) (sumat-app g a1 b c1 t ap1 k3))
  (let ((erased u) (erased e1) (erased e2)) (plus-assoc-r cx s1 s2 t s ax e))
  (values u s2 (SACons g a1 x cx s1 u px k1 e1) k2 e2))

; Reading g through p: the sum of g . p at xs is the sum of g at the images ys of xs.
(def-fns _ $ (erased sumat-map : (erased (List (Nat)) g p gp xs ys) (erased (Nat) s) (erased (Respects g p gp) rg) (subterm erased (Respects p xs ys) rp)
    (erased (SumAt gp xs s) k) -> (erased (SumAt g ys s) r))
  (let-match erased rp (RespCons _ xs1 ys1 x y pxy rp1) ((RespNil _) (let-match erased k (SANil _)) (SANil g)))
  (let-match erased k (SACons _ _ _ c s1 _ pc k1 a))
  (SACons g ys1 y c s1 s (respects-nth g p gp x y c rg pxy pc) (sumat-map g p gp xs1 ys1 s1 rg rp1 k1) a))

(def-fns _ $ (erased resp-notin : (erased (List (Nat)) q xs ls) (erased (Nat) x l) (subterm erased (Respects q xs ls) rp) (erased (Nth (Nat) q x l) px)
    (erased (NotIn l ls) nl) -> (erased (NotIn x xs) r))
  (let-match erased rp (RespCons _ xs1 ls1 y l2 py rp1) ((RespNil _) (NotInNil x)))
  (let-match erased nl (NotInCons _ _ _ ne nl1))
  (let ((erased (Apart (Nat) Lt x y) nxy))
    (match erased (nat-eq x y) _
      ((Unequal _ _ _ _ d) d)
      (absurd (Equal _ _ _) (let-match erased (nth-fn _ q x l l2 px py) (Refl _ _)) (apart-irrefl l ne))))
  (NotInCons x y xs1 nxy (resp-notin q xs1 ls1 x l rp1 px nl1)))

(def-fns _ $ (erased resp-distinct : (erased (List (Nat)) q xs ls) (subterm erased (Respects q xs ls) rp) (erased (Distinct ls) dl) -> (erased (Distinct xs) r))
  (let-match erased rp (RespCons _ xs1 ls1 x l px rp1) ((RespNil _) (DistNil)))
  (let-match erased dl (DistCons _ _ nl dl1))
  (DistCons x xs1 (resp-notin q xs1 ls1 x l rp1 px nl) (resp-distinct q xs1 ls1 rp1 dl1)))

(def-fns _ $ (erased under-incl : (erased (Nat) d) (erased (List (Nat)) xs ids) (subterm erased (Under xs d) u) (erased (Iota d ids) io) -> (erased (Incl xs ids) r))
  (let-match erased u (UnderCons xs1 x _ lx u1) ((UnderNil _) (InclNil ids)))
  (InclCons x xs1 ids (iota-in d x ids io lx) (under-incl d xs1 ids u1 io)))

(def-fns _ $ (erased perm-cover : (erased (Nat) d) (erased (List (Nat)) p q ids zs) (erased (HPerm d p q) pm) (subterm erased (Under zs d) u)
    -> (erased (Incl zs p) r))
  (let-match erased u (UnderCons zs1 x _ lx u1) ((UnderNil _) (InclNil p)))
  (let-match erased pm (HMkPerm _ _ _ ids2 io lp qp pq))
  (let ((erased y) (erased py) (erased _)) (perm-nth d x q p (perm-sym d p q pm) lx))
  (InclCons x zs1 p (nth-in p y x (respects-nth p q ids2 x y x pq py (iota-nth d x ids2 io lx))) (perm-cover d p q ids zs1 pm u1)))

; Summing g at the images of all darts under a permutation p is summing g at all darts.
(def-fns _ $ (erased perm-total : (erased (Nat) d s) (erased (List (Nat)) g p q gp ids) (erased (HPerm d p q) pm) (erased (Iota d ids) io)
    (erased (Respects g p gp) rg) (erased (SumAt gp ids s) k) -> (erased (SumAt g ids s) r))
  (let-match erased pm (HMkPerm _ _ _ ids2 io2 lp qp pq))
  (let-match erased (iota-fn d ids ids2 io io2) (Refl _ _))
  (let ((erased rid)) (respects-id-right d ids p io lp))
  (let ((erased uid)) (respects-under p ids p d rid lp))
  (perm-sum g p ids s (sumat-map g p gp ids p s rg rid k) (resp-distinct q p ids qp (iota-distinct d ids io)) (iota-distinct d ids io)
    (under-incl d p ids (perm-under d p q pm) io) (perm-cover d p q ids ids pm uid)))

; s is the sum of g at the k darts x, f x, ..., f^(k-1) x.
(def-adts $ (FSum : ((List (Nat)) f g) ((Nat) x k s) -> Type)
  enum
  (many FSZ : (erased (List (Nat)) f g) (erased (Nat) x) -> (FSum f g x (Zero) (Zero)))
  (many FSS : (erased (List (Nat)) f g) (erased (Nat) x y k c s1 s) (erased (Nth (Nat) g x c) p) (erased (Nth (Nat) f x y) py)
      (erased (FSum f g y k s1) rest) (erased (Add c s1 s) a) -> (FSum f g x (Succ k) s)))

; s is the sum, over the roots rs, of g along the face of each root (ks the arities).
(def-adts $ (RSum : ((List (Nat)) f g ks rs) ((Nat) s) -> Type)
  enum
  (many RSNil : (erased (List (Nat)) f g ks) -> (RSum f g ks (Nil (Nat)) (Zero)))
  (many RSCons : (erased (List (Nat)) f g ks rs) (erased (Nat) r a t s1 s) (erased (Nth (Nat) ks r a) pa) (erased (FSum f g r a t) ft)
      (erased (RSum f g ks rs s1) rest) (erased (Add t s1 s) ad) -> (RSum f g ks (Cons (Nat) r rs) s)))

(def-fns _ $ (erased path-fsum : (erased (List (Nat)) f g s0 xs) (erased (Nat) x y s) (subterm erased (Path f s0 x y xs) w) (erased (SumAt g xs s) k)
    -> (erased (Nat) m) (erased (Length (Nat) xs m) l) (erased (FSum f g x m s) r))
  (let-match erased w (PathStep _ _ xs1 _ z _ px out w1) ((PathHere _ _ _) (let-match erased k (SANil _)) (values (Zero) (LengthNil _) (FSZ f g x))))
  (let-match erased k (SACons _ _ _ c s1 _ pc k1 a))
  (let ((erased m) (erased l) (erased r)) (path-fsum f g s0 xs1 z y s1 w1 k1))
  (values (Succ m) (LengthCons _ x xs1 m l) (FSS f g x z m c s1 s pc px r a)))

(def-fns _ $ (erased fsum-fn : (erased (List (Nat)) f g) (erased (Nat) x k s t) (subterm erased (FSum f g x k s) p) (erased (FSum f g x k t) q)
    -> (erased (Eq (Nat) s t) e))
  (let-match erased p (FSS _ _ _ y k1 c s1 _ pc py p1 a) ((FSZ _ _ _) (let-match erased q (FSZ _ _ _)) (Refl _ s)))
  (let-match erased q (FSS _ _ _ y2 _ c2 t1 _ pc2 py2 q1 a2))
  (let-match erased (nth-fn _ f x y y2 py py2) (Refl _ _))
  (let-match erased (nth-fn _ g x c c2 pc pc2) (Refl _ _))
  (let-match erased (fsum-fn f g y k1 s1 t1 p1 q1) (Refl _ _))
  (add-fn c s1 s t a a2))

(def-fns _ $ (erased sumat-exists : (erased (Nat) d) (erased (List (Nat)) g xs) (erased (Length (Nat) g d) lg) (subterm erased (Under xs d) u)
    -> (erased (Nat) s) (erased (SumAt g xs s) k))
  (let-match erased u (UnderCons xs1 x _ lx u1) ((UnderNil _) (values (Zero) (SANil g))))
  (let ((erased c) (erased pc)) (nth-exists _ g d x lg lx))
  (let ((erased s1) (erased k1)) (sumat-exists d g xs1 lg u1))
  (let ((erased s) (erased a)) (add c s1))
  (values s (SACons g xs1 x c s1 s pc k1 a)))

; Along a face, a list of ones sums to the number of darts.
(def-fns _ $ (erased fsum-ones : (erased (Nat) d x k s) (erased (List (Nat)) f os) (erased (Repeat (Nat) d (Succ (Zero)) os) ro)
    (subterm erased (FSum f os x k s) p) -> (erased (Eq (Nat) k s) e))
  (let-match erased p (FSS _ _ _ y k1 c s1 _ pc py p1 a) ((FSZ _ _ _) (Refl _ (Zero))))
  (let-match erased (nth-fn _ os x c _ pc (repeat-nth _ d x _ os ro (nth-lt-length _ os x d c pc (repeat-length _ d _ os ro)))) (Refl _ _))
  (let-match erased (fsum-ones d y k1 s1 f os ro p1) (Refl _ _))
  (let-match erased a (AddSucc _ _ _ a1))
  (let-match erased a1 (AddZero _))
  (Refl _ k))

(def-fns _ $ (erased sumat-ones : (erased (Nat) d s) (erased (List (Nat)) os xs) (erased (Repeat (Nat) d (Succ (Zero)) os) ro)
    (subterm erased (SumAt os xs s) k) -> (erased (Length (Nat) xs s) l))
  (let-match erased k (SACons _ xs1 x c s1 _ pc k1 a) ((SANil _) (LengthNil _)))
  (let-match erased (nth-fn _ os x c _ pc (repeat-nth _ d x _ os ro (nth-lt-length _ os x d c pc (repeat-length _ d _ os ro)))) (Refl _ _))
  (let-match erased a (AddSucc _ _ _ a1))
  (let-match erased a1 (AddZero _))
  (LengthCons _ x xs1 s1 (sumat-ones d s1 os xs1 ro k1)))

(def-fns _ $ (erased under-app : (erased (Nat) d) (erased (List (Nat)) a b c) (subterm erased (AppN a b c) ap) (erased (Under a d) ua) (erased (Under b d) ub)
    -> (erased (Under c d) r))
  (let-match erased ap (AppCons a1 _ c1 x ap1) ((AppNil _) ub))
  (let-match erased ua (UnderCons _ _ _ lx ua1))
  (UnderCons c1 x d lx (under-app d a1 b c1 ap1 ua1 ub)))

(def-fns _ $ (erased ocat : (erased (Nat) d) (erased (List (Nat)) f ks rs) (erased (OrderList d f ks) ol) (subterm erased (Under rs d) u)
    -> (erased (List (Nat)) ls) (erased (OrbCat f rs ls) oc))
  (let-match erased u (UnderCons rs1 r _ lr u1) ((UnderNil _) (values (Nil _) (OCNil f))))
  (let ((erased a) (erased pa) (erased o)) (arity-at d r f ks ol lr))
  (let-match erased o (MkOrder _ xs _ y k py w l))
  (let ((erased ls1) (erased oc1)) (ocat d f ks rs1 ol u1))
  (let ((erased ls2) (erased ap)) (app-exists (Cons _ r xs) ls1))
  (values ls2 (OCCons f rs1 xs ls1 ls2 r y py w ap oc1)))

(def-fns _ $ (erased ocat-under : (erased (Nat) d) (erased (List (Nat)) f fi rs ls) (erased (HPerm d f fi) pf) (erased (Under rs d) u)
    (subterm erased (OrbCat f rs ls) oc) -> (erased (Under ls d) r))
  (let-match erased oc (OCCons _ rs1 xs ls1 _ r y py w ap oc1) ((OCNil _) (UnderNil d)))
  (let-match erased u (UnderCons _ _ _ lr u1))
  (let ((erased y2) (erased py2) (erased ly)) (perm-nth d r f fi pf lr))
  (let-match erased (nth-fn _ f r y y2 py py2) (Refl _ _))
  (let ((erased ux) (erased _)) (path-under d y r f fi _ xs pf w ly))
  (under-app d (Cons _ r xs) ls1 ls ap (UnderCons xs r d lr ux) (ocat-under d f fi rs1 ls1 pf u1 oc1)))

(def-fns _ $ (erased roots-cover : (erased (Nat) d) (erased (List (Nat)) p q) (erased (List (Bond)) g) (erased (List (Nat)) lab rs ls ids m)
    (erased (HPerm d p q) pm) (erased (Iota d ids) io) (erased (Length (Nat) lab d) ll) (erased (Graph d p g) gr) (erased (Rooted g rs ids lab) ro)
    (erased (OrbCat p rs ls) oc) (subterm erased (Incl m ids) sm) -> (erased (Incl m ls) r))
  (let-match erased sm (InclCons x m1 _ ix sm1) ((InclNil _) (InclNil ls)))
  (let ((erased j) (erased pj)) (in-nth x ids ix))
  (let-match erased (iota-at d j x ids io pj) (Refl _ _))
  (let ((erased lx)) (nth-lt-length _ ids x d x pj (iota-length d ids io)))
  (let ((erased rt) (erased prt)) (nth-exists _ lab d x ll lx))
  (let ((erased irt) (erased cn)) (classes-root g d ids lab rs x rt io ro prt lx))
  (InclCons x m1 ls (orbcat-cover d x rt p q g rs ls pm gr oc irt cn) (roots-cover d p q g lab rs ls ids m1 pm io ll gr ro oc sm1)))

; The roots rs of the faces, and the darts ls listed face by face from them: every dart once.
(def-fns _ $ (erased face-roots : (erased (Nat) d kf) (erased (List (Nat)) f fi ks ids) (erased (HPerm d f fi) pf) (erased (Orbits d f kf) ob)
    (erased (OrderList d f ks) ol) (erased (Iota d ids) io)
    -> (erased (List (Nat)) rs ls) (erased (Length (Nat) rs kf) lr) (erased (Under rs d) ur) (erased (OrbCat f rs ls) oc) (erased (Distinct ls) dl)
    (erased (Incl ls ids) i1) (erased (Incl ids ls) i2))
  (let-match erased ob (MkOrbits _ _ _ g gr cs))
  (let-match erased cs (MkClasses _ _ _ ids2 lab rs io2 ll lr dr fix cl ro))
  (let-match erased (iota-fn d ids ids2 io io2) (Refl _ _))
  (let ((erased ur)) (respects-under lab rs rs d fix ll))
  (let ((erased ls) (erased oc)) (ocat d f ks rs ol ur))
  (values rs ls lr ur oc (orbcat-distinct d f g lab rs rs ls gr cl fix (sub-refl rs) dr oc)
    (under-incl d ls ids (ocat-under d f fi rs ls pf ur oc) io)
    (roots-cover d f fi g lab rs ls ids ids pf io ll gr ro oc (incl-refl ids))))

(def-fns _ $ (erased orbcat-rsum : (erased (Nat) d s) (erased (List (Nat)) f g ks rs ls) (erased (OrderList d f ks) ol) (erased (Under rs d) u)
    (subterm erased (OrbCat f rs ls) oc) (erased (SumAt g ls s) k) -> (erased (RSum f g ks rs s) r))
  (let-match erased oc (OCCons _ rs1 xs ls1 _ r y py w ap oc1) ((OCNil _) (let-match erased k (SANil _)) (RSNil f g ks)))
  (let-match erased u (UnderCons _ _ _ lr u1))
  (let ((erased s1) (erased s2) (erased k1) (erased k2) (erased e)) (sumat-app g (Cons _ r xs) ls1 ls s ap k))
  (let-match erased k1 (SACons _ _ _ c t _ pc kt at))
  (let ((erased m) (erased l) (erased ft)) (path-fsum f g _ xs y r t w kt))
  (let ((erased a) (erased pa) (erased o)) (arity-at d r f ks ol lr))
  (let-match erased (order-fn f r a (Succ m) o (MkOrder f xs r y m py w l)) (Refl _ _))
  (RSCons f g ks rs1 r a s1 s2 s pa (FSS f g r y m c t s1 pc py ft at) (orbcat-rsum d s2 f g ks rs1 ls1 ol u1 oc1 k2) e))

; Summing g face by face gives the sum of g over all darts.
(def-fns _ $ (erased faces-sum : (erased (Nat) d s) (erased (List (Nat)) f g ks rs ls ids) (erased (OrderList d f ks) ol) (erased (Iota d ids) io)
    (erased (Under rs d) ur) (erased (OrbCat f rs ls) oc) (erased (Distinct ls) dl) (erased (Incl ls ids) i1) (erased (Incl ids ls) i2)
    (erased (SumAt g ids s) k) -> (erased (RSum f g ks rs s) r))
  (orbcat-rsum d s f g ks rs ls ol ur oc (perm-sum g ids ls s k (iota-distinct d ids io) dl i2 i1)))
