; Lemmas of geometry.v about lists of darts on distinct faces. Load after patch.sl.

(def-fns _ $ (erased in-label : (erased (List (Nat)) lab xs ls) (erased (Nat) x) (subterm erased (Respects lab xs ls) rp) (erased (In x xs) ix)
    -> (erased (Nat) l) (erased (Nth (Nat) lab x l) r))
  (let-match erased rp (RespCons _ xs1 ls1 j l pj rp1) (absurd (RespNil _) ix))
  (match erased ix _ ((InHere _ _) (values l pj)) ((InThere _ _ _ ix1) (in-label lab xs1 ls1 x rp1 ix1))))

; Two darts of a simple list on one face are one dart (simple_cface, and so scycle_cface).
(def-fns _ $ (erased simple-cface : (erased (List (Nat)) f p) (erased (Nat) a b) (erased (Simple f p) s) (erased (In a p) ia) (erased (In b p) ib)
    (erased (SomePath f (Nil (Nat)) a b) w) -> (erased (Eq (Nat) a b) e))
  (let-match erased s (MkSimple _ _ lab ls rf rp dl))
  (let-match erased w (MkSomePath _ _ xs _ _ pth))
  (let ((erased l) (erased pa)) (in-label lab p ls a rp ia))
  (simple-inj lab p ls a b l rp dl ia ib pa (path-label f lab (Nil _) xs a b l pth rf pa)))

(def-fns _ $ (erased path-reset : (erased (List (Nat)) p s s2 xs) (erased (Nat) a b) (subterm erased (Path p s a b xs) w) (erased (Disj xs s2) dj)
    -> (erased (Path p s2 a b xs) r))
  (let-match erased w (PathStep _ _ xs1 _ z _ pz _ w1) ((PathHere _ _ _) (PathHere p s2 a)))
  (let-match erased dj (DisjCons _ _ _ out dj1))
  (PathStep p s2 xs1 a z b pz out (path-reset p s s2 xs1 z b w1 dj1)))

; Orders are constant along cycles.
(def-fns _ $ (erased order-step : (erased (List (Nat)) p) (erased (Nat) x y k) (erased (Order p x k) o) (erased (Nth (Nat) p x y) py) -> (erased (Order p y k) r))
  (let-match erased o (MkOrder _ xs _ y1 k1 px w l))
  (let-match erased (nth-fn _ p x y y1 py px) (Refl _ _))
  (match erased w _
    ((PathHere _ _ _) o)
    ((PathStep _ _ xs1 _ z _ pz out w1)
      (let-match erased (walk-distinct p (Nil (Nat)) xs y x w) (DistCons _ _ oy _))
      (let-match erased out (NotInCons _ _ _ nyx _))
      (let-match erased l (LengthCons _ _ _ j l1))
      (let ((erased xs2) (erased sn) (erased w2))
        (path-snoc p (Cons (Nat) y (Nil (Nat))) xs1 z x y (path-reset p _ _ xs1 z x w1 (notin-disj1 y xs1 oy)) px
          (NotInCons x y (Nil (Nat)) (apart-sym y x nyx) (NotInNil x))))
      (MkOrder p xs2 y z (Succ j) pz w2 (snoc-length _ xs1 xs2 x j sn l1)))))

(def-fns _ $ (erased order-path : (erased (List (Nat)) p s xs) (erased (Nat) a b k) (subterm erased (Path p s a b xs) w) (erased (Order p a k) o) -> (erased (Order p b k) r))
  (let-match erased w (PathStep _ _ xs1 _ z _ pz _ w1) ((PathHere _ _ _) o))
  (order-path p s xs1 z b k w1 (order-step p a z k o pz)))

(def-fns _ $ (erased fpath-path : (erased (List (Nat)) n s q) (erased (Nat) z y w) (subterm erased (FPath n z q y) fp) (erased (Nth (Nat) n y w) py)
    (erased (Disj (Cons (Nat) z q) s) dj) -> (erased (Path n s z w (Cons (Nat) z q)) r))
  (let-match erased dj (DisjCons _ _ _ oz dj1))
  (match erased fp _
    ((FPNil _ _) (PathStep n s (Nil (Nat)) z w w py oz (PathHere n s w)))
    ((FPCons _ q1 _ z2 _ pz fp1) (PathStep n s q z z2 w pz oz (fpath-path n s q1 z2 y w fp1 py dj1)))))

(def-fns _ $ (erased fpath-reach : (erased (List (Nat)) n q) (erased (Nat) a b r) (subterm erased (FPath n a q b) fp) (erased (In r (Cons (Nat) a q)) ir)
    -> (erased (List (Nat)) xs) (erased (Path n (Nil (Nat)) a r xs) w))
  (let-match erased ir (InThere _ _ _ ir1) ((InHere _ _) (values (Nil _) (PathHere n _ a))))
  (let-match erased fp (FPCons _ q1 _ z _ pz fp1) (absurd (FPNil _ _) ir1))
  (let ((erased xs) (erased w)) (fpath-reach n q1 z b r fp1 ir1))
  (values (Cons _ a xs) (PathStep n _ xs a z r pz (NotInNil a) w)))

; A duplicate-free node cycle of m darts is the orbit of its first dart.
(def-fns _ $ (erased ring-order : (erased (List (Nat)) n q) (erased (Nat) x0 m) (erased (NCyc n (Cons (Nat) x0 q)) nc) (erased (Distinct (Cons (Nat) x0 q)) dr)
    (erased (Length (Nat) q m) lq) -> (erased (Order n x0 (Succ m)) r))
  (let-match erased nc (NCCons _ _ _ y fp back))
  (let-match erased dr (DistCons _ _ ox _))
  (match erased fp _
    ((FPNil _ _) (let-match erased lq (LengthNil _)) (MkOrder n (Nil (Nat)) x0 x0 (Zero) back (PathHere n _ x0) (LengthNil _)))
    ((FPCons _ q1 _ z _ pz fp1) (MkOrder n q x0 z m pz (fpath-path n (Cons (Nat) x0 (Nil (Nat))) q1 z y x0 fp1 back (notin-disj1 x0 q ox)) lq))))

(def-fns _ $ (erased ring-conn : (erased (Nat) d x y) (erased (List (Nat)) n R) (erased (List (Bond)) g) (erased (Graph d n g) gr) (erased (NCyc n R) nc)
    (erased (In x R) ix) (erased (In y R) iy) -> (erased (Conn g x y) r))
  (let-match erased nc (NCCons _ q a b fp _) (absurd (NCNil _) ix))
  (let ((erased xs) (erased wx)) (fpath-reach n q a b x fp ix))
  (let ((erased ys) (erased wy)) (fpath-reach n q a b y fp iy))
  (conn-cat g x a y (conn-sym g a x (path-graph-conn d a x n _ xs g wx gr)) (path-graph-conn d a y n _ ys g wy gr)))

(def-fns _ $ (erased path-in-ring : (erased (List (Nat)) n R s xs) (erased (Nat) a b) (erased (NCyc n R) nc) (erased (In a R) ia) (subterm erased (Path n s a b xs) w)
    -> (erased (In b R) r))
  (let-match erased w (PathStep _ _ xs1 _ z _ pz _ w1) ((PathHere _ _ _) ia))
  (path-in-ring n R s xs1 z b nc (ncyc-next n R a z nc ia pz) w1))

; s sums the node orders at the roots rs: m at r0, the root of the ring's class, when r0 is in rs, and 3 at the others.
(def-adts $ (QSum : ((Nat) r0 m) ((List (Nat)) rs) ((Nat) s) -> Type)
  enum
  (many QSOut : (erased (Nat) r0 m k s) (erased (List (Nat)) rs) (erased (NotIn r0 rs) o) (erased (Length (Nat) rs k) l) (erased (Mul k 3 s) ms)
      -> (QSum r0 m rs s))
  (many QSIn : (erased (Nat) r0 m k s t) (erased (List (Nat)) rs) (erased (In r0 rs) i) (erased (Length (Nat) rs (Succ k)) l) (erased (Mul k 3 t) mt)
      (erased (Add m t s) a) -> (QSum r0 m rs s)))

(def-fns _ $ (erased qroots : (erased (Nat) d m x0 r0) (erased (List (Nat)) n ni R ids lab rs) (erased (List (Bond)) g) (erased (HPerm d n ni) pm)
    (erased (Graph d n g) gr) (erased (NCyc n R) nc) (erased (In x0 R) i0) (erased (Order n x0 m) o0) (erased (OrdersOff n 3 R ids) oo) (erased (Iota d ids) io)
    (erased (Nth (Nat) lab x0 r0) p0) (erased (In r0 R) ir0) (erased (Const lab g) cl) (erased (Respects lab rs rs) fix)
    (subterm erased (Distinct rs) dr) (erased (Under rs d) u)
    -> (erased (List (Nat)) os) (erased (Nat) s) (erased (Orders n rs os) ob) (erased (QSum r0 m rs s) q) (erased (SumN os s) sm))
  (let-match erased dr (DistCons r rs1 out dr1)
    ((DistNil) (values (Nil _) (Zero) (OrdNil n) (QSOut r0 m (Zero) (Zero) (Nil _) (NotInNil r0) (LengthNil _) (MulZero 3)) (SumNil))))
  (let-match erased fix (RespCons _ _ _ _ _ prr fix1))
  (let-match erased u (UnderCons _ _ _ lr u1))
  (let ((erased os1) (erased s1) (erased ob1) (erased q1) (erased sm1)) (qroots d m x0 r0 n ni R ids lab rs1 g pm gr nc i0 o0 oo io p0 ir0 cl fix1 dr1 u1))
  (match erased (in-dec r R) _
    ((OrL _ _ ir)
      (let ((erased cn)) (ring-conn d x0 r n R g gr nc i0 ir))
      (let-match erased (nth-fn _ lab r r0 r (conn-const lab g x0 r r0 cn cl p0) prr) (Refl _ _))
      (let ((erased xs) (erased w)) (conn-path d x0 r n ni g pm gr cn))
      (let ((erased s) (erased a)) (add-ex m s1))
      (let-match erased q1 (QSOut _ _ k1 _ _ _ l1 ms) (absurd (QSIn _ _ _ _ _ _ i _ _ _) (apart-irrefl r0 (notin-in r0 r0 rs1 out i))))
      (values (Cons _ m os1) s (OrdCons n rs1 os1 r m (order-path n _ xs x0 r m w o0) ob1)
        (QSIn r0 m k1 s s1 _ (InHere r0 rs1) (LengthCons _ r rs1 k1 l1) ms a) (SumCons m s1 s os1 sm1 a)))
    ((OrR _ _ orr)
      (let ((erased ne)) (apart-sym r r0 (notin-in r r0 R orr ir0)))
      (let ((erased s) (erased a)) (add-ex 3 s1))
      (let ((erased a2)) (add-comm 3 s1 s a))
      (values (Cons _ 3 os1) s (OrdCons n rs1 os1 r 3 (oo-at n R ids 3 r oo (iota-in d r ids io lr) orr) ob1)
        (match erased q1 _
          ((QSOut _ _ k1 _ _ o1 l1 ms) (QSOut r0 m (Succ k1) s _ (NotInCons r0 r rs1 ne o1) (LengthCons _ r rs1 k1 l1) (MulSucc k1 3 s1 s ms a2)))
          ((QSIn _ _ k1 _ t1 _ i1 l1 mt at)
            (let ((erased t) (erased a3)) (add-ex t1 3))
            (let ((erased a4) (erased a5) (erased a6)) (add-assoc m t1 3 s1 s at a2))
            (let-match erased (add-fn t1 3 a4 t a5 a3) (Refl _ _))
            (QSIn r0 m (Succ k1) s t _ (InThere r0 r rs1 i1) (LengthCons _ r rs1 (Succ k1) l1) (MulSucc k1 3 t1 t mt a3) a6)))
        (SumCons 3 s1 s os1 sm1 a)))))

; A duplicate-free node cycle R of m darts off which every dart has node order 3: there are 1 + i node orbits and d = m + 3i darts.
(def-fns _ $ (erased ring-count : (erased (Nat) d kn m x0) (erased (List (Nat)) e n f q ids) (erased (Hypermap d e n f) h) (erased (NCyc n (Cons (Nat) x0 q)) nc)
    (erased (Distinct (Cons (Nat) x0 q)) dq) (erased (Length (Nat) q m) lq) (erased (OrdersOff n 3 (Cons (Nat) x0 q) ids) oo) (erased (Iota d ids) io0)
    (erased (Orbits d n kn) ob) -> (erased (Nat) i t) (erased (Eq (Nat) kn (Succ i)) ek) (erased (Mul i 3 t) mt) (erased (Add (Succ m) t d) ad))
  (let ((erased R)) (Cons (Nat) x0 q))
  (let ((erased nf) (erased ni) (erased fi) (erased _) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (let-match erased ob (MkOrbits _ _ _ g gr cs))
  (let-match erased cs (MkClasses _ _ _ ids1 lab rs io ll lr dr fix cl ro))
  (let-match erased (iota-fn d ids ids1 io0 io) (Refl _ _))
  (let-match erased nc (NCCons _ _ _ y fp back))
  (let ((erased i0)) (InHere x0 q))
  (let ((erased lx0)) (perm-val d y x0 n ni pn back))
  (let ((erased r0) (erased p0)) (nth-exists _ lab d x0 ll lx0))
  (let ((erased ir0s) (erased c0)) (classes-root g d ids lab rs x0 r0 io ro p0 lx0))
  (let ((erased xs) (erased w)) (conn-path d x0 r0 n ni g pn gr (conn-sym g r0 x0 c0)))
  (let ((erased ir0)) (path-in-ring n R _ xs x0 r0 nc i0 w))
  (let ((erased os) (erased s) (erased ob1) (erased qs) (erased sm))
    (qroots d (Succ m) x0 r0 n ni R ids lab rs g pn gr nc i0 (ring-order n q x0 m nc dq lq) oo io p0 ir0 cl fix dr
      (respects-under lab rs rs d fix ll)))
  (let-match erased (sumn-fn os s d sm (orbit-sum d n ni ids lab rs os g pn gr io ll dr fix cl ro ob1)) (Refl _ _))
  (let-match erased qs (QSIn _ _ k _ t _ _ lk mt ad) (absurd (QSOut _ _ _ _ _ o _ _) (apart-irrefl r0 (notin-in r0 r0 rs o ir0s))))
  (let-match erased (length-fn _ rs kn (Succ k) lr lk) (Refl _ _))
  (values k t (Refl _ kn) mt ad))
