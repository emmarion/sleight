; Permutations of the darts 0..d-1 as lists, their graphs, and their orbits.

; g bonds the entries of xs and ys at each position.
(def-adts $ (Zip : ((List (Nat)) xs ys) ((List (Bond)) g) -> Type)
  enum
  (many ZipNil : -> (Zip (Nil (Nat)) (Nil (Nat)) (Nil (Bond))))
  (many ZipCons : (erased (List (Nat)) xs ys) (erased (List (Bond)) g) (erased (Nat) x y) (erased (Zip xs ys g) rest)
      -> (Zip (Cons (Nat) x xs) (Cons (Nat) y ys) (Cons (Bond) (MkBond x y) g))))

; g bonds each dart x below d to the entry of p at x.
(def-adts $ (Graph : ((Nat) d) ((List (Nat)) p) ((List (Bond)) g) -> Type)
  enum
  (many MkGraph : (erased (Nat) d) (erased (List (Nat)) p ids) (erased (List (Bond)) g)
      (erased (Iota d ids) io) (erased (Length (Nat) p d) lp) (erased (Zip ids p g) z) -> (Graph d p g)))

; p is a permutation of the darts 0..d-1, with inverse q.
(def-adts $ (Perm : ((Nat) d) ((List (Nat)) p q) -> Type)
  enum
  (many MkPerm : (erased (Nat) d) (erased (List (Nat)) p q ids) (erased (Iota d ids) io) (erased (Length (Nat) p d) lp)
      (erased (Respects q p ids) qp) (erased (Respects p q ids) pq) -> (Perm d p q)))

; The darts 0..d-1 fall into k orbits of p.
(def-adts $ (Orbits : ((Nat) d) ((List (Nat)) p) ((Nat) k) -> Type)
  enum
  (many MkOrbits : (erased (Nat) d k) (erased (List (Nat)) p) (erased (List (Bond)) g) (erased (Graph d p g) gr) (erased (Classes g d k) cs)
      -> (Orbits d p k)))

; A walk along p from x to y, leaving from the darts xs in turn, none of them in s.
(def-adts $ (Path : ((List (Nat)) p s) ((Nat) x y) ((List (Nat)) xs) -> Type)
  enum
  (many PathHere : (erased (List (Nat)) p s) (erased (Nat) x) -> (Path p s x x (Nil (Nat))))
  (many PathStep : (erased (List (Nat)) p s xs) (erased (Nat) x z y) (erased (Nth (Nat) p x z) px) (erased (NotIn x s) out)
      (erased (Path p s z y xs) rest) -> (Path p s x y (Cons (Nat) x xs))))

(def-fns _ $ (erased zip-adj : (erased (List (Nat)) xs ys) (erased (List (Bond)) g) (erased (Nat) j x y) (subterm erased (Zip xs ys g) z)
    (erased (Nth (Nat) xs j x) px) (erased (Nth (Nat) ys j y) py) -> (erased (Adj g x y) r))
  (let-match erased z (ZipCons xs1 ys1 g1 x0 y0 z1) (absurd (ZipNil) px))
  (let-match erased px (NthThere _ _ _ j1 _ px1) ((NthHere _ _ _) (let-match erased py (NthHere _ _ _)) (AdjFwd g1 x y)))
  (let-match erased py (NthThere _ _ _ _ _ py1))
  (AdjThere g1 (MkBond x0 y0) x y (zip-adj xs1 ys1 g1 j1 x y z1 px1 py1)))

(def-adts $ (At2 : ((List (Nat)) xs ys) ((Nat) x y) -> Type)
  enum
  (many MkAt2 : (erased (List (Nat)) xs ys) (erased (Nat) j x y) (erased (Nth (Nat) xs j x) px) (erased (Nth (Nat) ys j y) py)
      -> (At2 xs ys x y)))

(def-fns _ $ (erased zip-adj-inv : (erased (List (Nat)) xs ys) (erased (List (Bond)) g) (erased (Nat) x y) (subterm erased (Zip xs ys g) z)
    (erased (Adj g x y) a) -> (erased (Or (At2 xs ys x y) (At2 xs ys y x)) r))
  (let-match erased z (ZipCons xs1 ys1 g1 x0 y0 z1) (absurd (ZipNil) a))
  (let-match erased a (AdjThere _ _ _ _ a1)
    ((AdjFwd _ _ _) (OrL _ _ (MkAt2 xs ys (Zero) x y (NthHere _ x xs1) (NthHere _ y ys1))))
    ((AdjBwd _ _ _) (OrR _ _ (MkAt2 xs ys (Zero) y x (NthHere _ y xs1) (NthHere _ x ys1)))))
  (match erased (zip-adj-inv xs1 ys1 g1 x y z1 a1) _
    ((OrL _ _ t) (let-match erased t (MkAt2 _ _ j _ _ px py))
      (OrL _ _ (MkAt2 xs ys (Succ j) x y (NthThere _ x0 xs1 j x px) (NthThere _ y0 ys1 j y py))))
    ((OrR _ _ t) (let-match erased t (MkAt2 _ _ j _ _ px py))
      (OrR _ _ (MkAt2 xs ys (Succ j) y x (NthThere _ x0 xs1 j y px) (NthThere _ y0 ys1 j x py))))))

(def-fns _ $ (erased iota-at : (erased (Nat) d j x) (erased (List (Nat)) ids) (erased (Iota d ids) io) (erased (Nth (Nat) ids j x) p)
    -> (erased (Eq (Nat) j x) e))
  (nth-fn _ ids j j x (iota-nth d j ids io (nth-lt-length _ ids j d x p (iota-length d ids io))) p))

(def-fns _ $ (erased graph-adj : (erased (Nat) d x y) (erased (List (Nat)) p) (erased (List (Bond)) g) (erased (Graph d p g) gr)
    (erased (Nth (Nat) p x y) px) -> (erased (Adj g x y) r))
  (let-match erased gr (MkGraph _ _ ids _ io lp z))
  (zip-adj ids p g x x y z (iota-nth d x ids io (nth-lt-length _ p x d y px lp)) px))

(def-fns _ $ (erased graph-adj-inv : (erased (Nat) d x y) (erased (List (Nat)) p) (erased (List (Bond)) g) (erased (Graph d p g) gr)
    (erased (Adj g x y) a) -> (erased (Or (Nth (Nat) p x y) (Nth (Nat) p y x)) r))
  (let-match erased gr (MkGraph _ _ ids _ io lp z))
  (match erased (zip-adj-inv ids p g x y z a) _
    ((OrL _ _ t) (let-match erased t (MkAt2 _ _ j _ _ px py)) (let-match erased (iota-at d j x ids io px) (Refl _ _)) (OrL _ _ py))
    ((OrR _ _ t) (let-match erased t (MkAt2 _ _ j _ _ px py)) (let-match erased (iota-at d j y ids io px) (Refl _ _)) (OrR _ _ py))))

(def-fns _ $ (erased perm-nth : (erased (Nat) d x) (erased (List (Nat)) p q) (erased (Perm d p q) pm) (erased (Lt x d) lt)
    -> (erased (Nat) y) (erased (Nth (Nat) p x y) px) (erased (Lt y d) ly))
  (let-match erased pm (MkPerm _ _ _ ids io lp qp pq))
  (let ((erased y) (erased px)) (nth-exists _ p d x lp lt))
  (let ((erased lq)) (respects-length-inv p q ids d pq (iota-length d ids io)))
  (values y px (nth-lt-length _ q y d x (respects-nth q p ids x y x qp px (iota-nth d x ids io lt)) lq)))

(def-fns _ $ (erased perm-inj : (erased (Nat) d x u w) (erased (List (Nat)) p q) (erased (Perm d p q) pm)
    (erased (Nth (Nat) p x w) px) (erased (Nth (Nat) p u w) pu) -> (erased (Eq (Nat) x u) e))
  (let-match erased pm (MkPerm _ _ _ ids io lp qp pq))
  (nth-fn _ q w x u (respects-nth q p ids x w x qp px (iota-nth d x ids io (nth-lt-length _ p x d w px lp)))
    (respects-nth q p ids u w u qp pu (iota-nth d u ids io (nth-lt-length _ p u d w pu lp)))))

(def-fns _ $ (erased zip-exists : (erased (List (Nat)) xs ys) (erased (Nat) n) (subterm erased (Length (Nat) xs n) lx) (erased (Length (Nat) ys n) ly)
    -> (erased (List (Bond)) g) (erased (Zip xs ys g) z))
  (let-match erased lx (LengthCons _ x xs1 n1 lx1) ((LengthNil _) (let-match erased ly (LengthNil _)) (values (Nil _) (ZipNil))))
  (let-match erased ly (LengthCons _ y ys1 _ ly1))
  (let ((erased g1) (erased z1)) (zip-exists xs1 ys1 n1 lx1 ly1))
  (values (Cons _ (MkBond x y) g1) (ZipCons xs1 ys1 g1 x y z1)))

(def-fns _ $ (erased perm-graph : (erased (Nat) d) (erased (List (Nat)) p q) (erased (Perm d p q) pm)
    -> (erased (List (Bond)) g) (erased (Graph d p g) gr))
  (let-match erased pm (MkPerm _ _ _ ids io lp qp pq))
  (let ((erased g) (erased z)) (zip-exists ids p d (iota-length d ids io) lp))
  (values g (MkGraph d p ids g io lp z)))

(def-fns _ $ (erased in-dec : (erased (Nat) x) (subterm erased (List (Nat)) s) -> (erased (Or (In x s) (NotIn x s)) r))
  (let-match erased s (Cons _ y s1) ((Nil _) (OrR _ _ (NotInNil x))))
  (let-match erased (nat-eq x y) (Unequal _ _ _ _ ne) ((Equal _ _ _) (OrL _ _ (InHere x s1))))
  (match erased (in-dec x s1) _
    ((OrL _ _ p) (OrL _ _ (InThere x y s1 p)))
    ((OrR _ _ q) (OrR _ _ (NotInCons x y s1 ne q)))))

(def-adts $ (SomePath : ((List (Nat)) p s) ((Nat) x y) -> Type)
  enum
  (many MkSomePath : (erased (List (Nat)) p s xs) (erased (Nat) x y) (erased (Path p s x y xs) w) -> (SomePath p s x y)))

(def-fns _ $ (erased path-start-in : (erased (List (Nat)) p s xs) (erased (Nat) x y) (erased (Path p s x y xs) w) -> (erased (In x (Cons (Nat) y xs)) r))
  (let-match erased w (PathStep _ _ xs1 _ _ _ _ _ _) ((PathHere _ _ _) (InHere x _)))
  (InThere x y _ (InHere x xs1)))

(def-fns _ $ (erased path-avoid : (erased (List (Nat)) p s xs) (erased (Nat) x y u) (subterm erased (Path p s x y xs) w) (erased (In u s) pu)
    -> (erased (NotIn u xs) r))
  (let-match erased w (PathStep _ _ xs1 _ z _ px out w1) ((PathHere _ _ _) (NotInNil u)))
  (NotInCons u x xs1 (apart-sym x u (notin-in x u s out pu)) (path-avoid p s xs1 z y u w1 pu)))

(def-fns _ $ (erased path-forget : (erased (List (Nat)) p s xs) (erased (Nat) x y) (subterm erased (Path p s x y xs) w)
    -> (erased (Path p (Nil (Nat)) x y xs) r))
  (let-match erased w (PathStep _ _ xs1 _ z _ px out w1) ((PathHere _ _ _) (PathHere p _ x)))
  (PathStep p _ xs1 x z y px (NotInNil x) (path-forget p s xs1 z y w1)))

(def-fns _ $ (erased path-cat : (erased (List (Nat)) p s xs ys) (erased (Nat) x y z) (subterm erased (Path p s x y xs) w)
    (erased (Path p s y z ys) v) -> (erased (List (Nat)) zs) (erased (Path p s x z zs) r))
  (let-match erased w (PathStep _ _ xs1 _ u _ px out w1) ((PathHere _ _ _) (values ys v)))
  (let ((erased zs1) (erased r1)) (path-cat p s xs1 ys u y z w1 v))
  (values (Cons _ x zs1) (PathStep p s zs1 x u z px out r1)))

(def-fns _ $ (erased path-snoc : (erased (List (Nat)) p s xs) (erased (Nat) x y z) (subterm erased (Path p s x y xs) w)
    (erased (Nth (Nat) p y z) py) (erased (NotIn y s) out) -> (erased (List (Nat)) xs2) (erased (Snoc (Nat) xs y xs2) sn) (erased (Path p s x z xs2) r))
  (let-match erased w (PathStep _ _ xs1 _ u _ px out1 w1)
    ((PathHere _ _ _) (values (Cons _ y (Nil _)) (SnocNil _ y) (PathStep p s _ y z z py out (PathHere p s z)))))
  (let ((erased xs3) (erased sn1) (erased r1)) (path-snoc p s xs1 u y z w1 py out))
  (values (Cons _ x xs3) (SnocCons _ x y xs1 xs3 sn1) (PathStep p s xs3 x u z px out1 r1)))

(def-fns _ $ (erased in-skip : (erased (Nat) w y x) (erased (List (Nat)) t) (erased (In w (Cons (Nat) y t)) p)
    -> (erased (In w (Cons (Nat) y (Cons (Nat) x t))) r))
  (let-match erased p (InThere _ _ _ p1) ((InHere _ _) (InHere w _)))
  (InThere w y _ (InThere w x t p1)))

(def-fns _ $ (erased in-drop : (erased (Nat) u y x) (erased (List (Nat)) t) (erased (In u (Cons (Nat) y (Cons (Nat) x t))) p)
    (erased (Apart (Nat) Lt u x) ne) -> (erased (In u (Cons (Nat) y t)) r))
  (let-match erased p (InThere _ _ _ p1) ((InHere _ _) (InHere u t)))
  (let-match erased p1 (InThere _ _ _ p2) (absurd (InHere _ _) (apart-irrefl u ne)))
  (InThere u y t p2))

(def-fns _ $ (erased in-tail : (erased (Nat) u y) (erased (List (Nat)) t) (erased (In u (Cons (Nat) y t)) p)
    (erased (Apart (Nat) Lt u y) ne) -> (erased (In u t) r))
  (let-match erased p (InThere _ _ _ p1) (absurd (InHere _ _) (apart-irrefl u ne)))
  p1)

; The step out of a dart left by the walk lands on the walk.
(def-fns _ $ (erased path-next : (erased (List (Nat)) p s xs) (erased (Nat) x y u w) (subterm erased (Path p s x y xs) pa)
    (erased (In u xs) pu) (erased (Nth (Nat) p u w) pw) -> (erased (In w (Cons (Nat) y xs)) r))
  (let-match erased pa (PathStep _ _ xs1 _ z _ px out pa1) (absurd (PathHere _ _ _) pu))
  (let-match erased pu (InThere _ _ _ pu1)
    ((InHere _ _)
      (let-match erased (nth-fn _ p x z w px pw) (Refl _ _))
      (in-skip z y x xs1 (path-start-in p s xs1 z y pa1))))
  (in-skip w y x xs1 (path-next p s xs1 z y u w pa1 pu1 pw)))

; Every dart the walk reaches after its start is reached from a dart it leaves.
(def-fns _ $ (erased path-prev : (erased (List (Nat)) p s xs) (erased (Nat) x y u) (subterm erased (Path p s x y xs) pa)
    (erased (In u (Cons (Nat) y xs)) pu) (erased (Apart (Nat) Lt u x) ne) -> (erased (Nat) v) (erased (In v xs) pv) (erased (Nth (Nat) p v u) pn))
  (let-match erased pa (PathStep _ _ xs1 _ z _ px out pa1)
    (absurd (PathHere _ _ _) (let-match erased pu (InHere _ _) (absurd (InThere _ _ _ pu1) pu1)) (apart-irrefl u ne)))
  (let ((erased pu2)) (in-drop u y x xs1 pu ne))
  (let-match erased (nat-eq u z) (Unequal _ _ _ _ nz) ((Equal _ _ _) (values x (InHere x xs1) px)))
  (let ((erased v) (erased pv) (erased pn)) (path-prev p s xs1 z y u pa1 pu2 nz))
  (values v (InThere v x xs1 pv) pn))

(def-fns _ $ (erased notin-snoc-cons : (erased (Nat) a w) (erased (List (Nat)) ps ps2) (subterm erased (Snoc (Nat) ps w ps2) sn)
    (erased (NotIn a (Cons (Nat) w ps)) out) -> (erased (NotIn a ps2) r))
  (let-match erased sn (SnocCons _ x _ ps1 ps3 sn1) ((SnocNil _ _) out))
  (let-match erased out (NotInCons _ _ _ nw out1))
  (let-match erased out1 (NotInCons _ _ _ nx out2))
  (NotInCons a x ps3 nx (notin-snoc-cons a w ps1 ps3 sn1 (NotInCons a w ps1 nw out2))))

(def-fns _ $ (erased distinct-snoc-cons : (erased (Nat) w) (erased (List (Nat)) ps ps2) (subterm erased (Snoc (Nat) ps w ps2) sn)
    (erased (Distinct (Cons (Nat) w ps)) dw) -> (erased (Distinct ps2) r))
  (let-match erased sn (SnocCons _ x _ ps1 ps3 sn1) ((SnocNil _ _) dw))
  (let-match erased dw (DistCons _ _ out dx))
  (let-match erased out (NotInCons _ _ _ nwx out1))
  (let-match erased dx (DistCons _ _ outx d1))
  (DistCons x ps3 (notin-snoc-cons x w ps1 ps3 sn1 (NotInCons x w ps1 (apart-sym w x nwx) outx))
    (distinct-snoc-cons w ps1 ps3 sn1 (DistCons w ps1 out1 d1))))

(def-fns _ $ (erased nth-in : (erased (List (Nat)) xs) (erased (Nat) i x) (subterm erased (Nth (Nat) xs i x) p) -> (erased (In x xs) r))
  (let-match erased p (NthThere _ y rest i1 _ p1) ((NthHere _ _ rest) (InHere x rest)))
  (InThere x y rest (nth-in rest i1 x p1)))

(def-fns _ $ (erased iota-in : (erased (Nat) d x) (erased (List (Nat)) ids) (erased (Iota d ids) io) (erased (Lt x d) lt) -> (erased (In x ids) r))
  (nth-in ids x x (iota-nth d x ids io lt)))

(def-fns _ $ (erased sub-snoc-cons : (erased (Nat) w) (erased (List (Nat)) ps ps2 s) (subterm erased (Snoc (Nat) ps w ps2) sn)
    (erased (Sub (Cons (Nat) w ps) s) sb) -> (erased (Sub ps2 s) r))
  (let-match erased sn (SnocCons _ x _ ps1 ps3 sn1) ((SnocNil _ _) sb))
  (let-match erased sb (SubCons _ _ _ pw sb1))
  (let-match erased sb1 (SubCons _ _ _ px sb2))
  (SubCons x ps3 s px (sub-snoc-cons w ps1 ps3 s sn1 (SubCons w ps1 s pw sb2))))

(def-fns _ $ (erased add-succ-left : (erased (Nat) a b c) (erased (Add a (Succ b) c) p) -> (erased (Add (Succ a) b c) q))
  (let ((erased c1) (erased e) (erased q1)) (add-succ-right-inv a b c p))
  (let-match erased e (Refl _ _))
  (AddSucc a b c1 q1))

(def-fns _ $ (erased lt-pos : (erased (Nat) z d) (erased (Lt z d) l) -> (erased (Nat) d1) (erased (Eq (Nat) d (Succ d1)) e))
  (match erased l _ ((LtZ b) (values b (Refl _ d))) ((LtS _ b _) (values b (Refl _ d)))))

; A walk that revisits a dart before reaching z, the dart before its start, is impossible.
(def-fns _ $ (erased absurd cycle-stuck : (erased (Nat) d z y w w2) (erased (List (Nat)) p q ps) (erased (Perm d p q) pm)
    (erased (Nth (Nat) p z y) pz) (erased (Path p (Nil (Nat)) y w ps) pa) (erased (Distinct (Cons (Nat) w ps)) dw)
    (erased (Apart (Nat) Lt w z) nwz) (erased (Nth (Nat) p w w2) pw) (erased (In w2 (Cons (Nat) w ps)) back) -> (erased (False) f))
  (let-match erased dw (DistCons _ _ out _))
  (let-match erased (nat-eq w2 y) (Unequal _ _ _ _ ne)
    (absurd (Equal _ _ _) (let-match erased (perm-inj d w z y p q pm pw pz) (Refl _ _)) (apart-irrefl w nwz)))
  (let ((erased v) (erased pv) (erased pn)) (path-prev p (Nil (Nat)) ps y w w2 pa back ne))
  (let-match erased (perm-inj d v w w2 p q pm pn pw) (Refl _ _))
  (apart-irrefl v (notin-in v v ps out pv)))

(def-fns _ $ (erased absurd cycle-full : (erased (Nat) d m w w2) (erased (List (Nat)) ids ps) (erased (Iota d ids) io)
    (erased (Distinct (Cons (Nat) w ps)) dw) (erased (Sub (Cons (Nat) w ps) ids) sb) (erased (Length (Nat) (Cons (Nat) w ps) m) lm)
    (erased (Add m (Zero) d) a) (erased (NotIn w2 (Cons (Nat) w ps)) out) (erased (Lt w2 d) l2) -> (erased (False) f))
  (let-match erased (add-fn m (Zero) m d (add-zero-right m) a) (Refl _ _))
  (let ((erased le)) (pigeonhole (Cons _ w2 (Cons _ w ps)) ids (Succ m) m (DistCons w2 _ out dw)
    (SubCons w2 _ ids (iota-in m w2 ids io l2) sb) (LengthCons _ w2 _ m lm) (iota-length m ids io)))
  (lt-irrefl (Succ m) le))

(def-fns _ $ (erased cycle-go : (erased (Nat) d m z y w) (erased (List (Nat)) p q ids ps) (erased (Perm d p q) pm) (erased (Iota d ids) io)
    (erased (Nth (Nat) p z y) pz) (erased (Path p (Nil (Nat)) y w ps) pa) (erased (Distinct (Cons (Nat) w ps)) dw)
    (erased (Sub (Cons (Nat) w ps) ids) sb) (erased (Lt w d) lw) (erased (Length (Nat) (Cons (Nat) w ps) m) lm) (subterm erased (Nat) f0)
    (erased (Add m f0 d) a) -> (erased (List (Nat)) xs) (erased (Path p (Nil (Nat)) y z xs) r))
  (let-match erased (nat-eq w z) (Unequal _ _ _ _ nwz) ((Equal _ _ _) (values ps pa)))
  (let ((erased w2) (erased pw) (erased l2)) (perm-nth d w p q pm lw))
  (let-match erased (in-dec w2 (Cons _ w ps)) (OrR _ _ out)
    (absurd (OrL _ _ back) (cycle-stuck d z y w w2 p q ps pm pz pa dw nwz pw back)))
  (let-match erased f0 (Succ f1) (absurd (Zero) (cycle-full d m w w2 ids ps io dw sb lm a out l2)))
  (let ((erased ps2) (erased sn) (erased pa2)) (path-snoc p (Nil (Nat)) ps y w w2 pa pw (NotInNil w)))
  (let ((erased ds2)) (distinct-snoc-cons w ps ps2 sn dw))
  (let-match erased lm (LengthCons _ _ _ m1 lm1))
  (let ((erased l3)) (snoc-length _ ps ps2 w m1 sn lm1))
  (cycle-go d (Succ m) z y w2 p q ids ps2 pm io pz pa2 (DistCons w2 ps2 (notin-snoc-cons w2 w ps ps2 sn out) ds2)
    (SubCons w2 ps2 ids (iota-in d w2 ids io l2) (sub-snoc-cons w ps ps2 ids sn sb)) l2 (LengthCons _ w2 ps2 m l3) f1
    (add-succ-left m f1 d a)))

; Walking along a permutation from the image of z comes back to z.
(def-fns _ $ (erased cycle : (erased (Nat) d z y) (erased (List (Nat)) p q) (erased (Perm d p q) pm) (erased (Nth (Nat) p z y) pz)
    (erased (Lt z d) lz) -> (erased (List (Nat)) xs) (erased (Path p (Nil (Nat)) y z xs) r))
  (let-match erased pm (MkPerm _ _ _ ids io lp qp pq))
  (let ((erased y2) (erased pz2) (erased ly)) (perm-nth d z p q pm lz))
  (let-match erased (nth-fn _ p z y y2 pz pz2) (Refl _ _))
  (let ((erased d1) (erased e)) (lt-pos z d lz))
  (let-match erased e (Refl _ _))
  (cycle-go d (Succ (Zero)) z y y p q ids (Nil _) pm io pz (PathHere p _ y) (DistCons y _ (NotInNil y) (DistNil))
    (SubCons y _ ids (iota-in d y ids io ly) (SubNil ids)) ly (LengthCons _ y _ (Zero) (LengthNil _)) d1 (AddSucc (Zero) d1 d1 (AddZero d1))))

; Darts joined in the graph of a permutation are joined by a walk along it.
(def-fns _ $ (erased conn-path : (erased (Nat) d x y) (erased (List (Nat)) p q) (erased (List (Bond)) g) (erased (Perm d p q) pm)
    (erased (Graph d p g) gr) (subterm erased (Conn g x y) c) -> (erased (List (Nat)) xs) (erased (Path p (Nil (Nat)) x y xs) r))
  (let-match erased c (ConnStep _ _ u _ a c1) ((ConnHere _ _) (values (Nil _) (PathHere p _ x))))
  (let ((erased xs1) (erased w1)) (conn-path d u y p q g pm gr c1))
  (let-match erased (graph-adj-inv d x u p g gr a) (OrR _ _ pu)
    ((OrL _ _ px) (values (Cons _ x xs1) (PathStep p _ xs1 x u y px (NotInNil x) w1))))
  (let-match erased pm (MkPerm _ _ _ ids io lp qp pq))
  (let ((erased xs2) (erased w2)) (cycle d u x p q pm pu (nth-lt-length _ p u d x pu lp)))
  (path-cat p _ xs2 xs1 x u y w2 w1))

(def-fns _ $ (erased perm-val : (erased (Nat) d x y) (erased (List (Nat)) p q) (erased (Perm d p q) pm) (erased (Nth (Nat) p x y) px)
    -> (erased (Lt y d) ly))
  (let-match erased pm (MkPerm _ _ _ ids io lp qp pq))
  (nth-lt-length _ q y d x (respects-nth q p ids x y x qp px (iota-nth d x ids io (nth-lt-length _ p x d y px lp)))
    (respects-length-inv p q ids d pq (iota-length d ids io))))

(def-fns _ $ (erased perm-inv : (erased (Nat) d x y) (erased (List (Nat)) p q) (erased (Perm d p q) pm) (erased (Nth (Nat) p x y) px)
    -> (erased (Nth (Nat) q y x) r))
  (let-match erased pm (MkPerm _ _ _ ids io lp qp pq))
  (respects-nth q p ids x y x qp px (iota-nth d x ids io (nth-lt-length _ p x d y px lp))))

(def-fns _ $ (erased perm-sym : (erased (Nat) d) (erased (List (Nat)) p q) (erased (Perm d p q) pm) -> (erased (Perm d q p) r))
  (let-match erased pm (MkPerm _ _ _ ids io lp qp pq))
  (MkPerm d q p ids io (respects-length-inv p q ids d pq (iota-length d ids io)) pq qp))

(def-fns _ $ (erased cut-first : (erased (List (Nat)) p s xs) (erased (Nat) x y) (subterm erased (Path p s x y xs) w)
    -> (erased (List (Nat)) xs2) (erased (Path p (Cons (Nat) y s) x y xs2) r))
  (let-match erased w (PathStep _ _ xs1 _ z _ px out w1) ((PathHere _ _ _) (values (Nil _) (PathHere p _ x))))
  (let-match erased (nat-eq x y) (Unequal _ _ _ _ ne) ((Equal _ _ _) (values (Nil _) (PathHere p _ x))))
  (let ((erased xs3) (erased w3)) (cut-first p s xs1 z y w1))
  (values (Cons _ x xs3) (PathStep p _ xs3 x z y px (NotInCons x y s ne out) w3)))

; Drop the part of a walk before its last departure from c.
(def-fns _ $ (erased cut-last : (erased (List (Nat)) p s xs) (erased (Nat) x y c c2) (subterm erased (Path p s x y xs) w)
    (erased (Nth (Nat) p c c2) pc) -> (erased (Or (SomePath p (Cons (Nat) c s) x y) (SomePath p (Cons (Nat) c s) c2 y)) r))
  (let-match erased w (PathStep _ _ xs1 _ z _ px out w1)
    ((PathHere _ _ _) (OrL _ _ (MkSomePath p _ (Nil _) x x (PathHere p _ x)))))
  (let-match erased (cut-last p s xs1 z y c c2 w1 pc) (OrL _ _ sp) ((OrR _ _ sp) (OrR _ _ sp)))
  (let-match erased sp (MkSomePath _ _ xs3 _ _ w3))
  (let-match erased (nat-eq x c) (Equal _ _ _)
    ((Unequal _ _ _ _ ne) (OrL _ _ (MkSomePath p _ (Cons _ x xs3) x y (PathStep p _ xs3 x z y px (NotInCons x c s ne out) w3)))))
  (let-match erased (nth-fn _ p x z c2 px pc) (Refl _ _))
  (OrR _ _ sp))

; A walk from x to y that never leaves y, and never leaves c unless it starts at c2, the step after c.
(def-fns _ $ (erased cut-both : (erased (List (Nat)) p xs) (erased (Nat) x y c c2) (erased (Path p (Nil (Nat)) x y xs) w)
    (erased (Nth (Nat) p c c2) pc)
    -> (erased (Or (SomePath p (Cons (Nat) c (Cons (Nat) y (Nil (Nat)))) x y) (SomePath p (Cons (Nat) c (Cons (Nat) y (Nil (Nat)))) c2 y)) r))
  (let ((erased xs2) (erased w2)) (cut-first p (Nil _) xs x y w))
  (cut-last p _ xs2 x y c c2 w2 pc))

; Every bond of g is a dart x and the entry of p at x.
(def-adts $ (Fun : ((List (Nat)) p) ((List (Bond)) g) -> Type)
  enum
  (many FunNil : (erased (List (Nat)) p) -> (Fun p (Nil (Bond))))
  (many FunCons : (erased (List (Nat)) p) (erased (List (Bond)) g) (erased (Nat) x y) (erased (Nth (Nat) p x y) px) (erased (Fun p g) rest)
      -> (Fun p (Cons (Bond) (MkBond x y) g))))

; Every bond of h is at some position of g.
(def-adts $ (Within : ((List (Bond)) h) ((List (Bond)) g) -> Type)
  enum
  (many WithinNil : (erased (List (Bond)) g) -> (Within (Nil (Bond)) g))
  (many WithinCons : (erased (List (Bond)) h g) (erased (Bond) b) (erased (Nat) j) (erased (Nth (Bond) g j b) p) (erased (Within h g) rest)
      -> (Within (Cons (Bond) b h) g)))

(def-fns _ $ (erased within-cons : (erased (List (Bond)) h g) (erased (Bond) b) (subterm erased (Within h g) w) -> (erased (Within h (Cons (Bond) b g)) r))
  (let-match erased w (WithinCons h1 _ b1 j p w1) ((WithinNil _) (WithinNil _)))
  (WithinCons h1 _ b1 (Succ j) (NthThere _ b g j b1 p) (within-cons h1 g b w1)))

(def-fns _ $ (erased within-self : (subterm erased (List (Bond)) g) -> (erased (Within g g) r))
  (let-match erased g (Cons _ b g1) ((Nil _) (WithinNil _)))
  (WithinCons g1 g b (Zero) (NthHere _ b g1) (within-cons g1 g1 b (within-self g1))))

(def-fns _ $ (erased zip-nth-inv : (erased (List (Nat)) xs ys) (erased (List (Bond)) g) (erased (Nat) j x y) (subterm erased (Zip xs ys g) z)
    (erased (Nth (Bond) g j (MkBond x y)) p) -> (erased (Nth (Nat) xs j x) px) (erased (Nth (Nat) ys j y) py))
  (let-match erased z (ZipCons xs1 ys1 g1 x0 y0 z1) (absurd (ZipNil) p))
  (let-match erased p (NthThere _ _ _ j1 _ p1) ((NthHere _ _ _) (values (NthHere _ x xs1) (NthHere _ y ys1))))
  (let ((erased px) (erased py)) (zip-nth-inv xs1 ys1 g1 j1 x y z1 p1))
  (values (NthThere _ x0 xs1 j1 x px) (NthThere _ y0 ys1 j1 y py)))

(def-fns _ $ (erased fun-within : (erased (Nat) d) (erased (List (Nat)) p ids) (erased (List (Bond)) g h) (erased (Iota d ids) io)
    (erased (Zip ids p g) z) (subterm erased (Within h g) w) -> (erased (Fun p h) r))
  (let-match erased w (WithinCons h1 _ b j pj w1) ((WithinNil _) (FunNil p)))
  (let-match erased b (MkBond x y))
  (let ((erased px) (erased py)) (zip-nth-inv ids p g j x y z pj))
  (let-match erased (iota-at d j x ids io px) (Refl _ _))
  (FunCons p h1 x y py (fun-within d p ids g h1 io z w1)))

(def-fns _ $ (erased graph-fun : (erased (Nat) d) (erased (List (Nat)) p) (erased (List (Bond)) g) (erased (Graph d p g) gr) -> (erased (Fun p g) r))
  (let-match erased gr (MkGraph _ _ ids _ io lp z))
  (fun-within d p ids g g io z (within-self g)))

; p2 is p with a sent to u and b to v.
(def-adts $ (Upd2 : ((List (Nat)) p) ((Nat) a u b v) ((List (Nat)) p2) -> Type)
  enum
  (many MkUpd2 : (erased (List (Nat)) p p1 p2) (erased (Nat) a u b v) (erased (Apart (Nat) Lt a b) ne)
      (erased (SetNth (Nat) p a u p1) s1) (erased (SetNth (Nat) p1 b v p2) s2) -> (Upd2 p a u b v p2)))

(def-adts $ (UpdCase : ((List (Nat)) p) ((Nat) a u b v x y) -> Type)
  enum
  (many UCa : (erased (List (Nat)) p) (erased (Nat) a u b v) -> (UpdCase p a u b v a u))
  (many UCb : (erased (List (Nat)) p) (erased (Nat) a u b v) -> (UpdCase p a u b v b v))
  (many UCo : (erased (List (Nat)) p) (erased (Nat) a u b v x y) (erased (Apart (Nat) Lt x a) na) (erased (Apart (Nat) Lt x b) nb)
      (erased (Nth (Nat) p x y) px) -> (UpdCase p a u b v x y)))

(def-fns _ $ (erased setnth-keep : (erased (List (Nat)) xs ys) (erased (Nat) i j y x) (erased (SetNth (Nat) xs i y ys) s)
    (erased (Nth (Nat) xs j x) p) (erased (Apart (Nat) Lt j i) ne) -> (erased (Nth (Nat) ys j x) r))
  (match erased ne _
    ((ApLt _ _ _ _ l) (setnth-nth-lt _ xs i j y x ys s p l))
    ((ApGt _ _ _ _ l) (setnth-nth-gt _ xs i j y x ys s p l))))

(def-fns _ $ (erased setnth-back : (erased (List (Nat)) xs ys) (erased (Nat) i j y x) (erased (SetNth (Nat) xs i y ys) s)
    (erased (Nth (Nat) ys j x) p) (erased (Apart (Nat) Lt j i) ne) -> (erased (Nth (Nat) xs j x) r))
  (match erased ne _
    ((ApLt _ _ _ _ l) (setnth-back-lt _ xs i j y x ys s p l))
    ((ApGt _ _ _ _ l) (setnth-back-gt _ xs i j y x ys s p l))))

(def-fns _ $ (erased upd2-a : (erased (List (Nat)) p p2) (erased (Nat) a u b v) (erased (Upd2 p a u b v p2) up) -> (erased (Nth (Nat) p2 a u) r))
  (let-match erased up (MkUpd2 _ p1 _ _ _ _ _ ne s1 s2))
  (setnth-keep p1 p2 b a v u s2 (setnth-nth _ p a u p1 s1) ne))

(def-fns _ $ (erased upd2-b : (erased (List (Nat)) p p2) (erased (Nat) a u b v) (erased (Upd2 p a u b v p2) up) -> (erased (Nth (Nat) p2 b v) r))
  (let-match erased up (MkUpd2 _ p1 _ _ _ _ _ ne s1 s2))
  (setnth-nth _ p1 b v p2 s2))

(def-fns _ $ (erased upd2-other : (erased (List (Nat)) p p2) (erased (Nat) a u b v x y) (erased (Upd2 p a u b v p2) up)
    (erased (Nth (Nat) p x y) px) (erased (Apart (Nat) Lt x a) na) (erased (Apart (Nat) Lt x b) nb) -> (erased (Nth (Nat) p2 x y) r))
  (let-match erased up (MkUpd2 _ p1 _ _ _ _ _ ne s1 s2))
  (setnth-keep p1 p2 b x v y s2 (setnth-keep p p1 a x u y s1 px na) nb))

(def-fns _ $ (erased upd2-case : (erased (List (Nat)) p p2) (erased (Nat) a u b v x y) (erased (Upd2 p a u b v p2) up)
    (erased (Nth (Nat) p2 x y) px) -> (erased (UpdCase p a u b v x y) r))
  (let-match erased up (MkUpd2 _ p1 _ _ _ _ _ ne s1 s2))
  (let-match erased (nat-eq x b) (Unequal _ _ _ _ nb)
    ((Equal _ _ _) (let-match erased (nth-fn _ p2 b y v px (setnth-nth _ p1 b v p2 s2)) (Refl _ _)) (UCb p a u b v)))
  (let ((erased q1)) (setnth-back p1 p2 b x v y s2 px nb))
  (let-match erased (nat-eq x a) (Unequal _ _ _ _ na)
    ((Equal _ _ _) (let-match erased (nth-fn _ p1 a y u q1 (setnth-nth _ p a u p1 s1)) (Refl _ _)) (UCa p a u b v)))
  (UCo p a u b v x y na nb (setnth-back p p1 a x u y s1 q1 na)))

(def-fns _ $ (erased upd2-length : (erased (List (Nat)) p p2) (erased (Nat) a u b v d) (erased (Upd2 p a u b v p2) up)
    (erased (Length (Nat) p d) l) -> (erased (Length (Nat) p2 d) r))
  (let-match erased up (MkUpd2 _ p1 _ _ _ _ _ ne s1 s2))
  (setnth-length _ p1 b d v p2 s2 (setnth-length _ p a d u p1 s1 l)))

(def-fns _ $ (erased upd2-exists : (erased (List (Nat)) p) (erased (Nat) a u b v d) (erased (Length (Nat) p d) l)
    (erased (Lt a d) la) (erased (Lt b d) lb) (erased (Apart (Nat) Lt a b) ne) -> (erased (List (Nat)) p2) (erased (Upd2 p a u b v p2) up))
  (let ((erased p1) (erased s1)) (setnth-exists _ p d a u l la))
  (let ((erased p2) (erased s2)) (setnth-exists _ p1 d b v (setnth-length _ p a d u p1 s1 l) lb))
  (values p2 (MkUpd2 p p1 p2 a u b v ne s1 s2)))

(def-fns _ $ (erased upd2-self : (erased (List (Nat)) p) (erased (Nat) a u b v d) (erased (Length (Nat) p d) l)
    (erased (Lt a d) la) (erased (Lt b d) lb) (erased (Apart (Nat) Lt a b) ne) (erased (Nth (Nat) p a u) pa) (erased (Nth (Nat) p b v) pb)
    -> (erased (Upd2 p a u b v p) up))
  (let ((erased p1) (erased s1)) (setnth-exists _ p d a u l la))
  (let-match erased (setnth-same _ p a u p1 pa s1) (Refl _ _))
  (let ((erased p2) (erased s2)) (setnth-exists _ p d b v l lb))
  (let-match erased (setnth-same _ p b v p2 pb s2) (Refl _ _))
  (MkUpd2 p p p a u b v ne s1 s2))

(def-fns _ $ (erased upd2-graph : (erased (List (Nat)) p p2) (erased (Nat) a u b v d) (erased (Upd2 p a u b v p2) up)
    (erased (Length (Nat) p d) l) -> (erased (List (Bond)) g2) (erased (Graph d p2 g2) gr))
  (let ((erased ids) (erased io)) (iota-exists d))
  (let ((erased lp2)) (upd2-length p p2 a u b v d up l))
  (let ((erased g2) (erased z)) (zip-exists ids p2 d (iota-length d ids io) lp2))
  (values g2 (MkGraph d p2 ids g2 io lp2 z)))

(def-fns _ $ (erased below-upd2 : (erased (Nat) d a u b v) (erased (List (Nat)) p q p2) (erased (List (Bond)) g2) (subterm erased (Fun p2 g2) f)
    (erased (Upd2 p a u b v p2) up) (erased (Perm d p q) pm) (erased (Lt a d) la) (erased (Lt u d) lu) (erased (Lt b d) lb) (erased (Lt v d) lv)
    -> (erased (Below g2 d) r))
  (let-match erased f (FunCons _ g1 x y px f1) ((FunNil _) (BelowNil d)))
  (let ((erased rest)) (below-upd2 d a u b v p q p2 g1 f1 up pm la lu lb lv))
  (let-match erased (upd2-case p p2 a u b v x y up px) (UCo _ _ _ _ _ _ _ _ _ q1)
    ((UCa _ _ _ _ _) (BelowCons g1 a u d la lu rest))
    ((UCb _ _ _ _ _) (BelowCons g1 b v d lb lv rest)))
  (let-match erased pm (MkPerm _ _ _ ids io lp qp pq))
  (BelowCons g1 x y d (nth-lt-length _ p x d y q1 lp) (perm-val d x y p q pm q1) rest))

; With h the graph of p0, p with a and b fixed, the graph of p2 joins what a-u, b-v and h join.
(def-fns _ $ (erased spans-upd2-in : (erased (Nat) d a u b v) (erased (List (Nat)) p p0 p2) (erased (List (Bond)) g0 g2)
    (subterm erased (Fun p2 g2) f) (erased (Upd2 p a u b v p2) up) (erased (Upd2 p a a b b p0) up0) (erased (Graph d p0 g0) gr0)
    -> (erased (Spans (Cons (Bond) (MkBond a u) (Cons (Bond) (MkBond b v) g0)) g2) r))
  (let-match erased f (FunCons _ g1 x y px f1) ((FunNil _) (SpansNil _)))
  (let ((erased h)) (Cons (Bond) (MkBond a u) (Cons (Bond) (MkBond b v) g0)))
  (let ((erased rest)) (spans-upd2-in d a u b v p p0 p2 g0 g1 f1 up up0 gr0))
  (match erased (upd2-case p p2 a u b v x y up px) _
    ((UCa _ _ _ _ _) (SpansCons h g1 a u (conn-adj h a u (AdjFwd _ a u)) rest))
    ((UCb _ _ _ _ _) (SpansCons h g1 b v (conn-adj h b v (AdjThere _ (MkBond a u) b v (AdjFwd g0 b v))) rest))
    ((UCo _ _ _ _ _ _ _ na nb q1)
      (SpansCons h g1 x y (conn-adj h x y (AdjThere _ (MkBond a u) x y (AdjThere g0 (MkBond b v) x y
        (graph-adj d x y p0 g0 gr0 (upd2-other p p0 a a b b x y up0 q1 na nb))))) rest))))

(def-fns _ $ (erased spans-upd2-out : (erased (Nat) d a u b v) (erased (List (Nat)) p p0 p2) (erased (List (Bond)) g0 g2)
    (subterm erased (Fun p0 g0) f) (erased (Upd2 p a u b v p2) up) (erased (Upd2 p a a b b p0) up0) (erased (Graph d p2 g2) gr2)
    -> (erased (Spans g2 g0) r))
  (let-match erased f (FunCons _ g1 x y px f1) ((FunNil _) (SpansNil _)))
  (let ((erased rest)) (spans-upd2-out d a u b v p p0 p2 g1 g2 f1 up up0 gr2))
  (match erased (upd2-case p p0 a a b b x y up0 px) _
    ((UCa _ _ _ _ _) (SpansCons g2 g1 a a (ConnHere g2 a) rest))
    ((UCb _ _ _ _ _) (SpansCons g2 g1 b b (ConnHere g2 b) rest))
    ((UCo _ _ _ _ _ _ _ na nb q1)
      (SpansCons g2 g1 x y (conn-adj g2 x y (graph-adj d x y p2 g2 gr2 (upd2-other p p2 a u b v x y up q1 na nb))) rest))))

; The classes of the graph of p2 are those of a-u, b-v and the graph of p0.
(def-fns _ $ (erased classes-upd2 : (erased (Nat) d k a u b v) (erased (List (Nat)) p q p0 p2) (erased (List (Bond)) g0 g2)
    (erased (Upd2 p a u b v p2) up) (erased (Upd2 p a a b b p0) up0) (erased (Graph d p0 g0) gr0) (erased (Graph d p2 g2) gr2)
    (erased (Perm d p q) pm) (erased (Lt a d) la) (erased (Lt u d) lu) (erased (Lt b d) lb) (erased (Lt v d) lv)
    (erased (Classes (Cons (Bond) (MkBond a u) (Cons (Bond) (MkBond b v) g0)) d k) cs) -> (erased (Classes g2 d k) r))
  (classes-equiv _ g2 d k cs (SpansCons g2 _ a u (conn-adj g2 a u (graph-adj d a u p2 g2 gr2 (upd2-a p p2 a u b v up)))
      (SpansCons g2 _ b v (conn-adj g2 b v (graph-adj d b v p2 g2 gr2 (upd2-b p p2 a u b v up)))
        (spans-upd2-out d a u b v p p0 p2 g0 g2 (graph-fun d p0 g0 gr0) up up0 gr2)))
    (spans-upd2-in d a u b v p p0 p2 g0 g2 (graph-fun d p2 g2 gr2) up up0 gr0)
    (below-upd2 d a u b v p q p2 g2 (graph-fun d p2 g2 gr2) up pm la lu lb lv)))

(def-fns _ $ (erased classes-upd2-back : (erased (Nat) d k a u b v) (erased (List (Nat)) p q p0 p2) (erased (List (Bond)) g0 g2)
    (erased (Upd2 p a u b v p2) up) (erased (Upd2 p a a b b p0) up0) (erased (Graph d p0 g0) gr0) (erased (Graph d p2 g2) gr2)
    (erased (Perm d p q) pm) (erased (Lt a d) la) (erased (Lt u d) lu) (erased (Lt b d) lb) (erased (Lt v d) lv)
    (erased (Classes g2 d k) cs) -> (erased (Classes (Cons (Bond) (MkBond a u) (Cons (Bond) (MkBond b v) g0)) d k) r))
  (classes-equiv g2 _ d k cs
    (spans-upd2-in d a u b v p p0 p2 g0 g2 (graph-fun d p2 g2 gr2) up up0 gr0)
    (SpansCons g2 _ a u (conn-adj g2 a u (graph-adj d a u p2 g2 gr2 (upd2-a p p2 a u b v up)))
      (SpansCons g2 _ b v (conn-adj g2 b v (graph-adj d b v p2 g2 gr2 (upd2-b p p2 a u b v up)))
        (spans-upd2-out d a u b v p p0 p2 g0 g2 (graph-fun d p0 g0 gr0) up up0 gr2)))
    (BelowCons _ a u d la lu (BelowCons _ b v d lb lv (below-upd2 d a a b b p q p0 g0 (graph-fun d p0 g0 gr0) up0 pm la la lb lb)))))
