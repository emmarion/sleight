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
