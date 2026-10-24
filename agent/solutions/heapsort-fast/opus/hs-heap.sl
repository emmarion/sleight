; Heap invariants over positions of a list, and their lemmas.

(def-fns _ $ (erased ule-refl : (erased Elt e) -> (erased (ULe e e) r))
  (let-match erased e (MkCopy _ u))
  (let-match erased u (MkU62 x p))
  (MkULe x p x p (MkLe x x (lt-succ x))))

(def-fns _ $ (erased ule-trans : (erased Elt e) (erased Elt f) (erased Elt g) (erased (ULe e f) p) (erased (ULe f g) q)
    -> (erased (ULe e g) r))
  (let-match erased p (MkULe x px y py xy))
  (let-match erased q (MkULe _ _ z pz yz))
  (let-match erased xy (MkLe _ _ xy1))
  (let-match erased yz (MkLe _ _ yz1))
  (MkULe x px z pz (MkLe x z (lt-le-trans x (Succ y) (Succ z) xy1 (LtS y (Succ z) yz1)))))

; c = 2p+1 or c = 2p+2.
(def-adts
  ((ParentOf : ((Nat) p) ((Nat) c) -> Type)
    enum
    (many PoL : (erased (Nat) p) (erased (Nat) d) (erased (Double p d) dd) -> (ParentOf p (Succ d)))
    (many PoR : (erased (Nat) p) (erased (Nat) d) (erased (Double p d) dd) -> (ParentOf p (Succ (Succ d))))))

(def-fns _ $ (erased parent-fn : (erased (Nat) p) (erased (Nat) q) (erased (Nat) c)
    (erased (ParentOf p c) pp) (erased (ParentOf q c) qq) -> (erased (Eq (Nat) p q) e))
  (match erased pp _
    ((PoL _ d dd)
      (match erased qq _
        ((PoL _ _ ee) (double-inj p q d dd ee))
        (absurd (PoR _ d2 ee) (double-parity p q d2 dd ee))))
    ((PoR _ d dd)
      (match erased qq _
        (absurd (PoL _ _ ee) (double-parity q p d ee dd))
        ((PoR _ _ ee) (double-inj p q d dd ee))))))

(def-fns _ $ (erased parent-lt : (erased (Nat) p) (erased (Nat) c) (erased (ParentOf p c) pp) -> (erased (Lt p c) r))
  (match erased pp _
    ((PoL _ d dd) (double-lt p d dd))
    ((PoR _ d dd) (lt-weaken p (Succ d) (double-lt p d dd)))))

(def-fns _ $ (erased parent-exists : (erased (Nat) c) (erased (Lt (Zero) c) pos) -> (erased (Nat) p) (erased (ParentOf p c) pp))
  (match erased (nat-halve c) _
    (absurd (HZ) pos)
    ((H1 m d dd) (values m (PoL m d dd)))
    ((H2 m d dd) (values m (PoR m d dd)))))

(def-adts
  ((LeCase : ((Nat) a) ((Nat) c) -> Type)
    enum
    (many LeEq : (erased (Nat) a) -> (LeCase a a))
    (many LeLt : (erased (Nat) a) (erased (Nat) c) (erased (Lt a c) p) -> (LeCase a c))))

(def-fns _ $ (erased le-case : (erased (Nat) a) (erased (Nat) c) (erased (Lt a (Succ c)) p) -> (erased (LeCase a c) r))
  (match erased (nat-cmp a c) _
    ((CLt _ _ _ _ q) (LeLt a c q))
    ((CEq _ _ _) (LeEq a))
    (absurd (CGt _ _ _ _ q) (lt-asym c a q p))))

(def-fns _ $ (erased absurd ne-irrefl : (erased (Nat) a) (erased (NeN a a) ne) -> (erased (False) f))
  (match erased ne _
    (absurd (NeL _ _ p) (lt-irrefl a p))
    (absurd (NeG _ _ p) (lt-irrefl a p))))

(def-adts
  ((EqOrNe : ((Nat) a) ((Nat) b) -> Type)
    enum
    (many IsEq : (erased (Nat) a) -> (EqOrNe a a))
    (many IsNe : (erased (Nat) a) (erased (Nat) b) (erased (NeN a b) ne) -> (EqOrNe a b))))

(def-fns _ $ (erased eq-or-ne : (erased (Nat) a) (erased (Nat) b) -> (erased (EqOrNe a b) r))
  (match erased (nat-cmp a b) _
    ((CLt _ _ _ _ q) (IsNe a b (NeL a b q)))
    ((CEq _ _ _) (IsEq a))
    ((CGt _ _ _ _ q) (IsNe a b (NeG a b q)))))

(def-fns _ $ (erased ne-of-gt : (erased (Nat) a) (erased (Nat) b) (erased (Lt b a) p) -> (erased (NeN a b) r))
  (NeG a b p))

; c >= n, or xs[c] <= xs[p].
(def-adts
  ((Bnd : ((List Elt) xs) ((Nat) n) ((Nat) c) ((Nat) p) -> Type)
    enum
    (many BOut : (erased (List Elt) xs) (erased (Nat) n) (erased (Nat) c) (erased (Nat) p) (erased (Lt n (Succ c)) out)
        -> (Bnd xs n c p))
    (many BIn : (erased (List Elt) xs) (erased (Nat) n) (erased (Nat) c) (erased (Nat) p) (erased Elt x) (erased Elt y)
        (erased (Nth Elt xs c x) nc) (erased (Nth Elt xs p y) np) (erased (ULe x y) le) -> (Bnd xs n c p))))

; Every position c in [a, n) is a child of k, or is no greater than its parent.
(def-adts
  ((Covers : ((List Elt) xs) ((Nat) n) ((Nat) k) ((Nat) a) -> Type)
    enum
    (many CEnd : (erased (List Elt) xs) (erased (Nat) n) (erased (Nat) k) (erased (Nat) a) (erased (Lt n (Succ a)) out)
        -> (Covers xs n k a))
    (many CSkip : (erased (List Elt) xs) (erased (Nat) n) (erased (Nat) k) (erased (Nat) a) (erased (ParentOf k a) pk)
        (erased (Lt a n) an) (erased (Covers xs n k (Succ a)) rest) -> (Covers xs n k a))
    (many COk : (erased (List Elt) xs) (erased (Nat) n) (erased (Nat) k) (erased (Nat) a) (erased (Nat) p)
        (erased Elt x) (erased Elt y) (erased (ParentOf p a) pa) (erased (Lt a n) an)
        (erased (Nth Elt xs a x) na) (erased (Nth Elt xs p y) np) (erased (ULe x y) le)
        (erased (Covers xs n k (Succ a)) rest) -> (Covers xs n k a))))

; The children of k are no greater than k's parent, unless k is below the covered range.
(def-adts
  ((Grand : ((List Elt) xs) ((Nat) n) ((Nat) k) ((Nat) a) -> Type)
    enum
    (many GLow : (erased (List Elt) xs) (erased (Nat) n) (erased (Nat) k) (erased (Nat) a) (erased (Lt k a) low)
        -> (Grand xs n k a))
    (many GPar : (erased (List Elt) xs) (erased (Nat) n) (erased (Nat) k) (erased (Nat) a) (erased (Nat) q) (erased (Nat) d)
        (erased (ParentOf q k) qk) (erased (Double k d) dd) (erased (Bnd xs n (Succ d) q) b1)
        (erased (Bnd xs n (Succ (Succ d)) q) b2) -> (Grand xs n k a))))

(def-fns _ $ (erased covers-lookup : (erased (List Elt) xs) (erased (Nat) n) (erased (Nat) k) (erased (Nat) a)
    (subterm erased (Covers xs n k a) cv) (erased (Nat) c) (erased (Lt a (Succ c)) ac) (erased (Lt c n) cn)
    (erased (Nat) p) (erased (ParentOf p c) pc) (erased (NeN p k) pk) (erased Elt x) (erased Elt y)
    (erased (Nth Elt xs c x) nc) (erased (Nth Elt xs p y) np) -> (erased (ULe x y) r))
  (match erased cv _
    (absurd (CEnd _ _ _ _ out) (lt-asym c a (lt-le-trans c n a cn out) ac))
    ((CSkip _ _ _ _ pk2 an rest)
      (let-match erased (le-case a c ac) (LeLt _ _ lt)
        (absurd (LeEq _) (let-match erased (parent-fn k p c pk2 pc) (Refl _ _)) (ne-irrefl k pk)))
      (covers-lookup xs n k (Succ a) rest c (LtS a c lt) cn p pc pk x y nc np))
    ((COk _ _ _ _ p2 x2 y2 pa an na np2 le rest)
      (let-match erased (le-case a c ac) (LeEq _)
        ((LeLt _ _ lt) (covers-lookup xs n k (Succ a) rest c (LtS a c lt) cn p pc pk x y nc np)))
      (let-match erased (parent-fn p2 p c pa pc) (Refl _ _))
      (let-match erased (nth-fn Elt xs c x2 x na nc) (Refl _ _))
      (let-match erased (nth-fn Elt xs p y2 y np2 np) (Refl _ _))
      le)))

(def-fns _ $ (erased covers-fill : (erased (List Elt) xs) (erased (Nat) n) (erased (Nat) k) (erased (Nat) a)
    (subterm erased (Covers xs n k a) cv) (erased (Nat) d) (erased (Double k d) dd)
    (erased (Bnd xs n (Succ d) k) b1) (erased (Bnd xs n (Succ (Succ d)) k) b2) (erased (Nat) kk)
    -> (erased (Covers xs n kk a) r))
  (let-match erased cv (CSkip _ _ _ _ pk an rest)
    ((CEnd _ _ _ _ out) (CEnd xs n kk a out))
    ((COk _ _ _ _ p x y pa an na np le rest)
      (COk xs n kk a p x y pa an na np le (covers-fill xs n k (Succ a) rest d dd b1 b2 kk))))
  (let ((erased tail1)) (covers-fill xs n k (Succ a) rest d dd b1 b2 kk))
  (match erased pk _
    ((PoL _ d1 dd1)
      (let-match erased (double-fn k d1 d dd1 dd) (Refl _ _))
      (let-match erased b1 (BIn _ _ _ _ x y nc nk le) (absurd (BOut _ _ _ _ out) (lt-asym a n an out)))
      (COk xs n kk a k x y pk an nc nk le tail1))
    ((PoR _ d1 dd1)
      (let-match erased (double-fn k d1 d dd1 dd) (Refl _ _))
      (let-match erased b2 (BIn _ _ _ _ x y nc nk le) (absurd (BOut _ _ _ _ out) (lt-asym a n an out)))
      (COk xs n kk a k x y pk an nc nk le tail1))))

(def-fns _ $ (erased bnd-trans : (erased (List Elt) xs) (erased (Nat) n) (erased (Nat) c) (erased (Nat) m) (erased (Nat) k)
    (erased (Bnd xs n c m) b) (erased Elt y) (erased Elt z) (erased (Nth Elt xs m y) nm) (erased (Nth Elt xs k z) nk)
    (erased (ULe y z) yz) -> (erased (Bnd xs n c k) r))
  (let-match erased b (BIn _ _ _ _ x y1 nc nm1 xy) ((BOut _ _ _ _ out) (BOut xs n c k out)))
  (let-match erased (nth-fn Elt xs m y1 y nm1 nm) (Refl _ _))
  (BIn xs n c k x z nc nk (ule-trans x y z xy yz)))
