(def-adts $ (View : ((Nat) k) ((Nat) j) -> Type)
  enum
  (many VHit : (erased (Nat) k) -> (View k k))
  (many VMiss : (erased (Nat) k i j) (erased (Skip k i j) p) -> (View k j)))

(def-fns _ $ (erased skip-ex : (subterm erased (Nat) k) (erased (Nat) i) -> (erased (Nat) j) (erased (Skip k i j) p))
  (let-match erased k (Succ k1) ((Zero) (values (Succ i) (SkipZ i))))
  (let-match erased i (Succ i1) ((Zero) (values (Zero) (SkipLo k1))))
  (let ((erased j1) (erased p1)) (skip-ex k1 i1))
  (values (Succ j1) (SkipHi k1 i1 j1 p1)))

(def-fns _ $ (erased skip-det : (erased (Nat) k i j1 j2) (subterm erased (Skip k i j1) p) (erased (Skip k i j2) q) -> (erased (Eq (Nat) j1 j2) e))
  (match erased p _
    ((SkipZ _) (let-match erased q (SkipZ _)) (Refl _ j1))
    ((SkipLo _) (let-match erased q (SkipLo _)) (Refl _ j1))
    ((SkipHi k1 i1 a p1)
      (let-match erased q (SkipHi _ _ b q1))
      (eq-cong-succ a b (skip-det k1 i1 a b p1 q1)))))

(def-fns _ $ (erased skip-inj : (erased (Nat) k i1 i2 j) (subterm erased (Skip k i1 j) p) (erased (Skip k i2 j) q) -> (erased (Eq (Nat) i1 i2) e))
  (match erased p _
    ((SkipZ _) (let-match erased q (SkipZ _)) (Refl _ i1))
    ((SkipLo _) (let-match erased q (SkipLo _)) (Refl _ i1))
    ((SkipHi k1 a j1 p1)
      (let-match erased q (SkipHi _ b _ q1))
      (eq-cong-succ a b (skip-inj k1 a b j1 p1 q1)))))

(def-fns _ $ (erased absurd skip-ne : (erased (Nat) k i) (subterm erased (Skip k i k) p) -> (erased (False) f))
  (match erased p _
    (absurd (SkipHi k1 i1 _ p1) (skip-ne k1 i1 p1))))

(def-fns _ $ (erased view : (subterm erased (Nat) k) (erased (Nat) j) -> (erased (View k j) v))
  (match erased k _
    ((Zero) (match erased j _ ((Zero) (VHit _)) ((Succ j1) (VMiss _ j1 j (SkipZ j1)))))
    ((Succ k1)
      (let-match erased j (Succ j1) ((Zero) (VMiss _ _ _ (SkipLo k1))))
      (match erased (view k1 j1) _
        ((VHit _) (VHit k))
        ((VMiss _ i _ p) (VMiss _ (Succ i) _ (SkipHi k1 i j1 p)))))))

(def-fns _ $ (erased skip-lt : (erased (Nat) i k) (subterm erased (Lt i k) p) -> (erased (Skip k i i) q))
  (match erased p _
    ((LtZ b) (SkipLo b))
    ((LtS a b p1) (SkipHi b a a (skip-lt a b p1)))))

(def-fns _ $ (erased skip-ge : (subterm erased (Nat) k) (erased (Nat) i) (erased (Lt k (Succ i)) p) -> (erased (Skip k i (Succ i)) q))
  (let-match erased k (Succ k1) ((Zero) (SkipZ i)))
  (let-match erased p (LtS _ _ p1))
  (let-match erased i (Succ i1) (absurd (Zero) p1))
  (SkipHi k1 i1 (Succ i1) (skip-ge k1 i1 p1)))

(def-fns _ $ (erased skip-comm : (erased (Nat) i x y c z w) (subterm erased (Skip i x y) p) (erased (Skip (Succ c) y z) q)
    (erased (Skip c x w) r) (erased (Lt i (Succ c)) lt) -> (erased (Skip i w z) s))
  (match erased p _
    ((SkipZ _)
      (let-match erased q (SkipHi _ _ z1 q1))
      (let-match erased (skip-det c x z1 w q1 r) (Refl _ _))
      (SkipZ w))
    ((SkipLo i1)
      (let-match erased lt (LtS _ _ lt1))
      (let-match erased c (Succ c1) (absurd (Zero) lt1))
      (let-match erased q (SkipLo _))
      (let-match erased r (SkipLo _))
      (SkipLo i1))
    ((SkipHi i1 x1 y1 p1)
      (let-match erased lt (LtS _ _ lt1))
      (let-match erased c (Succ c1) (absurd (Zero) lt1))
      (let-match erased q (SkipHi _ _ z1 q1))
      (let-match erased r (SkipHi _ _ w1 r1))
      (SkipHi i1 w1 z1 (skip-comm i1 x1 y1 c1 z1 w1 p1 q1 r1 lt1)))))
