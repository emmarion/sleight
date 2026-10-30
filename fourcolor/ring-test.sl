; slc std/nat.sl std/list.sl fourcolor/ring.sl fourcolor/ring-test.sl --goal proved
(let ((many two)) (Succ i1))
(let ((many lhs)) (EMul (EAdd (EVar i0) (EVar i1)) (EAdd (EVar i0) (EVar i1))))
(let ((many rhs)) (EAdd (EAdd (EMul (EVar i0) (EVar i0)) (EMul (ENum two) (EMul (EVar i0) (EVar i1)))) (EMul (EVar i1) (EVar i1))))
(comptime-match many (ring-check lhs rhs) (Some _ same))

(def-fns _ $ (erased square : (erased (Nat) a b s l aa ab ab2 t bb r)
    (erased (Add a b s) p1) (erased (Mul s s l) m1)
    (erased (Mul a a aa) m2) (erased (Mul a b ab) m3) (erased (Mul two ab ab2) m4) (erased (Add aa ab2 t) p2) (erased (Mul b b bb) m5)
    (erased (Add t bb r) p3) -> (erased (Eq (Nat) l r) e))
  (let ((erased env)) (Cons _ a $ Cons _ b $ Nil (Nat)))
  (let ((erased va)) (EvVar env i0 a (NthHere _ a _)))
  (let ((erased vb)) (EvVar env i1 b (NthThere _ a _ i0 b (NthHere _ b _))))
  (let ((erased vs)) (EvAdd env _ _ a b s va vb p1))
  (ring-sound env lhs rhs l r same (EvMul env _ _ s s l vs vs m1)
    (EvAdd env _ _ t bb r (EvAdd env _ _ aa ab2 t (EvMul env _ _ a a aa va va m2) (EvMul env _ _ two ab ab2 (EvNum env two) (EvMul env _ _ a b ab va vb m3) m4) p2)
      (EvMul env _ _ b b bb vb vb m5) p3)))

(def-adts $ (Square : -> Type)
  enum
  (many MkSquare : (erased (Level) L)
      (erased (Fn L (erased (Nat) a b s l aa ab ab2 t bb r)
          (erased (Add a b s) p1) (erased (Mul s s l) m1)
          (erased (Mul a a aa) m2) (erased (Mul a b ab) m3) (erased (Mul two ab ab2) m4) (erased (Add aa ab2 t) p2) (erased (Mul b b bb) m5)
          (erased (Add t bb r) p3) -> (erased (Eq (Nat) l r) e)) thm)
      -> (Square)))

(goal erased (Square))
(qed (MkSquare (level-of square) square))
