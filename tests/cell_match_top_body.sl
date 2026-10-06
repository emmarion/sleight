; expect: 2
(def-adts $ (Pair2 : -> Type) enum (many P : (many (Nat) a) (many (Nat) b) -> (Pair2)))
(let ((many a)) (Zero))
(let ((many b)) (Succ (Succ (Zero))))
(let ((unique u)) (cell-alloc (P (SlotHolds a) (SlotHolds b))))
(let ((unique v))
  (cell-match unique u (((Cell P (SlotHolds a) (SlotHolds b)) v at u))
    (P s t back)
    (let ((many z)) s)
    (let ((unique w)) back)
    w))
(let ((many p)) (at (v a b)))
(let-match many p (P x y)) y
