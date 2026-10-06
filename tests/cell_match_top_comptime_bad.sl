; error: `comptime-match` is a run-position statement
(def-adts $ (Pair2 : -> Type) enum (many P : (many (Nat) a) (many (Nat) b) -> (Pair2)))
(let ((many a)) (Zero))
(let ((many b)) (Succ (Succ (Zero))))
(let ((unique u)) (cell-alloc (P (SlotHolds a) (SlotHolds b))))
(let ((many k)) (P a b))
(let ((unique v))
  (cell-match unique u (((Cell P (SlotHolds a) (SlotHolds b)) v at u))
    (P s t back)
    (comptime-match many k (P x y))
    back))
(let ((many p)) (at (v a b)))
(let-match many p (P x y)) y
