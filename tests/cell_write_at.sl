; expect: 2
(def-adts $ (Pair2 : -> Type) enum (many P : (many (Nat) a) (many (Nat) b) -> (Pair2)))
(let ((many a)) (Zero))
(let ((many b)) (Succ (Succ (Zero))))
(let ((unique u)) (cell-alloc P))
(let ((unique u2)) (cell-write unique u (P (slot-of a) (slot-of b))))
(let ((many p)) (share (at unique (u2 a b))))
(let-match many p (P x y))
y
