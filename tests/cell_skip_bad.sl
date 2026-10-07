; error: not in its slot's location class
(def-adts $ (Box : -> Type) enum (many B : (many (Nat) n) -> (Box)))
(let ((many a)) (Zero))
(let ((many b)) (Zero))
(let ((unique u)) (cell-alloc (B (slot-of a))))
(let ((many v)) (share (u (at) b)))
