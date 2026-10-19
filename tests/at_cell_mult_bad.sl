; error: is taken at `unique` here; write `(at unique (...))`
(def-adts $ (Pair2 : -> Type) enum (many P : (many (Nat) a) (many (Nat) b) -> (Pair2)))
(let ((many a)) 0)
(let ((many b)) 2)
(let ((unique u)) (cell-alloc (P (slot-of a) (slot-of b))))
(let ((unique p)) (at erased (u a b)))
(let-match unique p (P x y)) y
