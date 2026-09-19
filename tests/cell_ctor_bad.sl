; error: value mismatch
(def-adts $ D : -> Type enum (many A : (many (Nat) n) -> (D)) (many B : (many (Nat) n) -> (D)))
(let (unique u) (cell-alloc A))
(let (unique v) (cell-write u (B _)))
