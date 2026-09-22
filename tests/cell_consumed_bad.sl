; error: conflicting non-erased uses
(def-adts $ (Box : -> Type) enum (many B : (unique (Nat) n) -> (Box)))
(let ((unique n)) (Zero))
(let ((unique u)) (cell-alloc B))
(let ((unique b)) (u n))
(let ((unique b2)) (B n))
