; error: used at unique
(def-adts $ (Box : -> Type) enum (many B : (unique (Nat) n) -> (Box)))
(def-fns _ $ (many take : (unique (Nat) n) -> (many (Nat) r)) (share n))
(let ((unique x)) (B (Zero)))
(let ((many y)) (share x))
(let-match many y (B n))
(take n)
