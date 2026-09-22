; expect: 1
(def-adts $ (Box : -> Type) enum (many B : (unique (Nat) n) -> (Box)))
(let ((unique x)) (B (Succ (Zero))))
(comptime-match unique x (B n u))
(let ((unique y)) (at (u n)))
(let-match unique y (B r _))
(share r)
