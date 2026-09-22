; error: many value x used at unique
(def-adts $ (Box : -> Type) enum (many B : (many (Nat) n) -> (Box)))
(let ((unique x)) (B (Succ (Zero))))
(comptime-match unique (share x) (B n cell))
n
