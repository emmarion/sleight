; error: share needs a unique value
(def-adts $ Box : -> Type enum (many B : (many (Nat) n) -> (Box)))
(let (many x) (B (Succ (Zero))))
(comptime-match many (share x) (B n))
n
