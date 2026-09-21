; expect: 1
(def-adts $ Box : -> Type enum (many B : (many (Nat) n) -> (Box)))
(let (unique x) (B (Succ (Zero))))
(comptime-match many (share x) (B n))
(let (many y) (share x))
n
