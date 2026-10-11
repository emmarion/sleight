; expect: 3
(def-adts $ (Box : -> Type) enum (many B : (unique (Nat) n) -> (Box)))
(def-fns _ $ (many box : (many (Nat) k) -> (unique (Box) b)) (B (Succ k)))
(comptime-match unique (box 2) (B n))
(share n)
