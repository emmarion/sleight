; expect: 2
(def-adts $ Pair2 : -> Type enum (many P : (many (Nat) a) (many (Nat) b) -> (Pair2)))
(let (unique u) (cell-alloc P))
(let (many p) (u (Zero) (Succ (Succ (Zero)))))
(let-match many p (P a b))
b
