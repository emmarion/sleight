; error: used at unique
(def-adts $ Cnt : -> Type enum (many C : (many (Nat) v) -> (Cnt)))
(def-adts $ Box : -> Type enum (many B : (unique (Cnt) c) -> (Box)))
(let (unique x) (B (C (Zero))))
(let (many y) (share x))
(let (many z) (share x))
(let-match many y (B n))
(let-match unique n (C v u))
(let (unique n2) (u (Succ (Succ (Succ (Zero))))))
(let-match many z (B m))
(let-match many (share m) (C w))
w
