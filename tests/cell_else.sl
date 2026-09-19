; expect: 1
(def-adts $ D : -> Type enum (many A : -> (D)) (many B : (many (Nat) n) -> (D)))
(def-fns _ $ many same : (unique (D) x) -> (unique x is r at x)
  (match unique x _ ((A u) (at (u))) (else y y)))
(let (unique x) (same (B (Succ (Zero)))))
(match many (share x) (((Nat) n)) (absurd A) ((B n) n))
