; expect: 2
(def-adts $ (Box : -> Type) enum (many B : (unique (Nat) n) -> (Box)))
(def-fns _ $ (many update : (unique (Box) x) -> (unique (Box) r at x))
  (let-match unique x (B n u))
  (u (Succ (Succ (Zero)))))
(let ((unique x)) (update (B (Zero))))
(let-match unique x (B n _))
(share n)
