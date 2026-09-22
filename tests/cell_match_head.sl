; expect: 1
(def-adts $ (D : -> Type) enum (many A : -> (D)))
(def-fns _ $ (many rebuild : (unique (D) x) -> (unique (D) r at x))
  ((match unique x (((Cell A) u at x)) ((A u) u))))
(let ((unique x)) (rebuild (A)))
(match many (share x) (((Nat) r)) ((A) (Succ (Zero))))
