; expect: 1
(def-adts $ (Box : -> Type) enum newtype (many B : (unique (Nat) n) -> (Box)))
(def-fns _ $ (many wrap : (unique (Nat) x) -> (unique (Box) r at x)) (B x))
(def-fns _ $ (many unwrap : (unique (Box) x) -> (unique (Nat) r at x))
  (let-match unique x (B y)) y)
(let ((unique r)) (unwrap (wrap (Succ (Zero)))))
(share r)
