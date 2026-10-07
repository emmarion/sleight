; error: the body of at-function `grow` does not erase to nothing, or to a reordering of variables: it stores, allocates or calls
(def-fns _ $ (many at grow : (many (Nat) x) -> (many (Nat) r at x))
  (let ((many y)) (Succ x))
  x)
