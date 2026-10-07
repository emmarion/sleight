; error: `tail` marks a call that compiles to one, and a call of at-function `same` is skipped
(def-fns _ $ (many at same : (many (Nat) x) -> (many (Nat) r at x)) x)
(def-fns _ $ (many go : (many (Nat) x) -> (many (Nat) r at x))
  (let ((many y)) (tail (same x)))
  y)
