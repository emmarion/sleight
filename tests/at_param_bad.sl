; error: argument 2, `y`, of `both` does not satisfy `at`
(def-fns _ $ (many both : (many (Nat) x) (many (Nat) y at x) -> (many (Nat) r at y))
  y)
(let ((many a)) 3)
(let ((many b)) 4)
(both a b)
