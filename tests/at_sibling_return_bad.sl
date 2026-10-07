; error: return does not satisfy `at`
(def-fns _ $ (many twin : (many (Nat) x) -> (many (Nat) a) (many (Nat) r at a))
  (values (Succ x) (Succ x)))
(twin 6)
