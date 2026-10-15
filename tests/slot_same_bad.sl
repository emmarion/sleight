; error: argument 2, `b`, of `nat-same` does not satisfy `at`
(def-fns _ $ (many bad : (many (Nat) x) (many (Nat) y) -> (many (ErasedOr (Eq (Nat) x y)) r))
  (nat-same x y))
