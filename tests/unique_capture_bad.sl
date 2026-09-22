; error: def-fns cannot capture
(def-fns _ $ (many outer : (unique (Nat) x) -> (many (Nat) r))
  (def-fns _ $ (many captured : -> (unique (Nat) r)) x)
  (Zero))
