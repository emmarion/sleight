(def-fns _ $ (many up : (subterm many (Nat) n) -> (many (Nat) m))
  (up (Succ n)))
(up (Zero))
