; error: expected a telescope or `_`, got `Zero`

(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) m))
  (match many n (Zero) ((Zero) n) ((Succ k) n)))
