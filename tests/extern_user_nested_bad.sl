; error: only the prelude may mark a definition `extern`
(def-fns _ $ (many outer : (many (Nat) x) -> (many (Nat) r))
  (def-fns _ $ (many extern inner : (many (Nat) y) -> (many (Nat) s)) y)
  (inner x))
