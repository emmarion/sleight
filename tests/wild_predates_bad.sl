; error: expected a `Predates` proof or `_`, got 3 : `(Nat)`

(def-fns _ $ (many g : (many (Nat) n) -> (many (Nat) m)) n)
(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) m))
  (notail $ g (predates 3) n))
