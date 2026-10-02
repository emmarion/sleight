; error: expected a `Subterm` proof or `_`, got `(Zero)` : `(Nat)`

(def-fns _ $ (many f : (subterm many (Nat) n) -> (many (Nat) m))
  (match many n _ ((Zero) n) ((Succ k) (notail $ f (subterm (Zero)) k))))
