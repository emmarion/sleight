(def-fns _ $ (many spin : (subterm many (Tree) t) -> (many (Nat) v))
  (notail $ spin t))

(MkUnit)
