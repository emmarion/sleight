; error: a `Matchable` constructor cannot be `unique`
(def-adts $ (Box : -> Type)
  enum
  (many MkBox : -> (Box)))
(def-fns _ $ (many f : (erased (Matchable enum Box (unique MkBox)) m) -> (many (Nat) n))
  (Zero))
(Zero)
