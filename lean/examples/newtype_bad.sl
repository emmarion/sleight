; a newtype's constructor must hold exactly one non-erased field
(def-adts $ (Pair2 : -> Type)
  enum newtype
  (many MkPair2 : (many (Nat) a) (many (Nat) b) -> (Pair2)))
(MkPair2 1 2)
