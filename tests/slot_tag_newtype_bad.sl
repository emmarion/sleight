; error: `slot-tag`: `Box` is a newtype, which has no tag slot
(def-adts $ (Box : -> Type) enum newtype (many B : (many (Nat) n) -> (Box)))
(def-fns _ $ (many f : (many (Box) b) ->)
  (slot-tag b)
  (values))
(Zero)
