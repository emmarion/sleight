; error: argument 2, `b`, of `SameSlot`: value mismatch: expected `(slot-of a)`, got `(slot-of b)`
(def-adts $ (SameSlot : ((Slot) a) (a is b) -> Type)
  enum
  (many MkSame : (erased (Slot) a) -> (SameSlot a a)))
(def-fns _ $ (many f : (many (Nat) a) (many (Nat) b)
    (erased (SameSlot (slot-of a) (slot-of b)) eq) -> (many (Nat) r))
  a)
