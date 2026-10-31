; error: `slot-tag`: `Mix` has a non-erased field, so it has no tag slot
(def-adts $ (Shade : -> Type)
  enum
  (many Red : -> (Shade))
  (many Mix : (many (Nat) n) -> (Shade)))
(def-fns _ $ (many f : (many (Shade) c) -> (many (Nat) r))
  (match many c (((Nat) r))
    ((Red) (Zero))
    ((Mix n) (slot-tag c) n)))
(Zero)
