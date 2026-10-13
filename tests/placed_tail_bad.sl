; error: marks a function call
; A placing primitive compiles to a renaming, not a call, so `tail` cannot mark it.
(def-adts $ (MyNat : -> Type) enum (many MyZero : -> (MyNat)))
(def-fns _ $ (many f : (unique (MyNat) n) -> (unique (Placed (slot-of n) (MyNat) n) p at n))
  (tail (place-at _ n)))
