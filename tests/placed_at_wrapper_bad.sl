; error: is neither
; A placing primitive is not an at-function, so the `at` wrapper's assertion fails on it.
(def-adts $ (MyNat : -> Type) enum (many MyZero : -> (MyNat)))
(def-fns _ $ (many f : (unique (MyNat) n) -> (unique (Placed (slot-of n) (MyNat) n) p at n))
  (at erased (place-at _ n)))
