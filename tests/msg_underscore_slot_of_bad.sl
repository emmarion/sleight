(def-fns _ $ (many f : (many (Nat) x) -> (erased (Slot) s))
  (slot-of _))
; error: `_` is not a name, and nothing is inferred here
