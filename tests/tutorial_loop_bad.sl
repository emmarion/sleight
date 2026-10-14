(def-fns _ $ (many loop : (subterm many (Nat) n) -> (many (Nat) m))
  (notail $ loop n))
; error: same-level call to `loop` decreases no subterm argument
