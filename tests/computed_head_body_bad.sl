(def-fns _ $ (many pick : (many (Special) s) -> (many (Special) r)) s)
(def-fns _ $ (many f : (many (Nat) a) -> (many (Nat) b))
  ((pick values) a))
; error: is not applicable
