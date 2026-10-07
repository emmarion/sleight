(def-fns _ $ (many f : (many (Nat) x) -> (many (Nat) n) (many (Nat) m))
  (values x _))
; error: tests/msg_underscore_values_bad.sl:2:13: error: `_` is not a name, and nothing is inferred here
