(def-fns _ $ (many f : (many (Nat) x) -> (many (Nat) q) (many (Nat) r)) (values x))
; error: tests/msg_body_values_bad.sl:1:73: error: `f` expects 2 return values, got 1: expected `(many (Nat) q) (many (Nat) r)`
; error: tests/msg_body_values_bad.sl:1:14: note: function `f` is declared here
