(def-unique _ $ (unique u : (many (Nat) x) -> (many (Nat) y)) x)
(u (Zero) (Zero))
; error: tests/msg_arity_unique_fn_bad.sl:2:1: error: `u` expects 1 argument, got 2: expected `(many (Nat) x)`
; error: tests/msg_arity_unique_fn_bad.sl:1:17: note: unique function `u` is declared here
