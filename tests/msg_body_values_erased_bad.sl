(def-fns _ $ (erased f : (many (Nat) x) -> (many (Nat) q) (many (Nat) r)) (values x))
(Zero)
; error: tests/msg_body_values_erased_bad.sl:1:75: error: `f` expects 2 return values, got 1: expected `(erased (Nat) q) (erased (Nat) r)`
; error: tests/msg_body_values_erased_bad.sl:1:14: note: function `f` is declared here
