(def-lvl L)
(def-fns L $ (many f : (erased Type _A) (many (Nat) x) -> (many (Nat) y)) x)
(def-fns _ $ (many pick : -> (many (Fn L (erased Type A) (many (Nat) x) -> (many (Nat) y)) r)) f)
((pick) (Nat) (Nil (Nat)))
; error: tests/msg_argtype_computed_bad.sl:4:15: error: argument 2, `x`, of the computed function: type mismatch: expected `(Nat)`, got `(List (Nat))`
; error: tests/msg_argtype_computed_bad.sl:4:2: note: the function is computed here
