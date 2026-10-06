(def-lvl L)
(def-fns L $ (many f : (erased Type A) (many (Nat) x) -> (many (Nat) y)) x)
(def-fns _ $ (many pick : -> (many (Fn L (erased Type A) (many (Nat) x) -> (many (Nat) y)) r)) f)
((pick) (Zero))
; error: tests/arity_computed_bad.sl:4:1: error: the computed function expects 2 arguments, got 1: expected `(erased Type A) (many (Nat) x)`
; error: tests/arity_computed_bad.sl:4:2: note: the function is computed here
