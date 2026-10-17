(def-lvl L)
(def-fns L $ (many f : (erased Type A) (many (Nat) x) -> (many (Nat) y)) x)
(def-fns _ $ (many id : (erased Type T) (many T v) -> (many T w)) v)
((id _ f) (Zero))
; error: tests/msg_arity_computed_call_bad.sl:4:1: error: the computed function expects 2 arguments, got 1: expected `(erased Type A) (many (Nat) x)`
; error: tests/msg_arity_computed_call_bad.sl:4:2: note: the function is computed here
; warns: tests/msg_arity_computed_call_bad.sl:2:24: warning: unused `A`; rename it `_A`
