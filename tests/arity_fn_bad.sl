(def-fns _ $ (many f : (erased Type A) (many (Nat) x) -> (many (Nat) y)) x)
(f (Nat) (Zero) (Zero))
; error: tests/arity_fn_bad.sl:2:1: error: `f` expects 2 arguments, got 3
; error: tests/arity_fn_bad.sl:1:14: note: `f` takes `(erased Type A) (many (Nat) x)`
