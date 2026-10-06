(def-fns _ $ (many f : (erased Type A) (many (Nat) x) -> (many (Nat) y)) x)
(let ((many h)) f)
(h (Zero))
; error: tests/msg_arity_let_alias_bad.sl:3:1: error: `h` expects 2 arguments, got 1: expected `(erased Type A) (many (Nat) x)`
; error: tests/msg_arity_let_alias_bad.sl:2:7: note: function `h` is declared here
