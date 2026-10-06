(def-fns _ $ (many f : (erased Type A) (many (Nat) x) -> (many (Nat) y)) x)
(let ((erased e)) (f (Zero)))
(Zero)
; error: tests/msg_arity_fn_erased_few_bad.sl:2:19: error: `f` expects 2 arguments, got 1: expected `(erased Type A) (erased (Nat) x)`
; error: tests/msg_arity_fn_erased_few_bad.sl:1:14: note: function `f` is declared here
