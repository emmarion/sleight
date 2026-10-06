(def-fns _ $ (many f : (erased Type A) (many A y) (many (Nat) _) -> (many (Nat) r)) (Zero))
(f (Nat) (Zero) (Nil (Nat)))
; error: tests/msg_argtype_anon_param_bad.sl:2:17: error: argument 3 of `f`: type mismatch: expected `(Nat)`, got `(List (Nat))`
; error: tests/msg_argtype_anon_param_bad.sl:1:14: note: function `f` is declared here
