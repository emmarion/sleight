(def-fns _ $ (many f : (erased Type A) (many (Nat) x) -> (many (Nat) y)) x)
(f (Nat) _)
; error: tests/msg_wild_not_erased_bad.sl:2:10: error: argument 2, `x`, of `f`: `_` stands only for an erased argument, and this one is not erased
; error: tests/msg_wild_not_erased_bad.sl:1:14: note: function `f` is declared here
