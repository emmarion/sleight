; needs: list
; error: argument 2, `head`, of `Cons`: `_` stands only for an erased argument, and this one is not erased
(Cons (Nat) _ (Nil (Nat)))
