; needs: list
; error: argument 1, `X`, of `len` is `_` and cannot be inferred
; Nothing in the call fixes the element type, so its `_` is still open at the call's paren.
(def-lvl A)
(def-fns A $ (many len : (erased Type X) (many (List X) _xs) -> (many (Nat) n)) (Zero))
(len _ (Nil _))
