; needs: list
; error: argument 1, `X`, of `len` is `_` and cannot be inferred
; Nothing in the call fixes the outer _, and the call is a boundary (DESIGN.md section 50).
(def-lvl A)
(def-fns A $ (many len : (erased Type X) (many (List X) _xs) -> (many (Nat) n)) (Zero))
(len _ (Nil _))
