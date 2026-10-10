; needs: list
; error: `__?1` is the `_` written here
; error: type mismatch: expected `(Maybe (Nat))`, got `(List __?1)`
(def-lvl A)
(def-fns A $ (many f : -> (many (Maybe (Nat)) m)) (Nil _))
(f)
