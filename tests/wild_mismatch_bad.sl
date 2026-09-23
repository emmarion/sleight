; needs: list
; error: type mismatch: expected `(Maybe (Nat))`, got `(List _)`
(def-lvl A)
(def-fns A $ (many f : -> (many (Maybe (Nat)) m)) (Nil _))
(f)
