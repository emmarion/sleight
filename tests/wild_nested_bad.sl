; needs: list
; error: argument 1 is _ and cannot be inferred
; Naive left to right: the inner Nil closes before anything fixes the outer _.
(def-lvl A)
(def-fns A $ many len : (erased Type X) (many (List X) xs) -> (many (Nat) n) (Zero))
(len _ (Nil _))
