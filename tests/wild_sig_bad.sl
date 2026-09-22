; needs: list
; error: cannot infer the _ in (List _)
; A function's signature is spelled out in full: a `_` in it is refused where its entry is bound.
(def-lvl A)
(def-fns A $ (many len : (many (List _) xs) -> (many (Nat) n)) (Zero))
(len (Nil (Nat)))
