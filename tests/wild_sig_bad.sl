; needs: list
; error: `_?1` is the `_` written here
; error: cannot infer the `_` in `(List _?1)`
; A function's signature is spelled out in full: a `_` in it is refused where its entry is bound.
(def-lvl A)
(def-fns A $ (many len : (many (List _) xs) -> (many (Nat) n)) (Zero))
(len (Nil (Nat)))
