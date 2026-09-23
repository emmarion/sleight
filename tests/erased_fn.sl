; needs: list
; error: erased function `f` called in a non-erased position

(def-lvl X)
(def-fns X $ (erased f : (many (Nat) n) -> (many (Nat) m)) n)
(f (Zero))
