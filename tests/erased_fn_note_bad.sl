; error: erased function `f` called in a non-erased position
; error: <**>: note: `f` is declared `erased` here

(def-lvl X)
(def-fns X $ (erased f : (many (Nat) n) -> (many (Nat) m)) n)
(let ((many x)) (f (Zero)))
