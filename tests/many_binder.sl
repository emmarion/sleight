; needs: list
; error: erased value

(def-lvl X)
(def-fns X $ many f : (many (Nat) n) -> (erased (Nat) m) n)
(let (many x) (f (Zero)))
