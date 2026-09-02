; needs: list
; error: erased value n used in a non-erased position

(def-lvl X)
(def-fns X $ many f : (erased (Nat) n) -> (many (Nat) m) n)
