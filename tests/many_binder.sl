; needs: list
; error: the return `m` of `f`, declared `erased`, used in a non-erased position

(def-lvl X)
(def-fns X $ (many f : (many (Nat) n) -> (erased (Nat) m)) n)
(let ((many x)) (f (Zero)))
