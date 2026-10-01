; needs: list
; error: `n`, declared `erased`, used in a non-erased position

(def-lvl X)
(def-fns X $ (many f : (erased (Nat) n) -> (many (Nat) m))
  (let ((many k)) n)
  k)
