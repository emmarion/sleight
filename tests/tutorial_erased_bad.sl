(def-fns _ $ (many oops : (erased (Nat) n) -> (many (Nat) m))
  n)
; error: `n`, declared `erased`, used in a non-erased position
