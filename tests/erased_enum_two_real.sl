; needs: list
; error: only one real branch

(def-lvl X)
(def-fns X $ many f : (erased (Nat) n) -> (many (Nat) m)
  (match erased n (((Nat) r))
    ((Zero) (Zero))
    ((Succ k) (Zero))))
