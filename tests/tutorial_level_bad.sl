(def-fns _ $ (many twice : (erased (Level) L) (many (Fn L (many (Nat) x) -> (many (Nat) y)) f)
    (many (Nat) n) -> (many (Nat) m))
  (f $ f n))
; error: `L` was not in scope when level `(level-of twice)` was minted
