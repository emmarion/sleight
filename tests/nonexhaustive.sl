; needs: list
; error: constructor `Succ` has 0 branches

(def-lvl X)
(def-fns X $ (many f : (many (Nat) n) -> (many (Nat) m))
  (match many n (((Nat) r))
    ((Zero) n)))
