; needs: list
; error: constructor `Zero` has 2 branches

(def-lvl X)
(def-fns X $ (many f : (many (Nat) n) -> (many (Nat) m))
  (match many n (((Nat) r))
    ((Zero) n)
    ((Zero) n)
    ((Succ k) k)))
