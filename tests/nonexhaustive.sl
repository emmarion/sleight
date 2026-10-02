; needs: list
; error: constructor `Succ` has no branch and is not refuted

(def-lvl X)
(def-fns X $ (many f : (many (Nat) n) -> (many (Nat) m))
  (match many n (((Nat) r))
    ((Zero) n)))
