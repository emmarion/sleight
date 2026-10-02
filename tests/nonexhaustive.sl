; needs: list
; error: constructor `Succ` has no branch and is not refuted, so this `match` needs a branch for it

(def-lvl X)
(def-fns X $ (many f : (many (Nat) n) -> (many (Nat) m))
  (match many n (((Nat) r))
    ((Zero) n)))
