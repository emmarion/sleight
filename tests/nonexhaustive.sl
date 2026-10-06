; needs: list
; error: this `match` is missing a branch for the following unrefuted constructor:
; error: note: value constructor `Succ`, which is declared here

(def-lvl X)
(def-fns X $ (many f : (many (Nat) n) -> (many (Nat) m))
  (match many n (((Nat) r))
    ((Zero) n)))
