; error: this `match` is missing a branch for the following unrefuted constructor:
; error: note: value constructor `LtS`, which is declared here

(def-lvl X)

(def-fns X $ (many absurd h : (erased (Nat) a) (many (Lt (Succ a) (Succ (Zero))) p) -> (many (Nat) n))
  (match erased p _ (absurd LtZ)))
