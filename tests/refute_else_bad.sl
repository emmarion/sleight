; error: a refuting match has no `else`

(def-lvl X)

(def-fns X $ (many absurd h : (erased (Nat) a) (many (Lt (Succ a) (Succ (Zero))) p) -> (many (Nat) n))
  (match erased p _ (absurd LtZ) (else (match erased p _ (absurd LtZ) (absurd (LtS x y q) q)))))
