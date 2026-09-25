; error: a branch of a refuting match is written `absurd`

(def-lvl X)

(def-fns X $ (many absurd h : (erased (Nat) a) (many (Lt (Succ a) (Succ (Zero))) p) -> (many (Nat) n))
  (match erased p _ ((LtS x y q) q)))
