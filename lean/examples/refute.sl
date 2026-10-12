; an absurd body may end by refuting the facts in force (DESIGN.md section 51)
(def-lvl X)
(def-fns X $ (many absurd lt-zero : (erased (Nat) a) (many (Lt a (Zero)) p) -> (many (Nat) n))
  p)
(def-fns X $ (many absurd lt-one : (erased (Nat) a) (many (Lt (Succ a) (Succ (Zero))) p) -> (many (Nat) n))
  (match erased p _
    (absurd LtZ)
    (absurd (LtS x y q) (match erased q _ (absurd LtZ) (absurd LtS)))))
(def-fns _ $ (many first : (many (Nat) n) (erased (Lt (Zero) n) p) -> (many (Nat) m))
  (match many n _
    (absurd (Zero) p)
    ((Succ k) k)))
(first (Succ (Succ (Zero))) (LtZ (Succ (Zero))))
