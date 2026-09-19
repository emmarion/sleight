; expect: 0
(def-fns _ $ many take : (unique (Special) s) -> (many (Nat) r) (Zero))
(def-lvl lv)
(def-fns lv $ many idf : (many (Nat) n) -> (many (Nat) r) n)
(let (unique u) (%Fn))
(let (many ((share u) lv (many (Nat) n) -> (many (Nat) r)) g) idf)
(take u)
