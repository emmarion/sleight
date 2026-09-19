; expect: 1
(def-lvl lv)
(def-fns lv $ many idf : (many (Nat) n) -> (many (Nat) r) n)
(let (unique u) (%Fn))
(let (many (u lv (many (Nat) n) -> (many (Nat) r)) g) idf)
(g (Succ (Zero)))
