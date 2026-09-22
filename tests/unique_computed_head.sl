; expect: 1
(def-unique _ $ (unique once : (many (Nat) n) -> (many (Nat) r)) n)
(def-unique _ $ (unique factory : -> (unique once is f)) once)
((factory) (Succ (Zero)))
