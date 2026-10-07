; error: `inc-noted` is declared `at` `inc` but its body is not a `delegate` call
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(def-fns _ $ (many inc-noted at inc : (many (Nat) n) (erased (Nat) note) -> (many (Nat) m))
  (inc n))
