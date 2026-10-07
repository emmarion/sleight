; error: `inc-noted` is declared `at` `dec` but delegates to `inc`
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(def-fns _ $ (many dec : (many (Nat) n) -> (many (Nat) m)) n)
(def-fns _ $ (many inc-noted at dec : (many (Nat) n) (erased (Nat) note) -> (many (Nat) m))
  (delegate (inc n)))
