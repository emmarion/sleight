; error: `_` cannot stand for an argument written `at`
(def-fns _ $ (many f : (erased (Nat) x) (erased (Nat) _y at x) -> (many (Nat) r)) 0)
(def-fns _ $ (many g : (erased (Nat) a) -> (many (Nat) r)) (f a _))
