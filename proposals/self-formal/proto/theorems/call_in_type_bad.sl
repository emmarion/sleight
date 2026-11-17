(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(def-fns _ $ (erased lemma : (erased (Nat) n) -> (erased (Eq (Nat) (f n) (Succ n)) e)) (Refl _ _))
