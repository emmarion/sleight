; error: of `f` does not satisfy `at` `(slot-of Slot)`
(def-fns _ $ (many f : (erased (Slot) s) (erased (Nat) _x at s) -> (many (Nat) r)) 0)
(def-fns _ $ (many g : (many (Nat) y) -> (many (Nat) r)) (f (slot-of Slot) y))
