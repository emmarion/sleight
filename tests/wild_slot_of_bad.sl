; error: argument 1, `n`, of `f`: `_` cannot stand for an argument whose slot the signature names
(def-fns _ $ (many f : (erased (Nat) n) (erased (Slot) t) (erased (Eq (Slot) t (slot-of n)) _p) -> ) (values))
(let ((erased x)) 3)
(let () (f _ (slot-of x) (Refl _ (slot-of x))))
