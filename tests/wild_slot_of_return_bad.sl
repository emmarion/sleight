; error: argument 1, `n`, of `f`: `_` cannot stand for an argument whose slot the signature names
(def-fns _ $ (many f : (erased (Nat) n) (erased (Nat) m) (erased (Eq (Nat) n m) _p) -> (erased (slot-of n) is s)) (slot-of n))
(let ((erased x)) 3)
(let ((erased _s)) (f _ x (Refl _ x)))
