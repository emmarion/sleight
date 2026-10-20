; error: argument 1, `n`, of `f`: `_` cannot stand for an argument whose slot the signature names
(def-fns _ $ (many f : (erased (Nat) n) (erased (Nat) _m at n) -> ) (values))
(let ((erased x)) 3)
(let () (f _ x))
