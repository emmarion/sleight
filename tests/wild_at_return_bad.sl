; error: argument 1, `n`, of `f`: `_` cannot stand for an argument whose slot the signature names
(def-fns _ $ (many f : (erased (Nat) n) (erased (Nat) _m) -> (erased n is r at n)) n)
(let ((erased x)) 3)
(let ((erased _r)) (f _ x))
