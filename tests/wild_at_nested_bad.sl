; error: argument 1, `n`, of `f`: `_` cannot stand for an argument whose slot the signature names
(def-lvl M)
(def-fns _ $ (many f : (erased (Nat) n) (erased (Fn M (erased (Nat) m at n) -> ) _g) -> ) (values))
(def-fns M $ (erased e : (erased (Nat) _m) -> ) (values))
(let () (f _ e))
