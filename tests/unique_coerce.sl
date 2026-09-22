; expect: 1
(def-adts $ (Owned : -> Type) enum newtype (many Own : (unique (Nat) n) -> (Owned)))
(let ((unique n)) (Succ (Zero)))
(let ((erased (Coercible (Unique) (Nat) n (Unique) (Owned) (Own n)) p))
  (coercible-wrap _ Own n))
(let ((unique b)) (coerce n p))
(let ((unique r)) (coerce b (coercible-sym p)))
(share r)
