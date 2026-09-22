; expect: 1
(def-adts $ (Owned : -> Type) enum newtype (many Own : (unique (Nat) n) -> (Owned)))
(let ((many n)) (Succ (Zero)))
(let ((erased p)) (coercible-share (coercible-wrap (Unique) Own n)))
(let ((many b)) (coerce n p))
(let ((many r)) (coerce b (coercible-sym p)))
r
