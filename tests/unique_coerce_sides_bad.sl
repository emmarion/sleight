; error: mismatch
(def-adts
  ((SharedBox : -> Type) enum newtype (many SharedBoxed : (many (Nat) n) -> (SharedBox)))
  ((Owned : -> Type) enum newtype (many Own : (unique (Nat) n) -> (Owned))))
(let ((many n)) (Succ (Zero)))
(let ((erased bad))
  (coercible-trans
    (coercible-sym (coercible-wrap (Unique) SharedBoxed n))
    (coercible-wrap (Unique) Own n)))
