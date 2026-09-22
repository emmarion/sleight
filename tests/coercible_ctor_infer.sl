; expect: 1
(def-adts
  ((Owned : -> Type) enum newtype (many Own : (unique (Nat) n) -> (Owned)))
  ((Holder : (Type A) -> Type) enum (many Hold : (erased Type A) (unique A x) -> (Holder A))))
(let ((unique n)) (Succ (Zero)))
(let ((erased (Coercible (Unique) (Holder (Nat)) (Hold (Nat) n)
                       (Unique) (Holder (Owned)) (Hold (Owned) (Own n))) p))
  (coercible-ctor _ Hold (Nat) (Owned) (coercible-wrap _ Own n)))
(let ((unique h)) (coerce (Hold (Nat) n) p))
(let-match unique h (Hold _ b _))
(let ((unique r)) (coerce b (coercible-sym (coercible-wrap (Unique) Own n))))
(share r)
