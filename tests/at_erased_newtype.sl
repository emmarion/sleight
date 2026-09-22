; expect: 0
(def-adts $ (Box : -> Type) enum newtype (many B : (many (Nat) n) -> (Box)))
(let ((erased z)) (B (Zero)))
(let ((erased p)) (coercible-sym (coercible-wrap (Shared) B (Zero))))
(let ((erased w)) (coerce (B (Zero)) p))
(def-fns _ $ (erased probe : -> (erased (Nat) r))
  (match erased (B (Zero)) (((Nat) q)) ((B m) m)))
(Zero)
