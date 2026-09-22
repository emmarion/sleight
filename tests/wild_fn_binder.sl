; needs: list
; expect: 2
; A `_` solved under a Fn binder: apply's A is read off the function argument's parameter type.

(def-lvl I)
(def-fns I $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(def-lvl A)
(def-fns A $ (many apply : (erased Type X) (many (Fn I (many X x) -> (many X y)) f) (many X v) -> (many X r))
  (f v))
(apply _ inc (Succ (Zero)))
