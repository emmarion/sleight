(def-fns _ $ (many bad-sub : (many (Nat) a) (many (Nat) b) -> (many (Nat) c))
  (let ((many c) (erased _)) (sub a b _))
  c)
; error: argument 3, `le`, of `sub` is `_` and cannot be inferred
