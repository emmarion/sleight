; externs: only
; error: `Mix` has a non-erased field, so its value is not a tag
(def-adts $ (Shade : -> Type)
  enum
  (many Red : -> (Shade))
  (many Mix : (erased (Nat) k) (many (Nat) n) -> (Shade)))
(let ((erased _)) (coercible-tag (Shared) Mix 1 2))
(Zero)
