; externs: only
; error: `Red` is a constructor of a union, which carries no tag
(def-adts $ (Shade : -> Type)
  union
  (many Red : -> (Shade))
  (many Green : -> (Shade)))
(let ((erased _)) (coercible-tag (Shared) Red))
(Zero)
