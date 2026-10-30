; externs: only
; error: `Ghost` is phantom, so it has no tag
(def-adts $ (Shade : -> Type)
  enum
  (many Red : -> (Shade))
  (erased Ghost : -> (Shade)))
(let ((erased _)) (coercible-tag (Shared) Ghost))
(Zero)
