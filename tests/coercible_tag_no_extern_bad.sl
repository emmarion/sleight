; externs: none
; error: `coercible-tag` needs the extern `Nat`, which `--no-extern` replaces with its model
(def-adts $ (Shade : -> Type)
  enum
  (many Red : -> (Shade))
  (many Green : -> (Shade)))
(let ((erased _)) (coercible-tag (Shared) Green))
(Zero)
