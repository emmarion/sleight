; prelude: none
; error: `coercible-tag` needs the prelude's `Nat`, which `--no-prelude` leaves out
(def-adts $ (Shade : -> Type)
  enum
  (many Red : -> (Shade))
  (many Green : -> (Shade)))
(let ((erased _)) (coercible-tag (Shared) Red))
(Red)
