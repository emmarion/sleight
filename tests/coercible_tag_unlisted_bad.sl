; externs: only
; error: `k` has no opened `Matchable` that lists it
(def-adts $ (Shade : -> Type)
  enum
  (many Red : -> (Shade))
  (many Green : -> (Shade)))
(def-fns _ $ (erased tag-of : (erased (ValCtor -> (Shade)) k) -> (erased (Nat) n))
  (let ((erased _)) (coercible-tag (Shared) k))
  (Zero))
(Zero)
