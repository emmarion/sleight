; needs: list
; error: value mismatch

(def-adts $ Meters : -> Type
  enum
  (many MkMeters : (many (Nat) n) -> (Meters)))

(let (many one) (Succ (Zero)))
(let (many two) (Succ one))
(coerce two (coercible-wrap MkMeters one))
