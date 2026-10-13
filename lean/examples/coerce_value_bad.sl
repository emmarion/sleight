(def-adts $ (Meters : -> Type)
  enum newtype
  (many MkMeters : (many (Nat) n) -> (Meters)))

(let ((erased p)) (coercible-wrap (Shared) MkMeters 1))
(coerce 2 p)
