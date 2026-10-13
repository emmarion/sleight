(def-adts $ (Box : -> Type)
  enum
  (many MkBox : (many (Nat) n) -> (Box)))

(let ((erased p)) (coercible-wrap (Shared) MkBox 1))
(coerce 1 p)
