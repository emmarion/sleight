; expect: 42
(def-adts $ (Meters : -> Type)
  enum newtype
  (many MkMeters : (many (Nat) n) -> (Meters)))

(let ((many m)) (MkMeters 42))
(let-match many m (MkMeters n))
(coerce m (coercible-sym (coercible-wrap (Shared) MkMeters n)))
