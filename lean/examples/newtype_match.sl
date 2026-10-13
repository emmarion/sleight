(def-adts $ (Meters : -> Type)
  enum newtype
  (many MkMeters : (many (Nat) n) -> (Meters)))

(def-fns _ $ (many add-m : (many (Meters) a) (many (Meters) b) -> (many (Meters) c))
  (let-match many a (MkMeters x))
  (match many b _
    ((MkMeters y) (MkMeters $ nat-add x y))))

(let ((erased p)) (coercible-sym (coercible-wrap (Shared) MkMeters 2)))
(let ((many two)) (coerce (MkMeters 2) p))
(add-m (MkMeters two) (MkMeters 3))
