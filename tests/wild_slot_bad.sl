; error: expected a `(Slot)` or `_`, got `(Nat)`

(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) v) -> (Box)))
(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) m))
  (let ((unique c)) (cell-alloc MkBox))
  (let ((unique d)) (cell-write unique c (MkBox n)))
  n)
