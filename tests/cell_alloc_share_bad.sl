; error: `(cell-alloc MkBox)`, a fresh cell and so unique, used at many without `share`

(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) v) -> (Box)))
(let ((many c)) (cell-alloc MkBox))
(Zero)
