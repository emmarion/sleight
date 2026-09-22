; error: phantom constructors have no cells
(def-adts $ (T : -> Type) enum (many Live : -> (T)) (erased Ghost : -> (T)))
(let ((erased c)) (cell-alloc Ghost))
