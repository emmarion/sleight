; error: `Ghost` is phantom, so its cell is used only in an erased position
(def-adts $ (T : -> Type) enum (many Live : -> (T)) (erased Ghost : -> (T)))
(let ((unique c)) (cell-alloc Ghost))
