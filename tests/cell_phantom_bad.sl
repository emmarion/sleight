; error: phantom constructor cannot be invoked
(def-adts $ T : -> Type enum (many Live : -> (T)) (erased Ghost : -> (T)))
(let (unique c) (cell-alloc Ghost))
(c)
