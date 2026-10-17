; error: newtype constructors have no cells
(def-adts $ (W : -> Type) enum newtype (many MkW : (many (Nat) n) -> (W)) (erased Ghost : -> (W)))
(let ((erased c)) (cell-alloc MkW))
