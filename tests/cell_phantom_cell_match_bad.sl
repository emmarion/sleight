; error: `Ghost` is phantom, so its cell is used only in an erased position
(def-adts $ (T : -> Type) enum (many Live : -> (T)) (erased Ghost : -> (T)))
(def-fns _ $ (many f : (many (Cell Ghost) u) -> (many (Nat) r))
  (cell-match many u _ (Ghost) 0))
