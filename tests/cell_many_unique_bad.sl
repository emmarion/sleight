; error: a cell at `many` mints its value only at `many`
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) n) -> (Box)))
(def-fns _ $ (many steal : (many (Box) b) -> (unique (Box) r))
  (let-match many b (MkBox n u))
  (at (u n)))
(steal (MkBox 1))
