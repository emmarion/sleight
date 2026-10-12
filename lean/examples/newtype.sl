; a newtype's one non-phantom constructor holds one non-erased field
(def-adts $ (Meters : -> Type)
  enum newtype
  (many MkMeters : (many (Nat) m) -> (Meters)))
(def-fns _ $ (many twice : (many (Meters) x) -> (many (Meters) y))
  (let-match many x (MkMeters m))
  (MkMeters (Succ (Succ m))))
(twice (MkMeters 1))
