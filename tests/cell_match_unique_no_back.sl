; expect: 1
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) n) -> (Box)))
(def-fns _ $ (many drop : (unique (Cell MkBox vacant-slot) u) -> (many (Nat) r))
  (cell-match unique u _ (MkBox s) 1))
(drop (cell-alloc MkBox))
