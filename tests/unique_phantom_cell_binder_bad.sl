; error: Ghost has 0 fields
(def-adts $ (T : -> Type) enum (many Live : -> (T)) (erased Ghost : -> (T)))
(def-fns _ $ (many choose : (unique (T) t) -> (many (Nat) r))
  (match unique t _
    ((Live cell) (Succ (Zero)))
    ((Ghost cell) (Zero))))
