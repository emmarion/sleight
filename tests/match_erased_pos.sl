; expect: 0
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) v) -> (Box)))
(def-fns _ $ (erased peek : (erased (Box) b) -> (erased (Nat) r))
  (match erased b _
    ((MkBox v) v)))
(def-fns _ $ (many run : (many (Box) _b) -> (many (Nat) r)) (Zero))
(run (MkBox (Zero)))
