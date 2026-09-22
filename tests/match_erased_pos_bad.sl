; error: a match in an erased position is written erased
(def-adts $ Box : -> Type enum (many MkBox : (many (Nat) v) -> (Box)))
(def-fns _ $ erased peek : (erased (Box) b) -> (erased (Nat) r)
  (match unique b _
    ((MkBox v cell) v)))
(Zero)
