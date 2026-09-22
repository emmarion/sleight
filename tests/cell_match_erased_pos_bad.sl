; error: cell-match in an erased position
(def-adts $ Box : -> Type enum (many MkBox : (many (Nat) v) -> (Box)))
(def-fns _ $ erased peek : (erased (Nat) z) -> (erased (Nat) r)
  (let (unique c) (cell-alloc MkBox))
  (cell-match many c (((Nat) s)) (MkBox sl) z))
(Zero)
