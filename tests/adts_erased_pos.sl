; DESIGN.md section 14: a `many` constructor may be defined in an erased position.
; expect: 0
(def-fns _ $ (erased peek : (erased (Nat) n) -> (erased (Nat) r))
  (def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) v) -> (Box)))
  n)
(Zero)
