(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) v) -> (Box)))
(def-fns _ $ (many answer : (many (Slot) a) (many (Slot) b) -> (many (Nat) r))
  (match many (slot-eq a b) _ ((ESome _ _) 1) ((ENone _) 0)))
(let ((many a)) (MkBox 5))
(let ((many b)) (MkBox 5))
(def-fns _ $ (many main : -> (many (Nat) out)) (answer (slot-of a) (slot-of b)))
main
