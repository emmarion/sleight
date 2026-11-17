(def-fns _ $ (many answer : (many (Slot) a) (many (Slot) b) -> (many (Nat) r))
  (match many (slot-eq a b) _ ((ESome _ _) 1) ((ENone _) 0)))
(def-fns _ $ (many run : (many (Nat) n) (many (Nat) m) -> (many (List (Nat)) out))
  (let ((many x) (erased _)) (add n 1))
  (let ((many y) (erased _)) (add m 1))
  (Cons _ (answer (slot-of x) (slot-of y)) $ Nil _))
(def-fns _ $ (many main : -> (many (List (Nat)) out)) (run 9223372036854775807 9223372036854775807))
main
