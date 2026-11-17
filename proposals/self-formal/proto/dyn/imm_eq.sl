(def-fns _ $ (many answer : (many (Slot) a) (many (Slot) b) -> (many (Nat) r))
  (match many (slot-eq a b) _ ((ESome _ _) 1) ((ENone _) 0)))
(def-fns _ $ (many run : (many (Nat) n) -> (many (List (Nat)) out))
  (let ((many x) (erased _)) (add n 2))
  (let ((many y)) 3)
  (Cons _ (answer (slot-of x) (slot-of y)) $ Cons _ (answer (slot-of n) vacant-slot) $ Nil _))
(def-fns _ $ (many main : -> (many (List (Nat)) out)) (run 1))
main
