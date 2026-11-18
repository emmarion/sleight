(def-fns _ $ (many answer : (many (Slot) a) (many (Slot) b) -> (many (Nat) r))
  (match many (slot-eq a b) _ ((ESome _ _) 1) ((ENone _) 0)))
(def-fns _ $ (many run : (many (String) x) -> (many (List (Nat)) out))
  (let ((many y)) (str-append x ""))
  (let ((many z)) (str-append "" x))
  (Cons _ (answer (slot-of x) (slot-of y)) $ Cons _ (answer (slot-of x) (slot-of z)) $ Nil _))
(def-fns _ $ (many main : -> (many (List (Nat)) out)) (run "ab"))
main
