(let ((many a)) (str-append "a" "b"))
(let ((many b)) (str-append "a" "b"))
(def-fns _ $ (many main : -> (many (Bool) r))
  (match many (slot-eq (slot-of a) (slot-of b)) _ ((ESome _ _) (BTrue)) ((ENone _) (BFalse))))
main
