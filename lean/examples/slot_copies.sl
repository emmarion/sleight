(def-fns _ $ (many fu : (unique (Slot) s) -> (many (Nat) r)) 0)
(def-fns _ $ (many fm : (many (Slot) s) -> (many (Nat) r)) 0)
(let ((many x)) 3)
(let ((many a)) (fm (slot-of x)))
(let ((many b)) (fu (slot-of x)))
(let ((many c)) (fm (slot-of x)))
0
