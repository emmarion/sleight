(def-fns _ $ (many same : (many (Slot) a) (many (Slot) b) -> (many (Bool) r))
  (match many (slot-eq a b) _ ((ESome _ _) (BTrue)) ((ENone _) (BFalse))))
(def-fns _ $ (many probe : -> (many (Bool) r))
  (let ((many x) (erased _)) (add 1 2))
  (let ((many y)) 3)
  (same (slot-of x) (slot-of y)))
(let ((many r)) (native-compute probe))
(comptime-match many r (BTrue))
r
