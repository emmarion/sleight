(def-fns _ $ (many build : (subterm many (Nat) n) (many (List (Nat)) acc) -> (many (List (Nat)) r))
  (match many n _ ((Zero) acc) ((Succ k) (tail $ build k (Cons _ 0 acc)))))
(let ((many xs)) (build 50002 (Nil _)))
(comptime-match many xs (Nil _))
