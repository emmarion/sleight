; tail and notail (DESIGN.md section 19) claim where a call sits after erasure
(def-fns _ $ (many count : (subterm many (Nat) n) (many (Nat) acc) -> (many (Nat) r))
  (match many n _
    ((Zero) acc)
    ((Succ k) (tail (count k (Succ acc))))))
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (let ((many r)) (notail (count n 1)))
  (Succ r))
(inc 2)
