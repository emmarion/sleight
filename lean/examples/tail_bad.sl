; a call whose result is then built on is not in tail position
(def-fns _ $ (many count : (subterm many (Nat) n) -> (many (Nat) r))
  (match many n _
    ((Zero) 0)
    ((Succ k) (Succ (tail (count k))))))
(count 2)
