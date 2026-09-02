; needs: list
; expect: (Succ (Succ (Zero)))
; A subterm parameter pinned by is: the recursive call decreases through the pinned structure.

(def-lvl X)
(def-fns X $ many count : (many (Nat) n) (subterm many (Succ n) is m) -> (many (Nat) r)
  (match many n (((Nat) r))
    ((Zero) m)
    ((Succ k)
      (let (erased p) (prove-subterm n m))
      (count k (subterm p) n))))
(count (Succ (Zero)) (Succ (Succ (Zero))))
