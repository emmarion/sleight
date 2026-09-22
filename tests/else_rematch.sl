; expect: 1
; An else forces no facts, so a match on the same scrutinee inside it keeps every branch.

(def-lvl X)

(def-fns X $ (many pred : (many (Nat) n) -> (many (Nat) m))
  (match many n (((Nat) r))
    ((Zero) (Zero))
    (else
      (match many n (((Nat) r2))
        ((Zero) (Zero))
        ((Succ j) j)))))

(pred (Succ (Succ (Zero))))
