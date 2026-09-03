; expect: (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))))))
; Ackermann under the lexicographic order: the outer call decreases the first subterm argument and leaves
; the second unconstrained, the inner call keeps the first and decreases the second.

(def-lvl K)
(def-fns K $ many ack : (subterm many (Nat) m) (subterm many (Nat) n) -> (many (Nat) r)
  (match many m _
    ((Zero) (Succ n))
    ((Succ m1)
      (match many n _
        ((Zero) (ack (subterm (prove-subterm m1 m)) m1 (Succ (Zero))))
        ((Succ n1) (ack (subterm (prove-subterm m1 m)) m1 (ack m (subterm (prove-subterm n1 n)) n1)))))))

(ack 2 3)
