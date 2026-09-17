; expect: 9
; tests/ackermann.sl with no annotations: the outer call's first subterm argument differs from its
; counterpart, so the inferred proof decreases there; the inner call keeps the first and so decreases the second.

(def-lvl K)
(def-fns K $ many ack : (subterm many (Nat) m) (subterm many (Nat) n) -> (many (Nat) r)
  (match many m _
    ((Zero) (Succ n))
    ((Succ m1)
      (match many n _
        ((Zero) (ack m1 (Succ (Zero))))
        ((Succ n1) (ack m1 (ack m n1)))))))

(ack 2 3)
