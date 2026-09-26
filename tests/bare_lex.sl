; expect: 9
; tests/ackermann.sl with no annotations: the outer call's first subterm argument differs from its
; counterpart, so the inferred proof decreases there; the inner call keeps the first and so decreases the second.

(def-lvl K)
(def-fns K $ (many ack : (subterm many (Nat) m) (subterm many (Nat) n) -> (many (Nat) r))
  (let-match many m (Succ m1) ((Zero) (Succ n)))
  (match many n _
    ((Zero) (tail $ ack m1 (Succ (Zero))))
    ((Succ n1) (tail $ ack m1 (notail $ ack m n1)))))

(ack 2 3)
