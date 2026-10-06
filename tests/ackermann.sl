; expect: 9
; Ackermann under the lexicographic order: the outer call decreases the first subterm argument and leaves
; the second unconstrained, the inner call keeps the first and decreases the second.

(def-lvl K)
(def-fns K $ (many ack : (subterm many (Nat) m) (subterm many (Nat) n) -> (many (Nat) r))
  (let-match many m (Succ m1) ((Zero) (Succ n)))
  (match many n _
    ((Zero) (tail $ ack (subterm (prove-subterm m1 m)) m1 (Succ (Zero))))
    ((Succ n1) (tail $ ack (subterm (prove-subterm m1 m)) m1 (notail $ ack m (subterm (prove-subterm n1 n)) n1)))))

(ack 2 3)
; warns: tests/ackermann.sl:9:25: warning: unnecessary `(subterm _)`; drop it
; warns: tests/ackermann.sl:10:78: warning: unnecessary `(subterm _)`; drop it
; warns: tests/ackermann.sl:10:28: warning: unnecessary `(subterm _)`; drop it
