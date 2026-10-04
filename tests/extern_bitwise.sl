; expect: (Cons _ 8 $ Cons _ 14 $ Cons _ 6 $ Cons _ 5 $ Cons _ 0 $ Cons _ 65 $ Nil _)
; Nat bitwise operations: one Bitwise relation indexed by a truth table, and-op, or-op and xor-op being three.

(let ((many r1) (erased q1)) (nat-and 12 10))
(let ((many r2) (erased q2)) (nat-or 12 10))
(let ((many r3) (erased q3)) (nat-xor 12 10))
(let ((many r4) (erased q4)) (nat-xor 0 5))
(let ((many r5) (erased q5)) (nat-and 255 0))
(let ((many r6) (erased q6)) (nat-or 1 64))
(Cons _ r1 $ Cons _ r2 $ Cons _ r3 $ Cons _ r4 $ Cons _ r5 $ Cons _ r6 $ Nil _)
