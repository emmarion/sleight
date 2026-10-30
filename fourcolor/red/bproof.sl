; Birkhoff2 to Birkhoff5 of birkhoff.v: the Birkhoff checks for rings of 2 to 5 faces, with Coq's iteration counts and basis
; programs, by the certified check of bcheck.sl run under native-compute, as birkhoff-proof. Load after bcheck.sl.

(def-fns _ $ (many j2 : -> (many (Chk (BirkhoffCheck (Zero) (Zero))) r))
  (birkhoff-check-c (Zero) (Zero) (Succ (Zero)) (Cons _ (Nil _) $ Nil _)))

(def-fns _ $ (many j3 : -> (many (Chk (BirkhoffCheck (Succ (Zero)) (Zero))) r))
  (birkhoff-check-c (Succ (Zero)) (Zero) (Succ (Zero)) (Cons _ (Cons _ (SY) $ Nil _) $ Nil _)))

(def-fns _ $ (many j4 : -> (many (Chk (BirkhoffCheck (Succ (Succ (Zero))) (Zero))) r))
  (birkhoff-check-c (Succ (Succ (Zero))) (Zero) 4 (Cons _ (Cons _ (SU) $ Nil _) $ Cons _ (Cons _ (SR 1) $ Cons _ (SU) $ Nil _) $ Nil _)))

(def-fns _ $ (many j5 : -> (many (Chk (BirkhoffCheck (Succ (Succ (Succ (Zero)))) (Succ (Zero)))) r))
  (birkhoff-check-c (Succ (Succ (Succ (Zero)))) (Succ (Zero)) 10
    (Cons _ (Cons _ (SU) $ Cons _ (SY) $ Nil _) $ Cons _ (Cons _ (SR 1) $ Cons _ (SU) $ Cons _ (SY) $ Nil _)
      $ Cons _ (Cons _ (SR 2) $ Cons _ (SU) $ Cons _ (SY) $ Nil _) $ Cons _ (Cons _ (SR 3) $ Cons _ (SU) $ Cons _ (SY) $ Nil _)
      $ Cons _ (Cons _ (SR 4) $ Cons _ (SU) $ Cons _ (SY) $ Nil _) $ Cons _ (Cons _ (SH) $ Cons _ (SR 4) $ Cons _ (SY) $ Cons _ (SY) $ Cons _ (SY) $ Nil _)
      $ Nil _)))

(let ((many r2) (many r3) (many r4) (many r5)) (native-compute j2 j3 j4 j5))
(comptime-match many r2 (CkY _ p2))
(comptime-match many r3 (CkY _ p3))
(comptime-match many r4 (CkY _ p4))
(comptime-match many r5 (CkY _ p5))

(let ((erased birkhoff-proof)) (MkBirkhoffChecks p2 p3 p4 p5))
