; expect: (MkState _ (MySucc $ MySucc $ MySucc $ MyZero) 1)
; The cells of a constructor with a field written `at`: a `cell-write` with one item per stored field, a
; reinvocation with every store skipped, and a `cell-match` with one binder per stored field.
(def-adts $ (MyNat : -> Type) enum
  (many MyZero : -> (MyNat))
  (many MySucc : (unique (MyNat) pred) -> (MyNat)))
(def-adts $ (State : ((Slot) s) -> Type) enum
  (many MkState : (many (Slot) s) (unique (MyNat) n at s) (many (Nat) steps) -> (State s)))
(def-fns _ $ (many bump-nat : (unique (MyNat) n) -> (unique (MyNat) r at n))
  (match unique n _
    ((MyZero u0) (u0))
    ((MySucc p u2) (u2 (MySucc p)))))
(def-fns _ $ (many step : (erased (Slot) s) (unique (State s) st) -> (unique (State s) st2 at st))
  (let-match unique st (MkState s2 n k u))
  (let ((unique n2)) (bump-nat n))
  (let ((many k2)) (Succ k))
  (let ((unique u2)) (cell-write unique u (MkState _ (slot-of k2))))
  (at (u2 s2 n2 k2)))
(def-fns _ $ (many through : (erased (Slot) s) (unique (State s) st) -> (unique (State s) st2 at st))
  (let-match unique st (MkState s2 n k u))
  (cell-match unique u _ (MkState a b u2)
    (at (u2 s2 n k))))
(let ((unique two)) (MySucc (MySucc (MyZero))))
(let ((unique st)) (MkState (slot-of two) two 0))
(let ((unique st2)) (step _ st))
(let ((unique st3)) (through _ st2))
(share st3)
