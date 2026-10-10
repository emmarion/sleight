; expect: (MySucc $ MyZero)
; `comptime-match` gives a field written `at` the word of its target as its Const value.
(def-adts $ (MyNat : -> Type) enum
  (many MyZero : -> (MyNat))
  (many MySucc : (unique (MyNat) pred) -> (MyNat)))
(def-adts $ (State : ((Slot) s) -> Type) enum
  (many MkState : (many (Slot) s) (unique (MyNat) n at s) (many (Nat) steps) -> (State s)))
(let ((unique two)) (MySucc (MySucc (MyZero))))
(let ((unique st)) (MkState (slot-of two) two 0))
(comptime-match unique st (MkState s n k u))
(let-match unique n (MySucc p))
(share p)
