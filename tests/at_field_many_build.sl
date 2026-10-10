; expect: (MySucc $ MySucc $ MyZero)
; Building at `many` a constructor whose field written `at` is labelled `unique`: the argument is taken at
; `many` (section 22), and a destructure at `many` hands the field out at `many`.
(def-adts $ (MyNat : -> Type) enum
  (many MyZero : -> (MyNat))
  (many MySucc : (unique (MyNat) pred) -> (MyNat)))
(def-adts $ (State : ((Slot) s) -> Type) enum
  (many MkState : (many (Slot) s) (unique (MyNat) n at s) (many (Nat) steps) -> (State s)))
(let ((many two)) (MySucc (MySucc (MyZero))))
(let ((many st)) (MkState (slot-of two) two 0))
(let-match many st (MkState s n k))
n
