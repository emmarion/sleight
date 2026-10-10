; error: does not satisfy `at`
(def-adts $ (MyNat : -> Type) enum
  (many MyZero : -> (MyNat))
  (many MySucc : (unique (MyNat) pred) -> (MyNat)))
(def-adts $ (State : ((Slot) s) -> Type) enum
  (many MkState : (many (Slot) s) (unique (MyNat) n at s) (many (Nat) steps) -> (State s)))
(let ((unique a)) (MyZero))
(let ((unique b)) (MyZero))
(let ((unique st)) (MkState (slot-of a) b 0))
(share st)
