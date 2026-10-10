; error: `at` cannot mark an argument written `at`
(def-adts $ (MyNat : -> Type) enum
  (many MyZero : -> (MyNat))
  (many MySucc : (unique (MyNat) pred) -> (MyNat)))
(def-adts $ (State : ((Slot) s) -> Type) enum
  (many MkState : (many (Slot) s) (unique (MyNat) n at s) (many (Nat) steps) -> (State s)))
(let ((unique a)) (MyZero))
(let ((unique u)) (cell-alloc MkState))
(let ((unique st)) (u (slot-of a) (at) a 0))
(share st)
