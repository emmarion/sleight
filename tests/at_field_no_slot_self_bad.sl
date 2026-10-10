; error: return does not satisfy `at`
; tests/at_field_thread.sl without the `slot-self`: the field is at the slot binder's own slot, not at `n`.
(def-adts $ (MyNat : -> Type) enum
  (many MyZero : -> (MyNat))
  (many MySucc : (unique (MyNat) pred) -> (MyNat)))
(def-adts $ (State : ((Slot) s) -> Type) enum
  (many MkState : (many (Slot) s) (unique (MyNat) n at s) (many (Nat) steps) -> (State s)))
(def-fns _ $ (many bump : (unique (MyNat) n) -> (unique (MyNat) r at n))
  (let ((unique st)) (MkState (slot-of n) n 0))
  (let-match unique st (MkState s n2 k))
  n2)
(let ((unique two)) (MySucc (MySucc (MyZero))))
(let ((unique r)) (bump two))
(share r)
