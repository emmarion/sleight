; error: does not satisfy `at`
; As tests/at_field_in_type.sl, the application in the type naming a variable not at the slot.
(def-adts $ (MyNat : -> Type) enum
  (many MyZero : -> (MyNat))
  (many MySucc : (unique (MyNat) pred) -> (MyNat)))
(def-adts $ (State : ((Slot) s) -> Type) enum
  (many MkState : (many (Slot) s) (many (MyNat) w at s) (many (Nat) e) -> (State s)))
(def-fns _ $ (many f : (many (Slot) s) (many (MyNat) w at s) (many (MyNat) v) (many (Nat) e)
    (erased (Eq (State s) (MkState s v e) (MkState s v e)) p) -> (many (Nat) r))
  e)
