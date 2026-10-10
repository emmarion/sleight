; expect: (MkState _ (MySucc $ MySucc $ MyZero) 0)
; A printed value with a field written `at`: the slot prints `_`, the field by its type from its target's word.
(def-adts $ (MyNat : -> Type) enum
  (many MyZero : -> (MyNat))
  (many MySucc : (unique (MyNat) pred) -> (MyNat)))
(def-adts $ (State : ((Slot) s) -> Type) enum
  (many MkState : (many (Slot) s) (unique (MyNat) n at s) (many (Nat) steps) -> (State s)))
(let ((unique two)) (MySucc (MySucc (MyZero))))
(let ((unique st)) (MkState (slot-of two) two 0))
(share st)
