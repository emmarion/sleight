; expect: (MkState _ (MySucc $ MyZero) 0)
; Applications of a constructor with a field written `at` inside types: in an `is` return, in an `Eq` index
; over sibling parameters, and over `(slot-of n)`, whose argument is bound first.
(def-adts $ (MyNat : -> Type) enum
  (many MyZero : -> (MyNat))
  (many MySucc : (unique (MyNat) pred) -> (MyNat)))
(def-adts $ (State : ((Slot) s) -> Type) enum
  (many MkState : (many (Slot) s) (many (MyNat) w at s) (many (Nat) e) -> (State s)))
(def-fns _ $ (many f : (many (Slot) s) (many (MyNat) w at s) (many (Nat) e)
    (erased (Eq (State s) (MkState s w e) (MkState s w e)) p) -> (many (MkState s w e) is st))
  (MkState s w e))
(let ((many n)) (MySucc (MyZero)))
(let ((erased q)) (Refl (State (slot-of n)) (MkState (slot-of n) n 0)))
(f (slot-of n) n 0 (Refl _ _))
