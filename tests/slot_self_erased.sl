; expect: 0
; `slot-self` on an erased `(Slot)` (section 35).
(def-fns _ $ (many f : (erased (Slot) s) -> (many (Nat) r))
  (slot-self s)
  (let ((erased (Eq (Slot) (slot-of s) s) _)) (Refl _ _))
  0)
(f vacant-slot)
