; expect: 0
; A constructor application as the erased argument of a parameter whose slot the signature names is bound
; first (U2a), so each call's slot is the atom of a binder of its own (AT_REDESIGN A2).
(def-fns _ $ (erased f : (many (Nat) p) -> (erased (slot-of p) is s)) (slot-of p))
(def-fns _ $ (many g : (erased (Nat) k) -> (many (Nat) r))
  (let ((erased s)) (f (Succ k)))
  (let ((erased (Eq (Slot) s s) e)) (Refl _ _))
  0)
(g 1)
