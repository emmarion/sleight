; expect: 0
; `slot-of` on an erased variable is an erased term (section 35): a parameter's slot named in a signature,
; and the slot of an erased binder forwarding a variable, which is that variable's (section 35).
(def-fns _ $ (many f : (erased (Nat) p) -> (erased (slot-of p) is s)) (slot-of p))
(def-fns _ $ (many g : (erased (Nat) x) -> (many (Nat) z))
  (let ((erased s)) (f x))
  (let ((erased (Eq (Slot) s (slot-of x)) e)) (Refl _ _))
  (let ((erased y)) x)
  (let ((erased (Eq (Slot) (slot-of y) (slot-of x)) e2)) (Refl _ _))
  0)
(g 1)
