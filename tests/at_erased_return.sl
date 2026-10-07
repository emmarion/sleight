; expect: 0
; An erased return written `at`: the promise is a slot rule, verified at the return and placing the caller's
; erased binder (section 36).
(def-fns _ $ (many f : (many (Nat) x) -> (erased (Nat) r at x)) x)
(def-fns _ $ (many g : (many (Nat) a) -> (many (Nat) z))
  (let ((erased r)) (f a))
  (let ((erased (Eq (Slot) (slot-of r) (slot-of a)) e)) (Refl _ _))
  0)
(g 1)
