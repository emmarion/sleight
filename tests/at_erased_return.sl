; expect: 0
; An erased return written `at`: the promise is a slot rule, verified at the return and placing the caller's
; erased binder (section 36).
(def-fns _ $ (many f : (many (Nat) _x) -> (erased (Nat) r at _x)) _x)
(def-fns _ $ (many g : (many (Nat) _a) -> (many (Nat) z))
  (let ((erased r)) (f _a))
  (let ((erased (Eq (Slot) (slot-of r) (slot-of _a)) _)) (Refl _ _))
  0)
(g 1)
