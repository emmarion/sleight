; error: type mismatch: expected `(Eq (Slot) (slot-of x) (slot-of w))`
; Two formal slots of erased arguments are equal only where the arguments are, so a `Refl` between them is
; refused here (ASSUMPTIONS 210).
(def-fns _ $ (erased f : (many (Nat) p) -> (erased (slot-of p) is s)) (slot-of p))
(def-fns _ $ (many g : (erased (Nat) x) (erased (Nat) w) -> (many (Nat) r))
  (let ((erased s)) (f x))
  (let ((erased t)) (f w))
  (def-fns _ $ (many h : (erased (Eq (Slot) s t) e) -> (many (Nat) r)) 0)
  (h (Refl _ _)))
