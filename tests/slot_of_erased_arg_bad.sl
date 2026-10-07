; error: type mismatch: expected `(Eq (Slot) s t)`
; The slots of two distinct erased arguments are two atoms, so a `Refl` between them is refused (section 35).
(def-fns _ $ (erased f : (many (Nat) p) -> (erased (slot-of p) is s)) (slot-of p))
(def-fns _ $ (many g : (erased (Nat) x) (erased (Nat) w) -> (many (Nat) r))
  (let ((erased s)) (f x))
  (let ((erased t)) (f w))
  (def-fns _ $ (many h : (erased (Eq (Slot) s t) e) -> (many (Nat) r)) 0)
  (h (Refl _ _)))
