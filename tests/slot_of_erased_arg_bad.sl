; error: type mismatch: expected `(Eq (Slot) (slot-of x) (slot-of w))`
; Two slots of distinct erased arguments are not equal, so a `Refl` between them is refused here; the message
; spells them as the formal terms the code binds today, before AT_REDESIGN A2's erased slots (HANDOFF).
(def-fns _ $ (erased f : (many (Nat) p) -> (erased (slot-of p) is s)) (slot-of p))
(def-fns _ $ (many g : (erased (Nat) x) (erased (Nat) w) -> (many (Nat) r))
  (let ((erased s)) (f x))
  (let ((erased t)) (f w))
  (def-fns _ $ (many h : (erased (Eq (Slot) s t) e) -> (many (Nat) r)) 0)
  (h (Refl _ _)))
