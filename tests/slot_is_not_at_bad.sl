; error: type mismatch
(def-adts $ (Box : -> Type) enum (many B : (many (Nat) n) -> (Box)))
(let ((unique x)) (B (Zero)))
(let ((unique y)) (B (Zero)))
(let ((erased (Eq (Slot) (slot-of x) (slot-of y)) bad))
  (Refl (Slot) (slot-of x)))
