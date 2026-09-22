; error: type mismatch
(def-adts $ (Box : -> Type) enum (many B : (many (Nat) n) -> (Box)))
(let ((unique x)) (B (Zero)))
(let ((unique y)) (B (Zero)))
(let ((erased (Eq (Slot) (SlotHolds x) (SlotHolds y)) bad))
  (Refl (Slot) (SlotHolds x)))
