; error: `slot-of` in a constructor's telescope cannot name `x`, bound by a telescope still being written
(def-adts $ (T : ((Slot) s) -> Type) enum (many C : (many (Nat) x) -> (T (slot-of x))))
