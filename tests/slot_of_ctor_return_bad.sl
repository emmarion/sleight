; error: `slot-of` cannot name `x`, an entry of a constructor's telescope still being written
(def-adts $ (T : ((Slot) s) -> Type) enum (many C : (many (Nat) x) -> (T (slot-of x))))
