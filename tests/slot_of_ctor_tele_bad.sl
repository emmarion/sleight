; error: `slot-of` in a constructor's telescope cannot name `n`, bound by a telescope still being written
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) n) (many (Eq (Slot) (slot-of n) (slot-of n)) e) -> (Box)))
