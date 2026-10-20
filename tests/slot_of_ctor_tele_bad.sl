; error: `slot-of` cannot name `n`, an entry of a constructor's telescope still being written
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) n) (many (Eq (Slot) (slot-of n) (slot-of n)) e) -> (Box)))
