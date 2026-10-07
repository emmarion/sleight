; error: `slot-of` cannot appear in a constructor's telescope
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) n) (many (Eq (Slot) (slot-of n) (slot-of n)) e) -> (Box)))
