(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) v) -> (Box)))
(let ((many z)) (MkBox 5))
(let ((many r)) (slot-eq (slot-of z) (slot-of z)))
(comptime-match many r (ESome _ e))
7
