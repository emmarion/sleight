; expect: (MkB $ Refl _ _)
; `slot-of` of a variable that no telescope binds, in a field's type.
(let ((many n)) 1)
(def-adts $ (B : -> Type) enum (many MkB : (many (Eq (Slot) (slot-of n) (slot-of n)) e) -> (B)))
(MkB (Refl _ _))
