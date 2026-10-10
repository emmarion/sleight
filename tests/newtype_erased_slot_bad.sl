; error: type mismatch: expected `(Eq (Slot) (slot-of w) (slot-of a))`
; An erased newtype application over `(Succ a)` is not at `a` (section 37).
(def-adts $ (W : -> Type) enum newtype (many MkW : (many (Nat) n) -> (W)))
(def-fns _ $ (many f : (many (Nat) a) -> (many (Nat) r))
  (let ((erased w)) (MkW (Succ a)))
  (let ((erased (Eq (Slot) (slot-of w) (slot-of a)) e)) (Refl _ _))
  0)
