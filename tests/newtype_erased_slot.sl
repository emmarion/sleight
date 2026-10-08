; expect: 0
; An erased newtype application over a non-variable argument (section 37) gives its binder a slot that
; nothing else names, as at `many`: equal to itself and to a field destructured from it, in both modes.
(def-adts $ (W : -> Type) enum newtype (many MkW : (many (Nat) n) -> (W)))
(def-fns _ $ (many f : (many (Nat) a) -> (many (Nat) r))
  (let ((erased w)) (MkW (Succ a)))
  (let ((erased (Eq (Slot) (slot-of w) (slot-of w)) e)) (Refl _ _))
  (let-match erased w (MkW n))
  (let ((erased (Eq (Slot) (slot-of n) (slot-of w)) e2)) (Refl _ _))
  (let ((many v)) (MkW (Succ a)))
  (let ((erased (Eq (Slot) (slot-of v) (slot-of v)) e3)) (Refl _ _))
  (let-match many v (MkW m))
  (let ((erased (Eq (Slot) (slot-of m) (slot-of v)) e4)) (Refl _ _))
  0)
(f 1)
