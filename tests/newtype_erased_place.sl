; expect: 1
; Newtype placement in erased code (section 37): an erased destructure puts the field at the scrutinee,
; and an erased application is at its argument.
(def-adts $ (W : -> Type) enum newtype (many MkW : (many (Nat) n) -> (W)))
(def-fns _ $ (many f : (many (W) w) -> (many (Nat) r))
  (let ((erased p)) (match erased w (((Eq (Slot) (slot-of w) (slot-of w)) p)) ((MkW n) (Refl _ (slot-of n)))))
  0)
(def-fns _ $ (many g : (many (Nat) a) (erased (W) w at a) -> (many (Nat) r)) a)
(def-fns _ $ (many h : (many (Nat) a) -> (many (Nat) r))
  (let ((erased w)) (MkW a))
  (g a w))
(h 1)
