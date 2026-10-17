; expect: 1
; Newtype placement in erased code (section 37): an erased destructure puts the field at the scrutinee,
; and an erased application is at its argument.
(def-adts $ (W : -> Type) enum newtype (many MkW : (many (Nat) n) -> (W)))
(def-fns _ $ (many f : (many (W) _w) -> (many (Nat) r))
  (let ((erased _)) (match erased _w (((Eq (Slot) (slot-of _w) (slot-of _w)) p)) ((MkW n) (Refl _ (slot-of n)))))
  0)
(def-fns _ $ (many g : (many (Nat) a) (erased (W) _w at a) -> (many (Nat) r)) a)
(def-fns _ $ (many h : (many (Nat) a) -> (many (Nat) r))
  (let ((erased w)) (MkW a))
  (g a w))
(h 1)
