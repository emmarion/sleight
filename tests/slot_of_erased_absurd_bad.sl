; error: is not refuted: it may be headed by `Refl`
; Equating the erased slots of two erased arguments says nothing about the arguments (AT_REDESIGN A2), so no
; contradiction follows from their values differing; the same program with the arguments `many` is
; tests/slot_of_many_absurd_bad.sl.
(def-fns _ $ (erased f : (many (Nat) p) -> (erased (slot-of p) is s)) (slot-of p))
(def-fns _ $ (many g : (erased (Nat) k) -> (many (Nat) r))
  (let ((erased s)) (f (Zero)))
  (let ((erased t)) (f (Succ k)))
  (def-fns _ $ (many absurd h : (erased (Eq (Slot) s t) e) -> (many (Nat) r)) e)
  0)
