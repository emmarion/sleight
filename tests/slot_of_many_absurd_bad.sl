; error: is not refuted: it may be headed by `Refl`
; The `many` image of tests/slot_of_erased_absurd_bad.sl, refused alike: slots say nothing about contents.
(def-fns _ $ (erased f : (many (Nat) p) -> (erased (slot-of p) is s)) (slot-of p))
(def-fns _ $ (many g : (many (Zero) is a) (erased (Nat) k) (many (Succ k) is b) -> (many (Nat) r))
  (let ((erased s)) (f a))
  (let ((erased t)) (f b))
  (def-fns _ $ (many absurd h : (erased (Eq (Slot) s t) e) -> (many (Nat) r)) e)
  0)
