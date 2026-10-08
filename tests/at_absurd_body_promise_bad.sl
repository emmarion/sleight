; error: return does not satisfy `at` `(slot-of a)`
; Code inside an absurd body obeys the `at` rules (section 36).
(def-fns _ $ (many absurd boom : (many (Nat) a) (many (Nat) b) (many (False) f) -> (many (Nat) r))
  (let ((erased r) (erased p))
    (match erased b (((Nat) r at a) ((Eq (Slot) (slot-of r) (slot-of b)) p))
      (else (values b (Refl _ (slot-of b))))))
  f)
0
