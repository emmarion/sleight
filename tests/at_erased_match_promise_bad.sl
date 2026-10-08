; error: return does not satisfy `at` `(slot-of a)`
; The `at` entry of an erased match is checked (section 14), as in tests/at_erased_fn_promise_bad.sl.
(def-fns _ $ (many id2 : (many (Nat) x) (many (Nat) y at x) -> (many (Nat) r)) y)
(def-fns _ $ (many go : (many (Nat) a) (many (Nat) b) -> (many (Nat) r))
  (let ((erased r) (erased p))
    (match erased b (((Nat) r at a) ((Eq (Slot) (slot-of r) (slot-of b)) p))
      (else (values b (Refl _ (slot-of b))))))
  (let-match erased p (Refl _ _))
  (id2 a b))
(go 1 2)
