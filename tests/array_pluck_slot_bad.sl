; error: value mismatch
; A plucked element is left Uninit over the opaque Slot array-pluck returns, which is not known vacant:
; the old word may still be in the array.

(def-fns _ $ (many leak-test : -> (many (Nat) result))
  (let ((unique a) (erased all)) (array-new (Nat) (Succ (Zero))))
  (let-match erased all (AUCons _ _ _ q))
  (let ((unique old) (unique b) (erased set)) (array-swap _ _ a (Zero) (Init _ (Succ (Zero))) _ (NthZ _ _ _ _)))
  (let-match erased set (SetZ _ _ _ _ _))
  (let ((unique v) (unique c) (erased s) (erased cleared)) (array-pluck _ _ b (Zero) _ (NthZ _ _ _ _)))
  (let-match erased cleared (SetZ _ _ _ _ _))
  (let ((unique (Uninit (Nat) (SlotVacant)) is gone) (unique d) (erased set2))
    (array-swap _ _ c (Zero) (Init _ (Zero)) _ (NthZ _ _ _ _)))
  (let-match unique v (Init _ x))
  (share x))
leak-test
