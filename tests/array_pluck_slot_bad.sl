; error: value mismatch
; A plucked element is left Uninit over the element's own slot (section 44), which is not known vacant:
; the old word may still be in the array.

(def-fns _ $ (many leak-test : -> (many (Nat) result))
  (let ((erased xs) (unique a) (erased all)) (array-new (Nat) (Succ (Zero))))
  (let-match erased all (RepeatCons _ _ _ _ q))
  (let ((unique old) (erased b-ix) (unique b) (erased set)) (array-swap _ _ a (Zero) (Init _ (Succ (Zero))) _ (NthHere _ _ _)))
  (let-match erased set (SetHere _ _ _ _))
  (let ((unique v) (erased c-ix) (unique c) (erased cleared)) (array-pluck _ _ b (Zero) _ (NthHere _ _ _)))
  (let-match erased cleared (SetHere _ _ _ _))
  (let ((unique (Uninit (Nat) vacant-slot) is gone) (erased d-ix) (unique d) (erased set2))
    (array-swap _ _ c (Zero) (Init _ (Zero)) _ (NthHere _ _ _)))
  (let-match unique v (Init _ x))
  (share x))
leak-test
