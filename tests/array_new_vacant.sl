; expect: 1
; array-new's Repeat proof says each element is Uninit over a vacant slot, so swapping a value in hands
; back an Uninit known to hold vacant-slot.

(def-fns _ $ (many vacant-test : -> (many (Nat) result))
  (let ((erased xs) (unique a) (erased all)) (array-new (Nat) (Succ (Zero))))
  (let-match erased all (RepeatCons _ _ _ _ q))
  (let ((unique (Uninit (Nat) vacant-slot) is old) (erased b-ix) (unique b) (erased set))
    (array-swap _ _ a (Zero) (Init _ (Succ (Zero))) _ (NthHere _ _ _)))
  (let-match erased set (SetHere _ _ _ _))
  (let ((unique v) (erased c-ix) (unique c) (erased p)) (array-pluck _ _ b (Zero) _ (NthHere _ _ _)))
  (let-match unique v (Init _ x))
  (share x))
vacant-test
