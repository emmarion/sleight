; expect: 7
(def-fns _ $ (many initialize-test : -> (many (Nat) result))
  (let ((erased xs) (unique a) (erased all)) (array-new (Nat) (Succ (Succ (Zero)))))
  (let-match erased all (RepeatCons _ _ _ _ q))
  (let-match erased q (RepeatCons _ _ _ _ nil))
  (let-match erased nil (RepeatNil _ _))
  (let ((erased b-ix) (unique b) (erased p))
    (array-place _ _ a (Zero) (Init _ (Succ (Succ (Succ (Zero))))) _ (NthHere _ _ _)))
  (let-match erased p (SetHere _ _ _ _))
  (let ((erased c-ix) (unique c) (erased p2))
    (array-place _ _ b (Succ (Zero)) (Init _ (Succ (Succ (Succ (Succ (Zero)))))) _
      (NthThere _ _ _ _ _ (NthHere _ _ _))))
  (let-match erased p2 (SetThere _ _ _ _ _ _ q2))
  (let-match erased q2 (SetHere _ _ _ _))
  (let ((erased raw) (erased witness))
    (init-witness _ _ _ c (AICons _ _ _ _ (AICons _ _ _ _ (AINil _)))))
  (let ((unique initialized)) (coerce c witness))
  (let-match unique initialized (ACons _ _ x rest))
  (let-match unique rest (ACons _ _ y end))
  (nat-add (share x) (share y)))
initialize-test
; warns: tests/array_initialize.sl:18:3: warning: match on `Array`: copies the array's tail, O(n); read with `array-get` and `array-length`, or their `-many` forms at many
; warns: lib/prelude.sl:1015:1: note: `;! warn` for `Array` is here
; warns: tests/array_initialize.sl:19:3: warning: match on `Array`: copies the array's tail, O(n); read with `array-get` and `array-length`, or their `-many` forms at many
; warns: lib/prelude.sl:1015:1: note: `;! warn` for `Array` is here
