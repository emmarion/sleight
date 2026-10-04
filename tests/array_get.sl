; expect: 9
(def-fns _ $ (many get-test : -> (many (Nat) result))
  (let ((unique a))
    (ACons _ _ (MkCopy _ (Succ (Succ (Succ (Succ (Zero))))))
      (ACons _ _ (MkCopy _ (Succ (Succ (Succ (Succ (Succ (Zero))))))) (ANil (Copy (Nat))))))
  (let ((many y) (unique b)) (array-get _ _ a (Succ (Zero)) _ (NthS _ _ _ _ _ _ (NthZ _ _ _ _))))
  (let ((many x) (unique c)) (array-get _ _ b (Zero) _ (NthZ _ _ _ _)))
  (nat-add x y))
get-test
; warns: tests/array_get.sl:4:6: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:868:1: note: `;! warn` for `ACons` is here
; warns: tests/array_get.sl:5:8: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:868:1: note: `;! warn` for `ACons` is here
