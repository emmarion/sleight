; expect: 9
(def-fns _ $ (many get-many-test : -> (many (Nat) result))
  (let ((many a)) (ACons _ _ 4 (ACons _ _ 5 (ANil (Nat)))))
  (let ((many y)) (array-get-many _ _ a (Succ (Zero)) _ (NthThere _ _ _ _ _ (NthHere _ _ _))))
  (let ((many x)) (array-get-many _ _ a (Zero) _ (NthHere _ _ _)))
  (nat-add x y))
get-many-test
; warns: tests/array_get_many.sl:3:20: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:1185:1: note: `;! warn` for `ACons` is here
; warns: tests/array_get_many.sl:3:33: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:1185:1: note: `;! warn` for `ACons` is here
