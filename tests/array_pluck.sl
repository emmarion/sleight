; expect: 9
(def-fns _ $ (many pluck-test : -> (many (Nat) result))
  (let ((unique a))
    (ACons _ _ (Init _ (Succ (Succ (Succ (Succ (Zero))))))
      (ACons _ _ (Init _ (Succ (Succ (Succ (Succ (Succ (Zero))))))) (ANil (MaybeUninit (Nat))))))
  (let ((unique item) (erased _) (unique b) (erased cleared))
    (array-pluck _ _ a (Succ (Zero)) _ (NthThere _ _ _ _ _ (NthHere _ _ _))))
  (let-match unique item (Init _ value))
  (let-match erased cleared (SetThere _ _ _ _ _ _ step))
  (let-match erased step (SetHere _ _ _ _))
  (let ((erased _) (unique c) (erased restored))
    (array-place _ _ b (Succ (Zero)) (Init _ value) _
      (NthThere _ _ _ _ _ (NthHere _ _ _))))
  (let-match erased restored (SetThere _ _ _ _ _ _ step2))
  (let-match erased step2 (SetHere _ _ _ _))
  (let ((erased _) (erased witness))
    (init-witness _ _ _ c (AICons _ _ _ _ (AICons _ _ _ _ (AINil _)))))
  (let ((unique initialized)) (coerce c witness))
  (let-match unique initialized (ACons _ _ x rest))
  (let-match unique rest (ACons _ _ y _))
  (nat-add (share x) (share y)))
pluck-test
; warns: tests/array_pluck.sl:4:6: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:1170:1: note: `;! warn` for `ACons` is here
; warns: tests/array_pluck.sl:5:8: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:1170:1: note: `;! warn` for `ACons` is here
; warns: tests/array_pluck.sl:19:3: warning: match on `Array`: copies the array's tail, O(n); read with `array-get` and `array-length`, or their `-many` forms at many
; warns: lib/prelude.sl:1171:1: note: `;! warn` for `Array` is here
; warns: tests/array_pluck.sl:20:3: warning: match on `Array`: copies the array's tail, O(n); read with `array-get` and `array-length`, or their `-many` forms at many
; warns: lib/prelude.sl:1171:1: note: `;! warn` for `Array` is here
