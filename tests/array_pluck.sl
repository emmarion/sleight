; expect: 9
(def-fns _ $ (many pluck-test : -> (many (Nat) result))
  (let ((unique a))
    (ACons _ _ (Init _ (Succ (Succ (Succ (Succ (Zero))))))
      (ACons _ _ (Init _ (Succ (Succ (Succ (Succ (Succ (Zero))))))) (ANil (MaybeUninit (Nat))))))
  (let ((unique item) (unique b) (erased cleared))
    (array-pluck _ _ a (Succ (Zero)) _ (NthS _ _ _ _ _ _ (NthZ _ _ _ _))))
  (let-match unique item (Init _ value))
  (let-match erased cleared (SetS _ _ _ _ _ _ _ step))
  (let-match erased step (SetZ _ _ _ _ _))
  (let ((unique c) (erased restored))
    (array-place _ _ b (Succ (Zero)) (Init _ value) _
      (NthS _ _ _ _ _ _ (NthZ _ _ _ _))))
  (let-match erased restored (SetS _ _ _ _ _ _ _ step2))
  (let-match erased step2 (SetZ _ _ _ _ _))
  (let ((erased raw) (erased witness))
    (init-witness _ _ c (AICons _ _ _ _ (AICons _ _ _ _ (AINil _)))))
  (let ((unique initialized)) (coerce c witness))
  (let-match unique initialized (ACons _ _ x rest))
  (let-match unique rest (ACons _ _ y end))
  (nat-add (share x) (share y)))
pluck-test
; warns: tests/array_pluck.sl:4:6: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:840:1: note: `;! warn` for `ACons` is here
; warns: tests/array_pluck.sl:5:8: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:840:1: note: `;! warn` for `ACons` is here
; warns: tests/array_pluck.sl:19:3: warning: match on `Array`: copies the array's tail, O(n); read with `array-get` and `array-length`
; warns: lib/prelude.sl:841:1: note: `;! warn` for `Array` is here
; warns: tests/array_pluck.sl:20:3: warning: match on `Array`: copies the array's tail, O(n); read with `array-get` and `array-length`
; warns: lib/prelude.sl:841:1: note: `;! warn` for `Array` is here
