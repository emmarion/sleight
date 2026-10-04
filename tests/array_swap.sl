; expect: 12
(def-fns _ $ (many swap-second : (unique (Array (Nat) (Succ (Succ (Succ (Zero))))) a)
    (erased (ANth (Nat) (Succ (Succ (Succ (Zero)))) a (Succ (Zero)) (Succ (Succ (Zero)))) nth) ->
    (unique (Succ (Succ (Zero))) is old)
    (unique (Array (Nat) (Succ (Succ (Succ (Zero))))) r at a))
  (let ((unique old) (unique r) (erased p))
    (array-swap _ _ a (Succ (Zero)) (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))) _ nth))
  (values old r))
(def-fns _ $ (many swap-test : -> (many (Nat) result))
  (let ((unique a)) (ACons _ _ (Succ (Zero))
    (ACons _ _ (Succ (Succ (Zero)))
      (ACons _ _ (Succ (Succ (Succ (Zero)))) (ANil (Nat))))))
  (let ((unique old) (unique b)) (swap-second a (NthS _ _ _ _ _ _ (NthZ _ _ _ _))))
  (let-match unique b (ACons _ _ x tl))
  (let-match unique tl (ACons _ _ y rest))
  (let-match unique rest (ACons _ _ z end))
  (nat-add (share old) (nat-add (share x) (nat-add (share y) (share z)))))
swap-test
; warns: tests/array_swap.sl:10:22: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:978:1: note: `;! warn` for `ACons` is here
; warns: tests/array_swap.sl:11:6: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:978:1: note: `;! warn` for `ACons` is here
; warns: tests/array_swap.sl:12:8: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:978:1: note: `;! warn` for `ACons` is here
; warns: tests/array_swap.sl:14:3: warning: match on `Array`: copies the array's tail, O(n); read with `array-get` and `array-length`, or their `-many` forms at many
; warns: lib/prelude.sl:979:1: note: `;! warn` for `Array` is here
; warns: tests/array_swap.sl:15:3: warning: match on `Array`: copies the array's tail, O(n); read with `array-get` and `array-length`, or their `-many` forms at many
; warns: lib/prelude.sl:979:1: note: `;! warn` for `Array` is here
; warns: tests/array_swap.sl:16:3: warning: match on `Array`: copies the array's tail, O(n); read with `array-get` and `array-length`, or their `-many` forms at many
; warns: lib/prelude.sl:979:1: note: `;! warn` for `Array` is here
