; expect: 12
(def-fns _ $ (many swap-second : (erased (List (Nat)) xs) (unique (Array (Nat) xs) a)
    (erased (Nth (Nat) xs (Succ (Zero)) (Succ (Succ (Zero)))) nth) ->
    (unique (Succ (Succ (Zero))) is old) (erased (List (Nat)) ys)
    (unique (Array (Nat) ys) r at a) (erased (SetNth (Nat) xs (Succ (Zero)) (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))) ys) p))
  (let ((unique old) (erased ys) (unique r) (erased p))
    (array-swap _ _ a (Succ (Zero)) (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))) _ nth))
  (values old ys r p))
(def-fns _ $ (many swap-test : -> (many (Nat) result))
  (let ((unique a)) (ACons _ _ (Succ (Zero))
    (ACons _ _ (Succ (Succ (Zero)))
      (ACons _ _ (Succ (Succ (Succ (Zero)))) (ANil (Nat))))))
  (let ((unique old) (erased _) (unique b) (erased p)) (swap-second _ a (NthThere _ _ _ _ _ (NthHere _ _ _))))
  (let-match erased p (SetThere _ _ _ _ _ _ p1))
  (let-match erased p1 (SetHere _ _ _ _))
  (let-match unique b (ACons _ _ x tl))
  (let-match unique tl (ACons _ _ y rest))
  (let-match unique rest (ACons _ _ z _))
  (nat-add (share old) (nat-add (share x) (nat-add (share y) (share z)))))
swap-test
; warns: tests/array_swap.sl:10:22: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:1308:1: note: `;! warn` for `ACons` is here
; warns: tests/array_swap.sl:11:6: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:1308:1: note: `;! warn` for `ACons` is here
; warns: tests/array_swap.sl:12:8: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:1308:1: note: `;! warn` for `ACons` is here
; warns: tests/array_swap.sl:16:3: warning: match on `Array`: copies the array's tail, O(n); read with `array-get` and `array-length`, or their `-many` forms at many
; warns: lib/prelude.sl:1309:1: note: `;! warn` for `Array` is here
; warns: tests/array_swap.sl:17:3: warning: match on `Array`: copies the array's tail, O(n); read with `array-get` and `array-length`, or their `-many` forms at many
; warns: lib/prelude.sl:1309:1: note: `;! warn` for `Array` is here
; warns: tests/array_swap.sl:18:3: warning: match on `Array`: copies the array's tail, O(n); read with `array-get` and `array-length`, or their `-many` forms at many
; warns: lib/prelude.sl:1309:1: note: `;! warn` for `Array` is here
