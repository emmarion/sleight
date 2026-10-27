; expect: 4
(def-fns _ $ (many first : -> (many (Nat) result))
  (let ((unique a)) (list-to-array _ (Cons _ (MkCopy _ 4) $ Cons _ (MkCopy _ 7) $ Nil _)))
  (let-match unique a (ACons _ _ hd _))
  (let-match unique hd (MkCopy _ v))
  v)
first
; warns: tests/array_match_warn.sl:4:3: warning: match on `Array`: copies the array's tail, O(n); read with `array-get` and `array-length`, or their `-many` forms at many
; warns: lib/prelude.sl:1239:1: note: `;! warn` for `Array` is here
