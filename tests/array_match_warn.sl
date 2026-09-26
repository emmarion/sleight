; expect: 4
(def-fns _ $ (many first : -> (many (Nat) result))
  (let ((erased n) (unique a) (erased p)) (list-to-array _ (Cons _ 4 $ Cons _ 7 $ Nil _)))
  (let-match erased p (AILCons _ _ _ _ _ p1))
  (let-match unique a (ACons _ _ hd tl))
  (let-match unique hd (MkCopy _ v))
  v)
first
; warns: tests/array_match_warn.sl:5:3: warning: match on `Array`: copies the array's tail, O(n); read with `array-get` and `array-length`, or their `-many` forms at many
; warns: lib/prelude.sl:830:1: note: `;! warn` for `Array` is here
