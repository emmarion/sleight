; expect: (MkU8 74 _)
(let-match many #\J (MkChar j))
(def-fns _ $ (many head : -> (many (U8) r))
  (let ((erased xs) (unique b) (erased p)) (bytes-make (Succ (Zero)) j))
  (let-match erased p (RepeatCons _ _ _ _ _))
  (let-match unique b (BCons _ hd tl) (absurd BNil))
  hd)
head
; warns: tests/bytes_match_warn.sl:6:3: warning: match on `Bytes`: copies the buffer's tail, O(n); read with `bytes-get` and `bytes-length`, or their `-many` forms at many
; warns: lib/prelude.sl:1200:1: note: `;! warn` for `Bytes` is here
