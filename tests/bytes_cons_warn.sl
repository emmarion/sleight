; expect: "J"
(let-match many #\J (MkChar j))
(def-fns _ $ (many cons-test : -> (many (String) r))
  (let ((unique b)) (BCons _ j (BNil)))
  (let ((many s) (erased _)) (bytes-str _ (share b)))
  s)
cons-test
; warns: tests/bytes_cons_warn.sl:4:22: warning: application of `BCons`: copies the whole buffer, O(n); allocate with `bytes-make` and fill with `bytes-set`
; warns: lib/prelude.sl:1411:1: note: `;! warn` for `BCons` is here
