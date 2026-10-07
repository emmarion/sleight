; expect: "KJ"
(let-match many #\J (MkChar j))
(let-match many #\K (MkChar k))
(def-fns _ $ (many set-test : -> (many (String) r))
  (let ((erased xs) (unique b) (erased p)) (bytes-make (Succ (Succ (Zero))) j))
  (let-match erased p (RepeatCons _ _ _ _ p1))
  (let ((erased ys) (unique b2) (erased q)) (bytes-set _ b (Zero) k _ (NthHere _ _ _)))
  (let ((many s) (erased sp)) (bytes-str _ (share b2)))
  s)
set-test
