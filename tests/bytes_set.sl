; expect: "KJ"
(let-match many #\J (MkChar j))
(let-match many #\K (MkChar k))
(def-fns _ $ (many set-test : -> (many (String) r))
  (let ((erased _) (unique b) (erased p)) (bytes-make (Succ (Succ (Zero))) j))
  (let-match erased p (RepeatCons _ _ _ _ _))
  (let ((erased _) (unique b2) (erased _)) (bytes-set _ b (Zero) k _ (NthHere _ _ _)))
  (let ((many s) (erased _)) (bytes-str _ (share b2)))
  s)
set-test
