; error: argument 6, `p`, of `NthThere`: type mismatch: expected `(Nth (U8) (Nil (U8)) (Zero) __?1)`
(let-match many #\J (MkChar j))
(def-fns _ $ (many past-end : -> (many (U8) r))
  (let ((erased xs) (unique b) (erased p)) (bytes-make (Succ (Zero)) j))
  (let-match erased p (RepeatCons _ _ _ _ p1))
  (let-match erased p1 (RepeatNil _ _))
  (bytes-get-many _ (share b) (Succ (Zero)) _ (NthThere _ _ _ _ _ (NthHere _ _ _))))
past-end
