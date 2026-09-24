; expect: 11
(def-fns _ $ (many from-list : -> (many (Nat) result))
  (let ((erased n) (unique a) (erased p)) (list-to-array _ (Cons _ 4 $ Cons _ 7 $ Nil _)))
  (let-match erased p (AILCons _ _ _ _ _ p1))
  (let-match erased p1 (AILCons _ _ _ _ _ p2))
  (let ((many x) (unique b)) (array-get _ _ a (Zero) _ (NthZ _ _ _ _)))
  (let ((many y) (unique c)) (array-get _ _ b (Succ (Zero)) _ (NthS _ _ _ _ _ _ (NthZ _ _ _ _))))
  (nat-add x y))
from-list
