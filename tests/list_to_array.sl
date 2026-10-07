; expect: 11
(def-fns _ $ (many from-list : -> (many (Nat) result))
  (let ((unique a)) (list-to-array _ (Cons _ (MkCopy _ 4) $ Cons _ (MkCopy _ 7) $ Nil _)))
  (let ((many x) (unique b)) (array-get _ _ a (Zero) _ (NthHere _ _ _)))
  (let ((many y) (unique c)) (array-get _ _ b (Succ (Zero)) _ (NthThere _ _ _ _ _ (NthHere _ _ _))))
  (nat-add x y))
from-list
