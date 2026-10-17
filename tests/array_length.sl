; expect: (MkPair _ _ 3 3)
(def-fns _ $ (many length-test : -> (many (Pair (Nat) (Nat)) result))
  (let ((unique a)) (list-to-array _ (Cons _ (MkCopy _ 4) $ Cons _ (MkCopy _ 7) $ Cons _ (MkCopy _ 9) $ Nil _)))
  (let ((many len) (erased _) (unique _)) (array-length _ _ a))
  (let ((erased _) (unique m) (erased _)) (array-new (Nat) 3))
  (let ((many len2) (erased _) (unique _)) (array-length _ _ m))
  (MkPair _ _ len len2))
length-test
