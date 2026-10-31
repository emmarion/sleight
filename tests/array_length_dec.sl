; expect: (MkPair _ _ 3 $ MkPair _ _ 0 0)
(def-fns _ $ (many length-dec-test : -> (many (Pair (Nat) $ Pair (Nat) (Nat)) result))
  (let ((unique a)) (list-to-array _ (Cons _ (MkCopy _ 4) $ Cons _ (MkCopy _ 7) $ Cons _ (MkCopy _ 9) $ Nil _)))
  (let ((erased _) (erased _) (many d) (unique a1)) (array-length-dec _ _ a))
  (let ((many n) (erased _) (unique a2)) (array-length _ _ a1))
  (let ((many c)) (share a2))
  (let ((erased _) (erased _) (many d2)) (array-length-dec-many _ _ c))
  (MkPair _ _ n $ MkPair _ _ (match many d _ ((Yes _ _ _ _ _) 0) ((No _ _ _ _ _) 1)) (match many d2 _ ((Yes _ _ _ _ _) 0) ((No _ _ _ _ _) 1))))
length-dec-test
