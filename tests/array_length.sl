; expect: (MkPair _ _ 3 3)
(def-fns _ $ (many length-test : -> (many (Pair (Nat) (Nat)) result))
  (let ((erased n) (unique a) (erased p)) (list-to-array _ (Cons _ 4 $ Cons _ 7 $ Cons _ 9 $ Nil _)))
  (let ((many len) (unique b)) (array-length _ _ a))
  (let ((unique m) (erased q)) (array-new (Nat) 3))
  (let ((many len2) (unique m2)) (array-length _ _ m))
  (MkPair _ _ len len2))
length-test
