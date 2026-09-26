; expect: (MkPair _ _ 3 3)
(def-fns _ $ (many length-many-test : -> (many (Pair (Nat) (Nat)) result))
  (let ((erased n) (unique a) (erased p)) (list-to-array _ (Cons _ 4 $ Cons _ 7 $ Cons _ 9 $ Nil _)))
  (let ((many b)) (share a))
  (let ((unique m) (erased q)) (array-new (Nat) 3))
  (let ((many m2)) (share m))
  (MkPair _ _ (array-length-many _ _ b) (array-length-many _ _ m2)))
length-many-test
