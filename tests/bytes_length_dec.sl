; expect: (MkPair _ _ 2 0)
(let-match many #\J (MkChar j))
(def-fns _ $ (many length-dec-test : -> (many (Pair (Nat) (Nat)) result))
  (let ((erased _) (unique b) (erased _)) (bytes-make 2 j))
  (let ((erased _) (erased _) (many d) (unique b1)) (bytes-length-dec _ b))
  (let ((many n) (erased _) (unique _)) (bytes-length _ b1))
  (MkPair _ _ n (match many d _ ((Yes _ _ _ _ _) 0) ((No _ _ _ _ _) 1))))
length-dec-test
