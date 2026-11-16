(let ((many prog-d))
  (lets
    (Cons _ (cell (AImm 1) nil)
      (Cons _ (CDo (ICopy (AVar 0) 0 (AImm 99))) (Nil _)))
    (CMatch (AVar 1)
      (Cons _ (CMatch (AVar 2) (Cons _ (CDo (ICon 1 (Cons _ (AVar 2) $ Cons _ (AVar 0) $ Nil _))) (Nil _)) (Nil _)) (Nil _))
      (Nil _))))

(MkPair _ _
  (run 100 (Nil _) (HNil) 0 (BelowNil 0) (Nil _) prog-d)
  (steps 100 (Nil _) (HNil) 0 (BelowNil 0) (KRun (Nil _) prog-d (KNil))))
