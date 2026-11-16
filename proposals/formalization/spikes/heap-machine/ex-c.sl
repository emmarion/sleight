(let ((many prog-c))
  (lets
    (Cons _ (cell (AImm 7) nil)
      (Cons _ (cell (AImm 7) nil)
        (Cons _ (CDo (ISame (AVar 1) (AVar 0)))
          (Cons _ (CDo (ISame (AVar 2) (AVar 2))) (Nil _)))))
    (CDo (ICon 1 (Cons _ (AVar 1) $ Cons _ (AVar 0) $ Nil _)))))

(MkPair _ _
  (run 100 (Nil _) (HNil) 0 (BelowNil 0) (Nil _) prog-c)
  (steps 100 (Nil _) (HNil) 0 (BelowNil 0) (KRun (Nil _) prog-c (KNil))))
