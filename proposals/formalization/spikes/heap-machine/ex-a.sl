(let ((many prog-a))
  (lets
    (Cons _ (cell (AImm 30) nil)
      (Cons _ (cell (AImm 20) (AVar 0))
        (Cons _ (cell (AImm 10) (AVar 0))
          (Cons _ (CDo (IWrite (AVar 1) 0 (AImm 99))) (Nil _)))))
    (CMatch (AVar 1)
      (Cons _ (CMatch (AVar 1) (Cons _ (var 0) (Nil _)) (Nil _)) (Nil _))
      (Nil _))))

(MkPair _ _
  (run 100 (Nil _) (HNil) 0 (BelowNil 0) (Nil _) prog-a)
  (steps 100 (Nil _) (HNil) 0 (BelowNil 0) (KRun (Nil _) prog-a (KNil))))
