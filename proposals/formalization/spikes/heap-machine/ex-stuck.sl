(def-fns _ $ (many outcome : (many (List (Code)) fns) (many (Code) c) -> (many (Pair (Halt) (Halt)) r))
  (let ((many (Halt) big))
    (match many (run 50 fns (HNil) 0 (BelowNil 0) (Nil _) c) _
      ((RanOk _ _ _ _ _ _ _ _ _ _) (Stuck (NoVar)))
      ((RanHalt _ _ _ _ why) why)))
  (let ((many (Halt) small))
    (match many (steps 50 fns (HNil) 0 (BelowNil 0) (KRun (Nil _) c (KNil))) _
      ((StepsOk _ _ _ _ _ _ _ _ _ _) (Stuck (NoVar)))
      ((StepsHalt _ _ _ why) why)))
  (MkPair _ _ big small))

(let ((many loop)) (Cons _ (CCall 0 (Nil _)) (Nil _)))

(Cons _ (outcome (Nil _) (var 5))
  (Cons _ (outcome (Nil _) (CCall 3 (Nil _)))
    (Cons _ (outcome (Nil _) (CDo (IWrite (AImm 4) 0 (AImm 1))))
      (Cons _ (outcome (Nil _) (CLet (cell nil nil) (CDo (IWrite (AVar 0) 7 (AImm 1)))))
        (Cons _ (outcome (Nil _) (CMatch (AImm 2) (Nil _) (Nil _)))
          (Cons _ (outcome loop (CCall 0 (Nil _))) (Nil _)))))))
