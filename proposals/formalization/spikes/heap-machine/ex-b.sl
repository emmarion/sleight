(let ((many append-into))
  (CMatch (AVar 2)
    (Cons _
      (lets
        (Cons _ (cell nil nil)
          (Cons _ (store 3 0 4)
            (Cons _ (store 4 1 1) (Nil _))))
        (CCall 0 (Cons _ (AVar 2) $ Cons _ (AVar 3) $ Cons _ (AVar 4) $ Cons _ (AVar 8) $ Nil _)))
      (Nil _))
    (Cons _ (CLet (store 0 0 1) (store 1 1 4)) (Nil _))))

(let ((many append-list))
  (CMatch (AVar 0)
    (Cons _
      (lets
        (Cons _ (cell nil nil)
          (Cons _ (CCall 0 (Cons _ (AVar 0) $ Cons _ (AVar 1) $ Cons _ (AVar 2) $ Cons _ (AVar 4) $ Nil _)) (Nil _)))
        (var 1))
      (Nil _))
    (Cons _ (var 1) (Nil _))))

(let ((many fns-b)) (Cons _ append-into $ Cons _ append-list $ Nil _))

(let ((many prog-b))
  (lets
    (Cons _ (cell (AImm 2) nil)
      (Cons _ (cell (AImm 1) (AVar 0))
        (Cons _ (cell (AImm 3) nil) (Nil _))))
    (CCall 1 (Cons _ (AVar 1) $ Cons _ (AVar 0) $ Nil _))))

(def-fns _ $ (many show-big : (many (Ran fns-b (HNil) (Nil (Word)) prog-b) r) -> (many (Pair (List (Nat)) (Ran fns-b (HNil) (Nil (Word)) prog-b)) out))
  (let-match many r (RanOk _ _ _ _ h _ _ w _ _) (else (MkPair _ _ (Nil _) r)))
  (MkPair _ _ (read-list 100 h w) r))

(MkPair _ _
  (show-big (run 100 fns-b (HNil) 0 (BelowNil 0) (Nil _) prog-b))
  (steps 200 fns-b (HNil) 0 (BelowNil 0) (KRun (Nil _) prog-b (KNil))))
