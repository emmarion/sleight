(let ((erased env1)) (Cons (Word) (WAddr 5) (Nil (Word))))
(let ((erased here)) (AVVar env1 (Zero) (WAddr 5) (NthHere _ (WAddr 5) (Nil _))))

(let ((erased (Prim (HNil) env1 (ISame (AVar (Zero)) (AVar (Zero))) (LYes) (HNil) (WImm (Succ (Zero)))) same-word-may-answer-yes))
  (PSameYes (HNil) env1 (AVar (Zero)) (AVar (Zero)) (WAddr 5) here here))

(let ((erased (Prim (HNil) env1 (ISame (AVar (Zero)) (AVar (Zero))) (LNo) (HNil) (WImm (Zero))) same-word-may-answer-no))
  (PSameNo (HNil) env1 (AVar (Zero)) (AVar (Zero)) (WAddr 5) (WAddr 5) here here))

(let ((erased lt37)) (prove-literal-lt 3 7))
(let ((erased b0)) (MkBlock 0 (Nil (Word))))
(let ((erased h1)) (HCons 7 b0 (HNil)))
(let ((erased env2)) (Cons (Word) (WAddr 7) (Nil (Word))))
(let ((erased args2)) (Cons (Atom) (AVar (Zero)) (Nil (Atom))))
(let ((erased b1)) (MkBlock 0 env2))
(let ((erased h2)) (HCons 3 b1 h1))
(let ((erased d1))
  (PCon (HNil) (Nil _) 0 (Nil _) (Nil _) 7 h1 (AVsNil (Nil _)) (MkAlloc (HNil) 7 b0 (FreshNil 7))))
(let ((erased d2))
  (PCon h1 env2 0 args2 env2 3 h2
    (AVsCons env2 (AVar (Zero)) (WAddr 7) (Nil _) (Nil _) (AVVar env2 (Zero) (WAddr 7) (NthHere _ (WAddr 7) (Nil _))) (AVsNil env2))
    (MkAlloc h1 3 b1 (FreshCons 3 7 b0 (HNil) (NeqLt 3 7 lt37) (FreshNil 3)))))

(let ((erased (Run (Nil (Code)) (HNil) (Nil (Word)) (CLet (CDo (ICon 0 (Nil (Atom)))) (CDo (ICon 0 args2)))
                (ChSeq (ChOne (LAddr 7)) (ChOne (LAddr 3))) h2 (WAddr 3)) second-address-below-first))
  (RunLet (Nil _) (HNil) (Nil _) (CDo (ICon 0 (Nil _))) (CDo (ICon 0 args2)) (ChOne (LAddr 7)) h1 (WAddr 7) (ChOne (LAddr 3)) h2 (WAddr 3)
    (RunDo (Nil _) (HNil) (Nil _) (ICon 0 (Nil _)) (LAddr 7) h1 (WAddr 7) d1)
    (RunDo (Nil _) h1 env2 (ICon 0 args2) (LAddr 3) h2 (WAddr 3) d2)))
