; needs: ../mini/base ../mini/term ../mini/core ../mini/eval
; expect: (MkEvaled _ _ (Cons _ (VCon 12 $ Cons _ (VCon 11 $ Nil _) $ Nil _) $ Nil _) _)
; Evaluation in mini/ of a hand-built program: Nat declared as 10 with Zero 11 and Succ 12, a predecessor
; function 13 over its parameter 14 matching on Zero and on Succ with field 15, applied to two.

(let (many zero) (CApp (CVar 11) (Nil _)))
(let (many two) (CApp (CVar 12) (Cons _ (CApp (CVar 12) (Cons _ zero (Nil _))) (Nil _))))
(let (many pred-body)
  (CMatch (CVar 14) (Cons _ (MkBranch 11 (Nil _) zero) (Cons _ (MkBranch 12 (Cons _ 15 (Nil _)) (CVar 15)) (Nil _)))))
(let (many program)
  (CStmt (SDefAdts (Cons _ 10 (Cons _ 11 (Cons _ 12 (Nil _)))))
    (CStmt (SDefFns (Cons _ (MkFnDef 13 (Cons _ 14 (Nil _)) pred-body) (Nil _)))
      (CCall (CVar 13) (Cons _ two (Nil _))))))
(eval 1000 (ENil) program)
