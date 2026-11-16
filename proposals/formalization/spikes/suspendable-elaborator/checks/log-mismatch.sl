(let ((many one)) (Succ (Zero)))
(let ((many log)) (Cons _ (MkEntry one (Zero) (RunsHalt)) (Nil _)))
(MkPair _ _ (elab (TRun 6) (Zero) log (Nil _)) (elab (TNode (TRun one) (TRun 6)) (Zero) log (Nil _)))
