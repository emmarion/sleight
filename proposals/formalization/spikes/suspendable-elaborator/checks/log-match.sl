(let ((many one)) (Succ (Zero)))
(let ((many log)) (Cons _ (MkEntry one (Zero) (RunsHalt)) (Nil _)))
(elab (TNode (TRun one) (TGen)) (Zero) log (Nil _))
