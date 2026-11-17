; run-total (complete.sl) on a one-instruction program, with its Runs derivation written out at the top
; level. Needs std/list.sl, spec.sl, machine.sl and complete.sl earlier on the command line.

(let ((many e0)) (Cons _ (VNum 0) $ Nil _))
(let ((many e1)) (Cons _ (VNum 7) $ Nil _))
(let ((erased spec)) (ExOp _ _ _ $ RSet e0 e1 (Nil _) (Zero) 7 $ SetHere _ (VNum 0) (VNum 7) (Nil _)))
(run-total (COp $ OSet (Zero) 7) (MkMem e0 $ Nil _) (MkMem e1 $ Nil _) spec)
