; Accepted (round-7 review of 06): a function at S given a packed-level closure state, made before S was
; minted, and a Predates about that state, applies the closure at a halt through predates-subterm, with no
; Predates packed in the state. Needs std/list.sl, spec.sl and machine.sl first.
(def-adts $ (HState : ((Cmd) c0) ((Mem) m0) -> Type)
  enum
  (many HS : (erased (Cmd) c0) (erased (Mem) m0) (many (List (Cmd)) k) (many (Mem) m) (erased (Level) L)
     (erased (Fn L (erased (Mem) mf) (erased (RunsAll m k mf) a) -> (erased (Runs m0 c0 mf) d)) inv) -> (HState c0 m0)))
(let ((many mem0)) (MkMem (Cons _ (VNum 9) $ Nil _) (Nil _)))
(def-fns _ $ (erased inv0 : (erased (Mem) mf) (erased (RunsAll mem0 (Nil (Cmd)) mf) a) -> (erased (Runs mem0 (CSkip) mf) d))
  (let-match erased a (RANil _))
  (ExSkip mem0))
(let ((many st0)) (HS (CSkip) mem0 (Nil _) mem0 _ inv0))
(def-lvl S)
(def-fns S $ (many use : (erased (Cmd) c0) (erased (Mem) m0) (many (HState c0 m0) st) (erased (Predates (HState c0 m0) st S) pst)
    -> (many (Outcome c0 m0) r))
  (let-match many st (HS _ _ k m L inv))
  (let ((erased ps)) (prove-subterm L st))
  (let ((erased pl)) (predates-subterm pst ps))
  (let-match many (step k m) (SHalt _) ((SNext _ _ k2 m2 s) (Stuck _ _)) ((SStuck _ _) (Stuck _ _)))
  (Halted _ _ m (inv (predates pl) m (RANil m))))
(let ((erased pst0)) (prove-predates st0 S))
(use (CSkip) mem0 st0 pst0)
