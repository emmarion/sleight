(def-adts
  ((Stepped : ((List (Code)) fns) ((Heap) h) ((Control) c) -> Type)
    enum
    (many StepOk : (erased (List (Code)) fns) (erased (Heap) h) (erased (Control) c)
       (many (Heap) h2) (many (Nat) next2) (erased (Below h2 next2) inv2) (many (Control) c2)
       (erased (Label) l) (erased (Step fns h c l h2 c2) d) -> (Stepped fns h c))
    (many StepFinal : (erased (List (Code)) fns) (erased (Heap) h) (many (Word) w) -> (Stepped fns h (KRet w (KNil))))
    (many StepStuck : (erased (List (Code)) fns) (erased (Heap) h) (erased (Control) c) (many (Why) why) -> (Stepped fns h c)))
  ((Stepsed : ((List (Code)) fns) ((Heap) h) ((Control) c) -> Type)
    enum
    (many StepsOk : (erased (List (Code)) fns) (erased (Heap) h) (erased (Control) c)
       (many (Heap) h2) (many (Nat) next2) (erased (Below h2 next2) inv2) (many (Word) w) (many (Nat) count)
       (erased (List (Label)) ls) (erased (Steps fns h c ls h2 (KRet w (KNil))) d) -> (Stepsed fns h c))
    (many StepsHalt : (erased (List (Code)) fns) (erased (Heap) h) (erased (Control) c) (many (Halt) why) -> (Stepsed fns h c))))

(def-fns _ $ (many step : (many (List (Code)) fns) (many (Heap) h) (many (Nat) next) (erased (Below h next) inv) (many (Control) c) ->
    (many (Stepped fns h c) r))
  (match many c _
    ((KRet w k)
      (match many k _
        ((KNil) (StepFinal fns h w))
        ((KLet env body k2) (StepOk _ _ _ h next inv (KRun (Cons _ w env) body k2) (LTau) $ StRet fns h w env body k2))))
    ((KRun env code k)
      (match many code _
        ((CDo i)
          (match many (prim h next inv env i) _
            ((PrimStuck _ _ _ why) (StepStuck _ _ _ why))
            ((PrimOk _ _ _ h2 next2 inv2 w l d) (StepOk _ _ _ h2 next2 inv2 (KRet w k) l $ StDo fns h env i k l h2 w d))))
        ((CLet rhs body) (StepOk _ _ _ h next inv (KRun env rhs (KLet env body k)) (LTau) $ StLet fns h env rhs body k))
        ((CMatch a blocks imms)
          (let-match many (atom-val env a) (AVHit _ _ w pa) ((AVMiss _ _) (StepStuck _ _ _ (NoVar))))
          (let-match many (select h w blocks imms) (SelHit _ _ _ _ body fs sel) ((SelMiss _ _ _ _ why) (StepStuck _ _ _ why)))
          (let ((many env2) (erased ct)) (cat fs env))
          (StepOk _ _ _ h next inv (KRun env2 body k) (LTau) $ StMatch fns h env a blocks imms k w body fs env2 pa sel ct))
        ((CCall g args)
          (let-match many (nth-dec _ fns g) (NthHit _ _ _ body pf) ((NthMiss _ _ _ _) (StepStuck _ _ _ (NoFn))))
          (let-match many (atom-vals env args) (AVsHit _ _ ws pa) ((AVsMiss _ _) (StepStuck _ _ _ (NoVar))))
          (StepOk _ _ _ h next inv (KRun ws body k) (LTau) $ StCall fns h env g args k body ws pf pa))))))

(def-fns _ $ (many steps : (subterm many (Nat) fuel) (many (List (Code)) fns) (many (Heap) h) (many (Nat) next) (erased (Below h next) inv)
    (many (Control) c) -> (many (Stepsed fns h c) r))
  (let-match many fuel (Succ f) ((Zero) (StepsHalt _ _ _ (OutOfFuel))))
  (let-match many (step fns h next inv c) (StepOk _ _ _ h1 next1 inv1 c1 l d)
    ((StepStuck _ _ _ why) (StepsHalt _ _ _ (Stuck why)))
    ((StepFinal _ _ w) (StepsOk _ _ _ h next inv w (Zero) (Nil _) $ StepsNil fns h c)))
  (match many (notail $ steps f fns h1 next1 inv1 c1) _
    ((StepsHalt _ _ _ why) (StepsHalt _ _ _ why))
    ((StepsOk _ _ _ h2 next2 inv2 w n ls q)
      (StepsOk _ _ _ h2 next2 inv2 w (Succ n) (Cons _ l ls) $ StepsCons fns h c l h1 c1 ls h2 (KRet w (KNil)) d q))))
