(def-fns _ $ (erased reach-trans : (erased (Env) env0) (erased (Core) c0) (erased (State env0 c0) s) (erased (State env0 c0) s1) (erased (State env0 c0) s2)
    (subterm erased (Reaches env0 c0 s s1) a) (erased (Reaches env0 c0 s1 s2) b) -> (erased (Reaches env0 c0 s s2) r))
  (match erased a _
    ((ReachHere _ _ _) b)
    ((ReachStep _ _ _ mid _ first rest) (ReachStep _ _ s mid s2 first (reach-trans _ _ mid s1 s2 rest b)))))

(def-fns _ $ (erased reach-one : (erased (Env) env0) (erased (Core) c0) (erased (State env0 c0) s) (erased (State env0 c0) s2)
    (erased (StepTo env0 c0 s s2) only) -> (erased (Reaches env0 c0 s s2) r))
  (ReachStep _ _ s s2 s2 only (ReachHere _ _ s2)))

(def-fns _ $ (erased reach-then : (erased (Env) env0) (erased (Core) c0) (erased (State env0 c0) s) (erased (State env0 c0) s1) (erased (State env0 c0) s2)
    (erased (Reaches env0 c0 s s1) a) (erased (StepTo env0 c0 s1 s2) last) -> (erased (Reaches env0 c0 s s2) r))
  (reach-trans _ _ s s1 s2 a (reach-one _ _ s1 s2 last)))

(def-fns _
  ((erased eval-reaches : (erased (Env) env) (erased (Core) c) (erased (List (Val)) vs) (subterm erased (Eval env c vs) d)
      (erased (Env) env0) (erased (Core) c0) (erased (Stack env c env0 c0) k) ->
      (erased (Eval env c vs) d2) (erased (Reaches env0 c0 (SEval env0 c0 env c k) (SRet env0 c0 env c vs d2 k)) r))
    (match erased d _
      ((EvVar _ x v p) (values (EvVar env x v p) (reach-one _ _ _ _ (StVar _ _ env x v p k))))
      ((EvApp _ h args ctor vals p q)
        (let ((erased p2) (erased to-head)) (eval-reaches env h _ p _ _ (KAppHead _ _ env h args k)))
        (let ((erased q2) (erased to-args)) (eval-list-reaches env args vals q _ _ (KAppArgs _ _ env h args ctor p2 k)))
        (values (EvApp env h args ctor vals p2 q2)
          (reach-trans _ _ _ _ _ to-head
            $ ReachStep _ _ _ _ _ (StRetAppHead _ _ env h args ctor p2 k)
            $ reach-then _ _ _ _ _ to-args (StRetAppArgs _ _ env h args ctor vals p2 q2 k))))
      ((EvCall _ fn args cenv group id ps body vals env1 env2 outs p q g b r)
        (let ((erased p2) (erased to-fn)) (eval-reaches env fn _ p _ _ (KCallFn _ _ env fn args k)))
        (let ((erased q2) (erased to-args)) (eval-list-reaches env args vals q _ _ (KCallArgs _ _ env fn args cenv group id ps body p2 k)))
        (let ((erased r2) (erased to-body)) (eval-reaches env2 body outs r _ _ (KCallBody _ _ env fn args cenv group id ps body vals env1 env2 p2 q2 g b k)))
        (values (EvCall env fn args cenv group id ps body vals env1 env2 outs p2 q2 g b r2)
          (ReachStep _ _ _ _ _ (StCall _ _ env fn args k)
            $ reach-trans _ _ _ _ _ to-fn
            $ ReachStep _ _ _ _ _ (StRetCallFn _ _ env fn args cenv group id ps body p2 k)
            $ reach-trans _ _ _ _ _ to-args
            $ ReachStep _ _ _ _ _ (StRetCallArgs _ _ env fn args cenv group id ps body vals env1 env2 p2 q2 g b k)
            $ reach-then _ _ _ _ _ to-body (StRetCallBody _ _ env fn args cenv group id ps body vals env1 env2 outs p2 q2 g b r2 k))))
      ((EvMatch _ scrut bs ctor fields ids body env1 outs p br b r)
        (let ((erased p2) (erased to-scrut)) (eval-reaches env scrut _ p _ _ (KMatchScrut _ _ env scrut bs k)))
        (let ((erased r2) (erased to-body)) (eval-reaches env1 body outs r _ _ (KMatchBody _ _ env scrut bs ctor fields ids body env1 p2 br b k)))
        (values (EvMatch env scrut bs ctor fields ids body env1 outs p2 br b r2)
          (ReachStep _ _ _ _ _ (StMatch _ _ env scrut bs k)
            $ reach-trans _ _ _ _ _ to-scrut
            $ ReachStep _ _ _ _ _ (StRetMatchScrut _ _ env scrut bs ctor fields ids body env1 p2 br b k)
            $ reach-then _ _ _ _ _ to-body (StRetMatchBody _ _ env scrut bs ctor fields ids body env1 outs p2 br b r2 k))))
      ((EvValues _ items vals q)
        (let ((erased q2) (erased to-items)) (eval-list-reaches env items vals q _ _ (KValues _ _ env items k)))
        (values (EvValues env items vals q2)
          (ReachStep _ _ _ _ _ (StValues _ _ env items k)
            $ reach-then _ _ _ _ _ to-items (StRetValues _ _ env items vals q2 k))))
      ((EvFormer _ t) (values (EvFormer env t) (reach-one _ _ _ _ (StFormer _ _ env t k))))
      ((EvToken _) (values (EvToken env) (reach-one _ _ _ _ (StToken _ _ env k))))
      ((EvStmt _ stmt rest env1 outs p q)
        (let ((erased (EvalStmt env stmt env1) p2)
              (erased (Reaches env0 c0 (SEval env0 c0 env (CStmt stmt rest) k) (SEval env0 c0 env1 rest (KStmtRest env0 c0 env stmt rest env1 p2 k))) to-stmt))
          (match erased p _
            ((EvLet _ ids rhs vals _ p1 b)
              (let ((erased p3) (erased to-rhs)) (eval-reaches env rhs vals p1 _ _ (KLetRhs _ _ env ids rhs rest k)))
              (values (EvLet env ids rhs vals env1 p3 b)
                (ReachStep _ _ _ _ _ (StLet _ _ env ids rhs rest k)
                  $ reach-then _ _ _ _ _ to-rhs (StRetLetRhs _ _ env ids rhs rest vals env1 p3 b k))))
            ((EvDefLvl _ x) (values p (reach-one _ _ _ _ (StDefLvl _ _ env x rest k))))
            ((EvDefFns _ defs _ g) (values p (reach-one _ _ _ _ (StDefFns _ _ env defs rest env1 g k))))
            ((EvDefAdts _ ids _ b) (values p (reach-one _ _ _ _ (StDefAdts _ _ env ids rest env1 b k))))))
        (let ((erased q2) (erased to-rest)) (eval-reaches env1 rest outs q _ _ (KStmtRest _ _ env stmt rest env1 p2 k)))
        (values (EvStmt env stmt rest env1 outs p2 q2)
          (reach-trans _ _ _ _ _ to-stmt
            $ reach-then _ _ _ _ _ to-rest (StRetStmtRest _ _ env stmt rest env1 outs p2 q2 k))))))
  ((erased eval-list-reaches : (erased (Env) env) (erased (List (Core)) cs) (erased (List (Val)) vs) (subterm erased (EvalList env cs vs) d)
      (erased (Env) env0) (erased (Core) c0) (erased (ListStack env cs env0 c0) k) ->
      (erased (EvalList env cs vs) d2) (erased (Reaches env0 c0 (SEvalList env0 c0 env cs k) (SRetList env0 c0 env cs vs d2 k)) r))
    (match erased d _
      ((EvLNil _) (values (EvLNil env) (reach-one _ _ _ _ (StListNil _ _ env k))))
      ((EvLCons _ c v rest vals p q)
        (let ((erased p2) (erased to-head)) (eval-reaches env c _ p _ _ (KListHead _ _ env c rest k)))
        (let ((erased q2) (erased to-rest)) (eval-list-reaches env rest vals q _ _ (KListTail _ _ env c rest v p2 k)))
        (values (EvLCons env c v rest vals p2 q2)
          (ReachStep _ _ _ _ _ (StListCons _ _ env c rest k)
            $ reach-trans _ _ _ _ _ to-head
            $ ReachStep _ _ _ _ _ (StRetListHead _ _ env c rest v p2 k)
            $ reach-then _ _ _ _ _ to-rest (StRetListTail _ _ env c rest v vals p2 q2 k)))))))
