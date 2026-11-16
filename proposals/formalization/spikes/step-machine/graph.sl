(def-adts
  ((StepTo : ((Env) env0) ((Core) c0) ((State env0 c0) s) ((State env0 c0) s2) -> Type)
    enum
    (many StVar : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Nat) x) (erased (Val) v) (erased (EnvOf env x v) p)
       (erased (Stack env (CVar x) env0 c0) k) ->
       (StepTo env0 c0 (SEval env0 c0 env (CVar x) k) (SRet env0 c0 env (CVar x) (Cons (Val) v (Nil (Val))) (EvVar env x v p) k)))
    (many StApp : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Core) h) (erased (List (Core)) args)
       (erased (Stack env (CApp h args) env0 c0) k) ->
       (StepTo env0 c0 (SEval env0 c0 env (CApp h args) k) (SEval env0 c0 env h (KAppHead env0 c0 env h args k))))
    (many StCall : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Core) fn) (erased (List (Core)) args)
       (erased (Stack env (CCall fn args) env0 c0) k) ->
       (StepTo env0 c0 (SEval env0 c0 env (CCall fn args) k) (SEval env0 c0 env fn (KCallFn env0 c0 env fn args k))))
    (many StMatch : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Core) scrut) (erased (List (Branch)) bs)
       (erased (Stack env (CMatch scrut bs) env0 c0) k) ->
       (StepTo env0 c0 (SEval env0 c0 env (CMatch scrut bs) k) (SEval env0 c0 env scrut (KMatchScrut env0 c0 env scrut bs k))))
    (many StValues : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (List (Core)) items)
       (erased (Stack env (CValues items) env0 c0) k) ->
       (StepTo env0 c0 (SEval env0 c0 env (CValues items) k) (SEvalList env0 c0 env items (KValues env0 c0 env items k))))
    (many StFormer : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Term) t)
       (erased (Stack env (CFormer t) env0 c0) k) ->
       (StepTo env0 c0 (SEval env0 c0 env (CFormer t) k) (SRet env0 c0 env (CFormer t) (Cons (Val) (VFormer t env) (Nil (Val))) (EvFormer env t) k)))
    (many StToken : (erased (Env) env0) (erased (Core) c0) (erased (Env) env)
       (erased (Stack env (CToken) env0 c0) k) ->
       (StepTo env0 c0 (SEval env0 c0 env (CToken) k) (SRet env0 c0 env (CToken) (Cons (Val) (VToken) (Nil (Val))) (EvToken env) k)))
    (many StLet : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (List (Nat)) ids) (erased (Core) rhs) (erased (Core) rest)
       (erased (Stack env (CStmt (SLet ids rhs) rest) env0 c0) k) ->
       (StepTo env0 c0 (SEval env0 c0 env (CStmt (SLet ids rhs) rest) k) (SEval env0 c0 env rhs (KLetRhs env0 c0 env ids rhs rest k))))
    (many StDefLvl : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Nat) x) (erased (Core) rest)
       (erased (Stack env (CStmt (SDefLvl x) rest) env0 c0) k) ->
       (StepTo env0 c0 (SEval env0 c0 env (CStmt (SDefLvl x) rest) k)
          (SEval env0 c0 (ECons x (VToken) env) rest (KStmtRest env0 c0 env (SDefLvl x) rest (ECons x (VToken) env) (EvDefLvl env x) k))))
    (many StDefFns : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (List (FnDef)) defs) (erased (Core) rest) (erased (Env) out)
       (erased (BindGroup env defs defs env out) g)
       (erased (Stack env (CStmt (SDefFns defs) rest) env0 c0) k) ->
       (StepTo env0 c0 (SEval env0 c0 env (CStmt (SDefFns defs) rest) k)
          (SEval env0 c0 out rest (KStmtRest env0 c0 env (SDefFns defs) rest out (EvDefFns env defs out g) k))))
    (many StDefAdts : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (List (Nat)) ids) (erased (Core) rest) (erased (Env) out)
       (erased (BindAtoms env ids out) b)
       (erased (Stack env (CStmt (SDefAdts ids) rest) env0 c0) k) ->
       (StepTo env0 c0 (SEval env0 c0 env (CStmt (SDefAdts ids) rest) k)
          (SEval env0 c0 out rest (KStmtRest env0 c0 env (SDefAdts ids) rest out (EvDefAdts env ids out b) k))))
    (many StListNil : (erased (Env) env0) (erased (Core) c0) (erased (Env) env)
       (erased (ListStack env (Nil (Core)) env0 c0) k) ->
       (StepTo env0 c0 (SEvalList env0 c0 env (Nil (Core)) k) (SRetList env0 c0 env (Nil (Core)) (Nil (Val)) (EvLNil env) k)))
    (many StListCons : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Core) c) (erased (List (Core)) cs)
       (erased (ListStack env (Cons (Core) c cs) env0 c0) k) ->
       (StepTo env0 c0 (SEvalList env0 c0 env (Cons (Core) c cs) k) (SEval env0 c0 env c (KListHead env0 c0 env c cs k))))
    (many StRetAppHead : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Core) h) (erased (List (Core)) args) (erased (Nat) ctor)
       (erased (Eval env h (Cons (Val) (VAtom ctor) (Nil (Val)))) p)
       (erased (Stack env (CApp h args) env0 c0) k) ->
       (StepTo env0 c0 (SRet env0 c0 env h (Cons (Val) (VAtom ctor) (Nil (Val))) p (KAppHead env0 c0 env h args k))
          (SEvalList env0 c0 env args (KAppArgs env0 c0 env h args ctor p k))))
    (many StRetCallFn : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Core) fn) (erased (List (Core)) args)
       (erased (Env) cenv) (erased (List (FnDef)) group) (erased (Nat) id) (erased (List (Nat)) ps) (erased (Core) body)
       (erased (Eval env fn (Cons (Val) (VClo cenv group (MkFnDef id ps body)) (Nil (Val)))) p)
       (erased (Stack env (CCall fn args) env0 c0) k) ->
       (StepTo env0 c0 (SRet env0 c0 env fn (Cons (Val) (VClo cenv group (MkFnDef id ps body)) (Nil (Val))) p (KCallFn env0 c0 env fn args k))
          (SEvalList env0 c0 env args (KCallArgs env0 c0 env fn args cenv group id ps body p k))))
    (many StRetCallBody : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Core) fn) (erased (List (Core)) args)
       (erased (Env) cenv) (erased (List (FnDef)) group) (erased (Nat) id) (erased (List (Nat)) ps) (erased (Core) body)
       (erased (List (Val)) vals) (erased (Env) env1) (erased (Env) env2) (erased (List (Val)) outs)
       (erased (Eval env fn (Cons (Val) (VClo cenv group (MkFnDef id ps body)) (Nil (Val)))) p) (erased (EvalList env args vals) q)
       (erased (BindGroup cenv group group cenv env1) g) (erased (BindAll env1 ps vals env2) b) (erased (Eval env2 body outs) r)
       (erased (Stack env (CCall fn args) env0 c0) k) ->
       (StepTo env0 c0 (SRet env0 c0 env2 body outs r (KCallBody env0 c0 env fn args cenv group id ps body vals env1 env2 p q g b k))
          (SRet env0 c0 env (CCall fn args) outs (EvCall env fn args cenv group id ps body vals env1 env2 outs p q g b r) k)))
    (many StRetMatchScrut : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Core) scrut) (erased (List (Branch)) bs)
       (erased (Nat) ctor) (erased (List (Val)) fields) (erased (List (Nat)) ids) (erased (Core) body) (erased (Env) env1)
       (erased (Eval env scrut (Cons (Val) (VCon ctor fields) (Nil (Val)))) p) (erased (BranchOf bs ctor ids body) br)
       (erased (BindAll env ids fields env1) b)
       (erased (Stack env (CMatch scrut bs) env0 c0) k) ->
       (StepTo env0 c0 (SRet env0 c0 env scrut (Cons (Val) (VCon ctor fields) (Nil (Val))) p (KMatchScrut env0 c0 env scrut bs k))
          (SEval env0 c0 env1 body (KMatchBody env0 c0 env scrut bs ctor fields ids body env1 p br b k))))
    (many StRetMatchBody : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Core) scrut) (erased (List (Branch)) bs)
       (erased (Nat) ctor) (erased (List (Val)) fields) (erased (List (Nat)) ids) (erased (Core) body) (erased (Env) env1) (erased (List (Val)) outs)
       (erased (Eval env scrut (Cons (Val) (VCon ctor fields) (Nil (Val)))) p) (erased (BranchOf bs ctor ids body) br)
       (erased (BindAll env ids fields env1) b) (erased (Eval env1 body outs) r)
       (erased (Stack env (CMatch scrut bs) env0 c0) k) ->
       (StepTo env0 c0 (SRet env0 c0 env1 body outs r (KMatchBody env0 c0 env scrut bs ctor fields ids body env1 p br b k))
          (SRet env0 c0 env (CMatch scrut bs) outs (EvMatch env scrut bs ctor fields ids body env1 outs p br b r) k)))
    (many StRetListHead : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Core) c) (erased (List (Core)) cs) (erased (Val) v)
       (erased (Eval env c (Cons (Val) v (Nil (Val)))) p)
       (erased (ListStack env (Cons (Core) c cs) env0 c0) k) ->
       (StepTo env0 c0 (SRet env0 c0 env c (Cons (Val) v (Nil (Val))) p (KListHead env0 c0 env c cs k))
          (SEvalList env0 c0 env cs (KListTail env0 c0 env c cs v p k))))
    (many StRetLetRhs : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (List (Nat)) ids) (erased (Core) rhs) (erased (Core) rest)
       (erased (List (Val)) vals) (erased (Env) out)
       (erased (Eval env rhs vals) p) (erased (BindAll env ids vals out) b)
       (erased (Stack env (CStmt (SLet ids rhs) rest) env0 c0) k) ->
       (StepTo env0 c0 (SRet env0 c0 env rhs vals p (KLetRhs env0 c0 env ids rhs rest k))
          (SEval env0 c0 out rest (KStmtRest env0 c0 env (SLet ids rhs) rest out (EvLet env ids rhs vals out p b) k))))
    (many StRetStmtRest : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Stmt) stmt) (erased (Core) rest) (erased (Env) env1)
       (erased (List (Val)) outs)
       (erased (EvalStmt env stmt env1) p) (erased (Eval env1 rest outs) r)
       (erased (Stack env (CStmt stmt rest) env0 c0) k) ->
       (StepTo env0 c0 (SRet env0 c0 env1 rest outs r (KStmtRest env0 c0 env stmt rest env1 p k))
          (SRet env0 c0 env (CStmt stmt rest) outs (EvStmt env stmt rest env1 outs p r) k)))
    (many StRetAppArgs : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Core) h) (erased (List (Core)) args) (erased (Nat) ctor)
       (erased (List (Val)) vals)
       (erased (Eval env h (Cons (Val) (VAtom ctor) (Nil (Val)))) p) (erased (EvalList env args vals) q)
       (erased (Stack env (CApp h args) env0 c0) k) ->
       (StepTo env0 c0 (SRetList env0 c0 env args vals q (KAppArgs env0 c0 env h args ctor p k))
          (SRet env0 c0 env (CApp h args) (Cons (Val) (VCon ctor vals) (Nil (Val))) (EvApp env h args ctor vals p q) k)))
    (many StRetCallArgs : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Core) fn) (erased (List (Core)) args)
       (erased (Env) cenv) (erased (List (FnDef)) group) (erased (Nat) id) (erased (List (Nat)) ps) (erased (Core) body)
       (erased (List (Val)) vals) (erased (Env) env1) (erased (Env) env2)
       (erased (Eval env fn (Cons (Val) (VClo cenv group (MkFnDef id ps body)) (Nil (Val)))) p) (erased (EvalList env args vals) q)
       (erased (BindGroup cenv group group cenv env1) g) (erased (BindAll env1 ps vals env2) b)
       (erased (Stack env (CCall fn args) env0 c0) k) ->
       (StepTo env0 c0 (SRetList env0 c0 env args vals q (KCallArgs env0 c0 env fn args cenv group id ps body p k))
          (SEval env0 c0 env2 body (KCallBody env0 c0 env fn args cenv group id ps body vals env1 env2 p q g b k))))
    (many StRetValues : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (List (Core)) items) (erased (List (Val)) vals)
       (erased (EvalList env items vals) q)
       (erased (Stack env (CValues items) env0 c0) k) ->
       (StepTo env0 c0 (SRetList env0 c0 env items vals q (KValues env0 c0 env items k))
          (SRet env0 c0 env (CValues items) vals (EvValues env items vals q) k)))
    (many StRetListTail : (erased (Env) env0) (erased (Core) c0) (erased (Env) env) (erased (Core) c) (erased (List (Core)) cs) (erased (Val) v)
       (erased (List (Val)) vs)
       (erased (Eval env c (Cons (Val) v (Nil (Val)))) p) (erased (EvalList env cs vs) q)
       (erased (ListStack env (Cons (Core) c cs) env0 c0) k) ->
       (StepTo env0 c0 (SRetList env0 c0 env cs vs q (KListTail env0 c0 env c cs v p k))
          (SRetList env0 c0 env (Cons (Core) c cs) (Cons (Val) v vs) (EvLCons env c v cs vs p q) k))))
  ((Reaches : ((Env) env0) ((Core) c0) ((State env0 c0) s) ((State env0 c0) s2) -> Type)
    enum
    (many ReachHere : (erased (Env) env0) (erased (Core) c0) (erased (State env0 c0) s) -> (Reaches env0 c0 s s))
    (many ReachStep : (erased (Env) env0) (erased (Core) c0) (erased (State env0 c0) s) (erased (State env0 c0) s1) (erased (State env0 c0) s2)
       (erased (StepTo env0 c0 s s1) first) (erased (Reaches env0 c0 s1 s2) rest) -> (Reaches env0 c0 s s2))))
