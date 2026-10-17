; mini/eval.sl -- big-step evaluation of core code (mini/core.sl) for the minimal language, as a relation
; with the function that derives it. An expression evaluates to as many values as its size (DESIGN.md
; section 27); a call rebinds the callee's group over the environment it closed over, then its parameters; a
; match selects the branch of the scrutinee's constructor and binds its fields. One session's proposal.

(def-adts
  ((Eval : ((Env) env) ((Core) c) ((List (Val)) vs) -> Type)
    enum
    (many EvVar : (erased (Env) env) (erased (Nat) x) (erased (Val) v) (erased (EnvOf env x v) p) -> (Eval env (CVar x) (Cons (Val) v (Nil (Val)))))
    (many EvApp : (erased (Env) env) (erased (Core) h) (erased (List (Core)) args) (erased (Nat) c) (erased (List (Val)) vals)
       (erased (Eval env h (Cons (Val) (VAtom c) (Nil (Val)))) p) (erased (EvalList env args vals) q) -> (Eval env (CApp h args) (Cons (Val) (VCon c vals) (Nil (Val)))))
    (many EvCall : (erased (Env) env) (erased (Core) fn) (erased (List (Core)) args) (erased (Env) cenv) (erased (List (FnDef)) group) (erased (Nat) id) (erased (List (Nat)) ps) (erased (Core) body)
       (erased (List (Val)) vals) (erased (Env) env1) (erased (Env) env2) (erased (List (Val)) outs)
       (erased (Eval env fn (Cons (Val) (VClo cenv group (MkFnDef id ps body)) (Nil (Val)))) p) (erased (EvalList env args vals) q)
       (erased (BindGroup cenv group group cenv env1) g) (erased (BindAll env1 ps vals env2) b) (erased (Eval env2 body outs) r) -> (Eval env (CCall fn args) outs))
    (many EvMatch : (erased (Env) env) (erased (Core) s) (erased (List (Branch)) bs) (erased (Nat) c) (erased (List (Val)) fields) (erased (List (Nat)) ids) (erased (Core) body)
       (erased (Env) env1) (erased (List (Val)) outs)
       (erased (Eval env s (Cons (Val) (VCon c fields) (Nil (Val)))) p) (erased (BranchOf bs c ids body) br) (erased (BindAll env ids fields env1) b) (erased (Eval env1 body outs) r)
       -> (Eval env (CMatch s bs) outs))
    (many EvValues : (erased (Env) env) (erased (List (Core)) items) (erased (List (Val)) vals) (erased (EvalList env items vals) q) -> (Eval env (CValues items) vals))
    (many EvFormer : (erased (Env) env) (erased (Term) t) -> (Eval env (CFormer t) (Cons (Val) (VFormer t env) (Nil (Val)))))
    (many EvToken : (erased (Env) env) -> (Eval env (CToken) (Cons (Val) (VToken) (Nil (Val)))))
    (many EvStmt : (erased (Env) env) (erased (Stmt) s) (erased (Core) rest) (erased (Env) env1) (erased (List (Val)) outs)
       (erased (EvalStmt env s env1) p) (erased (Eval env1 rest outs) q) -> (Eval env (CStmt s rest) outs)))
  ((EvalList : ((Env) env) ((List (Core)) cs) ((List (Val)) vs) -> Type)
    enum
    (many EvLNil : (erased (Env) env) -> (EvalList env (Nil (Core)) (Nil (Val))))
    (many EvLCons : (erased (Env) env) (erased (Core) c) (erased (Val) v) (erased (List (Core)) cs) (erased (List (Val)) vs)
       (erased (Eval env c (Cons (Val) v (Nil (Val)))) p) (erased (EvalList env cs vs) q) -> (EvalList env (Cons (Core) c cs) (Cons (Val) v vs))))
  ((EvalStmt : ((Env) env) ((Stmt) s) ((Env) out) -> Type)
    enum
    (many EvLet : (erased (Env) env) (erased (List (Nat)) ids) (erased (Core) rhs) (erased (List (Val)) vals) (erased (Env) out)
       (erased (Eval env rhs vals) p) (erased (BindAll env ids vals out) b) -> (EvalStmt env (SLet ids rhs) out))
    (many EvDefLvl : (erased (Env) env) (erased (Nat) x) -> (EvalStmt env (SDefLvl x) (ECons x (VToken) env)))
    (many EvDefFns : (erased (Env) env) (erased (List (FnDef)) defs) (erased (Env) out) (erased (BindGroup env defs defs env out) g) -> (EvalStmt env (SDefFns defs) out))
    (many EvDefAdts : (erased (Env) env) (erased (List (Nat)) ids) (erased (Env) out) (erased (BindAtoms env ids out) b) -> (EvalStmt env (SDefAdts ids) out))))

(def-adts
  ((Evaled : ((Env) env) ((Core) c) -> Type)
    enum
    (many MkEvaled : (erased (Env) env) (erased (Core) c) (many (List (Val)) vs) (erased (Eval env c vs) p) -> (Evaled env c))
    (many EvalStuck : (erased (Env) env) (erased (Core) c) -> (Evaled env c)))
  ((EvaledList : ((Env) env) ((List (Core)) cs) -> Type)
    enum
    (many MkEvaledList : (erased (Env) env) (erased (List (Core)) cs) (many (List (Val)) vs) (erased (EvalList env cs vs) p) -> (EvaledList env cs))
    (many EvalListStuck : (erased (Env) env) (erased (List (Core)) cs) -> (EvaledList env cs)))
  ((EvaledStmt : ((Env) env) ((Stmt) s) -> Type)
    enum
    (many MkEvaledStmt : (erased (Env) env) (erased (Stmt) s) (many (Env) out) (erased (EvalStmt env s out) p) -> (EvaledStmt env s))
    (many EvalStmtStuck : (erased (Env) env) (erased (Stmt) s) -> (EvaledStmt env s))))

(def-fns _
  ((many eval : (subterm many (Nat) fuel) (many (Env) env) (many (Core) c) -> (many (Evaled env c) r))
    (let-match many fuel (Succ f) ((Zero) (EvalStuck _ _)))
    (match many c _
      ((CVar x)
        (match many (env-dec env x) _
          ((EnvMiss _ _) (EvalStuck _ _))
          ((EnvHit _ _ v p) (MkEvaled _ _ (Cons _ v (Nil _)) $ EvVar env x v p))))
      ((CApp h args)
        (let-match many (notail $ eval f env h) (MkEvaled _ _ hv p) ((EvalStuck _ _) (EvalStuck _ _)))
        (let-match many hv (Cons _ v rest) ((Nil _) (EvalStuck _ _)))
        (let-match many rest (Nil _) (else (EvalStuck _ _)))
        (let-match many v (VAtom ctor) (else (EvalStuck _ _)))
        (match many (notail $ eval-list f env args) _
          ((EvalListStuck _ _) (EvalStuck _ _))
          ((MkEvaledList _ _ vals q) (MkEvaled _ _ (Cons _ (VCon ctor vals) (Nil _)) $ EvApp env h args ctor vals p q))))
      ((CCall fn args)
        (let-match many (notail $ eval f env fn) (MkEvaled _ _ fv p) ((EvalStuck _ _) (EvalStuck _ _)))
        (let-match many fv (Cons _ v rest) ((Nil _) (EvalStuck _ _)))
        (let-match many rest (Nil _) (else (EvalStuck _ _)))
        (let-match many v (VClo cenv group def) (else (EvalStuck _ _)))
        (let-match many def (MkFnDef id ps body))
        (let-match many (notail $ eval-list f env args) (MkEvaledList _ _ vals q) ((EvalListStuck _ _) (EvalStuck _ _)))
        (let ((many env1) (erased g)) (bind-group cenv group group cenv))
        (let-match many (bind-all env1 ps vals) (BDOk _ _ _ env2 bd) ((BDStuck _ _ _) (EvalStuck _ _)))
        (match many (notail $ eval f env2 body) _
          ((EvalStuck _ _) (EvalStuck _ _))
          ((MkEvaled _ _ outs r)
            (MkEvaled _ _ outs $ EvCall env fn args cenv group id ps body vals env1 env2 outs p q g bd r))))
      ((CMatch s bs)
        (let-match many (notail $ eval f env s) (MkEvaled _ _ sv p) ((EvalStuck _ _) (EvalStuck _ _)))
        (let-match many sv (Cons _ v rest) ((Nil _) (EvalStuck _ _)))
        (let-match many rest (Nil _) (else (EvalStuck _ _)))
        (let-match many v (VCon ctor fields) (else (EvalStuck _ _)))
        (let-match many (branch-dec bs ctor) (BrHit _ _ ids body br) ((BrMiss _ _) (EvalStuck _ _)))
        (let-match many (bind-all env ids fields) (BDOk _ _ _ env1 bd) ((BDStuck _ _ _) (EvalStuck _ _)))
        (match many (notail $ eval f env1 body) _
          ((EvalStuck _ _) (EvalStuck _ _))
          ((MkEvaled _ _ outs r) (MkEvaled _ _ outs $ EvMatch env s bs ctor fields ids body env1 outs p br bd r))))
      ((CValues items)
        (match many (notail $ eval-list f env items) _
          ((EvalListStuck _ _) (EvalStuck _ _))
          ((MkEvaledList _ _ vals q) (MkEvaled _ _ vals $ EvValues env items vals q))))
      ((CFormer t) (MkEvaled _ _ (Cons _ (VFormer t env) (Nil _)) $ EvFormer env t))
      ((CToken) (MkEvaled _ _ (Cons _ (VToken) (Nil _)) $ EvToken env))
      ((CStmt s rest)
        (let-match many (notail $ eval-stmt f env s) (MkEvaledStmt _ _ env1 p) ((EvalStmtStuck _ _) (EvalStuck _ _)))
        (match many (notail $ eval f env1 rest) _
          ((EvalStuck _ _) (EvalStuck _ _))
          ((MkEvaled _ _ outs q) (MkEvaled _ _ outs $ EvStmt env s rest env1 outs p q))))))
  ((many eval-list : (subterm many (Nat) fuel) (many (Env) env) (many (List (Core)) cs) -> (many (EvaledList env cs) r))
    (let-match many fuel (Succ f) ((Zero) (EvalListStuck _ _)))
    (let-match many cs (Cons _ c rest) ((Nil _) (MkEvaledList _ _ (Nil _) $ EvLNil env)))
    (let-match many (notail $ eval f env c) (MkEvaled _ _ vs p) ((EvalStuck _ _) (EvalListStuck _ _)))
    (let-match many vs (Cons _ v vrest) ((Nil _) (EvalListStuck _ _)))
    (let-match many vrest (Nil _) (else (EvalListStuck _ _)))
    (match many (notail $ eval-list f env rest) _
      ((EvalListStuck _ _) (EvalListStuck _ _))
      ((MkEvaledList _ _ vals q) (MkEvaledList _ _ (Cons _ v vals) $ EvLCons env c v rest vals p q))))
  ((many eval-stmt : (subterm many (Nat) fuel) (many (Env) env) (many (Stmt) s) -> (many (EvaledStmt env s) r))
    (let-match many fuel (Succ f) ((Zero) (EvalStmtStuck _ _)))
    (match many s _
      ((SLet ids rhs)
        (let-match many (notail $ eval f env rhs) (MkEvaled _ _ vals p) ((EvalStuck _ _) (EvalStmtStuck _ _)))
        (match many (bind-all env ids vals) _
          ((BDStuck _ _ _) (EvalStmtStuck _ _))
          ((BDOk _ _ _ out bd) (MkEvaledStmt _ _ out $ EvLet env ids rhs vals out p bd))))
      ((SDefLvl x) (MkEvaledStmt _ _ (ECons x (VToken) env) $ EvDefLvl env x))
      ((SDefFns defs)
        (let ((many out) (erased g)) (bind-group env defs defs env))
        (MkEvaledStmt _ _ out $ EvDefFns env defs out g))
      ((SDefAdts ids)
        (let ((many out) (erased b)) (bind-atoms env ids))
        (MkEvaledStmt _ _ out $ EvDefAdts env ids out b)))))

(MkUnit)
