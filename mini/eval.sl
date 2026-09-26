; mini/eval.sl -- big-step evaluation of core code (mini/core.sl) for the minimal language, as a relation
; with the function that derives it. An expression evaluates to as many values as its size (DESIGN.md
; section 16); a call rebinds the callee's group over the environment it closed over, then its parameters; a
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
          ((EnvMiss a b) (EvalStuck _ _))
          ((EnvHit a b v p) (MkEvaled _ _ (Cons _ v (Nil _)) $ EvVar env x v p))))
      ((CApp h args)
        (let-match many (notail $ eval f env h) (MkEvaled a b hv p) ((EvalStuck a b) (EvalStuck _ _)))
        (let-match many hv (Cons d v rest) ((Nil d) (EvalStuck _ _)))
        (let-match many rest (Nil e) (else (EvalStuck _ _)))
        (let-match many v (VAtom ctor) (else (EvalStuck _ _)))
        (match many (notail $ eval-list f env args) _
          ((EvalListStuck a2 b2) (EvalStuck _ _))
          ((MkEvaledList a2 b2 vals q) (MkEvaled _ _ (Cons _ (VCon ctor vals) (Nil _)) $ EvApp env h args ctor vals p q))))
      ((CCall fn args)
        (let-match many (notail $ eval f env fn) (MkEvaled a b fv p) ((EvalStuck a b) (EvalStuck _ _)))
        (let-match many fv (Cons d v rest) ((Nil d) (EvalStuck _ _)))
        (let-match many rest (Nil e) (else (EvalStuck _ _)))
        (let-match many v (VClo cenv group def) (else (EvalStuck _ _)))
        (let-match many def (MkFnDef id ps body))
        (let-match many (notail $ eval-list f env args) (MkEvaledList a2 b2 vals q) ((EvalListStuck a2 b2) (EvalStuck _ _)))
        (let ((many env1) (erased g)) (bind-group cenv group group cenv))
        (let-match many (bind-all env1 ps vals) (BDOk a3 b3 c3 env2 bd) ((BDStuck a3 b3 c3) (EvalStuck _ _)))
        (match many (notail $ eval f env2 body) _
          ((EvalStuck a4 b4) (EvalStuck _ _))
          ((MkEvaled a4 b4 outs r)
            (MkEvaled _ _ outs $ EvCall env fn args cenv group id ps body vals env1 env2 outs p q g bd r))))
      ((CMatch s bs)
        (let-match many (notail $ eval f env s) (MkEvaled a b sv p) ((EvalStuck a b) (EvalStuck _ _)))
        (let-match many sv (Cons d v rest) ((Nil d) (EvalStuck _ _)))
        (let-match many rest (Nil e) (else (EvalStuck _ _)))
        (let-match many v (VCon ctor fields) (else (EvalStuck _ _)))
        (let-match many (branch-dec bs ctor) (BrHit a2 b2 ids body br) ((BrMiss a2 b2) (EvalStuck _ _)))
        (let-match many (bind-all env ids fields) (BDOk a3 b3 c3 env1 bd) ((BDStuck a3 b3 c3) (EvalStuck _ _)))
        (match many (notail $ eval f env1 body) _
          ((EvalStuck a4 b4) (EvalStuck _ _))
          ((MkEvaled a4 b4 outs r) (MkEvaled _ _ outs $ EvMatch env s bs ctor fields ids body env1 outs p br bd r))))
      ((CValues items)
        (match many (notail $ eval-list f env items) _
          ((EvalListStuck a2 b2) (EvalStuck _ _))
          ((MkEvaledList a2 b2 vals q) (MkEvaled _ _ vals $ EvValues env items vals q))))
      ((CFormer t) (MkEvaled _ _ (Cons _ (VFormer t env) (Nil _)) $ EvFormer env t))
      ((CToken) (MkEvaled _ _ (Cons _ (VToken) (Nil _)) $ EvToken env))
      ((CStmt s rest)
        (let-match many (notail $ eval-stmt f env s) (MkEvaledStmt a b env1 p) ((EvalStmtStuck a b) (EvalStuck _ _)))
        (match many (notail $ eval f env1 rest) _
          ((EvalStuck a2 b2) (EvalStuck _ _))
          ((MkEvaled a2 b2 outs q) (MkEvaled _ _ outs $ EvStmt env s rest env1 outs p q))))))
  ((many eval-list : (subterm many (Nat) fuel) (many (Env) env) (many (List (Core)) cs) -> (many (EvaledList env cs) r))
    (let-match many fuel (Succ f) ((Zero) (EvalListStuck _ _)))
    (let-match many cs (Cons a c rest) ((Nil a) (MkEvaledList _ _ (Nil _) $ EvLNil env)))
    (let-match many (notail $ eval f env c) (MkEvaled a1 b1 vs p) ((EvalStuck a1 b1) (EvalListStuck _ _)))
    (let-match many vs (Cons d v vrest) ((Nil d) (EvalListStuck _ _)))
    (let-match many vrest (Nil e) (else (EvalListStuck _ _)))
    (match many (notail $ eval-list f env rest) _
      ((EvalListStuck a2 b2) (EvalListStuck _ _))
      ((MkEvaledList a2 b2 vals q) (MkEvaledList _ _ (Cons _ v vals) $ EvLCons env c v rest vals p q))))
  ((many eval-stmt : (subterm many (Nat) fuel) (many (Env) env) (many (Stmt) s) -> (many (EvaledStmt env s) r))
    (let-match many fuel (Succ f) ((Zero) (EvalStmtStuck _ _)))
    (match many s _
      ((SLet ids rhs)
        (let-match many (notail $ eval f env rhs) (MkEvaled a1 b1 vals p) ((EvalStuck a1 b1) (EvalStmtStuck _ _)))
        (match many (bind-all env ids vals) _
          ((BDStuck a3 b3 c3) (EvalStmtStuck _ _))
          ((BDOk a3 b3 c3 out bd) (MkEvaledStmt _ _ out $ EvLet env ids rhs vals out p bd))))
      ((SDefLvl x) (MkEvaledStmt _ _ (ECons x (VToken) env) $ EvDefLvl env x))
      ((SDefFns defs)
        (let ((many out) (erased g)) (bind-group env defs defs env))
        (MkEvaledStmt _ _ out $ EvDefFns env defs out g))
      ((SDefAdts ids)
        (let ((many out) (erased b)) (bind-atoms env ids))
        (MkEvaledStmt _ _ out $ EvDefAdts env ids out b)))))

(MkUnit)
