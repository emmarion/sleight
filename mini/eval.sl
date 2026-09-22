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
       (erased (Eval env s (Cons (Val) (VCon c fields) (Nil (Val)))) p) (erased (BranchOf bs c ids body) br) (erased (BindAll env ids fields env1) b) (erased (Eval env1 body outs) r) ->
       (Eval env (CMatch s bs) outs))
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
    (match many fuel _
      ((Zero) (EvalStuck _ _))
      ((Succ f)
        (match many c _
          ((CVar x)
            (match many (env-dec env x) _
              ((EnvMiss a b) (EvalStuck _ _))
              ((EnvHit a b v p) (MkEvaled _ _ (Cons _ v (Nil _)) $ EvVar env x v p))))
          ((CApp h args)
            (match many (eval f env h) _
              ((EvalStuck a b) (EvalStuck _ _))
              ((MkEvaled a b hv p)
                (match many hv _
                  ((Cons d v rest)
                    (match many rest _
                      ((Nil e)
                        (match many v _
                          ((VAtom ctor)
                            (match many (eval-list f env args) _
                              ((EvalListStuck a2 b2) (EvalStuck _ _))
                              ((MkEvaledList a2 b2 vals q) (MkEvaled _ _ (Cons _ (VCon ctor vals) (Nil _)) $ EvApp env h args ctor vals p q))))
                          (else (EvalStuck _ _))))
                      (else (EvalStuck _ _))))
                  ((Nil d) (EvalStuck _ _))))))
          ((CCall fn args)
            (match many (eval f env fn) _
              ((EvalStuck a b) (EvalStuck _ _))
              ((MkEvaled a b fv p)
                (match many fv _
                  ((Cons d v rest)
                    (match many rest _
                      ((Nil e)
                        (match many v _
                          ((VClo cenv group def)
                            (match many def _
                              ((MkFnDef id ps body)
                                (match many (eval-list f env args) _
                                  ((EvalListStuck a2 b2) (EvalStuck _ _))
                                  ((MkEvaledList a2 b2 vals q)
                                    (let ((many env1) (erased g)) (bind-group cenv group group cenv))
                                    (match many (bind-all env1 ps vals) _
                                      ((BDStuck a3 b3 c3) (EvalStuck _ _))
                                      ((BDOk a3 b3 c3 env2 bd)
                                        (match many (eval f env2 body) _
                                          ((EvalStuck a4 b4) (EvalStuck _ _))
                                          ((MkEvaled a4 b4 outs r)
                                            (MkEvaled _ _ outs $ EvCall env fn args cenv group id ps body vals env1 env2 outs p q g bd r))))))))))
                          (else (EvalStuck _ _))))
                      (else (EvalStuck _ _))))
                  ((Nil d) (EvalStuck _ _))))))
          ((CMatch s bs)
            (match many (eval f env s) _
              ((EvalStuck a b) (EvalStuck _ _))
              ((MkEvaled a b sv p)
                (match many sv _
                  ((Cons d v rest)
                    (match many rest _
                      ((Nil e)
                        (match many v _
                          ((VCon ctor fields)
                            (match many (branch-dec bs ctor) _
                              ((BrMiss a2 b2) (EvalStuck _ _))
                              ((BrHit a2 b2 ids body br)
                                (match many (bind-all env ids fields) _
                                  ((BDStuck a3 b3 c3) (EvalStuck _ _))
                                  ((BDOk a3 b3 c3 env1 bd)
                                    (match many (eval f env1 body) _
                                      ((EvalStuck a4 b4) (EvalStuck _ _))
                                      ((MkEvaled a4 b4 outs r) (MkEvaled _ _ outs $ EvMatch env s bs ctor fields ids body env1 outs p br bd r))))))))
                          (else (EvalStuck _ _))))
                      (else (EvalStuck _ _))))
                  ((Nil d) (EvalStuck _ _))))))
          ((CValues items)
            (match many (eval-list f env items) _
              ((EvalListStuck a2 b2) (EvalStuck _ _))
              ((MkEvaledList a2 b2 vals q) (MkEvaled _ _ vals $ EvValues env items vals q))))
          ((CFormer t) (MkEvaled _ _ (Cons _ (VFormer t env) (Nil _)) $ EvFormer env t))
          ((CToken) (MkEvaled _ _ (Cons _ (VToken) (Nil _)) $ EvToken env))
          ((CStmt s rest)
            (match many (eval-stmt f env s) _
              ((EvalStmtStuck a b) (EvalStuck _ _))
              ((MkEvaledStmt a b env1 p)
                (match many (eval f env1 rest) _
                  ((EvalStuck a2 b2) (EvalStuck _ _))
                  ((MkEvaled a2 b2 outs q) (MkEvaled _ _ outs $ EvStmt env s rest env1 outs p q))))))))))
  ((many eval-list : (subterm many (Nat) fuel) (many (Env) env) (many (List (Core)) cs) -> (many (EvaledList env cs) r))
    (match many fuel _
      ((Zero) (EvalListStuck _ _))
      ((Succ f)
        (match many cs _
          ((Nil a) (MkEvaledList _ _ (Nil _) $ EvLNil env))
          ((Cons a c rest)
            (match many (eval f env c) _
              ((EvalStuck a1 b1) (EvalListStuck _ _))
              ((MkEvaled a1 b1 vs p)
                (match many vs _
                  ((Cons d v vrest)
                    (match many vrest _
                      ((Nil e)
                        (match many (eval-list f env rest) _
                          ((EvalListStuck a2 b2) (EvalListStuck _ _))
                          ((MkEvaledList a2 b2 vals q) (MkEvaledList _ _ (Cons _ v vals) $ EvLCons env c v rest vals p q))))
                      (else (EvalListStuck _ _))))
                  ((Nil d) (EvalListStuck _ _))))))))))
  ((many eval-stmt : (subterm many (Nat) fuel) (many (Env) env) (many (Stmt) s) -> (many (EvaledStmt env s) r))
    (match many fuel _
      ((Zero) (EvalStmtStuck _ _))
      ((Succ f)
        (match many s _
          ((SLet ids rhs)
            (match many (eval f env rhs) _
              ((EvalStuck a1 b1) (EvalStmtStuck _ _))
              ((MkEvaled a1 b1 vals p)
                (match many (bind-all env ids vals) _
                  ((BDStuck a3 b3 c3) (EvalStmtStuck _ _))
                  ((BDOk a3 b3 c3 out bd) (MkEvaledStmt _ _ out $ EvLet env ids rhs vals out p bd))))))
          ((SDefLvl x) (MkEvaledStmt _ _ (ECons x (VToken) env) $ EvDefLvl env x))
          ((SDefFns defs)
            (let ((many out) (erased g)) (bind-group env defs defs env))
            (MkEvaledStmt _ _ out $ EvDefFns env defs out g))
          ((SDefAdts ids)
            (let ((many out) (erased b)) (bind-atoms env ids))
            (MkEvaledStmt _ _ out $ EvDefAdts env ids out b)))))))

(MkUnit)
