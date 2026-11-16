(def-fns _ $ (erased env-of-unique : (erased (Env) env) (erased (Nat) x) (erased (Val) v) (erased (Val) w) (subterm erased (EnvOf env x v) p) (erased (EnvOf env x w) q) -> (erased (Eq (Val) v w) e))
  (match erased p _
    ((EnvHere _ _ _)
      (match erased q _
        ((EnvHere _ _ _) (Refl (Val) v))
        (absurd (EnvThere _ _ _ _ _ n _) (neq-irrefl x n))))
    ((EnvThere _ _ _ _ rest n p2)
      (match erased q _
        (absurd (EnvHere _ _ _) (neq-irrefl x n))
        ((EnvThere _ _ _ _ _ _ q2) (env-of-unique rest x v w p2 q2))))))

(def-fns _ $ (erased bind-all-unique : (erased (Env) env) (erased (List (Nat)) ids) (erased (List (Val)) vs) (erased (Env) o1) (erased (Env) o2) (subterm erased (BindAll env ids vs o1) p) (erased (BindAll env ids vs o2) q) -> (erased (Eq (Env) o1 o2) e))
  (match erased p _
    ((BANil _) (match erased q _ ((BANil _) (Refl (Env) env))))
    ((BACons _ x v ids2 vs2 _ p2) (let-match erased q (BACons _ _ _ _ _ _ q2)) (bind-all-unique (ECons x v env) ids2 vs2 o1 o2 p2 q2))))

(def-fns _ $ (erased bind-group-unique : (erased (Env) cenv) (erased (List (FnDef)) group) (erased (List (FnDef)) defs) (erased (Env) env) (erased (Env) o1) (erased (Env) o2)
    (subterm erased (BindGroup cenv group defs env o1) p) (erased (BindGroup cenv group defs env o2) q) -> (erased (Eq (Env) o1 o2) e))
  (match erased p _
    ((BGNil _ _ _) (match erased q _ ((BGNil _ _ _) (Refl (Env) env))))
    ((BGCons _ _ id ps body rest _ _ p2)
      (let-match erased q (BGCons _ _ _ _ _ _ _ _ q2))
      (bind-group-unique cenv group rest (ECons id (VClo cenv group (MkFnDef id ps body)) env) o1 o2 p2 q2))))

(def-fns _ $ (erased bind-atoms-unique : (erased (Env) env) (erased (List (Nat)) ids) (erased (Env) o1) (erased (Env) o2) (subterm erased (BindAtoms env ids o1) p) (erased (BindAtoms env ids o2) q) -> (erased (Eq (Env) o1 o2) e))
  (match erased p _
    ((BTNil _) (match erased q _ ((BTNil _) (Refl (Env) env))))
    ((BTCons _ x rest _ p2) (let-match erased q (BTCons _ _ _ _ q2)) (bind-atoms-unique (ECons x (VAtom x) env) rest o1 o2 p2 q2))))

(def-fns _ $ (erased branch-of-unique : (erased (List (Branch)) bs) (erased (Nat) c) (erased (List (Nat)) f1) (erased (List (Nat)) f2) (erased (Core) b1) (erased (Core) b2)
    (subterm erased (BranchOf bs c f1 b1) p) (erased (BranchOf bs c f2 b2) q) -> (erased (Eq (List (Nat)) f1 f2) ef) (erased (Eq (Core) b1 b2) eb))
  (match erased p _
    ((BrHere _ _ _ _)
      (match erased q _
        ((BrHere _ _ _ _) (values (Refl (List (Nat)) f1) (Refl (Core) b1)))
        (absurd (BrThere _ _ _ _ _ _ _ n _) (neq-irrefl c n))))
    ((BrThere _ _ _ _ _ _ rest n p2)
      (match erased q _
        (absurd (BrHere _ _ _ _) (neq-irrefl c n))
        ((BrThere _ _ _ _ _ _ _ _ q2) (branch-of-unique rest c f1 f2 b1 b2 p2 q2))))))

(def-fns _
  ((erased eval-unique : (erased (Env) env) (erased (Core) c) (erased (List (Val)) v1) (erased (List (Val)) v2) (subterm erased (Eval env c v1) p) (erased (Eval env c v2) q) -> (erased (Eq (List (Val)) v1 v2) e))
    (match erased p _
      ((EvVar _ x v pe)
        (let-match erased q (EvVar _ _ w qe))
        (match erased (env-of-unique env x v w pe qe) _ ((Refl _ _) (Refl (List (Val)) v1))))
      ((EvApp _ h args ctor vals ph pa)
        (let-match erased q (EvApp _ _ _ ctor2 vals2 qh qa))
        (let-match erased (eval-unique env h (Cons _ (VAtom ctor) (Nil _)) (Cons _ (VAtom ctor2) (Nil _)) ph qh) (Refl _ _))
        (match erased (eval-list-unique env args vals vals2 pa qa) _ ((Refl _ _) (Refl (List (Val)) v1))))
      ((EvCall _ fn args cenv group id ps body vals env1 env2 _ pf pa pg pb pr)
        (let-match erased q (EvCall _ _ _ cenv3 group3 id3 ps3 body3 vals3 env13 env23 _ qf qa qg qb qr))
        (let-match erased (eval-unique env fn (Cons _ (VClo cenv group (MkFnDef id ps body)) (Nil _)) (Cons _ (VClo cenv3 group3 (MkFnDef id3 ps3 body3)) (Nil _)) pf qf) (Refl _ _))
        (let-match erased (eval-list-unique env args vals vals3 pa qa) (Refl _ _))
        (let-match erased (bind-group-unique cenv group group cenv env1 env13 pg qg) (Refl _ _))
        (let-match erased (bind-all-unique env1 ps vals env2 env23 pb qb) (Refl _ _))
        (eval-unique env2 body v1 v2 pr qr))
      ((EvMatch _ s bs ctor fields ids body env1 _ ps pbr pb pr)
        (let-match erased q (EvMatch _ _ _ ctor3 fields3 ids3 body3 env13 _ qs qbr qb qr))
        (let-match erased (eval-unique env s (Cons _ (VCon ctor fields) (Nil _)) (Cons _ (VCon ctor3 fields3) (Nil _)) ps qs) (Refl _ _))
        (let ((erased ef) (erased eb)) (branch-of-unique bs ctor ids ids3 body body3 pbr qbr))
        (let-match erased ef (Refl _ _))
        (let-match erased eb (Refl _ _))
        (let-match erased (bind-all-unique env ids fields env1 env13 pb qb) (Refl _ _))
        (eval-unique env1 body v1 v2 pr qr))
      ((EvValues _ items _ pl) (let-match erased q (EvValues _ _ _ ql)) (eval-list-unique env items v1 v2 pl ql))
      ((EvFormer _ _) (match erased q _ ((EvFormer _ _) (Refl (List (Val)) v1))))
      ((EvToken _) (match erased q _ ((EvToken _) (Refl (List (Val)) v1))))
      ((EvStmt _ s rest env1 _ ps pr)
        (let-match erased q (EvStmt _ _ _ env13 _ qs qr))
        (let-match erased (eval-stmt-unique env s env1 env13 ps qs) (Refl _ _))
        (eval-unique env1 rest v1 v2 pr qr))))
  ((erased eval-list-unique : (erased (Env) env) (erased (List (Core)) cs) (erased (List (Val)) v1) (erased (List (Val)) v2) (subterm erased (EvalList env cs v1) p) (erased (EvalList env cs v2) q) -> (erased (Eq (List (Val)) v1 v2) e))
    (match erased p _
      ((EvLNil _) (match erased q _ ((EvLNil _) (Refl (List (Val)) v1))))
      ((EvLCons _ c v rest vs ph pt)
        (let-match erased q (EvLCons _ _ w _ ws qh qt))
        (let-match erased (eval-unique env c (Cons _ v (Nil _)) (Cons _ w (Nil _)) ph qh) (Refl _ _))
        (match erased (eval-list-unique env rest vs ws pt qt) _ ((Refl _ _) (Refl (List (Val)) v1))))))
  ((erased eval-stmt-unique : (erased (Env) env) (erased (Stmt) s) (erased (Env) o1) (erased (Env) o2) (subterm erased (EvalStmt env s o1) p) (erased (EvalStmt env s o2) q) -> (erased (Eq (Env) o1 o2) e))
    (match erased p _
      ((EvLet _ ids rhs vals _ pr pb)
        (let-match erased q (EvLet _ _ _ vals3 _ qr qb))
        (let-match erased (eval-unique env rhs vals vals3 pr qr) (Refl _ _))
        (bind-all-unique env ids vals o1 o2 pb qb))
      ((EvDefLvl _ _) (match erased q _ ((EvDefLvl _ _) (Refl (Env) o1))))
      ((EvDefFns _ defs _ pg) (let-match erased q (EvDefFns _ _ _ qg)) (bind-group-unique env defs defs env o1 o2 pg qg))
      ((EvDefAdts _ ids _ pb) (let-match erased q (EvDefAdts _ _ _ qb)) (bind-atoms-unique env ids o1 o2 pb qb)))))

(MkUnit)
