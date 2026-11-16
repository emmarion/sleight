(def-fns _ $ (erased plus-total : (subterm erased (Nat) a) (erased (Nat) b) -> (erased (Nat) s) (erased (Plus a b s) p))
  (let-match erased a (Succ a2) ((Zero) (values b (PlusZ b))))
  (let ((erased s2) (erased p2)) (plus-total a2 b))
  (values (Succ s2) (PlusS a2 b s2 p2)))

(def-fns _ $ (erased plus-succ-right : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (subterm erased (Plus a b c) p) -> (erased (Plus a (Succ b) (Succ c)) q))
  (match erased p _
    ((PlusZ _) (PlusZ (Succ b)))
    ((PlusS a2 _ c2 p2) (PlusS a2 (Succ b) (Succ c2) (plus-succ-right a2 b c2 p2)))))

(def-fns _ $ (erased plus-comm : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (subterm erased (Plus a b c) p) -> (erased (Plus b a c) q))
  (match erased p _
    ((PlusZ _) (plus-zero b))
    ((PlusS a2 _ c2 p2) (plus-succ-right b a2 c2 (plus-comm a2 b c2 p2)))))

(def-fns _ $ (erased join : (erased (Nat) a) (erased (Nat) b) -> (erased (Nat) s) (erased (Plus b a s) ua) (erased (Plus a b s) ub))
  (let ((erased s) (erased ub)) (plus-total a b))
  (values s (plus-comm a b s ub) ub))

(def-fns _ $ (erased evallistd-weaken : (erased (Nat) k) (erased (Nat) n) (erased (Nat) m) (erased (Env) env) (erased (List (Core)) cs) (erased (List (Val)) vs)
    (subterm erased (Plus k n m) pl) (erased (EvalListD n env cs vs) d) -> (erased (EvalListD m env cs vs) p))
  (match erased pl _
    ((PlusZ _) d)
    ((PlusS k2 _ m2 pl2) (evallistd-step m2 env cs vs (evallistd-weaken k2 n m2 env cs vs pl2 d)))))

(def-fns _ $ (erased evalstmtd-weaken : (erased (Nat) k) (erased (Nat) n) (erased (Nat) m) (erased (Env) env) (erased (Stmt) s) (erased (Env) out)
    (subterm erased (Plus k n m) pl) (erased (EvalStmtD n env s out) d) -> (erased (EvalStmtD m env s out) p))
  (match erased pl _
    ((PlusZ _) d)
    ((PlusS k2 _ m2 pl2) (evalstmtd-step m2 env s out (evalstmtd-weaken k2 n m2 env s out pl2 d)))))

(def-fns _
  ((erased eval-sized : (erased (Env) env) (erased (Core) c) (erased (List (Val)) vs) (subterm erased (Eval env c vs) d) -> (erased (Nat) n) (erased (EvalD n env c vs) s))
    (match erased d _
      ((EvVar _ x v p) (values (Succ (Zero)) (DVar (Zero) env x v p)))
      ((EvApp _ h args ctor vals p q)
        (let ((erased a) (erased sp)) (eval-sized env h _ p))
        (let ((erased b) (erased sq)) (eval-list-sized env args vals q))
        (let ((erased f) (erased ua) (erased ub)) (join a b))
        (values (Succ f) (DApp f env h args ctor vals (evald-weaken b a f env h _ ua sp) (evallistd-weaken a b f env args vals ub sq))))
      ((EvCall _ fn args cenv group id ps body vals env1 env2 outs p q g bd r)
        (let ((erased a) (erased sp)) (eval-sized env fn _ p))
        (let ((erased b) (erased sq)) (eval-list-sized env args vals q))
        (let ((erased c2) (erased sr)) (eval-sized env2 body outs r))
        (let ((erased t) (erased ua) (erased ub)) (join a b))
        (let ((erased f) (erased ut) (erased uc)) (join t c2))
        (values (Succ f)
          (DCall f env fn args cenv group id ps body vals env1 env2 outs
            (evald-weaken c2 t f env fn _ ut (evald-weaken b a t env fn _ ua sp))
            (evallistd-weaken c2 t f env args vals ut (evallistd-weaken a b t env args vals ub sq))
            g bd
            (evald-weaken t c2 f env2 body outs uc sr))))
      ((EvMatch _ s bs ctor fields ids body env1 outs p br bd r)
        (let ((erased a) (erased sp)) (eval-sized env s _ p))
        (let ((erased b) (erased sr)) (eval-sized env1 body outs r))
        (let ((erased f) (erased ua) (erased ub)) (join a b))
        (values (Succ f) (DMatch f env s bs ctor fields ids body env1 outs (evald-weaken b a f env s _ ua sp) br bd (evald-weaken a b f env1 body outs ub sr))))
      ((EvValues _ items vals q)
        (let ((erased f) (erased sq)) (eval-list-sized env items vals q))
        (values (Succ f) (DValues f env items vals sq)))
      ((EvFormer _ t) (values (Succ (Zero)) (DFormer (Zero) env t)))
      ((EvToken _) (values (Succ (Zero)) (DToken (Zero) env)))
      ((EvStmt _ s rest env1 outs p q)
        (let ((erased a) (erased sp)) (eval-stmt-sized env s env1 p))
        (let ((erased b) (erased sq)) (eval-sized env1 rest outs q))
        (let ((erased f) (erased ua) (erased ub)) (join a b))
        (values (Succ f) (DStmt f env s rest env1 outs (evalstmtd-weaken b a f env s env1 ua sp) (evald-weaken a b f env1 rest outs ub sq))))))
  ((erased eval-list-sized : (erased (Env) env) (erased (List (Core)) cs) (erased (List (Val)) vs) (subterm erased (EvalList env cs vs) d) -> (erased (Nat) n) (erased (EvalListD n env cs vs) s))
    (let-match erased d (EvLCons _ c v rest vs2 p q) ((EvLNil _) (values (Succ (Zero)) (DLNil (Zero) env))))
    (let ((erased a) (erased sp)) (eval-sized env c _ p))
    (let ((erased b) (erased sq)) (eval-list-sized env rest vs2 q))
    (let ((erased f) (erased ua) (erased ub)) (join a b))
    (values (Succ f) (DLCons f env c v rest vs2 (evald-weaken b a f env c _ ua sp) (evallistd-weaken a b f env rest vs2 ub sq))))
  ((erased eval-stmt-sized : (erased (Env) env) (erased (Stmt) s) (erased (Env) out) (subterm erased (EvalStmt env s out) d) -> (erased (Nat) n) (erased (EvalStmtD n env s out) z))
    (let-match erased d (EvLet _ ids rhs vals _ p bd)
      ((EvDefLvl _ x) (values (Succ (Zero)) (DDefLvl (Zero) env x)))
      ((EvDefFns _ defs _ g) (values (Succ (Zero)) (DDefFns (Zero) env defs out g)))
      ((EvDefAdts _ ids _ b2) (values (Succ (Zero)) (DDefAdts (Zero) env ids out b2))))
    (let ((erased f) (erased sp)) (eval-sized env rhs vals p))
    (values (Succ f) (DLet f env ids rhs vals out sp bd))))

(def-lvl fuel-bound-lvl)

(def-adts $ (FuelBound : ((Env) env) ((Core) c) ((List (Val)) vs) -> Type)
  enum
  (many MkFuelBound : (erased (Env) env) (erased (Core) c) (erased (List (Val)) vs) (erased (Nat) n)
     (erased (Fn fuel-bound-lvl (erased (Nat) k) (erased (Nat) m) (erased (Plus k n m) pl) (many (Ran m env c) r) -> (many vs is v)) all)
     -> (FuelBound env c vs)))

(def-fns _ $ (erased fuel-bound : (erased (Env) env) (erased (Core) c) (erased (List (Val)) vs) (erased (Eval env c vs) d) -> (erased (FuelBound env c vs) b))
  (let ((erased n) (erased s)) (eval-sized env c vs d))
  (def-fns fuel-bound-lvl $ (erased all : (erased (Nat) k) (erased (Nat) m) (erased (Plus k n m) pl) (many (Ran m env c) r) -> (many vs is v))
    (fuel-is-unobservable k n m env c vs pl s r))
  (MkFuelBound env c vs n all))

(MkUnit)
