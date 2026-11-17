; Copy of proto/roundtrip/spec.sl with one extra, nondeterministic Step rule, SNumUp (second review of 07).
(def-adts $ (Tm : -> Type)
  enum
  (many Var : (many (Nat) i) -> (Tm))
  (many Lam : (many (Tm) body) -> (Tm))
  (many App : (many (Tm) f) (many (Tm) a) -> (Tm))
  (many Num : (many (Nat) n) -> (Tm)))

(def-adts $ (Val : -> Type)
  enum
  (many VNum : (many (Nat) n) -> (Val))
  (many VClo : (many (Tm) body) (many (List $ Val) env) -> (Val)))

(def-adts $ (Frame : -> Type)
  enum
  (many KArg : (many (Tm) a) (many (List $ Val) env) -> (Frame))
  (many KCall : (many (Val) f) -> (Frame)))

(def-adts $ (MSt : -> Type)
  enum
  (many Ev : (many (Tm) t) (many (List $ Val) env) (many (List $ Frame) k) -> (MSt))
  (many Rt : (many (Val) v) (many (List $ Frame) k) -> (MSt)))

(def-adts $ (Res : -> Type)
  enum
  (many RVal : (many (Val) v) -> (Res))
  (many RStuck : -> (Res)))

(def-adts $ (Out : -> Type)
  enum
  (many Go : (many (MSt) s) -> (Out))
  (many Halt : (many (Res) r) -> (Out)))

(def-adts $ (NoNth : (Type A) ((List A) xs) ((Nat) i) -> Type)
  enum
  (many NoNil : (erased Type A) (erased (Nat) i) -> (NoNth A (Nil A) i))
  (many NoCons : (erased Type A) (erased A x) (erased (List A) xs) (erased (Nat) i) (erased (NoNth A xs i) p)
     -> (NoNth A (Cons A x xs) (Succ i))))

(def-adts $ (Step : ((MSt) s) ((Out) o) -> Type)
  enum
  (many SVar : (erased (Nat) i) (erased (List $ Val) env) (erased (List $ Frame) k) (erased (Val) v)
     (erased (Nth (Val) env i v) p) -> (Step (Ev (Var i) env k) (Go $ Rt v k)))
  (many SVarNo : (erased (Nat) i) (erased (List $ Val) env) (erased (List $ Frame) k)
     (erased (NoNth (Val) env i) p) -> (Step (Ev (Var i) env k) (Halt $ RStuck)))
  (many SLam : (erased (Tm) b) (erased (List $ Val) env) (erased (List $ Frame) k)
     -> (Step (Ev (Lam b) env k) (Go $ Rt (VClo b env) k)))
  (many SApp : (erased (Tm) f) (erased (Tm) a) (erased (List $ Val) env) (erased (List $ Frame) k)
     -> (Step (Ev (App f a) env k) (Go $ Ev f env $ Cons (Frame) (KArg a env) k)))
  (many SNum : (erased (Nat) n) (erased (List $ Val) env) (erased (List $ Frame) k)
     -> (Step (Ev (Num n) env k) (Go $ Rt (VNum n) k)))
  (many SNumUp : (erased (Nat) n) (erased (List $ Val) env) (erased (List $ Frame) k)
     -> (Step (Ev (Num n) env k) (Go $ Rt (VNum (Succ n)) k)))
  (many SRetNil : (erased (Val) v) -> (Step (Rt v (Nil (Frame))) (Halt $ RVal v)))
  (many SArg : (erased (Val) v) (erased (Tm) a) (erased (List $ Val) env) (erased (List $ Frame) k)
     -> (Step (Rt v $ Cons (Frame) (KArg a env) k) (Go $ Ev a env $ Cons (Frame) (KCall v) k)))
  (many SCall : (erased (Val) v) (erased (Tm) b) (erased (List $ Val) env) (erased (List $ Frame) k)
     -> (Step (Rt v $ Cons (Frame) (KCall $ VClo b env) k) (Go $ Ev b (Cons (Val) v env) k)))
  (many SCallNum : (erased (Val) v) (erased (Nat) n) (erased (List $ Frame) k)
     -> (Step (Rt v $ Cons (Frame) (KCall $ VNum n) k) (Halt $ RStuck))))

(def-adts $ (Runs : ((MSt) s) ((Res) r) -> Type)
  enum
  (many RunHalt : (erased (MSt) s) (erased (Res) r) (erased (Step s (Halt r)) st) -> (Runs s r))
  (many RunGo : (erased (MSt) s) (erased (MSt) s2) (erased (Res) r) (erased (Step s (Go s2)) st)
     (erased (Runs s2 r) rest) -> (Runs s r)))

(def-adts $ (Reach : ((MSt) a) ((MSt) b) -> Type)
  enum
  (many ReachZ : (erased (MSt) a) -> (Reach a a))
  (many ReachS : (erased (MSt) a) (erased (MSt) b) (erased (MSt) c) (erased (Reach a b) r)
     (erased (Step b (Go c)) st) -> (Reach a c)))

(def-adts $ (Ctor : -> Type)
  enum
  (many CZero : -> (Ctor))
  (many CSucc : -> (Ctor))
  (many CClo : -> (Ctor)))

(def-adts $ (Known : -> Type)
  enum
  (many KNone : -> (Known))
  (many KIs : (many (Ctor) c) -> (Known)))

(def-adts $ (Ent : -> Type)
  enum
  (many MkEnt : (many (Val) v) (many (Known) k) -> (Ent)))

(def-adts $ (Stmt : -> Type)
  enum
  (many Let : (many (Tm) t) -> (Stmt))
  (many Assert : (many (Nat) i) (many (Ctor) c) -> (Stmt))
  (many Need : (many (Nat) i) (many (Ctor) c) -> (Stmt)))

(def-adts $ (Vals : ((List $ Ent) es) ((List $ Val) vs) -> Type)
  enum
  (many ValsNil : -> (Vals (Nil (Ent)) (Nil (Val))))
  (many ValsCons : (erased (Val) v) (erased (Known) k) (erased (List $ Ent) es) (erased (List $ Val) vs)
     (erased (Vals es vs) p) -> (Vals (Cons (Ent) (MkEnt v k) es) (Cons (Val) v vs))))

(def-adts $ (Evals : ((List $ Ent) es) ((Tm) t) ((Val) v) -> Type)
  enum
  (many MkEvals : (erased (List $ Ent) es) (erased (Tm) t) (erased (Val) v) (erased (List $ Val) env)
     (erased (Vals es env) ve) (erased (Runs (Ev t env (Nil (Frame))) (RVal v)) r) -> (Evals es t v)))

(def-adts $ (Sticks : ((List $ Ent) es) ((Tm) t) -> Type)
  enum
  (many MkSticks : (erased (List $ Ent) es) (erased (Tm) t) (erased (List $ Val) env)
     (erased (Vals es env) ve) (erased (Runs (Ev t env (Nil (Frame))) (RStuck)) r) -> (Sticks es t)))

(def-adts $ (Head : ((Val) v) ((Ctor) c) -> Type)
  enum
  (many HZero : -> (Head (VNum (Zero)) (CZero)))
  (many HSucc : (erased (Nat) n) -> (Head (VNum $ Succ n) (CSucc)))
  (many HClo : (erased (Tm) b) (erased (List $ Val) env) -> (Head (VClo b env) (CClo))))

(def-adts $ (CNe : ((Ctor) a) ((Ctor) b) -> Type)
  enum
  (many NeZS : -> (CNe (CZero) (CSucc)))
  (many NeZC : -> (CNe (CZero) (CClo)))
  (many NeSZ : -> (CNe (CSucc) (CZero)))
  (many NeSC : -> (CNe (CSucc) (CClo)))
  (many NeCZ : -> (CNe (CClo) (CZero)))
  (many NeCS : -> (CNe (CClo) (CSucc))))

(def-adts $ (NotIs : ((Known) k) ((Ctor) c) -> Type)
  enum
  (many NotNone : (erased (Ctor) c) -> (NotIs (KNone) c))
  (many NotOther : (erased (Ctor) a) (erased (Ctor) c) (erased (CNe a c) ne) -> (NotIs (KIs a) c)))

(def-adts $ (Elab : ((List $ Ent) es) ((List $ Stmt) p) -> Type)
  enum
  (many ElNil : (erased (List $ Ent) es) -> (Elab es (Nil (Stmt))))
  (many ElLet : (erased (List $ Ent) es) (erased (Tm) t) (erased (List $ Stmt) rest) (erased (Val) v)
     (erased (Evals es t v) ev) (erased (Elab (Cons (Ent) (MkEnt v (KNone)) es) rest) d)
     -> (Elab es (Cons (Stmt) (Let t) rest)))
  (many ElAssert : (erased (List $ Ent) es) (erased (Nat) i) (erased (Ctor) c) (erased (List $ Stmt) rest)
     (erased (Val) v) (erased (Known) k) (erased (List $ Ent) es2)
     (erased (Nth (Ent) es i (MkEnt v k)) nth) (erased (Head v c) hd)
     (erased (SetNth (Ent) es i (MkEnt v (KIs c)) es2) sn) (erased (Elab es2 rest) d)
     -> (Elab es (Cons (Stmt) (Assert i c) rest)))
  (many ElNeed : (erased (List $ Ent) es) (erased (Nat) i) (erased (Ctor) c) (erased (List $ Stmt) rest)
     (erased (Val) v) (erased (Nth (Ent) es i (MkEnt v (KIs c))) nth) (erased (Elab es rest) d)
     -> (Elab es (Cons (Stmt) (Need i c) rest))))

(def-adts $ (Fails : ((List $ Ent) es) ((List $ Stmt) p) -> Type)
  enum
  (many FLetStuck : (erased (List $ Ent) es) (erased (Tm) t) (erased (List $ Stmt) rest)
     (erased (Sticks es t) sk) -> (Fails es (Cons (Stmt) (Let t) rest)))
  (many FLetRest : (erased (List $ Ent) es) (erased (Tm) t) (erased (List $ Stmt) rest) (erased (Val) v)
     (erased (Evals es t v) ev) (erased (Fails (Cons (Ent) (MkEnt v (KNone)) es) rest) f)
     -> (Fails es (Cons (Stmt) (Let t) rest)))
  (many FAssertRange : (erased (List $ Ent) es) (erased (Nat) i) (erased (Ctor) c) (erased (List $ Stmt) rest)
     (erased (NoNth (Ent) es i) nn) -> (Fails es (Cons (Stmt) (Assert i c) rest)))
  (many FAssertHead : (erased (List $ Ent) es) (erased (Nat) i) (erased (Ctor) c) (erased (List $ Stmt) rest)
     (erased (Val) v) (erased (Known) k) (erased (Ctor) c2)
     (erased (Nth (Ent) es i (MkEnt v k)) nth) (erased (Head v c2) hd) (erased (CNe c c2) ne)
     -> (Fails es (Cons (Stmt) (Assert i c) rest)))
  (many FAssertRest : (erased (List $ Ent) es) (erased (Nat) i) (erased (Ctor) c) (erased (List $ Stmt) rest)
     (erased (Val) v) (erased (Known) k) (erased (List $ Ent) es2)
     (erased (Nth (Ent) es i (MkEnt v k)) nth) (erased (Head v c) hd)
     (erased (SetNth (Ent) es i (MkEnt v (KIs c)) es2) sn) (erased (Fails es2 rest) f)
     -> (Fails es (Cons (Stmt) (Assert i c) rest)))
  (many FNeedRange : (erased (List $ Ent) es) (erased (Nat) i) (erased (Ctor) c) (erased (List $ Stmt) rest)
     (erased (NoNth (Ent) es i) nn) -> (Fails es (Cons (Stmt) (Need i c) rest)))
  (many FNeedFact : (erased (List $ Ent) es) (erased (Nat) i) (erased (Ctor) c) (erased (List $ Stmt) rest)
     (erased (Val) v) (erased (Known) k) (erased (Nth (Ent) es i (MkEnt v k)) nth) (erased (NotIs k c) ni)
     -> (Fails es (Cons (Stmt) (Need i c) rest)))
  (many FNeedRest : (erased (List $ Ent) es) (erased (Nat) i) (erased (Ctor) c) (erased (List $ Stmt) rest)
     (erased (Val) v) (erased (Nth (Ent) es i (MkEnt v (KIs c))) nth) (erased (Fails es rest) f)
     -> (Fails es (Cons (Stmt) (Need i c) rest))))

(def-adts $ (Verdict : ((List $ Stmt) p) -> Type)
  enum
  (many Accepted : (erased (List $ Stmt) p) (erased (Elab (Nil (Ent)) p) d) -> (Verdict p))
  (many Rejected : (erased (List $ Stmt) p) (erased (Fails (Nil (Ent)) p) f) (many (String) why) -> (Verdict p)))

(def-adts $ (Turn : ((TyCtor ((List $ Stmt) p) -> Type) S) ((List $ Stmt) p) -> Type)
  enum
  (many More : (erased (TyCtor ((List $ Stmt) p) -> Type) S) (erased (List $ Stmt) p) (many (S p) s) -> (Turn S p))
  (many Fin : (erased (TyCtor ((List $ Stmt) p) -> Type) S) (erased (List $ Stmt) p) (many (Verdict p) v) -> (Turn S p)))
