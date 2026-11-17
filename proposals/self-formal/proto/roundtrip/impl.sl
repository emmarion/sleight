(def-adts $ (Find : (Type A) ((List A) xs) ((Nat) i) -> Type)
  enum
  (many FoundAt : (erased Type A) (erased (List A) xs) (erased (Nat) i) (many A x) (erased (Nth A xs i x) p) -> (Find A xs i))
  (many MissingAt : (erased Type A) (erased (List A) xs) (erased (Nat) i) (erased (NoNth A xs i) nn) -> (Find A xs i)))

(def-fns _ $ (many nth-find : (erased Type A) (subterm many (List A) xs) (many (Nat) i) -> (many (Find A xs i) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (MissingAt A xs i (NoNil A i))))
  (let-match many i (Succ j) ((Zero) (FoundAt A xs i x (NthHere A x rest))))
  (match many (notail (nth-find A rest j)) _
    ((FoundAt _ _ _ y p) (FoundAt A xs i y (NthThere A x rest j y p)))
    ((MissingAt _ _ _ nn) (MissingAt A xs i (NoCons A x rest j nn)))))

(def-fns _ $ (many set-nth : (erased Type A) (subterm many (List A) xs) (many (Nat) i) (many A y)
    (erased A x) (erased (Nth A xs i x) p) -> (many (List A) ys) (erased (SetNth A xs i y ys) q))
  (let-match many xs (Cons _ x0 rest) (absurd (Nil _) (match erased p _)))
  (let-match many i (Succ j) ((Zero) (let-match erased p (NthHere _ _ _)) (values (Cons A y rest) (SetHere A x0 y rest))))
  (let-match erased p (NthThere _ _ _ _ _ p1))
  (let ((many ys1) (erased q1)) (notail (set-nth A rest j y x p1)))
  (values (Cons A x0 ys1) (SetThere A x0 rest j y ys1 q1)))

(def-fns _ $ (many vals : (subterm many (List $ Ent) es) -> (many (List $ Val) vs) (erased (Vals es vs) p))
  (let-match many es (Cons _ e rest) ((Nil _) (values (Nil (Val)) (ValsNil))))
  (let-match many e (MkEnt v k))
  (let ((many vs1) (erased p1)) (notail (vals rest)))
  (values (Cons (Val) v vs1) (ValsCons v k rest vs1 p1)))

(def-fns _ $ (many head : (many (Val) v) -> (many (Ctor) c) (erased (Head v c) h))
  (let-match many v (VNum n) ((VClo b env) (values (CClo) (HClo b env))))
  (match many n _ ((Zero) (values (CZero) (HZero))) ((Succ m) (values (CSucc) (HSucc m)))))

(def-adts $ (CDec : ((Ctor) a) ((Ctor) b) -> Type)
  enum
  (many CSame : (erased (Ctor) a) -> (CDec a a))
  (many CDiff : (erased (Ctor) a) (erased (Ctor) b) (erased (CNe a b) ne) -> (CDec a b)))

(def-fns _ $ (many ctor-dec : (many (Ctor) a) (many (Ctor) b) -> (many (CDec a b) r))
  (match many a _
    ((CZero) (match many b _ ((CZero) (CSame a)) ((CSucc) (CDiff a b (NeZS))) ((CClo) (CDiff a b (NeZC)))))
    ((CSucc) (match many b _ ((CZero) (CDiff a b (NeSZ))) ((CSucc) (CSame a)) ((CClo) (CDiff a b (NeSC)))))
    ((CClo) (match many b _ ((CZero) (CDiff a b (NeCZ))) ((CSucc) (CDiff a b (NeCS))) ((CClo) (CSame a))))))

(def-fns _ $ (many mstep : (many (MSt) s) -> (many (Out) o) (erased (Step s o) p))
  (match many s _
    ((Ev t env k)
      (let-match many t (Var i)
        ((Lam b) (values (Go $ Rt (VClo b env) k) (SLam b env k)))
        ((App f a) (values (Go $ Ev f env $ Cons (Frame) (KArg a env) k) (SApp f a env k)))
        ((Num n) (values (Go $ Rt (VNum n) k) (SNum n env k))))
      (match many (nth-find (Val) env i) _
        ((FoundAt _ _ _ v p) (values (Go $ Rt v k) (SVar i env k v p)))
        ((MissingAt _ _ _ nn) (values (Halt $ RStuck) (SVarNo i env k nn)))))
    ((Rt v k)
      (let-match many k (Cons _ fr rest) ((Nil _) (values (Halt $ RVal v) (SRetNil v))))
      (let-match many fr (KCall f) ((KArg a env) (values (Go $ Ev a env $ Cons (Frame) (KCall v) rest) (SArg v a env rest))))
      (match many f _
        ((VClo b env) (values (Go $ Ev b (Cons (Val) v env) rest) (SCall v b env rest)))
        ((VNum n) (values (Halt $ RStuck) (SCallNum v n rest)))))))

(def-fns _ $ (erased reach-runs : (erased (MSt) a) (erased (MSt) b) (erased (Res) r)
    (subterm erased (Reach a b) p) (erased (Runs b r) q) -> (erased (Runs a r) e))
  (match erased p _
    ((ReachZ _) q)
    ((ReachS _ b0 _ p1 st) (reach-runs a b0 r p1 (RunGo b0 b r st q)))))

(def-adts $ (Ctx : ((List $ Stmt) p0) ((List $ Ent) es) ((List $ Stmt) p) -> Type)
  enum
  (many CTop : (erased (List $ Stmt) p0) -> (Ctx p0 (Nil (Ent)) p0))
  (many CLet : (erased (List $ Stmt) p0) (erased (List $ Ent) es) (erased (Tm) t) (erased (List $ Stmt) rest)
     (erased (Val) v) (erased (Ctx p0 es (Cons (Stmt) (Let t) rest)) c) (erased (Evals es t v) ev)
     -> (Ctx p0 (Cons (Ent) (MkEnt v (KNone)) es) rest))
  (many CAssert : (erased (List $ Stmt) p0) (erased (List $ Ent) es) (erased (Nat) i) (erased (Ctor) ct)
     (erased (List $ Stmt) rest) (erased (Val) v) (erased (Known) k) (erased (List $ Ent) es2)
     (erased (Ctx p0 es (Cons (Stmt) (Assert i ct) rest)) c)
     (erased (Nth (Ent) es i (MkEnt v k)) nth) (erased (Head v ct) hd)
     (erased (SetNth (Ent) es i (MkEnt v (KIs ct)) es2) sn) -> (Ctx p0 es2 rest))
  (many CNeed : (erased (List $ Stmt) p0) (erased (List $ Ent) es) (erased (Nat) i) (erased (Ctor) ct)
     (erased (List $ Stmt) rest) (erased (Val) v) (erased (Ctx p0 es (Cons (Stmt) (Need i ct) rest)) c)
     (erased (Nth (Ent) es i (MkEnt v (KIs ct))) nth) -> (Ctx p0 es rest)))

(def-fns _
  ((erased plug-elab : (erased (List $ Stmt) p0) (erased (List $ Ent) es) (erased (List $ Stmt) p)
      (subterm erased (Ctx p0 es p) c) (erased (Elab es p) d) -> (erased (Elab (Nil (Ent)) p0) r))
    (match erased c _
      ((CTop _) d)
      ((CLet _ es0 t rest v c1 ev) (plug-elab p0 es0 (Cons (Stmt) (Let t) rest) c1 (ElLet es0 t rest v ev d)))
      ((CAssert _ es0 i ct rest v k _ c1 nth hd sn)
        (plug-elab p0 es0 (Cons (Stmt) (Assert i ct) rest) c1 (ElAssert es0 i ct rest v k es nth hd sn d)))
      ((CNeed _ _ i ct rest v c1 nth) (plug-elab p0 es (Cons (Stmt) (Need i ct) rest) c1 (ElNeed es i ct rest v nth d)))))
  ((erased plug-fails : (erased (List $ Stmt) p0) (erased (List $ Ent) es) (erased (List $ Stmt) p)
      (subterm erased (Ctx p0 es p) c) (erased (Fails es p) f) -> (erased (Fails (Nil (Ent)) p0) r))
    (match erased c _
      ((CTop _) f)
      ((CLet _ es0 t rest v c1 ev) (plug-fails p0 es0 (Cons (Stmt) (Let t) rest) c1 (FLetRest es0 t rest v ev f)))
      ((CAssert _ es0 i ct rest v k _ c1 nth hd sn)
        (plug-fails p0 es0 (Cons (Stmt) (Assert i ct) rest) c1 (FAssertRest es0 i ct rest v k es nth hd sn f)))
      ((CNeed _ _ i ct rest v c1 nth) (plug-fails p0 es (Cons (Stmt) (Need i ct) rest) c1 (FNeedRest es i ct rest v nth f))))))

(def-adts $ (CState : ((List $ Stmt) p0) -> Type)
  enum
  (many Checking : (erased (List $ Stmt) p0) (many (List $ Ent) es) (many (List $ Stmt) p)
     (erased (Ctx p0 es p) c) -> (CState p0))
  (many Waiting : (erased (List $ Stmt) p0) (many (List $ Ent) es) (erased (Tm) t) (many (List $ Stmt) rest)
     (erased (Ctx p0 es (Cons (Stmt) (Let t) rest)) c)
     (erased (List $ Val) env) (erased (Vals es env) ve)
     (many (MSt) m) (erased (Reach (Ev t env (Nil (Frame))) m) r) -> (CState p0)))

(def-fns _ $ (many reject : (erased (List $ Stmt) p0) (erased (List $ Ent) es) (erased (List $ Stmt) p)
    (erased (Ctx p0 es p) c) (erased (Fails es p) f) (many (String) why) -> (many (Turn CState p0) o))
  (Fin CState p0 $ Rejected p0 (plug-fails p0 es p c f) why))

(def-fns _ $ (many check-assert : (erased (List $ Stmt) p0) (many (List $ Ent) es) (many (Nat) i) (many (Ctor) ct)
    (many (List $ Stmt) rest) (erased (Ctx p0 es (Cons (Stmt) (Assert i ct) rest)) c) -> (many (Turn CState p0) o))
  (let-match many (nth-find (Ent) es i) (FoundAt _ _ _ e nth)
    ((MissingAt _ _ _ nn) (reject p0 es _ c (FAssertRange es i ct rest nn) "assert: no such entry")))
  (let-match many e (MkEnt v k))
  (let ((many ct2) (erased hd)) (head v))
  (let-match many (ctor-dec ct ct2) (CSame _)
    ((CDiff _ _ ne) (reject p0 es _ c (FAssertHead es i ct rest v k ct2 nth hd ne) "assert: the value has another constructor")))
  (let ((many es2) (erased sn)) (set-nth (Ent) es i (MkEnt v (KIs ct)) e nth))
  (More CState p0 $ Checking p0 es2 rest (CAssert p0 es i ct rest v k es2 c nth hd sn)))

(def-fns _ $ (many check-need : (erased (List $ Stmt) p0) (many (List $ Ent) es) (many (Nat) i) (many (Ctor) ct)
    (many (List $ Stmt) rest) (erased (Ctx p0 es (Cons (Stmt) (Need i ct) rest)) c) -> (many (Turn CState p0) o))
  (let-match many (nth-find (Ent) es i) (FoundAt _ _ _ e nth)
    ((MissingAt _ _ _ nn) (reject p0 es _ c (FNeedRange es i ct rest nn) "need: no such entry")))
  (let-match many e (MkEnt v k))
  (let ((many no-fact)) "need: the fact is not known")
  (let-match many k (KIs ct2) ((KNone) (reject p0 es _ c (FNeedFact es i ct rest v k nth (NotNone ct)) no-fact)))
  (let-match many (ctor-dec ct2 ct) (CSame _)
    ((CDiff _ _ ne) (reject p0 es _ c (FNeedFact es i ct rest v k nth (NotOther ct2 ct ne)) no-fact)))
  (More CState p0 $ Checking p0 es rest (CNeed p0 es i ct rest v c nth)))

(def-fns _ $ (many cstep : (erased (List $ Stmt) p0) (many (CState p0) s) -> (many (Turn CState p0) o))
  (match many s _
    ((Checking _ es p c)
      (let-match many p (Cons _ st rest) ((Nil _) (Fin CState p0 $ Accepted p0 (plug-elab p0 es p c (ElNil es)))))
      (let-match many st (Let t)
        ((Assert i ct) (check-assert p0 es i ct rest c))
        ((Need i ct) (check-need p0 es i ct rest c)))
      (let ((many env) (erased ve)) (vals es))
      (More CState p0 $ Waiting p0 es t rest c env ve (Ev t env (Nil (Frame))) (ReachZ _)))
    ((Waiting _ es t rest c env ve m r)
      (let ((many o) (erased st)) (mstep m))
      (let-match many o (Halt res) ((Go m2) (More CState p0 $ Waiting p0 es t rest c env ve m2 (ReachS _ m m2 r st))))
      (let ((erased runs)) (reach-runs _ m res r (RunHalt m res st)))
      (let-match many res (RVal v)
        ((RStuck) (reject p0 es _ c (FLetStuck es t rest (MkSticks es t env ve runs)) "let: the compile-time run is stuck")))
      (More CState p0 $ Checking p0 (Cons (Ent) (MkEnt v (KNone)) es) rest (CLet p0 es t rest v c (MkEvals es t v env ve runs))))))

(def-fns _ $ (many start : (many (List $ Stmt) p0) -> (many (CState p0) s))
  (Checking p0 (Nil (Ent)) p0 (CTop p0)))
