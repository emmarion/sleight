; A fuel-free stepped machine: a CEK interpreter for an untyped CBV lambda calculus, and a toy checker
; that suspends into it for compile-time splices. Each step is a total function; drive loops over Program.

(def-adts $ (Op : -> Type)
  enum
  (many OAdd : -> (Op))
  (many OMul : -> (Op))
  (many OMonus : -> (Op)))

(def-adts $ (Tm : -> Type)
  enum
  (many Var : (many (Nat) i) -> (Tm))
  (many Lam : (many (Tm) body) -> (Tm))
  (many App : (many (Tm) f) (many (Tm) a) -> (Tm))
  (many Num : (many (Nat) n) -> (Tm))
  (many Prim : (many (Op) o) (many (Tm) a) (many (Tm) b) -> (Tm))
  (many IfZ : (many (Tm) c) (many (Tm) t) (many (Tm) e) -> (Tm)))

(def-adts $ (Val : -> Type)
  enum
  (many VNum : (many (Nat) n) -> (Val))
  (many VClo : (many (Tm) body) (many (List $ Val) env) -> (Val)))

(def-adts $ (Frame : -> Type)
  enum
  (many KArg : (many (Tm) a) (many (List $ Val) env) -> (Frame))
  (many KCall : (many (Val) f) -> (Frame))
  (many KPrimR : (many (Op) o) (many (Tm) b) (many (List $ Val) env) -> (Frame))
  (many KPrimL : (many (Op) o) (many (Nat) a) -> (Frame))
  (many KIf : (many (Tm) t) (many (Tm) e) (many (List $ Val) env) -> (Frame)))

(def-adts $ (State : -> Type)
  enum
  (many Eval : (many (Tm) t) (many (List $ Val) env) (many (List $ Frame) k) -> (State))
  (many Ret : (many (Val) v) (many (List $ Frame) k) -> (State)))

(def-adts $ (Final : -> Type)
  enum
  (many Halted : (many (Val) v) -> (Final))
  (many Failed : (many (String) m) -> (Final)))

(def-adts $ (Out : (Type S) -> Type)
  enum
  (many Next : (erased Type S) (many S s) -> (Out S))
  (many Done : (erased Type S) (many (Final) f) -> (Out S)))

(def-fns _ $ (many lookup : (subterm many (List $ Val) env) (many (Nat) i) -> (many (Maybe $ Val) r))
  (let-match many env (Cons _ v rest) ((Nil _) (None _)))
  (match many i _
    ((Zero) (Some _ v))
    ((Succ j) (tail (lookup rest j)))))

(def-fns _ $ (many monus : (many (Nat) a) (subterm many (Nat) b) -> (many (Nat) c))
  (let-match many b (Succ j) ((Zero) a))
  (match many (notail (monus a j)) _ ((Zero) 0) ((Succ p) p)))

(def-fns _ $ (many prim : (many (Op) o) (many (Nat) a) (many (Nat) b) -> (many (Nat) c))
  (match many o _
    ((OAdd) (let ((many c) (erased _)) (add a b)) c)
    ((OMul) (let ((many c) (erased _)) (mul a b)) c)
    ((OMonus) (monus a b))))

(def-fns _ $ (many fetch : (many (List $ Val) env) (many (Nat) i) (many (List $ Frame) k) -> (many (Out $ State) o))
  (let-match many (lookup env i) (Some _ v) ((None _) (Done _ $ Failed "unbound")))
  (Next _ $ Ret v k))

(def-fns _ $ (many step : (many (State) s) -> (many (Out $ State) o))
  (match many s _
    ((Eval t env k)
      (match many t _
        ((Var i) (fetch env i k))
        ((Lam b) (Next _ $ Ret (VClo b env) k))
        ((App f a) (Next _ $ Eval f env $ Cons _ (KArg a env) k))
        ((Num n) (Next _ $ Ret (VNum n) k))
        ((Prim o a b) (Next _ $ Eval a env $ Cons _ (KPrimR o b env) k))
        ((IfZ c th el) (Next _ $ Eval c env $ Cons _ (KIf th el env) k))))
    ((Ret v k)
      (let-match many k (Cons _ fr rest) ((Nil _) (Done _ $ Halted v)))
      (match many fr _
        ((KArg a env) (Next _ $ Eval a env $ Cons _ (KCall v) rest))
        ((KCall f)
          (let-match many f (VClo b env) ((VNum _) (Done _ $ Failed "applied a number")))
          (Next _ $ Eval b (Cons _ v env) rest))
        ((KPrimR o b env)
          (let-match many v (VNum n) ((VClo _ _) (Done _ $ Failed "arithmetic on a closure")))
          (Next _ $ Eval b env $ Cons _ (KPrimL o n) rest))
        ((KPrimL o a)
          (let-match many v (VNum n) ((VClo _ _) (Done _ $ Failed "arithmetic on a closure")))
          (Next _ $ Ret (VNum $ prim o a n) rest))
        ((KIf th el env)
          (let-match many v (VNum n) ((VClo _ _) (Done _ $ Failed "branch on a closure")))
          (match many n _ ((Zero) (Next _ $ Eval th env rest)) ((Succ _) (Next _ $ Eval el env rest))))))))

(def-adts $ (Src : -> Type)
  enum
  (many SNum : (many (Nat) n) -> (Src))
  (many SVar : (many (Nat) i) -> (Src))
  (many SAdd : (many (Src) a) (many (Src) b) -> (Src))
  (many SLet : (many (Src) a) (many (Src) b) -> (Src))
  (many SRun : (many (Tm) t) -> (Src)))

(def-adts $ (CFrame : -> Type)
  enum
  (many FAdd1 : (many (Src) b) (many (Nat) d) -> (CFrame))
  (many FAdd2 : (many (Tm) a) -> (CFrame))
  (many FLet1 : (many (Src) b) (many (Nat) d) -> (CFrame))
  (many FLet2 : (many (Tm) a) -> (CFrame)))

(def-adts $ (MState : -> Type)
  enum
  (many Checking : (many (Src) s) (many (Nat) d) (many (List $ CFrame) ks) -> (MState))
  (many Built : (many (Tm) t) (many (List $ CFrame) ks) -> (MState))
  (many Comptime : (many (State) c) (many (List $ CFrame) ks) -> (MState))
  (many Running : (many (State) c) -> (MState)))

(def-fns _ $ (many check-var : (many (Nat) i) (many (Nat) d) (many (List $ CFrame) ks) -> (many (Out $ MState) o))
  (match many (lt-dec i d) _
    ((Yes _ _ _ _ _) (Next _ $ Built (Var i) ks))
    ((No _ _ _ _ _) (Done _ $ Failed $ str-append "rejected: unbound variable " $ nat-str i))))

(def-fns _ $ (many check : (many (Src) s) (many (Nat) d) (many (List $ CFrame) ks) -> (many (Out $ MState) o))
  (match many s _
    ((SNum n) (Next _ $ Built (Num n) ks))
    ((SVar i) (check-var i d ks))
    ((SAdd a b) (Next _ $ Checking a d $ Cons _ (FAdd1 b d) ks))
    ((SLet a b) (Next _ $ Checking a d $ Cons _ (FLet1 b d) ks))
    ((SRun t) (Next _ $ Comptime (Eval t (Nil _) (Nil _)) ks))))

(def-fns _ $ (many built : (many (Tm) t) (many (List $ CFrame) ks) -> (many (Out $ MState) o))
  (let-match many ks (Cons _ fr rest) ((Nil _) (Next _ $ Running $ Eval t (Nil _) (Nil _))))
  (match many fr _
    ((FAdd1 b d) (Next _ $ Checking b d $ Cons _ (FAdd2 t) rest))
    ((FAdd2 a) (Next _ $ Built (Prim (OAdd) a t) rest))
    ((FLet1 b d) (Next _ $ Checking b (Succ d) $ Cons _ (FLet2 t) rest))
    ((FLet2 a) (Next _ $ Built (App (Lam t) a) rest))))

(def-fns _ $ (many spliced : (many (Out $ State) o) (many (List $ CFrame) ks) -> (many (Out $ MState) r))
  (let-match many o (Done _ f) ((Next _ c) (Next _ $ Comptime c ks)))
  (let-match many f (Halted v) ((Failed m) (Done _ $ Failed $ str-append "rejected: compile-time run stuck: " m)))
  (let-match many v (VNum n) ((VClo _ _) (Done _ $ Failed "rejected: a splice gave a closure")))
  (Next _ $ Built (Num n) ks))

(def-fns _ $ (many running : (many (Out $ State) o) -> (many (Out $ MState) r))
  (match many o _
    ((Next _ c) (Next _ $ Running c))
    ((Done _ f) (Done _ f))))

(def-fns _ $ (many mstep : (many (MState) m) -> (many (Out $ MState) o))
  (match many m _
    ((Checking s d ks) (check s d ks))
    ((Built t ks) (built t ks))
    ((Comptime c ks) (spliced (step c) ks))
    ((Running c) (running $ step c))))

(def-adts $ (Burst : -> Type)
  enum
  (many Paused : (many (MState) s) (many (Nat) taken) -> (Burst))
  (many Ended : (many (Final) f) (many (Nat) taken) -> (Burst)))

(def-fns _ $ (many burst : (many (MState) s) (subterm many (Nat) budget) (many (Nat) taken) -> (many (Burst) b))
  (let-match many budget (Succ k) ((Zero) (Paused s taken)))
  (match many (mstep s) _
    ((Next _ s2) (tail (burst s2 k (Succ taken))))
    ((Done _ f) (Ended f (Succ taken)))))

(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes _ _ za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))
(let ((many d1)) (lt-dec 1 u8-modulus))
(comptime-match many d1 (Yes _ _ za1 zb1 zp1))
(let ((many code1)) (MkU8 1 zp1))

(def-fns _ $ (many show-val : (many (Val) v) -> (many (String) s))
  (match many v _ ((VNum n) (nat-str n)) ((VClo _ _) "<closure>")))

(def-fns _ $ (many arg-nat : (many (List $ String) args) (many (Nat) dflt) -> (many (Nat) n) (many (List $ String) rest))
  (let-match many args (Cons _ a rest) ((Nil _) (values dflt (Nil _))))
  (match many (str-nat a) _ ((Some _ n) (values n rest)) ((None _) (values dflt rest))))

(let ((many wz)) (Lam $ App (Var 1) $ Lam $ App (App (Var 1) (Var 1)) (Var 0)))
(let ((many z)) (Lam $ App wz wz))
(let ((many sum-body)) (Lam $ Lam $ IfZ (Var 0) (Num 0) $ Prim (OAdd) (Var 0) $ App (Var 1) $ Prim (OMonus) (Var 0) (Num 1)))
(def-fns _ $ (many sum-to : (many (Nat) n) -> (many (Tm) t)) (App (App z sum-body) (Num n)))

(let ((many omega)) (App (Lam $ App (Var 0) (Var 0)) (Lam $ App (Var 0) (Var 0))))

(def-fns _ $ (many sources : (many (Nat) which) (many (Nat) n) -> (many (Src) s))
  (let ((many twice)) (SLet (SRun $ sum-to n) $ SAdd (SVar 0) (SVar 0)))
  (let-match many which (Succ k) ((Zero) (SAdd twice $ SRun $ Prim (OMul) (Num 2) (Num 3))))
  (let-match many k (Succ j) ((Zero) (SAdd twice $ SVar 1)))
  (match many j _
    ((Zero) (SAdd twice $ SRun $ App (Num 1) (Num 2)))
    ((Succ _) (SAdd (SRun omega) twice))))

(def-lvl PA)
(def-lvl P)

(def-fns PA $ (many drive : (many (MState) s) (many (Nat) batch) (many (Nat) steps) (many (Nat) conts) (unique (World) w at vacant-slot) ->
    (unique (World) w2 at w) (unique (Program P) p))
  (match many (burst s batch 0) _
    ((Paused s2 t)
      (let ((many steps2) (erased _)) (add steps t))
      (def-unique P $ (unique again : (unique (World) v at vacant-slot) -> (unique (World) v2 at v) (unique (Program P) p))
        (drive s2 batch steps2 (Succ conts) v))
      (values w (Continue P again)))
    ((Ended f t)
      (let ((many steps2) (erased _)) (add steps t))
      (let ((many counts)) (str-append " after " $ str-append (nat-str steps2) $ str-append " steps, " $ str-append (nat-str $ Succ conts) " Program steps\n"))
      (match many f _
        ((Halted v)
          (let ((unique w1) (many _)) (world-do _ w (WriteOut $ str-append "value " $ str-append (show-val v) counts)))
          (values w1 (Exit P code0)))
        ((Failed m)
          (let ((unique w1) (many _)) (world-do _ w (WriteOut $ str-append m counts)))
          (values w1 (Exit P code1)))))))
