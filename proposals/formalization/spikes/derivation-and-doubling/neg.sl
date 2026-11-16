(def-adts
  ((NoEnv : ((Env) env) ((Nat) x) -> Type)
    enum
    (many NoEnvNil : (erased (Nat) x) -> (NoEnv (ENil) x))
    (many NoEnvCons : (erased (Nat) x) (erased (Nat) y) (erased (Val) w) (erased (Env) rest) (erased (Neq x y) n) (erased (NoEnv rest x) p) -> (NoEnv (ECons y w rest) x)))
  ((EnvDec2 : ((Env) env) ((Nat) x) -> Type)
    enum
    (many EnvHit2 : (erased (Env) env) (erased (Nat) x) (many (Val) v) (erased (EnvOf env x v) p) -> (EnvDec2 env x))
    (many EnvMiss2 : (erased (Env) env) (erased (Nat) x) (erased (NoEnv env x) p) -> (EnvDec2 env x))))

(def-fns _ $ (many env-dec2 : (subterm many (Env) env) (many (Nat) x) -> (many (EnvDec2 env x) r))
  (let-match many env (ECons y w rest) ((ENil) (EnvMiss2 _ _ $ NoEnvNil x)))
  (let-match many (nat-dec x y) (NDDiff _ _ n) ((NDSame _) (EnvHit2 _ _ w $ EnvHere x w rest)))
  (match many (notail $ env-dec2 rest x) _
    ((EnvHit2 _ _ v p) (EnvHit2 _ _ v $ EnvThere x y v w rest n p))
    ((EnvMiss2 _ _ p) (EnvMiss2 _ _ $ NoEnvCons x y w rest n p))))

(def-fns _ $ (erased absurd no-env-absurd : (erased (Env) env) (erased (Nat) x) (erased (Val) v) (subterm erased (EnvOf env x v) p) (erased (NoEnv env x) q) -> (erased (False) f))
  (match erased p _
    (absurd (EnvHere _ _ _) (let-match erased q (NoEnvCons _ _ _ _ n _)) (neq-irrefl x n))
    (absurd (EnvThere _ _ _ _ rest _ p2) (let-match erased q (NoEnvCons _ _ _ _ _ q2)) (no-env-absurd rest x v p2 q2))))

(def-adts
  ((NoBind : ((Env) env) ((List (Nat)) ids) ((List (Val)) vs) -> Type)
    enum
    (many NBShort : (erased (Env) env) (erased (Nat) x) (erased (List (Nat)) ids) -> (NoBind env (Cons (Nat) x ids) (Nil (Val))))
    (many NBLong : (erased (Env) env) (erased (Val) v) (erased (List (Val)) vs) -> (NoBind env (Nil (Nat)) (Cons (Val) v vs)))
    (many NBStep : (erased (Env) env) (erased (Nat) x) (erased (Val) v) (erased (List (Nat)) ids) (erased (List (Val)) vs) (erased (NoBind (ECons x v env) ids vs) p)
       -> (NoBind env (Cons (Nat) x ids) (Cons (Val) v vs))))
  ((BindDec2 : ((Env) env) ((List (Nat)) ids) ((List (Val)) vs) -> Type)
    enum
    (many BDOk2 : (erased (Env) env) (erased (List (Nat)) ids) (erased (List (Val)) vs) (many (Env) out) (erased (BindAll env ids vs out) p) -> (BindDec2 env ids vs))
    (many BDNo : (erased (Env) env) (erased (List (Nat)) ids) (erased (List (Val)) vs) (erased (NoBind env ids vs) p) -> (BindDec2 env ids vs))))

(def-fns _ $ (many bind-all2 : (many (Env) env) (subterm many (List (Nat)) ids) (many (List (Val)) vs) -> (many (BindDec2 env ids vs) r))
  (let-match many ids (Cons _ x rest)
    ((Nil _) (match many vs _ ((Nil _) (BDOk2 _ _ _ env $ BANil env)) ((Cons _ v vrest) (BDNo _ _ _ $ NBLong env v vrest)))))
  (let-match many vs (Cons _ v vrest) ((Nil _) (BDNo _ _ _ $ NBShort env x rest)))
  (match many (notail $ bind-all2 (ECons x v env) rest vrest) _
    ((BDNo _ _ _ p) (BDNo _ _ _ $ NBStep env x v rest vrest p))
    ((BDOk2 _ _ _ out p) (BDOk2 _ _ _ out $ BACons env x v rest vrest out p))))

(def-fns _ $ (erased absurd no-bind-absurd : (erased (Env) env) (erased (List (Nat)) ids) (erased (List (Val)) vs) (erased (Env) out) (subterm erased (BindAll env ids vs out) p) (erased (NoBind env ids vs) q) -> (erased (False) f))
  (match erased p _
    (absurd (BANil _) q)
    (absurd (BACons _ x v ids2 vs2 _ p2) (let-match erased q (NBStep _ _ _ _ _ q2)) (no-bind-absurd (ECons x v env) ids2 vs2 out p2 q2))))

(def-adts
  ((NoBranch : ((List (Branch)) bs) ((Nat) c) -> Type)
    enum
    (many NoBrNil : (erased (Nat) c) -> (NoBranch (Nil (Branch)) c))
    (many NoBrCons : (erased (Nat) c) (erased (Nat) d) (erased (List (Nat)) fields) (erased (Core) body) (erased (List (Branch)) rest) (erased (Neq c d) n) (erased (NoBranch rest c) p)
       -> (NoBranch (Cons (Branch) (MkBranch d fields body) rest) c)))
  ((BranchDec2 : ((List (Branch)) bs) ((Nat) c) -> Type)
    enum
    (many BrHit2 : (erased (List (Branch)) bs) (erased (Nat) c) (many (List (Nat)) fields) (many (Core) body) (erased (BranchOf bs c fields body) p) -> (BranchDec2 bs c))
    (many BrNo : (erased (List (Branch)) bs) (erased (Nat) c) (erased (NoBranch bs c) p) -> (BranchDec2 bs c))))

(def-fns _ $ (many branch-dec2 : (subterm many (List (Branch)) bs) (many (Nat) c) -> (many (BranchDec2 bs c) r))
  (let-match many bs (Cons _ b rest) ((Nil _) (BrNo _ _ $ NoBrNil c)))
  (let-match many b (MkBranch d fields2 body2))
  (let-match many (nat-dec c d) (NDDiff _ _ n) ((NDSame _) (BrHit2 _ _ fields2 body2 $ BrHere c fields2 body2 rest)))
  (match many (notail $ branch-dec2 rest c) _
    ((BrHit2 _ _ fields body p) (BrHit2 _ _ fields body $ BrThere c d fields fields2 body body2 rest n p))
    ((BrNo _ _ p) (BrNo _ _ $ NoBrCons c d fields2 body2 rest n p))))

(def-fns _ $ (erased absurd no-branch-absurd : (erased (List (Branch)) bs) (erased (Nat) c) (erased (List (Nat)) fields) (erased (Core) body) (subterm erased (BranchOf bs c fields body) p) (erased (NoBranch bs c) q) -> (erased (False) f))
  (match erased p _
    (absurd (BrHere _ _ _ _) (let-match erased q (NoBrCons _ _ _ _ _ n _)) (neq-irrefl c n))
    (absurd (BrThere _ _ _ _ _ _ rest _ p2) (let-match erased q (NoBrCons _ _ _ _ _ _ q2)) (no-branch-absurd rest c fields body p2 q2))))

(let ((many kind-con)) (Zero))
(let ((many kind-atom)) (Succ (Zero)))
(let ((many kind-clo)) (Succ (Succ (Succ (Zero)))))

(def-adts
  ((KindOf : ((Val) v) ((Nat) k) -> Type)
    enum
    (many KOCon : (erased (Nat) h) (erased (List (Val)) args) -> (KindOf (VCon h args) (Zero)))
    (many KOAtom : (erased (Nat) id) -> (KindOf (VAtom id) (Succ (Zero))))
    (many KOFormer : (erased (Term) t) (erased (Env) env) -> (KindOf (VFormer t env) (Succ (Succ (Zero)))))
    (many KOClo : (erased (Env) env) (erased (List (FnDef)) group) (erased (FnDef) def) -> (KindOf (VClo env group def) (Succ (Succ (Succ (Zero))))))
    (many KOToken : -> (KindOf (VToken) (Succ (Succ (Succ (Succ (Zero))))))))
  ((NotSingle : ((List (Val)) vs) -> Type)
    enum
    (many NSNil : -> (NotSingle (Nil (Val))))
    (many NSMany : (erased (Val) v) (erased (Val) w) (erased (List (Val)) rest) -> (NotSingle (Cons (Val) v (Cons (Val) w rest)))))
  ((BadShape : ((List (Val)) vs) ((Nat) want) -> Type)
    enum
    (many BSNotSingle : (erased (List (Val)) vs) (erased (Nat) want) (erased (NotSingle vs) p) -> (BadShape vs want))
    (many BSKind : (erased (Val) v) (erased (Nat) want) (erased (Nat) k) (erased (KindOf v k) p) (erased (Neq k want) n) -> (BadShape (Cons (Val) v (Nil (Val))) want)))
  ((SingleDec : ((List (Val)) vs) -> Type)
    enum
    (many IsSingle : (many (Val) v) -> (SingleDec (Cons (Val) v (Nil (Val)))))
    (many NotOne : (erased (List (Val)) vs) (erased (NotSingle vs) p) -> (SingleDec vs)))
  ((ShapeDec : ((List (Val)) vs) ((Nat) want) -> Type)
    enum
    (many ShapeOk : (erased (Nat) want) (many (Val) v) (erased (KindOf v want) p) -> (ShapeDec (Cons (Val) v (Nil (Val))) want))
    (many ShapeBad : (erased (List (Val)) vs) (erased (Nat) want) (erased (BadShape vs want) p) -> (ShapeDec vs want))))

(def-fns _ $ (many kind-of : (many (Val) v) -> (many (Nat) k) (erased (KindOf v k) p))
  (match many v _
    ((VCon h args) (values (Zero) (KOCon h args)))
    ((VAtom id) (values (Succ (Zero)) (KOAtom id)))
    ((VFormer t env) (values (Succ (Succ (Zero))) (KOFormer t env)))
    ((VClo env group def) (values (Succ (Succ (Succ (Zero)))) (KOClo env group def)))
    ((VToken) (values (Succ (Succ (Succ (Succ (Zero))))) (KOToken)))))

(def-fns _ $ (many single-dec : (many (List (Val)) vs) -> (many (SingleDec vs) r))
  (let-match many vs (Cons _ v rest) ((Nil _) (NotOne _ (NSNil))))
  (match many rest _ ((Nil _) (IsSingle v)) ((Cons _ w rest2) (NotOne _ $ NSMany v w rest2))))

(def-fns _ $ (many shape-dec : (many (List (Val)) vs) (many (Nat) want) -> (many (ShapeDec vs want) r))
  (let-match many (single-dec vs) (IsSingle v) ((NotOne _ ns) (ShapeBad _ _ $ BSNotSingle vs want ns)))
  (let ((many k) (erased ko)) (kind-of v))
  (match many (nat-dec k want) _
    ((NDSame _) (ShapeOk _ v ko))
    ((NDDiff _ _ ne) (ShapeBad _ _ $ BSKind v want k ko ne))))

(def-fns _ $ (erased kind-of-unique : (erased (Val) v) (erased (Nat) k1) (erased (Nat) k2) (erased (KindOf v k1) p) (erased (KindOf v k2) q) -> (erased (Eq (Nat) k1 k2) e))
  (match erased p _
    ((KOCon _ _) (match erased q _ ((KOCon _ _) (Refl (Nat) k1))))
    ((KOAtom _) (match erased q _ ((KOAtom _) (Refl (Nat) k1))))
    ((KOFormer _ _) (match erased q _ ((KOFormer _ _) (Refl (Nat) k1))))
    ((KOClo _ _ _) (match erased q _ ((KOClo _ _ _) (Refl (Nat) k1))))
    ((KOToken) (match erased q _ ((KOToken) (Refl (Nat) k1))))))

(def-fns _ $ (erased absurd bad-shape-absurd : (erased (Val) v) (erased (Nat) want) (erased (KindOf v want) ko) (erased (BadShape (Cons (Val) v (Nil (Val))) want) bs) -> (erased (False) f))
  (match erased bs _
    (absurd (BSNotSingle _ _ ns) ns)
    (absurd (BSKind _ _ k ko2 ne) (let-match erased (kind-of-unique v k want ko2 ko) (Refl _ _)) (neq-irrefl want ne))))

(MkUnit)
