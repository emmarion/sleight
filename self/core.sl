; self/core.sl -- the compiler's data: the restricted type grammar (DESIGN.md section 5) as terms with de
; Bruijn telescopes, the special-form registry (section 27), runtime values and post-erasure code, the
; scope environment with its fact table (sections 3, 18), canonicalization, instantiation and the part of
; forced unification a trusting compiler needs. Mirrors lib/term.ml, lib/value.ml and lib/env.ml.

(def-adts $ (Mult : -> Type)
  enum
  (many Erased : -> (Mult))
  (many Many : -> (Mult))
  (many Once : -> (Mult)))

(let ((many many-one)) $ Cons _ (Many) $ Nil _)

; The entries of [xs] sit at the many positions of [ms], in order.
(def-adts
  ((Picked : (Type A) ((List $ Mult) ms) ((List A) xs) -> Type)
    enum
    (many PkNil : (erased Type A) -> (Picked A (Nil (Mult)) (Nil A)))
    (many PkMany : (erased Type A) (erased (List $ Mult) ms) (erased A x) (erased (List A) xs) (erased (Picked A ms xs) p) -> (Picked A (Cons (Mult) (Many) ms) (Cons A x xs)))
    (many PkOnce : (erased Type A) (erased (List $ Mult) ms) (erased A x) (erased (List A) xs) (erased (Picked A ms xs) p) -> (Picked A (Cons (Mult) (Once) ms) (Cons A x xs)))
    (many PkErased : (erased Type A) (erased (List $ Mult) ms) (erased (List A) xs) (erased (Picked A ms xs) p) -> (Picked A (Cons (Mult) (Erased) ms) xs))))

(def-fns _ $ (many picked-of : (erased Type A) (subterm many (List $ Mult) ms) (many (List A) xs) (erased (Lockstep (Mult) A ms xs) lock) -> (many (List A) r) (erased (Picked A ms r) pk))
  (let-match many ms (Cons _ m rest) ((Nil _) (values (Nil _) (PkNil _))))
  (let-match erased lock (LsCons ta tb x0 y0 xs0 ys0 p))
  (let-match many xs (Cons b x xrest))
  (let ((many r) (erased pk)) $ notail $ picked-of _ rest xrest p)
  (match many m _
    ((Many) (values (Cons _ x r) (PkMany _ rest x r pk)))
    ((Once) (values (Cons _ x r) (PkOnce _ rest x r pk)))
    ((Erased) (values r (PkErased _ rest r pk)))))

(def-fns _ $ (erased picked-along : (erased Type A) (erased Type B) (erased (List $ Mult) ms) (erased (List A) xs) (erased (List B) ys) (subterm erased (Picked A ms xs) p) (erased (Lockstep A B xs ys) q) -> (erased (Picked B ms ys) r))
  (match erased p _
    ((PkNil _)
      (let-match erased q (LsNil c d))
      (PkNil _))
    ((PkMany _ ms2 _ _ p2)
      (let-match erased q (LsCons c d x3 y xs3 ys2 q2))
      (PkMany _ ms2 y ys2 $ picked-along _ _ _ _ _ p2 q2))
    ((PkOnce _ ms2 _ _ p2)
      (let-match erased q (LsCons c d x3 y xs3 ys2 q2))
      (PkOnce _ ms2 y ys2 $ picked-along _ _ _ _ _ p2 q2))
    ((PkErased _ ms2 _ p2) (PkErased _ ms2 ys $ picked-along _ _ _ _ _ p2 q))))

; Two lists picked from one erasure list walk in lockstep.
(def-fns _ $ (erased picked-lockstep : (erased Type A) (erased Type B) (erased (List $ Mult) ms) (erased (List A) xs) (erased (List B) ys) (subterm erased (Picked A ms xs) p) (erased (Picked B ms ys) q) -> (erased (Lockstep A B xs ys) lk))
  (match erased p _
    ((PkNil _)
      (let-match erased q (PkNil b))
      (LsNil _ _))
    ((PkMany _ _ x xs2 p2)
      (let-match erased q (PkMany b ms3 y ys2 q2))
      (LsCons _ _ x y xs2 ys2 $ picked-lockstep _ _ _ _ _ p2 q2))
    ((PkOnce _ _ x xs2 p2)
      (let-match erased q (PkOnce b ms3 y ys2 q2))
      (LsCons _ _ x y xs2 ys2 $ picked-lockstep _ _ _ _ _ p2 q2))
    ((PkErased _ _ _ p2)
      (let-match erased q (PkErased b ms3 ys2 q2))
      (picked-lockstep _ _ _ _ _ p2 q2))))

; Two erasure lists with the same many entries.
(def-adts $ (ManySame : ((List $ Mult) a) ((List $ Mult) b) -> Type)
  enum
  (many MsNil : -> (ManySame (Nil (Mult)) (Nil (Mult))))
  (many MsMany : (erased (List $ Mult) a) (erased (List $ Mult) b) (erased (ManySame a b) p) -> (ManySame (Cons (Mult) (Many) a) (Cons (Mult) (Many) b)))
  (many MsOnce : (erased (List $ Mult) a) (erased (List $ Mult) b) (erased (ManySame a b) p) -> (ManySame (Cons (Mult) (Once) a) (Cons (Mult) (Once) b)))
  (many MsManyOnce : (erased (List $ Mult) a) (erased (List $ Mult) b) (erased (ManySame a b) p) -> (ManySame (Cons (Mult) (Many) a) (Cons (Mult) (Once) b)))
  (many MsOnceMany : (erased (List $ Mult) a) (erased (List $ Mult) b) (erased (ManySame a b) p) -> (ManySame (Cons (Mult) (Once) a) (Cons (Mult) (Many) b)))
  (many MsErasedL : (erased (List $ Mult) a) (erased (List $ Mult) b) (erased (ManySame a b) p) -> (ManySame (Cons (Mult) (Erased) a) b))
  (many MsErasedR : (erased (List $ Mult) a) (erased (List $ Mult) b) (erased (ManySame a b) p) -> (ManySame a (Cons (Mult) (Erased) b))))

(def-fns _ $ (erased picked-same : (erased Type A) (erased (List $ Mult) a) (erased (List $ Mult) b) (erased (List A) xs) (subterm erased (ManySame a b) p) (erased (Picked A a xs) q) -> (erased (Picked A b xs) r))
  (match erased p _
    ((MsNil) q)
    ((MsMany _ b2 p2) (let-match erased q (PkMany t a3 x xs2 q2)) (PkMany _ b2 x xs2 $ picked-same _ _ _ _ p2 q2))
    ((MsOnce _ b2 p2) (let-match erased q (PkOnce t a3 x xs2 q2)) (PkOnce _ b2 x xs2 $ picked-same _ _ _ _ p2 q2))
    ((MsManyOnce _ b2 p2) (let-match erased q (PkMany t a3 x xs2 q2)) (PkOnce _ b2 x xs2 $ picked-same _ _ _ _ p2 q2))
    ((MsOnceMany _ b2 p2) (let-match erased q (PkOnce t a3 x xs2 q2)) (PkMany _ b2 x xs2 $ picked-same _ _ _ _ p2 q2))
    ((MsErasedL _ _ p2) (let-match erased q (PkErased t a3 xs2 q2)) (picked-same _ _ _ _ p2 q2))
    ((MsErasedR _ b2 p2) (PkErased _ b2 xs $ picked-same _ _ _ _ p2 q))))

(def-fns _ $ (many mults-same : (subterm many (List $ Mult) a) (subterm many (List $ Mult) b) -> (many (Maybe $ ManySame a b) r))
  (match many a _
    ((Nil _)
      (let-match many b (Cons _ n br) ((Nil _) (Some _ (MsNil))))
      (match many n _
        ((Many) (None _)) ((Once) (None _))
        ((Erased) (match many (notail $ mults-same a br) _ ((Some _ p) (Some _ $ MsErasedR _ _ p)) ((None _) (None _))))))
    ((Cons _ m ar)
      (match many m _
        ((Erased) (match many (notail $ mults-same ar b) _ ((Some _ p) (Some _ $ MsErasedL _ _ p)) ((None _) (None _))))
        ((Many) (match many b _ ((Nil _) (None _)) ((Cons _ n br) (match many n _
          ((Many) (match many (notail $ mults-same ar br) _ ((Some _ p) (Some _ $ MsMany _ _ p)) ((None _) (None _))))
          ((Once) (match many (notail $ mults-same ar br) _ ((Some _ p) (Some _ $ MsManyOnce _ _ p)) ((None _) (None _))))
          ((Erased) (match many (notail $ mults-same a br) _ ((Some _ p) (Some _ $ MsErasedR _ _ p)) ((None _) (None _))))))))
        ((Once) (match many b _ ((Nil _) (None _)) ((Cons _ n br) (match many n _
          ((Many) (match many (notail $ mults-same ar br) _ ((Some _ p) (Some _ $ MsOnceMany _ _ p)) ((None _) (None _))))
          ((Once) (match many (notail $ mults-same ar br) _ ((Some _ p) (Some _ $ MsOnce _ _ p)) ((None _) (None _))))
          ((Erased) (match many (notail $ mults-same a br) _ ((Some _ p) (Some _ $ MsErasedR _ _ p)) ((None _) (None _))))))))))))

(def-adts $ (Disc : -> Type)
  enum
  (many DEnum : -> (Disc))
  (many DUnion : -> (Disc)))

; Where a message points: the file and the position within it (ASSUMPTIONS 194).
(def-adts $ (Loc : -> Type)
  enum
  (many MkLoc : (many (String) file) (many (Pos) pos) -> (Loc)))

(def-adts
  ((Term : -> Type)
    enum
    (many TVar : (many (Nat) id) -> (Term))
    (many TBound : (many (Nat) k) -> (Term))
    (many TApp : (many (Term) head) (many (List $ Term) args) -> (Term))
    (many TCell : (many (Term) head) (many (List $ Term) args) -> (Term))
    (many TFn : (many (Bool) uq) (many (Term) level) (many (List $ Entry) params) (many (List $ Entry) rets) -> (Term))
    (many TTyCtor : (many (List $ Entry) params) -> (Term))
    (many TValCtor : (many (List $ Entry) params) (many (Term) ret) -> (Term))
    (many TMatchable : (many (Disc) disc) (many (Bool) nt) (many (Bool) ex) (many (Term) ty) (many (List $ MCtor) ctors) -> (Term))
    (many TSlotHolds : (many (Term) c) -> (Term))
    (many TErr : (many (String) msg) -> (Term)))
  ((Entry : -> Type)
    enum
    (many MkEntry : (many (Maybe $ String) name) (many (Bool) is-sub) (many (Mult) mult) (many (Sg) sg) (many (Maybe $ Term) place) (many (Maybe $ Loc) site) -> (Entry)))
  ((Sg : -> Type)
    enum
    (many SgTy : (many (Term) t) -> (Sg))
    (many SgIs : (many (Term) t) (many (Term) ty) -> (Sg)))
  ((MCtor : -> Type)
    enum
    (many MkMCtor : (many (Mult) m) (many (Term) c) -> (MCtor))))

(def-fns _ $ (many entry-place : (many (Entry) e) -> (many (Maybe $ Term) p))
  (match many e _ ((MkEntry _ _ _ _ place _) place)))

(def-fns _ $ (many sg-term : (many (Sg) sg) -> (many (Term) t))
  (match many sg _ ((SgTy t) t) ((SgIs t _) t)))

(def-fns _ $ (many entry-mult : (many (Entry) e) -> (many (Mult) m))
  (match many e _ ((MkEntry _ _ m _ _ _) m)))

(def-fns _ $ (many entry-sg : (many (Entry) e) -> (many (Sg) sg))
  (match many e _ ((MkEntry _ _ _ sg _ _) sg)))

(def-fns _ $ (many entry-name : (many (Entry) e) -> (many (Maybe $ String) n))
  (match many e _ ((MkEntry n _ _ _ _ _) n)))

(def-fns _ $ (many entry-sub : (many (Entry) e) -> (many (Bool) s))
  (match many e _ ((MkEntry _ s _ _ _ _) s)))

(def-fns _ $ (many mult-name : (many (Mult) m) -> (many (String) s))
  (match many m _ ((Erased) "erased") ((Many) "many") ((Once) "unique")))

(def-fns _ $ (many mult-is-many : (many (Mult) m) -> (many (Bool) r))
  (match many m _ ((Erased) (BFalse)) ((Many) (BTrue)) ((Once) (BTrue))))

(def-fns _ $ (many under : (many (Mult) pos) (many (Mult) m) -> (many (Mult) r))
  (match many pos _ ((Erased) (Erased)) ((Many) m) ((Once) m)))

; The position of a list of expected multiplicities: erased when the list is non-empty and every entry is.
(def-adts $ (PosOf : ((List $ Mult) ms) ((Mult) pos) -> Type)
  enum
  (many PoNil : -> (PosOf (Nil (Mult)) (Many)))
  (many PoMany : (erased (List $ Mult) rest) -> (PosOf (Cons (Mult) (Many) rest) (Many)))
  (many PoOnce : (erased (List $ Mult) rest) -> (PosOf (Cons (Mult) (Once) rest) (Many)))
  (many PoOnly : -> (PosOf (Cons (Mult) (Erased) (Nil (Mult))) (Erased)))
  (many PoErased : (erased (Mult) m) (erased (List $ Mult) rest) (erased (Mult) p) (erased (PosOf (Cons (Mult) m rest) p) q) -> (PosOf (Cons (Mult) (Erased) (Cons (Mult) m rest)) p)))

(def-fns _ $ (many pos-of : (subterm many (List $ Mult) ms) -> (many (Mult) r) (erased (PosOf ms r) pf))
  (let-match many ms (Cons _ m rest) ((Nil _) (values (Many) (PoNil))))
  (let-match many m (Erased) ((Many) (values (Many) (PoMany _))) ((Once) (values (Many) (PoOnce _))))
  (let-match many rest (Cons _ _ _) ((Nil _) (values (Erased) (PoOnly))))
  (let ((many p) (erased q)) $ tail $ pos-of rest)
  (values p (PoErased _ _ _ q)))

(def-fns _ $ (many pos-mult : (many (List $ Mult) ms) -> (many (Mult) r))
  (match many ms _
    ((Cons _ m rest) (match many m _ ((Once) (match many rest _ ((Nil _) (Once)) ((Cons _ _ _) (Many)))) (else (let ((many r) (erased pf)) (pos-of ms)) r)))
    ((Nil _) (Many))))

(def-fns _ $ (many mult-is-once : (many (Mult) m) -> (many (Bool) r))
  (match many m _ ((Once) (BTrue)) (else (BFalse))))

(def-fns _ $ (many field-under : (many (Mult) pos) (many (Mult) m) -> (many (Mult) r))
  (match many pos _ ((Erased) (Erased)) ((Once) m) ((Many) (match many m _ ((Once) (Many)) (else m)))))

(def-fns _ $ (many many-count : (subterm many (List $ Entry) es) -> (many (Nat) n))
  (let-match many es (Cons _ e rest) ((Nil _) (Zero)))
  (match many (entry-mult e) _
    ((Many) (Succ $ notail $ many-count rest))
    ((Once) (Succ $ notail $ many-count rest))
    ((Erased) (tail $ many-count rest))))

(def-fns _ $ (many tele-mults : (subterm many (List $ Entry) es) -> (many (List $ Mult) ms))
  (match many es _
    ((Nil _) (Nil _))
    ((Cons _ e rest) (Cons _ (entry-mult e) $ notail $ tele-mults rest))))

; ---- The special-form registry (section 27), grouped by where each is dispatched.

(def-adts
  ((Sp : -> Type)
    enum
    (many SpStmt : (many (StmtK) k) -> (Sp))
    (many SpFormer : (many (FormerK) k) -> (Sp))
    (many SpExpr : (many (ExprK) k) -> (Sp))
    (many SpMark : (many (MarkK) k) -> (Sp)))
  ((StmtK : -> Type)
    enum
    (many StLet : -> (StmtK)) (many StDefLvl : -> (StmtK)) (many StDefFns : -> (StmtK)) (many StDefUnique : -> (StmtK))
    (many StDefAdts : -> (StmtK)) (many StComptimeMatch : -> (StmtK)) (many StLetMatch : -> (StmtK)) (many StUnary : -> (StmtK))
    (many StOpenAdt : -> (StmtK)) (many StDumpContext : -> (StmtK)))
  ((FormerK : -> Type)
    enum
    (many FoFn : -> (FormerK)) (many FoTyCtor : -> (FormerK)) (many FoValCtor : -> (FormerK))
    (many FoMatchable : -> (FormerK)) (many FoUniqueFn : -> (FormerK)) (many FoCell : -> (FormerK)))
  ((ExprK : -> Type)
    enum
    (many ExMatch : -> (ExprK)) (many ExMatchableOf : -> (ExprK)) (many ExSlotHolds : -> (ExprK)) (many ExSlotVacant : -> (ExprK)) (many ExShare : -> (ExprK)) (many ExCellAlloc : -> (ExprK)) (many ExCellWrite : -> (ExprK)) (many ExCellMatch : -> (ExprK)) (many ExCoercibleShare : -> (ExprK))
    (many ExNumeralOf : -> (ExprK)) (many ExLevelOf : -> (ExprK)) (many ExProveSubterm : -> (ExprK))
    (many ExProvePredates : -> (ExprK)) (many ExValues : -> (ExprK)) (many ExPredatesTrans : -> (ExprK))
    (many ExSubtermTrans : -> (ExprK)) (many ExPredatesSubterm : -> (ExprK)) (many ExCoerce : -> (ExprK))
    (many ExCoercibleRefl : -> (ExprK)) (many ExCoercibleSym : -> (ExprK)) (many ExCoercibleTrans : -> (ExprK))
    (many ExCoercibleWrap : -> (ExprK)) (many ExCoercibleCtor : -> (ExprK)) (many ExCoercibleOf : -> (ExprK)) (many ExDelegateOf : -> (ExprK))
    (many ExDistinct : -> (ExprK)) (many ExOpenAbsurd : -> (ExprK)))
  ((MarkK : -> Type)
    enum
    (many MkErased : -> (MarkK)) (many MkMany : -> (MarkK)) (many MkUnique : -> (MarkK)) (many MkAt : -> (MarkK)) (many MkColon : -> (MarkK)) (many MkIs : -> (MarkK))
    (many MkArrow : -> (MarkK)) (many MkSubterm : -> (MarkK)) (many MkEnum : -> (MarkK)) (many MkUnion : -> (MarkK))
    (many MkTail : -> (MarkK)) (many MkDelegate : -> (MarkK)) (many MkPredates : -> (MarkK)) (many MkAbsurd : -> (MarkK))
    (many MkNewtypeMark : -> (MarkK)) (many MkExtern : -> (MarkK)) (many MkElse : -> (MarkK)) (many MkNoTail : -> (MarkK))))

(def-fns _ $ (many stmt-code : (many (StmtK) k) -> (many (Nat) n))
  (match many k _ ((StLet) 0) ((StDefLvl) 1) ((StDefFns) 2) ((StDefAdts) 3) ((StComptimeMatch) 4) ((StLetMatch) 5) ((StUnary) 6) ((StOpenAdt) 7) ((StDefUnique) 8) ((StDumpContext) 9)))

(def-fns _ $ (many former-code : (many (FormerK) k) -> (many (Nat) n))
  (match many k _ ((FoFn) 0) ((FoTyCtor) 1) ((FoValCtor) 2) ((FoMatchable) 3) ((FoUniqueFn) 4) ((FoCell) 5)))

(def-fns _ $ (many expr-code : (many (ExprK) k) -> (many (Nat) n))
  (match many k _
    ((ExMatch) 0) ((ExMatchableOf) 1) ((ExSlotHolds) 2) ((ExSlotVacant) 20) ((ExShare) 21) ((ExCellAlloc) 22) ((ExCellWrite) 23) ((ExCellMatch) 24) ((ExCoercibleShare) 25) ((ExNumeralOf) 3) ((ExLevelOf) 4) ((ExProveSubterm) 5)
    ((ExProvePredates) 6) ((ExValues) 7) ((ExPredatesTrans) 8) ((ExSubtermTrans) 9) ((ExPredatesSubterm) 10)
    ((ExCoerce) 11) ((ExCoercibleRefl) 12) ((ExCoercibleSym) 13) ((ExCoercibleTrans) 14) ((ExCoercibleWrap) 15)
    ((ExCoercibleCtor) 16) ((ExCoercibleOf) 17) ((ExDistinct) 18) ((ExOpenAbsurd) 19) ((ExDelegateOf) 26)))

(def-fns _ $ (many mark-code : (many (MarkK) k) -> (many (Nat) n))
  (match many k _
    ((MkErased) 0) ((MkMany) 1) ((MkColon) 2) ((MkIs) 3) ((MkArrow) 4) ((MkSubterm) 5) ((MkEnum) 6) ((MkUnion) 7)
    ((MkTail) 8) ((MkDelegate) 9) ((MkPredates) 10) ((MkAbsurd) 11) ((MkNewtypeMark) 12) ((MkExtern) 13) ((MkElse) 14) ((MkUnique) 15) ((MkAt) 16) ((MkNoTail) 17)))

(def-fns _ $ (many sp-arity : (many (Sp) sp) -> (many (Maybe $ Nat) n))
  (match many sp _
    ((SpMark k) (match many k _ ((MkTail) (Some _ 1)) ((MkNoTail) (Some _ 1)) ((MkDelegate) (Some _ 1)) (else (None _))))
    ((SpExpr k)
      (match many k _
        ((ExMatchableOf) (Some _ 1)) ((ExNumeralOf) (Some _ 1)) ((ExLevelOf) (Some _ 1)) ((ExCoercibleSym) (Some _ 1)) ((ExCoercibleShare) (Some _ 1)) ((ExCoercibleOf) (Some _ 1)) ((ExDelegateOf) (Some _ 1))
        ((ExProveSubterm) (Some _ 2)) ((ExProvePredates) (Some _ 2)) ((ExPredatesTrans) (Some _ 2)) ((ExSubtermTrans) (Some _ 2)) ((ExPredatesSubterm) (Some _ 2)) ((ExCoerce) (Some _ 2)) ((ExCoercibleRefl) (Some _ 2)) ((ExCoercibleTrans) (Some _ 2))
        (else (None _))))
    (else (None _))))

(def-fns _ $ (many sp-eq : (many (Sp) a) (many (Sp) b) -> (many (Bool) r))
  (match many a _
    ((SpStmt ka) (match many b _ ((SpStmt kb) (nat-eq (stmt-code ka) $ stmt-code kb)) (else (BFalse))))
    ((SpFormer ka) (match many b _ ((SpFormer kb) (nat-eq (former-code ka) $ former-code kb)) (else (BFalse))))
    ((SpExpr ka) (match many b _ ((SpExpr kb) (nat-eq (expr-code ka) $ expr-code kb)) (else (BFalse))))
    ((SpMark ka) (match many b _ ((SpMark kb) (nat-eq (mark-code ka) $ mark-code kb)) (else (BFalse))))))

(def-adts $ (SpEntry : -> Type)
  enum
  (many MkSpEntry : (many (String) name) (many (Sp) sp) -> (SpEntry)))

(def-fns _ $ (many sp-cons : (many (String) name) (many (Sp) sp) (many (List $ SpEntry) rest) -> (many (List $ SpEntry) r))
  (Cons _ (MkSpEntry name sp) rest))

; Every special form by name, in the order of lib/special.ml; a form's constructor index in the Special
; ADT is its position here.
(let ((many sp-table))
  $ sp-cons "let" (SpStmt $ StLet) $ sp-cons "def-lvl" (SpStmt $ StDefLvl) $ sp-cons "def-fns" (SpStmt $ StDefFns) $ sp-cons "def-unique" (SpStmt $ StDefUnique) $
  sp-cons "def-adts" (SpStmt $ StDefAdts) $ sp-cons "comptime-match" (SpStmt $ StComptimeMatch) $
  sp-cons "let-match" (SpStmt $ StLetMatch) $ sp-cons "unary" (SpStmt $ StUnary) $ sp-cons "distinct" (SpExpr $ ExDistinct) $
  sp-cons "open-adt" (SpStmt $ StOpenAdt) $ sp-cons "open-absurd" (SpExpr $ ExOpenAbsurd) $
  sp-cons "Fn" (SpFormer $ FoFn) $ sp-cons "UniqueFn" (SpFormer $ FoUniqueFn) $ sp-cons "TyCtor" (SpFormer $ FoTyCtor) $ sp-cons "ValCtor" (SpFormer $ FoValCtor) $
  sp-cons "Matchable" (SpFormer $ FoMatchable) $
  sp-cons "cell-alloc" (SpExpr $ ExCellAlloc) $ sp-cons "cell-write" (SpExpr $ ExCellWrite) $ sp-cons "cell-match" (SpExpr $ ExCellMatch) $ sp-cons "Cell" (SpFormer $ FoCell) $ sp-cons "SlotHolds" (SpExpr $ ExSlotHolds) $ sp-cons "SlotVacant" (SpExpr $ ExSlotVacant) $ sp-cons "at" (SpMark $ MkAt) $ sp-cons "share" (SpExpr $ ExShare) $ sp-cons "match" (SpExpr $ ExMatch) $ sp-cons "matchable-of" (SpExpr $ ExMatchableOf) $
  sp-cons "numeral-of" (SpExpr $ ExNumeralOf) $ sp-cons "level-of" (SpExpr $ ExLevelOf) $ sp-cons "prove-subterm" (SpExpr $ ExProveSubterm) $
  sp-cons "prove-predates" (SpExpr $ ExProvePredates) $ sp-cons "values" (SpExpr $ ExValues) $
  sp-cons "predates-trans" (SpExpr $ ExPredatesTrans) $ sp-cons "subterm-trans" (SpExpr $ ExSubtermTrans) $
  sp-cons "predates-subterm" (SpExpr $ ExPredatesSubterm) $
  sp-cons "coerce" (SpExpr $ ExCoerce) $ sp-cons "coercible-refl" (SpExpr $ ExCoercibleRefl) $ sp-cons "coercible-sym" (SpExpr $ ExCoercibleSym) $
  sp-cons "coercible-trans" (SpExpr $ ExCoercibleTrans) $ sp-cons "coercible-wrap" (SpExpr $ ExCoercibleWrap) $
  sp-cons "coercible-ctor" (SpExpr $ ExCoercibleCtor) $ sp-cons "coercible-of" (SpExpr $ ExCoercibleOf) $ sp-cons "delegate-of" (SpExpr $ ExDelegateOf) $ sp-cons "coercible-share" (SpExpr $ ExCoercibleShare) $ sp-cons "dump-context" (SpStmt $ StDumpContext) $
  sp-cons "erased" (SpMark $ MkErased) $ sp-cons "many" (SpMark $ MkMany) $ sp-cons "unique" (SpMark $ MkUnique) $ sp-cons ":" (SpMark $ MkColon) $
  sp-cons "is" (SpMark $ MkIs) $ sp-cons "->" (SpMark $ MkArrow) $ sp-cons "subterm" (SpMark $ MkSubterm) $
  sp-cons "enum" (SpMark $ MkEnum) $ sp-cons "union" (SpMark $ MkUnion) $ sp-cons "tail" (SpMark $ MkTail) $ sp-cons "notail" (SpMark $ MkNoTail) $
  sp-cons "delegate" (SpMark $ MkDelegate) $ sp-cons "predates" (SpMark $ MkPredates) $ sp-cons "absurd" (SpMark $ MkAbsurd) $
  sp-cons "newtype" (SpMark $ MkNewtypeMark) $ sp-cons "extern" (SpMark $ MkExtern) $ sp-cons "else" (SpMark $ MkElse) (Nil _))

(def-fns _ $ (many sp-of-index : (many (Nat) i) -> (many (Maybe $ Sp) r))
  (match many (list-nth _ sp-table i) _
    ((NthMiss _ _ _ _) (None _))
    ((NthHit _ _ _ e _) (match many e _ ((MkSpEntry _ sp) (Some _ sp))))))

; ---- Scopes of the post-erasure code: a context is the frames of non-erased ids the code binds, innermost
; first; a variable carries the path to its frame and its place there, and a runtime environment holds
; one list of values per frame, in step with the frame's ids.

(def-adts
  ((At : ((Nat) x) ((List $ Nat) f) -> Type)
    enum
    (many AtHere : (erased (Nat) x) (erased (List $ Nat) rest) -> (At x (Cons (Nat) x rest)))
    (many AtThere : (erased (Nat) x) (erased (Nat) y) (erased (List $ Nat) rest) (many (At x rest) p) -> (At x (Cons (Nat) y rest))))
  ((Mem : ((Nat) x) ((List $ List $ Nat) ctx) -> Type)
    enum
    (many MHere : (erased (Nat) x) (erased (List $ Nat) f) (erased (List $ List $ Nat) ctx) (many (At x f) p) -> (Mem x (Cons (List (Nat)) f ctx)))
    (many MThere : (erased (Nat) x) (erased (List $ Nat) f) (erased (List $ List $ Nat) ctx) (many (Mem x ctx) p) -> (Mem x (Cons (List (Nat)) f ctx)))))

(def-fns _ $ (many at-dec : (many (Nat) x) (subterm many (List $ Nat) f) -> (many (Maybe $ At x f) r))
  (let-match many f (Cons _ y rest) ((Nil _) (None _)))
  (match many (nat-cmp x y) _
    ((CEq _ _ _) (Some _ $ AtHere _ _))
    (else (match many (notail $ at-dec x rest) _ ((Some _ p) (Some _ $ AtThere _ _ _ p)) ((None _) (None _))))))

(def-fns _ $ (many mem-dec : (many (Nat) x) (subterm many (List $ List $ Nat) ctx) -> (many (Maybe $ Mem x ctx) r))
  (let-match many ctx (Cons _ f rest) ((Nil _) (None _)))
  (match many (at-dec x f) _
    ((Some _ p) (Some _ $ MHere _ _ _ p))
    ((None _) (match many (notail $ mem-dec x rest) _ ((Some _ p) (Some _ $ MThere _ _ _ p)) ((None _) (None _))))))

; The place of each id of a frame, for code that refers to the frame's binders in turn.
(def-adts $ (AtIn : ((List $ Nat) f) -> Type)
  enum
  (many MkAtIn : (erased (List $ Nat) f) (many (Nat) x) (many (At x f) p) -> (AtIn f)))

(def-fns _ $ (many at-ins-there-lock : (erased (Nat) y) (erased (List $ Nat) rest) (subterm many (List $ AtIn rest) ps) -> (many (List $ AtIn (Cons (Nat) y rest)) r) (erased (Lockstep (AtIn rest) (AtIn (Cons (Nat) y rest)) ps r) lk))
  (let-match many ps (Cons _ p more) ((Nil _) (values (Nil _) (LsNil _ _))))
  (let ((many r) (erased lk)) $ notail $ at-ins-there-lock y rest more)
  (match many p _ ((MkAtIn _ x q) (values (Cons _ (MkAtIn _ x $ AtThere _ _ _ q) r) (LsCons _ _ p (MkAtIn _ x $ AtThere _ _ _ q) more r lk)))))

(def-fns _ $ (many at-ins : (subterm many (List $ Nat) f) -> (many (List $ AtIn f) r) (erased (Lockstep (Nat) (AtIn f) f r) lk))
  (let-match many f (Cons _ x rest) ((Nil _) (values (Nil _) (LsNil _ _))))
  (let ((many more) (erased lk)) $ notail $ at-ins rest)
  (let ((many shifted) (erased ls)) $ at-ins-there-lock x rest more)
  (values (Cons _ (MkAtIn _ x $ AtHere _ _) shifted) (LsCons _ _ x (MkAtIn _ x $ AtHere _ _) rest shifted $ lockstep-trans _ _ _ _ _ _ lk ls)))

; ---- The FFI's types and functions (section 41; lib/ffi.ml), each decided from its name once, at its extern mark.

(def-adts
  ((ExtType : -> Type)
    enum
    (many ExtArray : -> (ExtType)) (many ExtNat : -> (ExtType)) (many ExtHalf : -> (ExtType)) (many ExtString : -> (ExtType)))
  ((Extern : ((Nat) arity) -> Type)
    enum
    (many ExArrayNew : -> (Extern 1)) (many ExArraySwap : -> (Extern 3)) (many ExArrayPluck : -> (Extern 2)) (many ExArrayPlace : -> (Extern 3))
    (many ExArraySwapImm : -> (Extern 3)) (many ExArrayPlaceImm : -> (Extern 3)) (many ExArrayLength : -> (Extern 1)) (many ExListToArray : -> (Extern 1)) (many ExArrayMake : -> (Extern 2))
    (many ExAdd : -> (Extern 2)) (many ExSub : -> (Extern 2)) (many ExMul : -> (Extern 2)) (many ExDiv : -> (Extern 2)) (many ExDivmod : -> (Extern 2)) (many ExNatCmp : -> (Extern 2)) (many ExNatMod : -> (Extern 2)) (many ExAppend : -> (Extern 2))
    (many ExNatHalve : -> (Extern 1)) (many ExTrim : -> (Extern 1)) (many ExFlatten : -> (Extern 1))
    (many ExStrCmp : -> (Extern 2)) (many ExStrLength : -> (Extern 1)) (many ExStrSplit : -> (Extern 2)) (many ExNatStr : -> (Extern 1))
    (many ExU62Add : -> (Extern 2)) (many ExU62Sub : -> (Extern 2)) (many ExU62Mul : -> (Extern 2)) (many ExU62Div : -> (Extern 2)) (many ExU62Divmod : -> (Extern 2)) (many ExU62Mod : -> (Extern 2)) (many ExU62Cmp : -> (Extern 2))
    (many ExLtDec : -> (Extern 2)) (many ExU62LtDec : -> (Extern 2)) (many ExArrayGet : -> (Extern 2))
    (many ExArrayGetMany : -> (Extern 2)) (many ExArrayLengthMany : -> (Extern 1)))
  ((SomeExtern : -> Type)
    enum
    (many MkSomeExtern : (erased (Nat) n) (many (Extern n) e) -> (SomeExtern))))

(def-fns _ $ (many ext-type-name : (many (ExtType) t) -> (many (String) s))
  (match many t _ ((ExtArray) "Array") ((ExtNat) "Nat") ((ExtHalf) "Half") ((ExtString) "String")))

; The shape an implementation's view has (lib/ffi_core.ml), which its model must have too: the many-field
; arities of the non-phantom constructors in order, every one of them tagged. An extern function that builds
; a plain type's values records that type's shape the same way; one that builds none records nothing.
(def-fns _ $ (many ext-type-shape : (many (ExtType) t) -> (many (List $ Nat) s))
  (match many t _
    ((ExtArray) (Cons _ 0 $ Cons _ 2 $ Nil _))
    ((ExtNat) (Cons _ 0 $ Cons _ 1 $ Nil _))
    ((ExtHalf) (Cons _ 0 $ Cons _ 1 $ Cons _ 1 $ Nil _))
    ((ExtString) (Cons _ 0 $ Cons _ 2 $ Nil _))))

(def-fns _ $ (many ext-result-shape : (erased (Nat) n) (many (Extern n) e) -> (many (Maybe $ List $ Nat) s))
  (let ((many (List $ Nat) cmp)) (Cons _ 0 $ Cons _ 0 $ Cons _ 0 $ Nil _))
  (let ((many (List $ Nat) dec)) (Cons _ 0 $ Cons _ 0 $ Nil _))
  (match many e _
    ((ExArrayNew) (None _)) ((ExArraySwap) (None _)) ((ExArrayPluck) (None _)) ((ExArrayPlace) (None _))
    ((ExArraySwapImm) (None _)) ((ExArrayPlaceImm) (None _)) ((ExArrayLength) (None _)) ((ExListToArray) (None _)) ((ExArrayMake) (None _))
    ((ExNatCmp) (Some _ cmp)) ((ExStrCmp) (Some _ cmp))
    ((ExAdd) (None _)) ((ExSub) (None _)) ((ExMul) (None _)) ((ExDiv) (None _)) ((ExDivmod) (None _))
    ((ExNatMod) (None _)) ((ExAppend) (None _)) ((ExNatHalve) (None _)) ((ExTrim) (None _))
    ((ExFlatten) (None _)) ((ExStrLength) (None _)) ((ExStrSplit) (None _)) ((ExNatStr) (None _))
    ((ExU62Add) (None _)) ((ExU62Sub) (None _)) ((ExU62Mul) (None _)) ((ExU62Div) (None _)) ((ExU62Divmod) (None _)) ((ExU62Mod) (None _)) ((ExU62Cmp) (Some _ cmp))
    ((ExLtDec) (Some _ dec)) ((ExU62LtDec) (Some _ dec)) ((ExArrayGet) (None _))
    ((ExArrayGetMany) (None _)) ((ExArrayLengthMany) (None _))))

(def-fns _ $ (many ext-type-of : (many (String) name) -> (many (Maybe $ ExtType) r))
  (match many (str-cmp name "Nat") _
    ((CEq _ _ _) (Some _ $ ExtNat))
    (else (match many (str-cmp name "Half") _
      ((CEq _ _ _) (Some _ $ ExtHalf))
      (else (match many (str-cmp name "String") _ ((CEq _ _ _) (Some _ $ ExtString)) (else (match many (str-eq name "Array") _ ((BTrue) (Some _ $ ExtArray)) ((BFalse) (None _))))))))))

(def-fns _ $ (many ext-arity : (erased (Nat) n) (many (Extern n) e) -> (many n is m))
  (match many e _
    ((ExArrayNew) 1) ((ExArraySwap) 3) ((ExArrayPluck) 2) ((ExArrayPlace) 3)
    ((ExArraySwapImm) 3) ((ExArrayPlaceImm) 3) ((ExArrayLength) 1) ((ExListToArray) 1) ((ExArrayMake) 2)
    ((ExAdd) 2) ((ExSub) 2) ((ExMul) 2) ((ExDiv) 2) ((ExDivmod) 2) ((ExNatCmp) 2) ((ExNatMod) 2) ((ExAppend) 2)
    ((ExNatHalve) 1) ((ExTrim) 1) ((ExFlatten) 1) ((ExStrCmp) 2) ((ExStrLength) 1) ((ExStrSplit) 2) ((ExNatStr) 1)
    ((ExU62Add) 2) ((ExU62Sub) 2) ((ExU62Mul) 2) ((ExU62Div) 2) ((ExU62Divmod) 2) ((ExU62Mod) 2) ((ExU62Cmp) 2)
    ((ExLtDec) 2) ((ExU62LtDec) 2) ((ExArrayGet) 2) ((ExArrayGetMany) 2) ((ExArrayLengthMany) 1)))

(def-fns _ $ (many ext-twin : (erased (Nat) n) (many (Extern n) e) -> (many (Extern n) r))
  (match many e _
    ((ExU62Add) (ExAdd)) ((ExU62Sub) (ExSub)) ((ExU62Mul) (ExMul)) ((ExU62Div) (ExDiv)) ((ExU62Divmod) (ExDivmod))
    ((ExU62Mod) (ExNatMod)) ((ExU62Cmp) (ExNatCmp)) ((ExU62LtDec) (ExLtDec)) ((ExArrayGet) (ExArrayPluck))
    ((ExArrayGetMany) (ExArrayPluck)) ((ExArrayLengthMany) (ExArrayLength))
    ((ExArraySwapImm) (ExArraySwap)) ((ExArrayPlaceImm) (ExArrayPlace))
    (else e)))

(def-fns _ $ (many ext-name : (erased (Nat) n) (many (Extern n) e) -> (many (String) s))
  (match many e _
    ((ExArrayNew) "array-new") ((ExArraySwap) "array-swap") ((ExArrayPluck) "array-pluck") ((ExArrayPlace) "array-place")
    ((ExArraySwapImm) "array-swap-imm") ((ExArrayPlaceImm) "array-place-imm") ((ExArrayLength) "array-length") ((ExListToArray) "list-to-array") ((ExArrayMake) "array-make")
    ((ExAdd) "add") ((ExSub) "sub") ((ExMul) "mul") ((ExDiv) "div") ((ExDivmod) "divmod") ((ExNatCmp) "nat-cmp") ((ExNatMod) "nat-mod") ((ExAppend) "append")
    ((ExNatHalve) "nat-halve") ((ExTrim) "trim") ((ExFlatten) "flatten")
    ((ExStrCmp) "str-cmp") ((ExStrLength) "str-length") ((ExStrSplit) "str-split") ((ExNatStr) "nat-str")
    ((ExU62Add) "u62-add") ((ExU62Sub) "u62-sub") ((ExU62Mul) "u62-mul") ((ExU62Div) "u62-div") ((ExU62Divmod) "u62-divmod") ((ExU62Mod) "u62-mod") ((ExU62Cmp) "u62-cmp")
    ((ExLtDec) "lt-dec") ((ExU62LtDec) "u62-lt-dec") ((ExArrayGet) "array-get")
    ((ExArrayGetMany) "array-get-many") ((ExArrayLengthMany) "array-length-many")))

(let ((many externs))
  $ Cons _ (MkSomeExtern _ $ ExArrayNew) $ Cons _ (MkSomeExtern _ $ ExArraySwap) $ Cons _ (MkSomeExtern _ $ ExArrayPluck) $ Cons _ (MkSomeExtern _ $ ExArrayPlace) $ Cons _ (MkSomeExtern _ $ ExArraySwapImm) $ Cons _ (MkSomeExtern _ $ ExArrayPlaceImm) $
  Cons _ (MkSomeExtern _ $ ExArrayLength) $ Cons _ (MkSomeExtern _ $ ExListToArray) $ Cons _ (MkSomeExtern _ $ ExArrayMake) $ Cons _ (MkSomeExtern _ $ ExAdd) $ Cons _ (MkSomeExtern _ $ ExSub) $ Cons _ (MkSomeExtern _ $ ExMul) $ Cons _ (MkSomeExtern _ $ ExDiv) $ Cons _ (MkSomeExtern _ $ ExDivmod) $ Cons _ (MkSomeExtern _ $ ExNatCmp) $ Cons _ (MkSomeExtern _ $ ExNatMod) $ Cons _ (MkSomeExtern _ $ ExAppend) $
  Cons _ (MkSomeExtern _ $ ExNatHalve) $ Cons _ (MkSomeExtern _ $ ExTrim) $ Cons _ (MkSomeExtern _ $ ExFlatten) $
  Cons _ (MkSomeExtern _ $ ExStrCmp) $ Cons _ (MkSomeExtern _ $ ExStrLength) $ Cons _ (MkSomeExtern _ $ ExStrSplit) $ Cons _ (MkSomeExtern _ $ ExNatStr) $
  Cons _ (MkSomeExtern _ $ ExU62Add) $ Cons _ (MkSomeExtern _ $ ExU62Sub) $ Cons _ (MkSomeExtern _ $ ExU62Mul) $ Cons _ (MkSomeExtern _ $ ExU62Div) $ Cons _ (MkSomeExtern _ $ ExU62Divmod) $ Cons _ (MkSomeExtern _ $ ExU62Mod) $ Cons _ (MkSomeExtern _ $ ExU62Cmp) $
  Cons _ (MkSomeExtern _ $ ExLtDec) $ Cons _ (MkSomeExtern _ $ ExU62LtDec) $ Cons _ (MkSomeExtern _ $ ExArrayGet) $
  Cons _ (MkSomeExtern _ $ ExArrayGetMany) $ Cons _ (MkSomeExtern _ $ ExArrayLengthMany) (Nil _))

(def-fns _ $ (many extern-named : (subterm many (List $ SomeExtern) es) (many (String) name) -> (many (Maybe $ SomeExtern) r))
  (let-match many es (Cons _ e rest) ((Nil _) (None _)))
  (match many (match many e (((Bool) _)) ((MkSomeExtern _ x) (str-eq name $ ext-name _ x))) _
    ((BTrue) (Some _ e))
    ((BFalse) (tail $ extern-named rest name))))

(def-fns _ $ (many extern-of : (many (String) name) -> (many (Maybe $ SomeExtern) r))
  (extern-named externs name))

; ---- Blocks, frames and post-erasure code (lib/value.ml): a value is an address into self/heap.sl's
; store, and a block holds section 38's representation with every address in it below its own.

(def-adts
  ((Payload : -> Type)
    enum
    (many PNat : (many (Nat) n) -> (Payload))
    (many PHalf : (many (Nat) n) -> (Payload))
    (many PStr : (many (String) s) -> (Payload)))
  ; [tagged]: an enum with more than one non-phantom constructor (section 38); [ctors]: the non-phantom
  ; ones at their discriminants; [ext]: the extern type's name where the FFI holds it (section 41); a
  ; constructor's [shape] is its type's many-field arities in order, which fixes the representation.
  ((Adt : -> Type)
    enum
    (many MkAdt : (many (String) name) (many (Bool) tagged) (many (List $ Ctor) ctors) (many (Maybe $ ExtType) ext) (many (Bool) nt) -> (Adt)))
  ((Ctor : -> Type)
    enum
    (many MkCtor : (many (String) name) (many (Nat) id) (many (Nat) index) (many (Nat) arity) (many (Bool) tagged) (many (Maybe $ ExtType) ext) (many (List $ Nat) shape) (many (Bool) nt) -> (Ctor)))
  ((Block : (Type R) -> Type)
    enum
    (many BArray : (erased Type R) (many (Nat) len) (many (IdMap R) elems) -> (Block R))
    (many BTag : (erased Type R) (many (Ctor) c) (many (List R) fields) -> (Block R))
    (many BTup : (erased Type R) (many (List R) fields) -> (Block R))
    (many BExt : (erased Type R) (many (Payload) p) -> (Block R))
    (many BCtorFn : (erased Type R) (many (Ctor) c) -> (Block R))
    (many BMat : (erased Type R) (many (Adt) adt) -> (Block R))
    (many BGroup : (erased Type R) (erased (List $ Nat) gids) (erased (List $ List $ Nat) ctx) (many (Group gids ctx) g) (many (Frames R ctx) env) -> (Block R))
    (many BFn : (erased Type R) (many R group) (many (Nat) member) (many (Nat) id) -> (Block R))
    (many BToken : (erased Type R) -> (Block R))
    (many BError : (erased Type R) (many (String) msg) -> (Block R)))
  ; [ctx]: the frames in scope, innermost first; a group's frame holds its block's address, a member being
  ; made when read.
  ((Frames : (Type R) ((List $ List $ Nat) ctx) -> Type)
    enum
    (many FrNil : (erased Type R) -> (Frames R (Nil (List (Nat)))))
    (many FrVals : (erased Type R) (erased (List $ List $ Nat) ctx) (many (List $ Nat) f) (many (List R) vs) (erased (Lockstep (Nat) R f vs) lk) (many (Frames R ctx) rest) -> (Frames R (Cons (List (Nat)) f ctx)))
    (many FrGroup : (erased Type R) (erased (List $ List $ Nat) ctx) (many (List $ Nat) gids) (many R group) (many (Group gids ctx) members) (many (Frames R ctx) rest) -> (Frames R (Cons (List (Nat)) gids ctx))))
  ; [gids]: the frame the group binds, its functions' ids in order.
  ((Group : ((List $ Nat) gids) ((List $ List $ Nat) ctx) -> Type)
    enum
    (many MkGroup : (erased (List $ List $ Nat) ctx) (many (List $ Nat) gids) (many (List $ Pair (Nat) $ Func gids ctx) fns) (erased (Lockstep (Nat) (Pair (Nat) $ Func gids ctx) gids fns) lk) -> (Group gids ctx)))
  ; [top]: defined by a run-position def-fns; the body binds the parameters over the group over the
  ; defining scope. [impl]: the FFI's implementation with the constructors of the plain type it builds,
  ; read off the model's return type at the extern mark (section 41).
  ((Impl : -> Type)
    enum
    (many MkImpl : (many (SomeExtern) e) (many (List $ Ctor) cs) -> (Impl)))
  ((Func : ((List $ Nat) gids) ((List $ List $ Nat) ctx) -> Type)
    enum
    (many MkFunc : (erased (List $ Nat) gids) (erased (List $ List $ Nat) ctx) (many (List $ Mult) rets) (many (String) name) (many (Nat) id) (many (List $ Nat) params) (many (Code (Cons (List (Nat)) params (Cons (List (Nat)) gids ctx)) rets) body) (many (Maybe $ Impl) impl) (many (Bool) top) -> (Func gids ctx))
    (many MkAlias : (erased (List $ Nat) gids) (erased (List $ List $ Nat) ctx) (many (String) name) (many (Nat) id) (many (Code (Cons (List (Nat)) gids ctx) many-one) target) -> (Func gids ctx)))
  ; [ctx]: the frames in scope; [ms]: the multiplicities of the values the code produces, the many ones being
  ; what runs (section 16); a node that has to make values on its own holds them as data. A Const entry is
  ; named by its id and read from the store when the code runs (section 34); a value elaboration embeds is
  ; a closed block, allocated when reached.
  ((Code : ((List $ List $ Nat) ctx) ((List $ Mult) ms) -> Type)
    enum
    (many CVar : (erased (List $ List $ Nat) ctx) (many (Nat) id) (many (Mem id ctx) p) -> (Code ctx many-one))
    (many CConst : (erased (List $ List $ Nat) ctx) (many (Nat) id) -> (Code ctx many-one))
    (many CValue : (erased (List $ List $ Nat) ctx) (many (Block (Ref Block (HEmpty Block))) v) -> (Code ctx many-one))
    (many CErased : (erased (List $ List $ Nat) ctx) (many (List $ Mult) ms) -> (Code ctx ms))
    (many CValues : (erased (List $ List $ Nat) ctx) (many (List $ Mult) ms) (many (List $ Code ctx many-one) cs) (erased (Picked (Code ctx many-one) ms cs) pk) -> (Code ctx ms))
    (many CApp : (erased (List $ List $ Nat) ctx) (many (List $ Mult) ms) (many (Code ctx many-one) f) (many (List $ Code ctx many-one) args) (many (CC) cc) -> (Code ctx ms))
    (many CLet : (erased (List $ List $ Nat) ctx) (many (List $ Mult) ms) (erased (List $ Mult) ns) (many (List $ Nat) ids) (erased (Picked (Nat) ms ids) pk) (many (Code ctx ms) rhs) (many (Code (Cons (List (Nat)) ids ctx) ns) rest) -> (Code ctx ns))
    (many CLetRec : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ns) (erased (List $ Nat) gids) (many (Group gids ctx) g) (many (Code (Cons (List (Nat)) gids ctx) ns) rest) -> (Code ctx ns))
    (many CMatch : (erased (List $ List $ Nat) ctx) (many (List $ Mult) ns) (many (Code ctx many-one) scrut) (many (Shape ctx) shape) (many (List $ Branch ctx ns) branches) (many (Maybe $ Code (Cons (List (Nat)) (Nil (Nat)) ctx) ns) dflt) (many (List $ Nat) live) -> (Code ctx ns))
    (many CCellAlloc : (erased (List $ List $ Nat) ctx) (many (Ctor) ctor) (many (List $ Code ctx many-one) slots) -> (Code ctx many-one))
    (many CCellWrite : (erased (List $ List $ Nat) ctx) (many (Ctor) ctor) (many (Code ctx many-one) cell) (many (List $ Pair (Nat) $ Code ctx many-one) slots) -> (Code ctx many-one))
    (many CCellRead : (erased (List $ List $ Nat) ctx) (many (Ctor) ctor) (many (Nat) index) (many (Code ctx many-one) cell) -> (Code ctx many-one))
    (many CAbsurd : (erased (List $ List $ Nat) ctx) (many (List $ Mult) ms) -> (Code ctx ms))
    (many CError : (erased (List $ List $ Nat) ctx) (many (List $ Mult) ms) (many (String) msg) -> (Code ctx ms)))
  ((CC : -> Type)
    enum
    (many CCPlain : -> (CC)) (many CCTail : -> (CC)) (many CCDelegate : -> (CC)) (many CCCtor : -> (CC)) (many CCNoTail : -> (CC))
    ; a same-level call in a non-erased position carrying no mark, where the tail-position check warns
    (many CCSame : (many (Loc) site) (many (Term) callee) -> (CC)))
  ((Shape : ((List $ List $ Nat) ctx) -> Type)
    enum
    (many ShKnown : (erased (List $ List $ Nat) ctx) (many (Adt) adt) -> (Shape ctx))
    (many ShHeld : (erased (List $ List $ Nat) ctx) (many (Code ctx many-one) c) (many (Adt) adt) -> (Shape ctx))
    (many ShNone : (erased (List $ List $ Nat) ctx) -> (Shape ctx)))
  ((Branch : ((List $ List $ Nat) ctx) ((List $ Mult) ns) -> Type)
    enum
    (many MkBranch : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ns) (many (Nat) disc) (many (List $ Nat) ids) (many (Code (Cons (List (Nat)) ids ctx) ns) body) -> (Branch ctx ns))))

; Widening the bound of every holder of addresses is a coerce (section 38).

(def-fns _ $ (erased frames-widen : (erased (Hist Block) b) (erased (Hist Block) c) (erased (Suffix Block c b) le) (erased (List $ List $ Nat) ctx) (subterm erased (Frames (Ref Block b) ctx) env) -> (erased (Frames (Ref Block c) ctx) env2) (erased (Coercible (Shared) (Frames (Ref Block b) ctx) env (Shared) (Frames (Ref Block c) ctx) env2) p))
  (match erased env _
    ((FrNil _) (values (FrNil _) (coercible-ctor (Shared) FrNil (Ref Block b) (Ref Block c))))
    ((FrVals _ cx f vs lk rest)
      (let ((erased vs2) (erased pv) (erased lk2)) (refs-widen-lk _ b c le f vs lk))
      (let ((erased rest2) (erased pr)) (frames-widen b c le cx rest))
      (values (FrVals _ _ f vs2 lk2 rest2) (coercible-ctor (Shared) FrVals (Ref Block b) (Ref Block c) cx cx (coercible-refl (Shared) f) pv lk lk2 pr)))
    ((FrGroup _ cx gids g grp rest)
      (let ((erased g2) (erased pg)) (ref-widen _ b c le g))
      (let ((erased rest2) (erased pr)) (frames-widen b c le cx rest))
      (values (FrGroup _ _ gids g2 grp rest2) (coercible-ctor (Shared) FrGroup (Ref Block b) (Ref Block c) cx cx (coercible-refl (Shared) gids) pg (coercible-refl (Shared) grp) pr)))))

(def-fns _ $ (many array-block : (erased Type R) (many (List R) xs) -> (many (Block R) b))
  (BArray _ (list-length _ xs) $ idmap-of-list _ xs 0 $ MEmpty _))

(def-fns _ $ (erased block-widen : (erased (Hist Block) b) (erased (Hist Block) c) (erased (Suffix Block c b) le) (erased (Block (Ref Block b)) blk) -> (erased (Block (Ref Block c)) blk2) (erased (Coercible (Shared) (Block (Ref Block b)) blk (Shared) (Block (Ref Block c)) blk2) p))
  (match erased blk _
    ((BArray _ n es)
      (let ((erased es2) (erased pe)) (idmap-widen Block b c le es))
      (values (BArray _ n es2) (coercible-ctor (Shared) BArray (Ref Block b) (Ref Block c) (coercible-refl (Shared) n) pe)))
    ((BTag _ ct fields)
      (let ((erased fs2) (erased pf)) (refs-widen _ b c le fields))
      (values (BTag _ ct fs2) (coercible-ctor (Shared) BTag (Ref Block b) (Ref Block c) (coercible-refl (Shared) ct) pf)))
    ((BTup _ fields)
      (let ((erased fs2) (erased pf)) (refs-widen _ b c le fields))
      (values (BTup _ fs2) (coercible-ctor (Shared) BTup (Ref Block b) (Ref Block c) pf)))
    ((BExt _ p) (values (BExt _ p) (coercible-ctor (Shared) BExt (Ref Block b) (Ref Block c) (coercible-refl (Shared) p))))
    ((BCtorFn _ ct) (values (BCtorFn _ ct) (coercible-ctor (Shared) BCtorFn (Ref Block b) (Ref Block c) (coercible-refl (Shared) ct))))
    ((BMat _ adt) (values (BMat _ adt) (coercible-ctor (Shared) BMat (Ref Block b) (Ref Block c) (coercible-refl (Shared) adt))))
    ((BGroup _ gids cx g env)
      (let ((erased env2) (erased pe)) (frames-widen b c le cx env))
      (values (BGroup _ _ _ g env2) (coercible-ctor (Shared) BGroup (Ref Block b) (Ref Block c) gids gids cx cx (coercible-refl (Shared) g) pe)))
    ((BFn _ g i id)
      (let ((erased g2) (erased pg)) (ref-widen _ b c le g))
      (values (BFn _ g2 i id) (coercible-ctor (Shared) BFn (Ref Block b) (Ref Block c) pg (coercible-refl (Shared) i) (coercible-refl (Shared) id))))
    ((BToken _) (values (BToken _) (coercible-ctor (Shared) BToken (Ref Block b) (Ref Block c))))
    ((BError _ m) (values (BError _ m) (coercible-ctor (Shared) BError (Ref Block b) (Ref Block c) (coercible-refl (Shared) m))))))

(def-fns _ $ (many at-get : (erased Type B) (erased (Nat) x) (erased (List $ Nat) f) (subterm many (At x f) p) (many (List B) vs) (erased (Lockstep (Nat) B f vs) lk) -> (many B v) (erased (Subterm B v (List B) vs) q))
  (match many p _
    ((AtHere _ _)
      (let-match erased lk (LsCons ta tb x0 v0 xs vs0 q))
      (let-match many vs (Cons a v more))
      (values v $ prove-subterm v vs))
    ((AtThere _ _ _ q)
      (let-match erased lk (LsCons ta tb x0 v0 xs vs0 q2))
      (let-match many vs (Cons a v more))
      (let ((many w) (erased sq)) $ tail $ at-get _ _ _ q more q2)
      (values w $ subterm-trans sq $ prove-subterm more vs))))

(def-fns _ $ (many ctor-newtype : (many (Ctor) c) -> (many (Bool) r))
  (match many c _ ((MkCtor _ _ _ _ _ _ _ nt) nt)))
(def-fns _ $ (many ctor-tagged : (many (Ctor) c) -> (many (Bool) r))
  (match many c _ ((MkCtor _ _ _ _ tg _ _ _) tg)))
(def-fns _ $ (many adt-newtype : (many (Adt) a) -> (many (Bool) r))
  (match many a _ ((MkAdt _ _ _ _ nt) nt)))

(def-fns _ $ (many ctor-index : (many (Ctor) c) -> (many (Nat) i))
  (match many c _ ((MkCtor _ _ ix _ _ _ _ _) ix)))

(def-fns _ $ (many ctor-arity : (many (Ctor) c) -> (many (Nat) i))
  (match many c _ ((MkCtor _ _ _ ar _ _ _ _) ar)))

(def-fns _ $ (many ctor-name : (many (Ctor) c) -> (many (String) s))
  (match many c _ ((MkCtor n _ _ _ _ _ _ _) n)))

(def-fns _ $ (many ctor-id : (many (Ctor) c) -> (many (Nat) s))
  (match many c _ ((MkCtor _ id _ _ _ _ _ _) id)))

(def-fns _ $ (many ctor-shape : (many (Ctor) c) -> (many (List $ Nat) s))
  (match many c _ ((MkCtor _ _ _ _ _ _ sh _) sh)))

(def-fns _ $ (many ctor-arities : (subterm many (List $ Ctor) cs) -> (many (List $ Nat) r))
  (match many cs _
    ((Nil _) (Nil _))
    ((Cons _ c rest) (Cons _ (ctor-arity c) $ notail $ ctor-arities rest))))

(def-fns _ $ (many adt-tagged : (many (Adt) a) -> (many (Bool) t))
  (match many a _ ((MkAdt _ tg _ _ _) tg)))

(def-fns _ $ (many adt-ext : (many (Adt) a) -> (many (Maybe $ ExtType) e))
  (match many a _ ((MkAdt _ _ _ ext _) ext)))

(def-fns _ $ (many adt-ctors : (many (Adt) a) -> (many (List $ Ctor) cs))
  (match many a _ ((MkAdt _ _ cs _ _) cs)))

(def-fns _ $ (many adt-name : (many (Adt) a) -> (many (String) s))
  (match many a _ ((MkAdt n _ _ _ _) n)))

(def-fns _
  ((many recast : (erased (List $ List $ Nat) ctx) (many (List $ Mult) ns) (many (List $ Mult) ms) (erased (ManySame ms ns) same) (subterm many (Code ctx ms) c) -> (many (Code ctx ns) r))
    (let-match many c (CMatch _ _ scrut shape branches dfl live)
      ((CVar _ x p) (CValues _ ns (Cons _ (CVar _ x p) $ Nil _) $ picked-same _ _ _ _ same $ PkMany _ (Nil _) (CVar _ x p) (Nil _) $ PkNil _))
      ((CConst _ x) (CValues _ ns (Cons _ (CConst _ x) $ Nil _) $ picked-same _ _ _ _ same $ PkMany _ (Nil _) (CConst _ x) (Nil _) $ PkNil _))
      ((CValue _ v) (CValues _ ns (Cons _ (CValue _ v) $ Nil _) $ picked-same _ _ _ _ same $ PkMany _ (Nil _) (CValue _ v) (Nil _) $ PkNil _))
      ((CErased _ _) (CErased _ ns))
      ((CValues _ _ cs pk) (CValues _ ns cs $ picked-same _ _ _ _ same pk))
      ((CApp _ _ f args cc) (CApp _ ns f args cc))
      ((CLet _ ms2 _ ids pk rhs rest) (CLet _ ms2 _ ids pk rhs $ notail $ recast _ ns ms same rest))
      ((CLetRec _ _ _ g rest) (CLetRec _ _ _ g $ notail $ recast _ ns ms same rest))
      ((CCellAlloc _ _ _) (CValues _ ns (Cons _ c $ Nil _) $ picked-same _ _ _ _ same $ PkMany _ (Nil _) c (Nil _) $ PkNil _))
      ((CCellWrite _ _ _ _) (CValues _ ns (Cons _ c $ Nil _) $ picked-same _ _ _ _ same $ PkMany _ (Nil _) c (Nil _) $ PkNil _))
      ((CCellRead _ _ _ _) (CValues _ ns (Cons _ c $ Nil _) $ picked-same _ _ _ _ same $ PkMany _ (Nil _) c (Nil _) $ PkNil _))
      ((CAbsurd _ _) (CAbsurd _ ns))
      ((CError _ _ m) (CError _ ns m)))
    (CMatch _ ns scrut shape (notail $ recast-branches _ ns ms same branches)
      (match many dfl (((Maybe $ Code (Cons (List (Nat)) (Nil (Nat)) ctx) ns) _)) ((Some _ d) (Some _ $ notail $ recast _ ns ms same d)) ((None _) (None _))) live))
  ((many recast-branches : (erased (List $ List $ Nat) ctx) (many (List $ Mult) ns) (many (List $ Mult) ms) (erased (ManySame ms ns) same) (subterm many (List $ Branch ctx ms) bs) -> (many (List $ Branch ctx ns) r))
    (match many bs _
      ((Nil _) (Nil _))
      ((Cons _ b rest) (match many b _ ((MkBranch _ _ d ids body) (Cons _ (MkBranch _ _ d ids $ notail $ recast _ ns ms same body) $ notail $ recast-branches _ ns ms same rest)))))))

(def-fns _ $ (many func-params : (erased (List $ Nat) gids) (erased (List $ List $ Nat) ctx) (many (Func gids ctx) f) -> (many (List $ Nat) ps))
  (match many f _ ((MkFunc _ _ _ _ _ ps _ _ _) ps) ((MkAlias _ _ _ _ _) (Nil _))))

(def-fns _ $ (many func-name : (erased (List $ Nat) gids) (erased (List $ List $ Nat) ctx) (many (Func gids ctx) f) -> (many (String) b))
  (match many f _ ((MkFunc _ _ _ n _ _ _ _ _) n) ((MkAlias _ _ n _ _) n)))

(def-fns _ $ (many func-id : (erased (List $ Nat) gids) (erased (List $ List $ Nat) ctx) (many (Func gids ctx) f) -> (many (Nat) b))
  (match many f _ ((MkFunc _ _ _ _ id _ _ _ _) id) ((MkAlias _ _ _ id _) id)))

(def-fns _ $ (many func-impl : (erased (List $ Nat) gids) (erased (List $ List $ Nat) ctx) (many (Func gids ctx) f) -> (many (Maybe $ Impl) b))
  (match many f _ ((MkFunc _ _ _ _ _ _ _ impl _) impl) ((MkAlias _ _ _ _ _) (None _))))

(def-fns _ $ (many func-top : (erased (List $ Nat) gids) (erased (List $ List $ Nat) ctx) (many (Func gids ctx) f) -> (many (Bool) b))
  (match many f _ ((MkFunc _ _ _ _ _ _ _ _ top) top) ((MkAlias _ _ _ _ _) (BFalse))))

; ---- Decidable equality on ids, with inequality as the order either way so a refuted branch stays refutable.

(def-adts
  ((Neq : ((Nat) a) ((Nat) b) -> Type)
    enum
    (many NeqLt : (erased (Nat) a) (erased (Nat) b) (erased (Lt a b) p) -> (Neq a b))
    (many NeqGt : (erased (Nat) a) (erased (Nat) b) (erased (Lt b a) p) -> (Neq a b)))
  ((NatDec : ((Nat) a) ((Nat) b) -> Type)
    enum
    (many BYes : (erased (Nat) a) (erased (Nat) b) (erased (Eq (Nat) a b) p) -> (NatDec a b))
    (many BNo : (erased (Nat) a) (erased (Nat) b) (erased (Neq a b) p) -> (NatDec a b))))

(def-fns _ $ (erased absurd le-lt-absurd : (erased (Nat) a) (erased (Nat) b) (erased (Lt a (Succ b)) p) (erased (Lt b a) q) -> (erased (False) f))
  (lt-asym b a q p))

(def-fns _ $ (erased absurd neq-irrefl : (erased (Nat) a) (erased (Neq a a) p) -> (erased (False) f))
  (match erased p _
    (absurd (NeqLt _ _ q) (lt-irrefl a q))
    (absurd (NeqGt _ _ q) (lt-irrefl a q))))

(def-fns _ $ (erased neq-sym : (erased (Nat) a) (erased (Nat) b) (erased (Neq a b) p) -> (erased (Neq b a) q))
  (match erased p _ ((NeqLt _ _ q) (NeqGt _ _ q)) ((NeqGt _ _ q) (NeqLt _ _ q))))

(def-fns _ $ (erased neq-pred : (erased (Nat) a) (erased (Nat) b) (erased (Neq (Succ a) (Succ b)) p) -> (erased (Neq a b) q))
  (match erased p _
    ((NeqLt _ _ q)
      (let-match erased q (LtS x2 y2 q2))
      (NeqLt _ _ q2))
    ((NeqGt _ _ q)
      (let-match erased q (LtS x2 y2 q2))
      (NeqGt _ _ q2))))

(def-fns _ $ (erased neq-half : (erased (Nat) a) (erased (Nat) da) (erased (Nat) b) (erased (Nat) db) (erased (Double a da) dda) (erased (Double b db) ddb) (erased (Neq da db) p) -> (erased (Neq a b) q))
  (match erased p _
    ((NeqLt _ _ q) (NeqLt _ _ $ double-lt-inv a da b db dda ddb q))
    ((NeqGt _ _ q) (NeqGt _ _ $ double-lt-inv b db a da ddb dda q))))

(def-fns _ $ (many nat-eq-dec : (many (Nat) a) (many (Nat) b) -> (many (NatDec a b) r))
  (match many (nat-cmp a b) _
    ((CLt _ _ _ _ p) (BNo _ _ $ NeqLt _ _ p))
    ((CEq _ _ _) (BYes _ _ $ Refl _ a))
    ((CGt _ _ _ _ q) (BNo _ _ $ NeqGt _ _ q))))

; ---- The rules list: membership, appending at the end as a relation, and membership through a path context.

(def-adts
  ((Rule : -> Type)
    enum
    (many MkRule : (many (Nat) x) (many (Term) t) -> (Rule)))
  ((MemRule : ((Nat) x) ((Term) t) ((List $ Rule) rules) -> Type)
    enum
    (many MRHere : (erased (Nat) x) (erased (Term) t) (erased (List $ Rule) rest) -> (MemRule x t $ Cons (Rule) (MkRule x t) rest))
    (many MRThere : (erased (Nat) x) (erased (Term) t) (erased (Rule) r) (erased (List $ Rule) rest) (erased (MemRule x t rest) m) -> (MemRule x t $ Cons (Rule) r rest)))
  ((AppendR : ((List $ Rule) rules) ((Rule) r) ((List $ Rule) res) -> Type)
    enum
    (many ApNil : (erased (Rule) r) -> (AppendR (Nil $ Rule) r $ Cons (Rule) r $ Nil $ Rule))
    (many ApCons : (erased (Rule) a) (erased (List $ Rule) rest) (erased (Rule) r) (erased (List $ Rule) res) (erased (AppendR rest r res) p) -> (AppendR (Cons (Rule) a rest) r $ Cons (Rule) a res)))
  ((MemRuleW : ((List $ Digit) ctx) ((Nat) inner) ((Term) t) ((List $ Rule) rules) -> Type)
    enum
    (many MWNil : (erased (Nat) x) (erased (Term) t) (erased (List $ Rule) rules) (erased (MemRule x t rules) m) -> (MemRuleW (Nil $ Digit) x t rules))
    (many MW1 : (erased (List $ Digit) ctx) (erased (Nat) x) (erased (Nat) d) (erased (Double x d) dd) (erased (Term) t) (erased (List $ Rule) rules) (erased (MemRuleW ctx (Succ d) t rules) m) -> (MemRuleW (Cons (Digit) (D1) ctx) x t rules))
    (many MW2 : (erased (List $ Digit) ctx) (erased (Nat) x) (erased (Nat) d) (erased (Double x d) dd) (erased (Term) t) (erased (List $ Rule) rules) (erased (MemRuleW ctx (Succ (Succ d)) t rules) m) -> (MemRuleW (Cons (Digit) (D2) ctx) x t rules))))

(def-fns _ $ (erased append-rule : (subterm erased (List $ Rule) rules) (erased (Rule) r) -> (erased (List $ Rule) res) (erased (AppendR rules r res) p))
  (let-match erased rules (Cons _ x rest) ((Nil _) (values (Cons _ r $ Nil _) $ ApNil _)))
  (let ((erased res) (erased p)) $ append-rule rest r)
  (values (Cons _ x res) $ ApCons _ _ _ _ p))

(def-fns _ $ (erased mem-append : (erased (Nat) x) (erased (Term) t) (erased (List $ Rule) rules) (erased (Rule) r) (erased (List $ Rule) res) (subterm erased (MemRule x t rules) m) (erased (AppendR rules r res) ap) -> (erased (MemRule x t res) m2))
  (match erased m _
    ((MRHere _ _ _)
      (let-match erased ap (ApCons a rest2 r2 res2 ap2))
      (MRHere _ _ _))
    ((MRThere _ _ _ _ m1)
      (let-match erased ap (ApCons a rest2 r2 res2 ap2))
      (MRThere _ _ _ _ $ mem-append x t rest2 r res2 m1 ap2))))

(def-fns _ $ (erased mem-last : (erased (Nat) x) (erased (Term) t) (erased (List $ Rule) rules) (erased (List $ Rule) res) (subterm erased (AppendR rules (MkRule x t) res) ap) -> (erased (MemRule x t res) m))
  (match erased ap _
    ((ApNil _) (MRHere _ _ _))
    ((ApCons _ rest _ res2 ap2) (MRThere _ _ _ _ $ mem-last x t rest res2 ap2))))

(def-fns _ $ (erased wrap-mw : (erased (List $ Digit) ctx) (erased (Nat) a) (erased (Nat) x) (subterm erased (Wrap ctx a x) w) (erased (Term) t) (erased (List $ Rule) rules) (erased (MemRule x t rules) m) -> (erased (MemRuleW ctx a t rules) r))
  (match erased w _
    ((WNil _) (MWNil _ _ _ m))
    ((W1 ctx1 _ d1 dd1 _ q) (MW1 _ _ _ dd1 _ _ $ wrap-mw ctx1 (Succ d1) x q t rules m))
    ((W2 ctx1 _ d1 dd1 _ q) (MW2 _ _ _ dd1 _ _ $ wrap-mw ctx1 (Succ (Succ d1)) x q t rules m))))

(def-fns _ $ (erased mw-unwrap : (erased (List $ Digit) ctx) (erased (Nat) a) (erased (Nat) x) (subterm erased (Wrap ctx a x) w) (erased (Term) t) (erased (List $ Rule) rules) (erased (MemRuleW ctx a t rules) m) -> (erased (MemRule x t rules) r))
  (match erased w _
    ((WNil _)
      (let-match erased m (MWNil a1 t1 r1 m1))
      m1)
    ((W1 _ _ d1 dd1 _ q)
      (let-match erased m (MW1 c2 a2 d2 dd2 t2 r2 m1))
      (match erased (double-fn a d1 d2 dd1 dd2) _ ((Refl _ _) (mw-unwrap _ _ _ q _ _ m1))))
    ((W2 _ _ d1 dd1 _ q)
      (let-match erased m (MW2 c2 a2 d2 dd2 t2 r2 m1))
      (match erased (double-fn a d1 d2 dd1 dd2) _ ((Refl _ _) (mw-unwrap _ _ _ q _ _ m1))))))

(def-fns _ $ (erased mw-append : (erased (List $ Digit) ctx) (erased (Nat) a) (erased (Term) t) (erased (List $ Rule) rules) (subterm erased (MemRuleW ctx a t rules) m) (erased (Rule) r) (erased (List $ Rule) res) (erased (AppendR rules r res) ap) -> (erased (MemRuleW ctx a t res) m2))
  (match erased m _
    ((MWNil _ _ _ m1) (MWNil _ _ _ $ mem-append a t rules r res m1 ap))
    ((MW1 c1 _ d1 dd1 _ _ m1) (MW1 _ _ _ dd1 _ _ $ mw-append c1 (Succ d1) t rules m1 r res ap))
    ((MW2 c1 _ d1 dd1 _ _ m1) (MW2 _ _ _ dd1 _ _ $ mw-append c1 (Succ (Succ d1)) t rules m1 r res ap))))
; ---- The fact table, indexed by its number of rule-free entries (ASSUMPTIONS 94). Sums are relations,
; since a type may not call a function; [In] is the path to a rule-free entry, and ruling one out returns
; the table at the predecessor count, which is what unification's measure steps down on.

(def-adts
  ((Plus3 : ((Nat) h) ((Nat) a) ((Nat) b) ((Nat) c) -> Type)
    enum
    (many P3Z : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Add a b c) p) -> (Plus3 (Zero) a b c))
    (many P3S : (erased (Nat) h) (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Plus3 h a b c) p) -> (Plus3 (Succ h) a b $ Succ c)))
  ((Pred : ((Nat) a) ((Nat) b) ((Nat) c) -> Type)
    enum
    (many MkPred : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Add a b c) q) -> (Pred a b $ Succ c)))
  ((Pred3 : ((Nat) h) ((Nat) a) ((Nat) b) ((Nat) c) -> Type)
    enum
    (many MkPred3 : (erased (Nat) h) (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Plus3 h a b c) q) -> (Pred3 h a b $ Succ c))))

(def-fns _ $ (erased plus-right : (subterm erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Add a (Succ b) c) p) -> (erased (Pred a b c) r))
  (let-match erased p (AddSucc a1 _ _ q) ((AddZero _) (MkPred _ _ _ $ AddZero b)))
  (match erased (plus-right _ _ _ q) _
    ((MkPred _ _ c2 q2) (MkPred _ _ _ $ AddSucc a1 b c2 q2))))

(def-fns _ $ (erased plus3-mid-succ : (subterm erased (Nat) h) (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Plus3 h a b c) p) -> (erased (Plus3 h (Succ a) b $ Succ c) r))
  (match erased p _
    ((P3Z _ _ _ q) (P3Z _ _ _ $ AddSucc a b c q))
    ((P3S h1 _ _ c1 q) (P3S _ _ _ _ $ plus3-mid-succ h1 a b c1 q))))

(def-fns _ $ (erased plus3-right-succ : (subterm erased (Nat) h) (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Plus3 h a b c) p) -> (erased (Plus3 h a (Succ b) $ Succ c) r))
  (match erased p _
    ((P3Z _ _ _ q) (P3Z _ _ _ $ add-succ-right a b c q))
    ((P3S h1 _ _ c1 q) (P3S _ _ _ _ $ plus3-right-succ h1 a b c1 q))))

(def-fns _ $ (erased plus3-mid : (subterm erased (Nat) h) (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Plus3 h (Succ a) b c) p) -> (erased (Pred3 h a b c) r))
  (match erased p _
    ((P3Z _ _ _ q)
      (let-match erased q (AddSucc a2 b2 c2 q2))
      (MkPred3 _ _ _ _ $ P3Z a b c2 q2))
    ((P3S h1 _ _ _ q)
      (match erased (plus3-mid _ _ _ _ q) _
        ((MkPred3 _ _ _ c2 q2) (MkPred3 _ _ _ _ $ P3S h1 a b c2 q2))))))

(def-fns _ $ (erased plus3-right : (subterm erased (Nat) h) (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Plus3 h a (Succ b) c) p) -> (erased (Pred3 h a b c) r))
  (match erased p _
    ((P3Z _ _ _ q)
      (match erased (plus-right _ _ _ q) _
        ((MkPred _ _ c2 q2) (MkPred3 _ _ _ _ $ P3Z a b c2 q2))))
    ((P3S h1 _ _ _ q)
      (match erased (plus3-right _ _ _ _ q) _
        ((MkPred3 _ _ _ c2 q2) (MkPred3 _ _ _ _ $ P3S h1 a b c2 q2))))))

(def-adts
  ((Here : ((Nat) h) -> Type)
    enum
    (many HNone : -> (Here $ Zero))
    (many HRuled : (many (Term) ty) (many (Term) t) -> (Here $ Zero))
    (many HFree : (many (Term) ty) -> (Here $ Succ $ Zero)))
  ((Facts : ((Nat) n) -> Type)
    enum
    (many FEmpty : -> (Facts $ Zero))
    (many FNode : (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (many (Here h) here) (many (Facts n1) one) (many (Facts n2) two) (erased (Plus3 h n1 n2 m) p) -> (Facts m)))
  ((In : ((Nat) x) ((Nat) n) ((Facts n) f) -> Type)
    enum
    (many InHere : (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Term) ty) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 (Succ $ Zero) n1 n2 m) p)
       -> (In (Zero) m $ FNode (Succ $ Zero) n1 n2 m (HFree ty) one two p))
    (many In1 : (erased (Nat) x) (erased (Nat) d) (erased (Double x d) dd) (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Here h) here) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 h n1 n2 m) p) (erased (In x n1 one) q)
       -> (In (Succ d) m $ FNode h n1 n2 m here one two p))
    (many In2 : (erased (Nat) x) (erased (Nat) d) (erased (Double x d) dd) (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Here h) here) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 h n1 n2 m) p) (erased (In x n2 two) q)
       -> (In (Succ (Succ d)) m $ FNode h n1 n2 m here one two p)))
  ((RuledIn : ((Nat) x) ((Nat) n) ((Facts n) f) -> Type)
    enum
    (many RHere : (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Term) ty) (erased (Term) t) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 (Zero) n1 n2 m) p)
       -> (RuledIn (Zero) m $ FNode (Zero) n1 n2 m (HRuled ty t) one two p))
    (many R1 : (erased (Nat) x) (erased (Nat) d) (erased (Double x d) dd) (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Here h) here) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 h n1 n2 m) p) (erased (RuledIn x n1 one) q)
       -> (RuledIn (Succ d) m $ FNode h n1 n2 m here one two p))
    (many R2 : (erased (Nat) x) (erased (Nat) d) (erased (Double x d) dd) (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Here h) here) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 h n1 n2 m) p) (erased (RuledIn x n2 two) q)
       -> (RuledIn (Succ (Succ d)) m $ FNode h n1 n2 m here one two p)))
  ((Ins : ((Nat) x) ((Nat) n) ((Facts n) f) ((Nat) n2) ((Facts n2) f2) -> Type)
    enum
    (many InsLeaf : (erased (Term) ty) (erased (Plus3 (Succ $ Zero) (Zero) (Zero) $ Succ $ Zero) p)
       -> (Ins (Zero) (Zero) (FEmpty) (Succ $ Zero) $ FNode (Succ $ Zero) (Zero) (Zero) (Succ $ Zero) (HFree ty) (FEmpty) (FEmpty) p))
    (many InsGrow1 : (erased (Nat) x) (erased (Nat) d) (erased (Double x d) dd) (erased (Facts $ Succ $ Zero) one) (erased (Ins x (Zero) (FEmpty) (Succ $ Zero) one) q) (erased (Add (Succ $ Zero) (Zero) $ Succ $ Zero) p)
       -> (Ins (Succ d) (Zero) (FEmpty) (Succ $ Zero) $ FNode (Zero) (Succ $ Zero) (Zero) (Succ $ Zero) (HNone) one (FEmpty) $ P3Z (Succ $ Zero) (Zero) (Succ $ Zero) p))
    (many InsGrow2 : (erased (Nat) x) (erased (Nat) d) (erased (Double x d) dd) (erased (Facts $ Succ $ Zero) two) (erased (Ins x (Zero) (FEmpty) (Succ $ Zero) two) q) (erased (Add (Zero) (Succ $ Zero) $ Succ $ Zero) p)
       -> (Ins (Succ (Succ d)) (Zero) (FEmpty) (Succ $ Zero) $ FNode (Zero) (Zero) (Succ $ Zero) (Succ $ Zero) (HNone) (FEmpty) two $ P3Z (Zero) (Succ $ Zero) (Succ $ Zero) p))
    (many InsHere : (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Term) ty) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 (Zero) n1 n2 m) p)
       -> (Ins (Zero) m (FNode (Zero) n1 n2 m (HNone) one two p) (Succ m) $ FNode (Succ $ Zero) n1 n2 (Succ m) (HFree ty) one two $ P3S (Zero) n1 n2 m p))
    (many Ins1 : (erased (Nat) x) (erased (Nat) d) (erased (Double x d) dd) (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Here h) here) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 h n1 n2 m) p)
       (erased (Nat) k1) (erased (Nat) m2) (erased (Facts k1) one2) (erased (Plus3 h k1 n2 m2) p2) (erased (Ins x n1 one k1 one2) q)
       -> (Ins (Succ d) m (FNode h n1 n2 m here one two p) m2 $ FNode h k1 n2 m2 here one2 two p2))
    (many Ins2 : (erased (Nat) x) (erased (Nat) d) (erased (Double x d) dd) (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Here h) here) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 h n1 n2 m) p)
       (erased (Nat) k2) (erased (Nat) m2) (erased (Facts k2) two2) (erased (Plus3 h n1 k2 m2) p2) (erased (Ins x n2 two k2 two2) q)
       -> (Ins (Succ (Succ d)) m (FNode h n1 n2 m here one two p) m2 $ FNode h n1 k2 m2 here one two2 p2)))
  ((Out : ((Nat) x) ((Term) t) ((Nat) n) ((Facts n) f) ((Nat) k) ((Facts k) f2) -> Type)
    enum
    (many OutHere : (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Term) ty) (erased (Term) t) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 (Zero) n1 n2 m) p)
       -> (Out (Zero) t (Succ m) (FNode (Succ $ Zero) n1 n2 (Succ m) (HFree ty) one two $ P3S (Zero) n1 n2 m p) m $ FNode (Zero) n1 n2 m (HRuled ty t) one two p))
    (many Out1 : (erased (Nat) x) (erased (Nat) d) (erased (Double x d) dd) (erased (Term) t) (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Here h) here) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 h n1 n2 m) p)
       (erased (Nat) k1) (erased (Nat) m2) (erased (Facts k1) one2) (erased (Plus3 h k1 n2 m2) p2) (erased (Out x t n1 one k1 one2) q)
       -> (Out (Succ d) t m (FNode h n1 n2 m here one two p) m2 $ FNode h k1 n2 m2 here one2 two p2))
    (many Out2 : (erased (Nat) x) (erased (Nat) d) (erased (Double x d) dd) (erased (Term) t) (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Here h) here) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 h n1 n2 m) p)
       (erased (Nat) k2) (erased (Nat) m2) (erased (Facts k2) two2) (erased (Plus3 h n1 k2 m2) p2) (erased (Out x t n2 two k2 two2) q)
       -> (Out (Succ (Succ d)) t m (FNode h n1 n2 m here one two p) m2 $ FNode h n1 k2 m2 here one two2 p2)))
  ((Taken : ((Nat) x) ((Nat) n) ((Facts n) f) -> Type)
    enum
    (many TFree : (erased (Nat) x) (erased (Nat) n) (erased (Facts n) f) (erased (In x n f) p) -> (Taken x n f))
    (many TRuled : (erased (Nat) x) (erased (Nat) n) (erased (Facts n) f) (erased (RuledIn x n f) p) -> (Taken x n f)))
  ((Inserted : ((Nat) x) ((Nat) n) ((Facts n) f) -> Type)
    enum
    (many IKept : (erased (Nat) x) (erased (Nat) n) (erased (Facts n) f) (erased (Taken x n f) q) -> (Inserted x n f))
    (many IGrew : (erased (Nat) x) (erased (Nat) n) (erased (Facts n) f) (many (Facts $ Succ n) f2) (erased (Ins x n f (Succ n) f2) r) (erased (In x (Succ n) f2) q) -> (Inserted x n f)))
  ((Removed : ((Nat) x) ((Term) t) ((Nat) n) ((Facts n) f) -> Type)
    enum
    (many MkRemoved : (erased (Nat) x) (erased (Term) t) (erased (Nat) k) (erased (Facts $ Succ k) f) (many (Facts k) f2) (erased (Out x t (Succ k) f k f2) r) -> (Removed x t (Succ k) f))))

; Agreement between the table and the rules list, one direction each: every ruled entry's rule is in the
; list, at the key its path spells; every key of the list is a ruled entry.
(def-adts
  ((C1Here : ((List $ Digit) ctx) ((Nat) h) ((Here h) here) ((List $ Rule) rules) -> Type)
    enum
    (many C1None : (erased (List $ Digit) ctx) (erased (List $ Rule) rules) -> (C1Here ctx (Zero) (HNone) rules))
    (many C1Free : (erased (List $ Digit) ctx) (erased (Term) ty) (erased (List $ Rule) rules) -> (C1Here ctx (Succ $ Zero) (HFree ty) rules))
    (many C1Ruled : (erased (List $ Digit) ctx) (erased (Term) ty) (erased (Term) t) (erased (List $ Rule) rules) (erased (MemRuleW ctx (Zero) t rules) m) -> (C1Here ctx (Zero) (HRuled ty t) rules)))
  ((C1 : ((List $ Digit) ctx) ((Nat) n) ((Facts n) f) ((List $ Rule) rules) -> Type)
    enum
    (many C1Empty : (erased (List $ Digit) ctx) (erased (List $ Rule) rules) -> (C1 ctx (Zero) (FEmpty) rules))
    (many C1Node : (erased (List $ Digit) ctx) (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Here h) here) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 h n1 n2 m) p) (erased (List $ Rule) rules)
       (erased (C1Here ctx h here rules) ch) (erased (C1 (Cons (Digit) (D1) ctx) n1 one rules) c1) (erased (C1 (Cons (Digit) (D2) ctx) n2 two rules) c2)
       -> (C1 ctx m (FNode h n1 n2 m here one two p) rules)))
  ((AllRuled : ((List $ Nat) ks) ((Nat) n) ((Facts n) f) -> Type)
    enum
    (many ARNil : (erased (Nat) n) (erased (Facts n) f) -> (AllRuled (Nil $ Nat) n f))
    (many ARCons : (erased (Nat) z) (erased (List $ Nat) ks) (erased (Nat) n) (erased (Facts n) f) (erased (RuledIn z n f) r) (erased (AllRuled ks n f) rest) -> (AllRuled (Cons (Nat) z ks) n f)))
  ((Keys : ((List $ Nat) seen) ((List $ Rule) rules) ((List $ Nat) ks) -> Type)
    enum
    (many KNil : (erased (List $ Nat) seen) -> (Keys seen (Nil $ Rule) seen))
    (many KCons : (erased (List $ Nat) seen) (erased (Nat) x) (erased (Term) t) (erased (List $ Rule) rest) (erased (List $ Nat) ks) (erased (Keys (Cons (Nat) x seen) rest ks) k) -> (Keys seen (Cons (Rule) (MkRule x t) rest) ks)))
  ((Looked : ((Nat) x) ((Nat) n) ((Facts n) f) ((Nat) xg) ((List $ Rule) rules) -> Type)
    enum
    (many LNone : (erased (Nat) x) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) xg) (erased (List $ Rule) rules) -> (Looked x n f xg rules))
    (many LRuled : (erased (Nat) x) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) xg) (erased (List $ Rule) rules) (many (Term) ty) (many (Term) t) (erased (MemRule xg t rules) m) -> (Looked x n f xg rules))
    (many LFree : (erased (Nat) x) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) xg) (erased (List $ Rule) rules) (many (Term) ty) (erased (In x n f) p) -> (Looked x n f xg rules))))

(def-fns _ $ (erased absurd in-empty : (erased (Nat) x) (erased (In x (Zero) $ FEmpty) p) -> (erased (False) f))
  p)


(def-fns _ $ (erased absurd in-ruled-clash : (erased (Nat) x) (erased (Nat) n) (erased (Facts n) f) (subterm erased (In x n f) p) (erased (RuledIn x n f) q) -> (erased (False) r))
  (match erased p _
    (absurd (InHere _ _ _ _ _ _ _) q)
    (absurd (In1 x1 d1 dd1 _ _ _ _ _ _ _ _ q1)
      (match erased q _
        (absurd (R1 x2 _ dd2 _ _ _ _ _ _ _ _ q2)
          (let-match erased (double-inj x1 x2 d1 dd1 dd2) (Refl _ _))
          (in-ruled-clash _ _ _ q1 q2))
        (absurd (R2 x2 d2 dd2 _ _ _ _ _ _ _ _ _) (double-parity x1 x2 d2 dd1 dd2))))
    (absurd (In2 x1 d1 dd1 _ _ _ _ _ _ _ _ q1)
      (match erased q _
        (absurd (R1 x2 _ dd2 _ _ _ _ _ _ _ _ _) (double-parity x2 x1 d1 dd2 dd1))
        (absurd (R2 x2 _ dd2 _ _ _ _ _ _ _ _ q2)
          (let-match erased (double-inj x1 x2 d1 dd1 dd2) (Refl _ _))
          (in-ruled-clash _ _ _ q1 q2))))))

; Every key of a table is at most c: at each node, the key its path spells is, when the node holds an
; entry, and so on in both subtrees.
(def-adts
  ((AboveHere : ((List $ Digit) ctx) ((Nat) c) ((Nat) h) ((Here h) here) -> Type)
    enum
    (many AHNone : (erased (List $ Digit) ctx) (erased (Nat) c) -> (AboveHere ctx c (Zero) $ HNone))
    (many AHKey : (erased (List $ Digit) ctx) (erased (Nat) c) (erased (Nat) h) (erased (Here h) here) (erased (Nat) y) (erased (Wrap ctx (Zero) y) w) (erased (Lt y (Succ c)) le) -> (AboveHere ctx c h here)))
  ((Above : ((List $ Digit) ctx) ((Nat) c) ((Nat) n) ((Facts n) f) -> Type)
    enum
    (many AbEmpty : (erased (List $ Digit) ctx) (erased (Nat) c) -> (Above ctx c (Zero) $ FEmpty))
    (many AbNode : (erased (List $ Digit) ctx) (erased (Nat) c) (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Here h) here) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 h n1 n2 m) p)
       (erased (AboveHere ctx c h here) ah) (erased (Above (Cons (Digit) (D1) ctx) c n1 one) a1) (erased (Above (Cons (Digit) (D2) ctx) c n2 two) a2) -> (Above ctx c m $ FNode h n1 n2 m here one two p))))

(def-fns _ $ (erased above-in : (erased (List $ Digit) ctx) (erased (Nat) c) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) x) (erased (Nat) y) (erased (Above ctx c n f) ab) (subterm erased (In x n f) p) (erased (Wrap ctx x y) w) -> (erased (Lt y (Succ c)) le))
  (match erased p _
    ((InHere _ _ _ _ _ _ _)
      (let-match erased ab (AbNode c2 c3 h4 n5 n6 m7 here8 one9 two10 p11 ah a1 a2))
      (let-match erased ah (AHKey c4 c5 h6 here7 y2 w2 le2))
      (match erased (wrap-fn _ _ _ _ w2 w) _ ((Refl _ _) le2)))
    ((In1 x1 d1 dd1 _ _ _ _ _ _ _ _ q)
      (let-match erased ab (AbNode c2 c3 h4 n5 n6 m7 here8 one9 two10 p11 ah a1 a2))
      (above-in _ _ _ _ _ _ a1 q $ W1 ctx x1 d1 dd1 y w))
    ((In2 x1 d1 dd1 _ _ _ _ _ _ _ _ q)
      (let-match erased ab (AbNode c2 c3 h4 n5 n6 m7 here8 one9 two10 p11 ah a1 a2))
      (above-in _ _ _ _ _ _ a2 q $ W2 ctx x1 d1 dd1 y w))))

(def-fns _ $ (erased above-ruledin : (erased (List $ Digit) ctx) (erased (Nat) c) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) x) (erased (Nat) y) (erased (Above ctx c n f) ab) (subterm erased (RuledIn x n f) p) (erased (Wrap ctx x y) w) -> (erased (Lt y (Succ c)) le))
  (match erased p _
    ((RHere _ _ _ _ _ _ _ _)
      (let-match erased ab (AbNode c2 c3 h4 n5 n6 m7 here8 one9 two10 p11 ah a1 a2))
      (let-match erased ah (AHKey c4 c5 h6 here7 y2 w2 le2))
      (match erased (wrap-fn _ _ _ _ w2 w) _ ((Refl _ _) le2)))
    ((R1 x1 d1 dd1 _ _ _ _ _ _ _ _ q)
      (let-match erased ab (AbNode c2 c3 h4 n5 n6 m7 here8 one9 two10 p11 ah a1 a2))
      (above-ruledin _ _ _ _ _ _ a1 q $ W1 ctx x1 d1 dd1 y w))
    ((R2 x1 d1 dd1 _ _ _ _ _ _ _ _ q)
      (let-match erased ab (AbNode c2 c3 h4 n5 n6 m7 here8 one9 two10 p11 ah a1 a2))
      (above-ruledin _ _ _ _ _ _ a2 q $ W2 ctx x1 d1 dd1 y w))))

(def-fns _ $ (erased above-taken : (erased (Nat) c) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) x) (erased (Above (Nil $ Digit) c n f) ab) (erased (Taken x n f) t) -> (erased (Lt x (Succ c)) le))
  (match erased t _
    ((TFree _ _ _ p) (above-in _ _ _ _ _ _ ab p $ WNil x))
    ((TRuled _ _ _ p) (above-ruledin _ _ _ _ _ _ ab p $ WNil x))))

(def-fns _ $ (erased above-ins : (erased (List $ Digit) ctx) (erased (Nat) c) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) n2) (erased (Facts n2) f2) (erased (Nat) x) (erased (Nat) y) (erased (Above ctx c n f) ab) (subterm erased (Ins x n f n2 f2) i) (erased (Wrap ctx x y) w) (erased (Lt y (Succ c)) le) -> (erased (Above ctx c n2 f2) ab2))
  (match erased i _
    ((InsLeaf _ _) (AbNode _ _ _ _ _ _ _ _ _ _ (AHKey ctx c (Succ _) (HFree _) y w le) (AbEmpty (Cons (Digit) _ _) c) $ AbEmpty (Cons (Digit) _ _) c))
    ((InsGrow1 x1 d1 dd1 one q _)
      (AbNode _ _ _ _ _ _ _ _ _ _ (AHNone ctx c)
        (above-ins (Cons (Digit) _ _) c (Zero) (FEmpty) (Succ _) one x1 y (AbEmpty (Cons (Digit) _ _) c) q (W1 ctx x1 d1 dd1 y w) le)
        $ AbEmpty (Cons (Digit) _ _) c))
    ((InsGrow2 x1 d1 dd1 two q _)
      (AbNode _ _ _ _ _ _ _ _ _ _ (AHNone ctx c)
        (AbEmpty (Cons (Digit) _ _) c)
        $ above-ins (Cons (Digit) _ _) c (Zero) (FEmpty) (Succ _) two x1 y (AbEmpty (Cons (Digit) _ _) c) q (W2 ctx x1 d1 dd1 y w) le))
    ((InsHere _ _ _ _ _ _ _)
      (let-match erased ab (AbNode c2 c3 h4 n5 n6 m7 here8 one9 two10 p11 ah a1 a2))
      (AbNode _ _ _ _ _ _ _ _ _ _ (AHKey ctx c (Succ _) (HFree _) y w le) a1 a2))
    ((Ins1 x1 d1 dd1 _ n1 _ _ _ one _ _ k1 _ one2 _ q)
      (let-match erased ab (AbNode c2 c3 h4 n5 n6 m7 here8 one9 two10 p11 ah a1 a2))
      (AbNode _ _ _ _ _ _ _ _ _ _ ah (above-ins (Cons (Digit) _ _) c n1 one k1 one2 x1 y a1 q (W1 ctx x1 d1 dd1 y w) le) a2))
    ((Ins2 x1 d1 dd1 _ _ n2b _ _ _ two _ k2 _ two2 _ q)
      (let-match erased ab (AbNode c2 c3 h4 n5 n6 m7 here8 one9 two10 p11 ah a1 a2))
      (AbNode _ _ _ _ _ _ _ _ _ _ ah a1 $ above-ins (Cons (Digit) _ _) c n2b two k2 two2 x1 y a2 q (W2 ctx x1 d1 dd1 y w) le))))

(def-fns _ $ (erased above-out : (erased (List $ Digit) ctx) (erased (Nat) c) (erased (Nat) x) (erased (Term) t) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) k) (erased (Facts k) f2) (erased (Above ctx c n f) ab) (subterm erased (Out x t n f k f2) o) -> (erased (Above ctx c k f2) ab2))
  (match erased o _
    ((OutHere _ _ _ _ _ _ _ _)
      (let-match erased ab (AbNode c2 c3 h4 n5 n6 m7 here8 one9 two10 p11 ah a1 a2))
      (let-match erased ah (AHKey c4 c5 h6 here7 y w le))
      (AbNode _ _ _ _ _ _ _ _ _ _ (AHKey ctx c (Zero) (HRuled _ _) y w le) a1 a2))
    ((Out1 x1 _ _ t1 _ n1 _ _ _ one _ _ k1 _ one2 _ q)
      (let-match erased ab (AbNode c2 c3 h4 n5 n6 m7 here8 one9 two10 p11 ah a1 a2))
      (AbNode _ _ _ _ _ _ _ _ _ _ ah (above-out (Cons (Digit) _ _) c x1 t1 n1 one k1 one2 a1 q) a2))
    ((Out2 x1 _ _ t1 _ _ n2 _ _ _ two _ k2 _ two2 _ q)
      (let-match erased ab (AbNode c2 c3 h4 n5 n6 m7 here8 one9 two10 p11 ah a1 a2))
      (AbNode _ _ _ _ _ _ _ _ _ _ ah a1 $ above-out (Cons (Digit) _ _) c x1 t1 n2 two k2 two2 a2 q))))

(def-fns _ $ (erased above-weaken : (erased (List $ Digit) ctx) (erased (Nat) c) (erased (Nat) c2) (erased (Nat) n) (erased (Facts n) f) (subterm erased (Above ctx c n f) ab) (erased (Lt c (Succ c2)) le) -> (erased (Above ctx c2 n f) ab2))
  (let-match erased ab (AbNode _ _ h n1 n2 _ here one two _ ah a1 a2) ((AbEmpty _ _) (AbEmpty _ _)))
  (AbNode _ _ _ _ _ _ _ _ _ _
    (match erased ah (((AboveHere ctx c2 h here) _)) ((AHNone _ _) (AHNone ctx c2)) ((AHKey _ _ _ _ y w le0) (AHKey ctx c2 h here y w $ le-trans y c c2 le0 le)))
    (above-weaken (Cons (Digit) _ _) c c2 n1 one a1 le)
    $ above-weaken (Cons (Digit) _ _) c c2 n2 two a2 le))

(def-fns _ $ (erased absurd taken-empty : (erased (Nat) x) (erased (Taken x (Zero) $ FEmpty) t) -> (erased (False) f))
  (match erased t _
    (absurd (TFree _ _ _ p) (in-empty _ p))
    (absurd (TRuled _ _ _ p) p)))

(def-fns _ $ (erased taken-1 : (erased (Nat) x) (erased (Nat) d) (erased (Double x d) dd) (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Here h) here) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 h n1 n2 m) p) (erased (Taken x n1 one) t) -> (erased (Taken (Succ d) m $ FNode h n1 n2 m here one two p) r))
  (match erased t _
    ((TFree _ _ _ q) (TFree _ _ _ $ In1 x d dd h n1 n2 m here one two p q))
    ((TRuled _ _ _ q) (TRuled _ _ _ $ R1 x d dd h n1 n2 m here one two p q))))

(def-fns _ $ (erased taken-2 : (erased (Nat) x) (erased (Nat) d) (erased (Double x d) dd) (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Here h) here) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 h n1 n2 m) p) (erased (Taken x n2 two) t) -> (erased (Taken (Succ (Succ d)) m $ FNode h n1 n2 m here one two p) r))
  (match erased t _
    ((TFree _ _ _ q) (TFree _ _ _ $ In2 x d dd h n1 n2 m here one two p q))
    ((TRuled _ _ _ q) (TRuled _ _ _ $ R2 x d dd h n1 n2 m here one two p q))))

(def-fns _ $ (many facts-lookup : (many (Nat) x) (erased (Nat) n) (subterm many (Facts n) f) (erased (List $ Digit) ctx) (erased (Nat) xg) (erased (Wrap ctx x xg) w) (erased (List $ Rule) rules) (erased (C1 ctx n f rules) c) -> (many (Looked x n f xg rules) r))
  (let-match many f (FNode h n1 n2 m here one two p3) ((FEmpty) (LNone _ _ _ _ _)))
  (match many (nat-halve x) _
    ((HZ)
      (let-match many here (HRuled ty t)
        ((HNone) (LNone _ _ _ _ _))
        ((HFree ty) (LFree _ _ _ _ _ ty $ InHere n1 n2 m ty one two p3)))
      (let ((erased (C1Here ctx h here rules) ch)) $ match erased c _ ((C1Node _ _ _ _ _ _ _ _ _ _ ch _ _) ch))
      (let ((erased (MemRuleW ctx (Zero) t rules) mw)) $ match erased ch _ ((C1Ruled _ _ _ _ mw) mw))
      (LRuled _ _ _ _ _ ty t $ mw-unwrap ctx (Zero) xg w t rules mw))
    ((H1 x1 d dd)
      (let ((erased (C1 (Cons _ (D1) ctx) n1 one rules) c1)) $ match erased c _ ((C1Node _ _ _ _ _ _ _ _ _ _ _ c1 _) c1))
      (let ((many r)) (tail $ facts-lookup x1 _ one _ _ (W1 ctx x1 d dd xg w) _ c1))
      (let ((erased r2) (erased cp)) $ match erased r (((Looked x n f xg rules) r2) ((Coercible (Shared) (Looked x1 n1 one xg rules) r (Shared) (Looked x n f xg rules) r2) cp))
        ((LNone _ _ _ _ _) (values (LNone _ _ _ _ _) (coercible-ctor (Shared) LNone x1 x n1 n one f xg xg rules rules)))
        ((LRuled _ _ _ _ _ ty t mr) (values (LRuled _ _ _ _ _ ty t mr) (coercible-ctor (Shared) LRuled x1 x n1 n one f xg xg rules rules (coercible-refl (Shared) ty) (coercible-refl (Shared) t) mr mr)))
        ((LFree _ _ _ _ _ ty q) (values (LFree _ _ _ _ _ ty $ In1 x1 d dd h n1 n2 m here one two p3 q) (coercible-ctor (Shared) LFree x1 x n1 n one f xg xg rules rules (coercible-refl (Shared) ty) q $ In1 x1 d dd h n1 n2 m here one two p3 q))))
      (coerce r cp))
    ((H2 x1 d dd)
      (let ((erased (C1 (Cons _ (D2) ctx) n2 two rules) c2)) $ match erased c _ ((C1Node _ _ _ _ _ _ _ _ _ _ _ _ c2) c2))
      (let ((many r)) (tail $ facts-lookup x1 _ two _ _ (W2 ctx x1 d dd xg w) _ c2))
      (let ((erased r2) (erased cp)) $ match erased r (((Looked x n f xg rules) r2) ((Coercible (Shared) (Looked x1 n2 two xg rules) r (Shared) (Looked x n f xg rules) r2) cp))
        ((LNone _ _ _ _ _) (values (LNone _ _ _ _ _) (coercible-ctor (Shared) LNone x1 x n2 n two f xg xg rules rules)))
        ((LRuled _ _ _ _ _ ty t mr) (values (LRuled _ _ _ _ _ ty t mr) (coercible-ctor (Shared) LRuled x1 x n2 n two f xg xg rules rules (coercible-refl (Shared) ty) (coercible-refl (Shared) t) mr mr)))
        ((LFree _ _ _ _ _ ty q) (values (LFree _ _ _ _ _ ty $ In2 x1 d dd h n1 n2 m here one two p3 q) (coercible-ctor (Shared) LFree x1 x n2 n two f xg xg rules rules (coercible-refl (Shared) ty) q $ In2 x1 d dd h n1 n2 m here one two p3 q))))
      (coerce r cp))))

; A new rule-free entry; an occupied position is left as it is.
(def-fns _ $ (many facts-insert : (subterm many (Nat) x) (erased (Nat) n) (many (Facts n) f) (many (Term) ty) -> (many (Inserted x n f) r))
  (match many f _
    ((FEmpty)
      (match many (nat-halve x) _
        ((HZ)
          (let ((erased p0)) $ P3S _ _ _ _ $ P3Z (Zero) (Zero) (Zero) $ AddZero $ Zero)
          (IGrew _ _ _ (FNode _ _ _ _ (HFree ty) (FEmpty) (FEmpty) _) (InsLeaf ty p0) $ InHere (Zero) (Zero) (Succ _) ty (FEmpty) (FEmpty) p0))
        ((H1 x1 d dd)
          (let-match many (notail $ facts-insert (subterm (lt-subterm x1 x $ double-lt x1 d dd)) x1 _ (FEmpty) ty) (IGrew _ _ _ one r q1)
            (absurd (IKept _ _ _ q) (taken-empty _ q)))
          (let ((erased p0)) $ add-zero-right $ Succ $ Zero)
          (IGrew _ _ _ (FNode _ _ _ _ (HNone) one (FEmpty) _) (InsGrow1 x1 d dd one r p0)
            $ In1 x1 d dd (Zero) (Succ _) (Zero) (Succ _) (HNone) one (FEmpty) (P3Z (Succ _) (Zero) (Succ _) p0) q1))
        ((H2 x1 d dd)
          (let-match many (notail $ facts-insert (subterm (lt-subterm x1 x $ lt-weaken x1 (Succ d) $ double-lt x1 d dd)) x1 _ (FEmpty) ty) (IGrew _ _ _ two r q1)
            (absurd (IKept _ _ _ q) (taken-empty _ q)))
          (let ((erased p0)) $ AddZero $ Succ $ Zero)
          (IGrew _ _ _ (FNode _ _ _ _ (HNone) (FEmpty) two _) (InsGrow2 x1 d dd two r p0)
            $ In2 x1 d dd (Zero) (Zero) (Succ _) (Succ _) (HNone) (FEmpty) two (P3Z (Zero) (Succ _) (Succ _) p0) q1))))
    ((FNode h n1 n2 m here one two p3)
      (match many (nat-halve x) _
        ((HZ)
          (match many here _
            ((HNone) (IGrew _ _ _ (FNode _ _ _ _ (HFree ty) one two _) (InsHere n1 n2 m ty one two p3) $ InHere n1 n2 (Succ _) ty one two $ P3S (Zero) n1 n2 m p3))
            ((HRuled ty0 t0) (IKept _ _ _ $ TRuled x n f $ RHere n1 n2 m ty0 t0 one two p3))
            ((HFree ty0) (IKept _ _ _ $ TFree x n f $ InHere n1 n2 m ty0 one two p3))))
        ((H1 x1 d dd)
          (let-match many (notail $ facts-insert (subterm (lt-subterm x1 x $ double-lt x1 d dd)) x1 _ one ty) (IGrew _ _ _ one2 r q1)
            ((IKept _ _ _ q) (IKept _ _ _ $ taken-1 x1 d dd h n1 n2 m here one two p3 q)))
          (let ((erased p4)) $ plus3-mid-succ _ _ _ _ p3)
          (IGrew _ _ _ (FNode _ _ _ _ here one2 two _) (Ins1 x1 d dd h n1 n2 m here one two p3 (Succ _) (Succ _) one2 p4 r) $ In1 x1 d dd h (Succ _) n2 (Succ _) here one2 two p4 q1))
        ((H2 x1 d dd)
          (let-match many (notail $ facts-insert (subterm (lt-subterm x1 x $ lt-weaken x1 (Succ d) $ double-lt x1 d dd)) x1 _ two ty) (IGrew _ _ _ two2 r q1)
            ((IKept _ _ _ q) (IKept _ _ _ $ taken-2 x1 d dd h n1 n2 m here one two p3 q)))
          (let ((erased p4)) $ plus3-right-succ _ _ _ _ p3)
          (IGrew _ _ _ (FNode _ _ _ _ here one two2 _) (Ins2 x1 d dd h n1 n2 m here one two p3 (Succ _) (Succ _) two2 p4 r) $ In2 x1 d dd h n1 (Succ _) (Succ _) here one two2 p4 q1))))))

; Rules a rule-free entry out, at the path its proof gives.
(def-fns _ $ (many facts-rule-out : (erased (Nat) n) (subterm many (Facts n) f) (many (Nat) x) (erased (In x n f) p) (many (Term) t) -> (many (Removed x t n f) r))
  (let-match many f (FNode h n1 n2 m here one two p3) (absurd FEmpty (in-empty _ p)))
  (match many (nat-halve x) _
    ((HZ)
      (let-match many here (HFree ty) (absurd HNone p) (absurd (HRuled _ _) p))
      (let-match erased p3 (P3S h1 a1 b1 c1 q))
      (MkRemoved _ _ _ _ (FNode _ _ _ _ (HRuled ty t) one two _) $ OutHere n1 n2 c1 ty t one two q))
    ((H1 x1 d dd)
      (let ((erased (In x1 n1 one) q)) $ match erased p _
        ((In1 x2 _ dd2 _ _ _ _ _ _ _ _ q0) (match erased (double-inj x2 x1 d dd2 dd) _ ((Refl _ _) q0)))
        (absurd (In2 x2 d2 dd2 _ _ _ _ _ _ _ _ _) (double-parity x1 x2 d2 dd dd2)))
      (let-match many (notail $ facts-rule-out _ one x1 q t) (MkRemoved _ _ k1 _ one2 r))
      (match erased (plus3-mid _ _ _ _ p3) _
        ((MkPred3 _ _ _ c2 q2) (MkRemoved _ _ _ _ (FNode _ _ _ _ here one2 two _) $ Out1 x1 d dd t h n1 n2 m here one two p3 k1 c2 one2 q2 r))))
    ((H2 x1 d dd)
      (let ((erased (In x1 n2 two) q)) $ match erased p _
        (absurd (In1 x2 _ dd2 _ _ _ _ _ _ _ _ _) (double-parity x2 x1 d dd2 dd))
        ((In2 x2 _ dd2 _ _ _ _ _ _ _ _ q0) (match erased (double-inj x2 x1 d dd2 dd) _ ((Refl _ _) q0))))
      (let-match many (notail $ facts-rule-out _ two x1 q t) (MkRemoved _ _ k2 _ two2 r))
      (match erased (plus3-right _ _ _ _ p3) _
        ((MkPred3 _ _ _ c2 q2) (MkRemoved _ _ _ _ (FNode _ _ _ _ here one two2 _) $ Out2 x1 d dd t h n1 n2 m here one two p3 k2 c2 two2 q2 r))))))

; ---- Transport of the agreement proofs through an insert, a rule-out and an append.

(def-fns _ $ (erased ruledin-ins : (erased (Nat) z) (erased (Nat) x) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) n2) (erased (Facts n2) f2) (subterm erased (Ins x n f n2 f2) i) (erased (RuledIn z n f) r) -> (erased (RuledIn z n2 f2) r2))
  (match erased i _
    (absurd (InsLeaf _ _) r)
    (absurd (InsGrow1 _ _ _ _ _ _) r)
    (absurd (InsGrow2 _ _ _ _ _ _) r)
    ((InsHere _ _ _ _ _ _ _)
      (match erased r _
        ((R1 _ _ ddz _ _ _ _ _ _ _ _ q1) (R1 _ _ ddz _ _ _ _ _ _ _ _ q1))
        ((R2 _ _ ddz _ _ _ _ _ _ _ _ q1) (R2 _ _ ddz _ _ _ _ _ _ _ _ q1))))
    ((Ins1 x1 _ _ _ n1 _ _ _ one _ _ k1 _ one2 _ q)
      (match erased r _
        ((RHere _ _ _ _ _ _ _ _) (RHere _ _ _ _ _ _ _ _))
        ((R1 z1 _ ddz _ _ _ _ _ _ _ _ q1) (R1 _ _ ddz _ _ _ _ _ _ _ _ $ ruledin-ins z1 x1 n1 one k1 one2 q q1))
        ((R2 _ _ ddz _ _ _ _ _ _ _ _ q1) (R2 _ _ ddz _ _ _ _ _ _ _ _ q1))))
    ((Ins2 x1 _ _ _ _ a2 _ _ _ two _ k2 _ two2 _ q)
      (match erased r _
        ((RHere _ _ _ _ _ _ _ _) (RHere _ _ _ _ _ _ _ _))
        ((R1 _ _ ddz _ _ _ _ _ _ _ _ q1) (R1 _ _ ddz _ _ _ _ _ _ _ _ q1))
        ((R2 z1 _ ddz _ _ _ _ _ _ _ _ q1) (R2 _ _ ddz _ _ _ _ _ _ _ _ $ ruledin-ins z1 x1 a2 two k2 two2 q q1))))))

(def-fns _ $ (erased ruledin-out : (erased (Nat) z) (erased (Nat) x) (erased (Term) t) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) k) (erased (Facts k) f2) (subterm erased (Out x t n f k f2) o) (erased (RuledIn z n f) r) -> (erased (RuledIn z k f2) r2))
  (match erased o _
    ((OutHere _ _ _ _ _ _ _ _)
      (match erased r _
        ((R1 _ _ ddz _ _ _ _ _ _ _ _ q1) (R1 _ _ ddz _ _ _ _ _ _ _ _ q1))
        ((R2 _ _ ddz _ _ _ _ _ _ _ _ q1) (R2 _ _ ddz _ _ _ _ _ _ _ _ q1))))
    ((Out1 x1 _ _ t0 _ n1 _ _ _ one _ _ k1 _ one2 _ q)
      (match erased r _
        ((RHere _ _ _ _ _ _ _ _) (RHere _ _ _ _ _ _ _ _))
        ((R1 z1 _ ddz _ _ _ _ _ _ _ _ q1) (R1 _ _ ddz _ _ _ _ _ _ _ _ $ ruledin-out z1 x1 t0 n1 one k1 one2 q q1))
        ((R2 _ _ ddz _ _ _ _ _ _ _ _ q1) (R2 _ _ ddz _ _ _ _ _ _ _ _ q1))))
    ((Out2 x1 _ _ t0 _ _ a2 _ _ _ two _ k2 _ two2 _ q)
      (match erased r _
        ((RHere _ _ _ _ _ _ _ _) (RHere _ _ _ _ _ _ _ _))
        ((R1 _ _ ddz _ _ _ _ _ _ _ _ q1) (R1 _ _ ddz _ _ _ _ _ _ _ _ q1))
        ((R2 z1 _ ddz _ _ _ _ _ _ _ _ q1) (R2 _ _ ddz _ _ _ _ _ _ _ _ $ ruledin-out z1 x1 t0 a2 two k2 two2 q q1))))))

(def-fns _ $ (erased ruledin-out-new : (erased (Nat) x) (erased (Term) t) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) k) (erased (Facts k) f2) (subterm erased (Out x t n f k f2) o) -> (erased (RuledIn x k f2) r))
  (match erased o _
    ((OutHere _ _ _ _ _ _ _ _) (RHere _ _ _ _ _ _ _ _))
    ((Out1 x1 _ dd1 t0 _ n1 _ _ _ one _ _ k1 _ one2 _ q) (R1 _ _ dd1 _ _ _ _ _ _ _ _ $ ruledin-out-new x1 t0 n1 one k1 one2 q))
    ((Out2 x1 _ dd1 t0 _ _ a2 _ _ _ two _ k2 _ two2 _ q) (R2 _ _ dd1 _ _ _ _ _ _ _ _ $ ruledin-out-new x1 t0 a2 two k2 two2 q))))

(def-fns _ $ (erased allruled-ins : (erased (List $ Nat) ks) (erased (Nat) x) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) n2) (erased (Facts n2) f2) (erased (Ins x n f n2 f2) i) (subterm erased (AllRuled ks n f) a) -> (erased (AllRuled ks n2 f2) a2))
  (match erased a _
    ((ARNil _ _) (ARNil _ _))
    ((ARCons z rest _ _ r q) (ARCons _ _ _ _ (ruledin-ins z x n f n2 f2 i r) $ allruled-ins rest x n f n2 f2 i q))))

(def-fns _ $ (erased allruled-out : (erased (List $ Nat) ks) (erased (Nat) x) (erased (Term) t) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) k) (erased (Facts k) f2) (erased (Out x t n f k f2) o) (subterm erased (AllRuled ks n f) a) -> (erased (AllRuled ks k f2) a2))
  (match erased a _
    ((ARNil _ _) (ARNil _ _))
    ((ARCons z rest _ _ r q) (ARCons _ _ _ _ (ruledin-out z x t n f k f2 o r) $ allruled-out rest x t n f k f2 o q))))

(def-fns _ $ (erased c1here-append : (erased (List $ Digit) ctx) (erased (Nat) h) (erased (Here h) here) (erased (List $ Rule) rules) (erased (C1Here ctx h here rules) ch) (erased (Rule) r) (erased (List $ Rule) res) (erased (AppendR rules r res) ap) -> (erased (C1Here ctx h here res) ch2))
  (match erased ch _
    ((C1None _ _) (C1None _ _))
    ((C1Free _ _ _) (C1Free _ _ _))
    ((C1Ruled _ _ t _ mw) (C1Ruled _ _ _ _ $ mw-append ctx (Zero) t rules mw r res ap))))

(def-fns _ $ (erased c1-append : (erased (List $ Digit) ctx) (erased (Nat) n) (erased (Facts n) f) (erased (List $ Rule) rules) (subterm erased (C1 ctx n f rules) c) (erased (Rule) r) (erased (List $ Rule) res) (erased (AppendR rules r res) ap) -> (erased (C1 ctx n f res) c2))
  (let-match erased c (C1Node _ h n1 n2 _ here one two _ _ ch c1 c2) ((C1Empty _ _) (C1Empty _ _)))
  (C1Node _ _ _ _ _ _ _ _ _ _ (c1here-append ctx h here rules ch r res ap)
    (c1-append (Cons (Digit) _ _) n1 one rules c1 r res ap)
    $ c1-append (Cons (Digit) _ _) n2 two rules c2 r res ap))

(def-fns _ $ (erased c1-ins : (erased (List $ Digit) ctx) (erased (Nat) x) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) n2) (erased (Facts n2) f2) (subterm erased (Ins x n f n2 f2) i) (erased (List $ Rule) rules) (erased (C1 ctx n f rules) c) -> (erased (C1 ctx n2 f2 rules) c2))
  (match erased i _
    ((InsLeaf ty _) (C1Node _ _ _ _ _ _ _ _ _ _ (C1Free ctx ty rules) (C1Empty (Cons (Digit) _ _) rules) $ C1Empty (Cons (Digit) (D2) _) rules))
    ((InsGrow1 x1 _ _ one q _)
      (C1Node _ _ _ _ _ _ _ _ _ _ (C1None ctx rules)
        (c1-ins (Cons (Digit) (D1) _) x1 (Zero) (FEmpty) (Succ _) one q rules $ C1Empty (Cons (Digit) (D1) ctx) rules)
        $ C1Empty (Cons (Digit) (D2) _) rules))
    ((InsGrow2 x1 _ _ two q _)
      (C1Node _ _ _ _ _ _ _ _ _ _ (C1None ctx rules)
        (C1Empty (Cons (Digit) (D1) _) rules)
        $ c1-ins (Cons (Digit) (D2) _) x1 (Zero) (FEmpty) (Succ _) two q rules $ C1Empty (Cons (Digit) (D2) ctx) rules))
    ((InsHere _ _ _ ty _ _ _)
      (let-match erased c (C1Node c0 h0 a0 b0 m0 here0 one0 two0 p0 r0 ch c1 c2))
      (C1Node _ _ _ _ _ _ _ _ _ _ (C1Free ctx ty rules) c1 c2))
    ((Ins1 x1 _ _ _ n1 _ _ _ one _ _ k1 _ one2 _ q)
      (let-match erased c (C1Node c0 h0 a0 b0 m0 here0 one0 two0 p0 r0 ch c1 c2))
      (C1Node _ _ _ _ _ _ _ _ _ _ ch (c1-ins (Cons (Digit) (D1) _) x1 n1 one k1 one2 q rules c1) c2))
    ((Ins2 x1 _ _ _ _ a2 _ _ _ two _ k2 _ two2 _ q)
      (let-match erased c (C1Node c0 h0 a0 b0 m0 here0 one0 two0 p0 r0 ch c1 c2))
      (C1Node _ _ _ _ _ _ _ _ _ _ ch c1 $ c1-ins (Cons (Digit) (D2) _) x1 a2 two k2 two2 q rules c2))))

(def-fns _ $ (erased c1-out : (erased (List $ Digit) ctx) (erased (Nat) x) (erased (Nat) xg) (erased (Wrap ctx x xg) w) (erased (Term) t) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) k) (erased (Facts k) f2) (subterm erased (Out x t n f k f2) o)
    (erased (List $ Rule) rules) (erased (C1 ctx n f rules) c) (erased (List $ Rule) res) (erased (AppendR rules (MkRule xg t) res) ap) -> (erased (C1 ctx k f2 res) c2))
  (match erased o _
    ((OutHere n1 n2 _ ty t0 one two _)
      (let-match erased c (C1Node c0 h0 a0 b0 m0 here0 one0 two0 p0 r0 ch c1 c2))
      (C1Node _ _ _ _ _ _ _ _ _ _
        (C1Ruled ctx ty t0 res $ wrap-mw ctx (Zero) xg w t0 res $ mem-last xg t0 rules res ap)
        (c1-append (Cons (Digit) _ _) n1 one rules c1 (MkRule _ _) res ap)
        $ c1-append (Cons (Digit) _ _) n2 two rules c2 (MkRule _ _) res ap))
    ((Out1 x1 d1 dd1 _ h n1 a2 _ here one two _ k1 _ one2 _ q)
      (let-match erased c (C1Node c0 h0 a0 b0 m0 here0 one0 two0 p0 r0 ch c1 c2))
      (C1Node _ _ _ _ _ _ _ _ _ _ (c1here-append ctx h here rules ch (MkRule _ _) res ap)
        (c1-out (Cons (Digit) _ _) x1 xg (W1 ctx x1 d1 dd1 xg w) t n1 one k1 one2 q rules c1 res ap)
        $ c1-append (Cons (Digit) _ _) a2 two rules c2 (MkRule _ _) res ap))
    ((Out2 x1 d1 dd1 _ h n1 a2 _ here one two _ k2 _ two2 _ q)
      (let-match erased c (C1Node c0 h0 a0 b0 m0 here0 one0 two0 p0 r0 ch c1 c2))
      (C1Node _ _ _ _ _ _ _ _ _ _ (c1here-append ctx h here rules ch (MkRule _ _) res ap)
        (c1-append (Cons (Digit) _ _) n1 one rules c1 (MkRule _ _) res ap)
        $ c1-out (Cons (Digit) _ _) x1 xg (W2 ctx x1 d1 dd1 xg w) t a2 two k2 two2 q rules c2 res ap))))

(def-fns _ $ (erased keys-snoc : (erased (List $ Nat) seen) (erased (List $ Rule) rules) (erased (List $ Nat) ks) (subterm erased (Keys seen rules ks) k) (erased (Nat) x) (erased (Term) t) (erased (List $ Rule) res) (erased (AppendR rules (MkRule x t) res) ap) -> (erased (Keys seen res $ Cons (Nat) x ks) k2))
  (match erased k _
    ((KNil _)
      (let-match erased ap (ApNil r))
      (KCons _ _ _ _ _ $ KNil $ Cons (Nat) _ _))
    ((KCons _ _ _ rest _ k1)
      (let-match erased ap (ApCons a rest2 r res2 ap2))
      (KCons _ _ _ _ _ $ keys-snoc (Cons (Nat) _ _) rest ks k1 x t res2 ap2))))
; ---- Freshness: every variable of a term is a rule-free entry of a table. Canonicalization returns it.

(def-adts
  ((Fr : ((Nat) n) ((Facts n) f) ((Term) t) -> Type)
    enum
    (many FrVar : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) x) (erased (In x n f) p) -> (Fr n f $ TVar x))
    (many FrBound : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) k) -> (Fr n f $ TBound k))
    (many FrApp : (erased (Nat) n) (erased (Facts n) f) (erased (Term) h) (erased (List $ Term) args) (erased (Fr n f h) p) (erased (FrL n f args) q) -> (Fr n f $ TApp h args))
    (many FrCell : (erased (Nat) n) (erased (Facts n) f) (erased (Term) h) (erased (List $ Term) args) (erased (Fr n f h) p) (erased (FrL n f args) q) -> (Fr n f $ TCell h args))
    (many FrFn : (erased (Nat) n) (erased (Facts n) f) (erased (Bool) uq) (erased (Term) l) (erased (List $ Entry) ps) (erased (List $ Entry) rs) (erased (Fr n f l) p) (erased (FrT n f ps) q) (erased (FrT n f rs) r) -> (Fr n f (TFn uq l ps rs)))
    (many FrTyCtor : (erased (Nat) n) (erased (Facts n) f) (erased (List $ Entry) ps) (erased (FrT n f ps) q) -> (Fr n f $ TTyCtor ps))
    (many FrValCtor : (erased (Nat) n) (erased (Facts n) f) (erased (List $ Entry) ps) (erased (Term) ret) (erased (FrT n f ps) q) (erased (Fr n f ret) p) -> (Fr n f $ TValCtor ps ret))
    (many FrMatchable : (erased (Nat) n) (erased (Facts n) f) (erased (Disc) d) (erased (Bool) nt) (erased (Bool) ex) (erased (Term) ty) (erased (List $ MCtor) cs) (erased (Fr n f ty) p) (erased (FrM n f cs) q) -> (Fr n f (TMatchable d nt ex ty cs)))
    (many FrSlotHolds : (erased (Nat) n) (erased (Facts n) f) (erased (Term) c) -> (Fr n f $ TSlotHolds c))
    (many FrErr : (erased (Nat) n) (erased (Facts n) f) (erased (String) m) -> (Fr n f $ TErr m)))
  ((FrL : ((Nat) n) ((Facts n) f) ((List $ Term) ts) -> Type)
    enum
    (many FrLNil : (erased (Nat) n) (erased (Facts n) f) -> (FrL n f $ Nil $ Term))
    (many FrLCons : (erased (Nat) n) (erased (Facts n) f) (erased (Term) t) (erased (List $ Term) rest) (erased (Fr n f t) p) (erased (FrL n f rest) q) -> (FrL n f $ Cons (Term) t rest)))
  ((FrT : ((Nat) n) ((Facts n) f) ((List $ Entry) es) -> Type)
    enum
    (many FrTNil : (erased (Nat) n) (erased (Facts n) f) -> (FrT n f $ Nil $ Entry))
    (many FrTCons : (erased (Nat) n) (erased (Facts n) f) (erased (Maybe $ String) nm) (erased (Bool) s) (erased (Mult) mu) (erased (Sg) sg) (erased (Maybe $ Term) place) (erased (Maybe $ Loc) site) (erased (List $ Entry) rest) (erased (FrS n f sg) p) (erased (FrT n f rest) q) -> (FrT n f $ Cons (Entry) (MkEntry nm s mu sg place site) rest)))
  ((FrS : ((Nat) n) ((Facts n) f) ((Sg) sg) -> Type)
    enum
    (many FrSTy : (erased (Nat) n) (erased (Facts n) f) (erased (Term) t) (erased (Fr n f t) p) -> (FrS n f $ SgTy t))
    (many FrSIs : (erased (Nat) n) (erased (Facts n) f) (erased (Term) t) (erased (Term) ty) (erased (Fr n f t) p) -> (FrS n f $ SgIs t ty)))
  ((FrM : ((Nat) n) ((Facts n) f) ((List $ MCtor) cs) -> Type)
    enum
    (many FrMNil : (erased (Nat) n) (erased (Facts n) f) -> (FrM n f $ Nil $ MCtor))
    (many FrMCons : (erased (Nat) n) (erased (Facts n) f) (erased (Mult) mu) (erased (Term) c) (erased (List $ MCtor) rest) (erased (Fr n f c) p) (erased (FrM n f rest) q) -> (FrM n f $ Cons (MCtor) (MkMCtor mu c) rest))))

; A guard for a term being canonicalized: nothing at the top, or a table in which the term is fresh and
; every key seen so far is ruled, which is how the term's variables are known not to be those keys.
(def-adts
  ((Guard : ((Term) t) ((List $ Nat) seen) -> Type)
    enum
    (many GTop : (erased (Term) t) -> (Guard t $ Nil $ Nat))
    (many GAv : (erased (Term) t) (erased (List $ Nat) seen) (erased (Nat) n) (erased (Facts n) f) (erased (Fr n f t) p) (erased (AllRuled seen n f) a) -> (Guard t seen)))
  ((GuardL : ((List $ Term) ts) ((List $ Nat) seen) -> Type)
    enum
    (many GLTop : (erased (List $ Term) ts) -> (GuardL ts $ Nil $ Nat))
    (many GLAv : (erased (List $ Term) ts) (erased (List $ Nat) seen) (erased (Nat) n) (erased (Facts n) f) (erased (FrL n f ts) p) (erased (AllRuled seen n f) a) -> (GuardL ts seen)))
  ((GuardT : ((List $ Entry) es) ((List $ Nat) seen) -> Type)
    enum
    (many GTTop : (erased (List $ Entry) es) -> (GuardT es $ Nil $ Nat))
    (many GTAv : (erased (List $ Entry) es) (erased (List $ Nat) seen) (erased (Nat) n) (erased (Facts n) f) (erased (FrT n f es) p) (erased (AllRuled seen n f) a) -> (GuardT es seen)))
  ((GuardS : ((Sg) sg) ((List $ Nat) seen) -> Type)
    enum
    (many GSTop : (erased (Sg) sg) -> (GuardS sg $ Nil $ Nat))
    (many GSAv : (erased (Sg) sg) (erased (List $ Nat) seen) (erased (Nat) n) (erased (Facts n) f) (erased (FrS n f sg) p) (erased (AllRuled seen n f) a) -> (GuardS sg seen)))
  ((GuardM : ((List $ MCtor) cs) ((List $ Nat) seen) -> Type)
    enum
    (many GMTop : (erased (List $ MCtor) cs) -> (GuardM cs $ Nil $ Nat))
    (many GMAv : (erased (List $ MCtor) cs) (erased (List $ Nat) seen) (erased (Nat) n) (erased (Facts n) f) (erased (FrM n f cs) p) (erased (AllRuled seen n f) a) -> (GuardM cs seen))))

(def-fns _ $ (erased fr-var : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) x) (erased (Fr n f $ TVar x) p) -> (erased (In x n f) q))
  (let-match erased p (FrVar a b c q))
  q)

(def-fns _ $ (erased fr-app : (erased (Nat) n) (erased (Facts n) f) (erased (Term) h) (erased (List $ Term) args) (erased (Fr n f $ TApp h args) p) -> (erased (Fr n f h) ph) (erased (FrL n f args) pa))
  (let-match erased p (FrApp a b c d ph pa))
  (values ph pa))

(def-fns _ $ (erased fr-cell : (erased (Nat) n) (erased (Facts n) f) (erased (Term) h) (erased (List $ Term) args) (erased (Fr n f $ TCell h args) p) -> (erased (Fr n f h) ph) (erased (FrL n f args) pa))
  (let-match erased p (FrCell a b c d ph pa))
  (values ph pa))

(def-fns _ $ (erased fr-fn : (erased (Nat) n) (erased (Facts n) f) (erased (Bool) uq) (erased (Term) l) (erased (List $ Entry) ps) (erased (List $ Entry) rs) (erased (Fr n f (TFn uq l ps rs)) p) -> (erased (Fr n f l) pl) (erased (FrT n f ps) pp) (erased (FrT n f rs) pr))
  (let-match erased p (FrFn a b _ c d e pl pp pr))
  (values pl pp pr))

(def-fns _ $ (erased fr-tyctor : (erased (Nat) n) (erased (Facts n) f) (erased (List $ Entry) ps) (erased (Fr n f $ TTyCtor ps) p) -> (erased (FrT n f ps) pp))
  (let-match erased p (FrTyCtor a b c pp))
  pp)

(def-fns _ $ (erased fr-valctor : (erased (Nat) n) (erased (Facts n) f) (erased (List $ Entry) ps) (erased (Term) ret) (erased (Fr n f $ TValCtor ps ret) p) -> (erased (FrT n f ps) pp) (erased (Fr n f ret) pr))
  (let-match erased p (FrValCtor a b c d pp pr))
  (values pp pr))

(def-fns _ $ (erased fr-matchable : (erased (Nat) n) (erased (Facts n) f) (erased (Disc) d) (erased (Bool) nt) (erased (Bool) ex) (erased (Term) ty) (erased (List $ MCtor) cs) (erased (Fr n f (TMatchable d nt ex ty cs)) p) -> (erased (Fr n f ty) pt) (erased (FrM n f cs) pc))
  (let-match erased p (FrMatchable a b c _ _ e g pt pc))
  (values pt pc))



(def-fns _ $ (erased frl-cons : (erased (Nat) n) (erased (Facts n) f) (erased (Term) t) (erased (List $ Term) rest) (erased (FrL n f $ Cons (Term) t rest) p) -> (erased (Fr n f t) pt) (erased (FrL n f rest) pr))
  (let-match erased p (FrLCons a b c d pt pr))
  (values pt pr))

(def-fns _ $ (erased frt-cons : (erased (Nat) n) (erased (Facts n) f) (erased (Maybe $ String) nm) (erased (Bool) s) (erased (Mult) mu) (erased (Sg) sg) (erased (Maybe $ Term) place) (erased (Maybe $ Loc) site) (erased (List $ Entry) rest) (erased (FrT n f $ Cons (Entry) (MkEntry nm s mu sg place site) rest) p) -> (erased (FrS n f sg) ps) (erased (FrT n f rest) pr))
  (let-match erased p (FrTCons a b c d e g _ _ h ps pr))
  (values ps pr))

(def-fns _ $ (erased frs-ty : (erased (Nat) n) (erased (Facts n) f) (erased (Term) t) (erased (FrS n f $ SgTy t) p) -> (erased (Fr n f t) pt))
  (let-match erased p (FrSTy a b c pt))
  pt)

(def-fns _ $ (erased frs-is : (erased (Nat) n) (erased (Facts n) f) (erased (Term) t) (erased (Term) ty) (erased (FrS n f $ SgIs t ty) p) -> (erased (Fr n f t) pt))
  (let-match erased p (FrSIs a b c d pt))
  pt)

(def-fns _ $ (erased frm-cons : (erased (Nat) n) (erased (Facts n) f) (erased (Mult) mu) (erased (Term) c) (erased (List $ MCtor) rest) (erased (FrM n f $ Cons (MCtor) (MkMCtor mu c) rest) p) -> (erased (Fr n f c) pc) (erased (FrM n f rest) pr))
  (let-match erased p (FrMCons a b d e g pc pr))
  (values pc pr))

(def-fns _ $ (erased guard-app : (erased (Term) h) (erased (List $ Term) args) (erased (List $ Nat) seen) (erased (Guard (TApp h args) seen) g) -> (erased (Guard h seen) gh) (erased (GuardL args seen) ga))
  (let-match erased g (GAv _ _ _ _ p a) ((GTop _) (values (GTop _) $ GLTop _)))
  (let ((erased ph) (erased pa)) $ fr-app _ _ _ _ p)
  (values (GAv _ _ _ _ ph a) $ GLAv _ _ _ _ pa a))

(def-fns _ $ (erased guard-cell : (erased (Term) h) (erased (List $ Term) args) (erased (List $ Nat) seen) (erased (Guard (TCell h args) seen) g) -> (erased (Guard h seen) gh) (erased (GuardL args seen) ga))
  (let-match erased g (GAv _ _ _ _ p a) ((GTop _) (values (GTop _) $ GLTop _)))
  (let ((erased ph) (erased pa)) $ fr-cell _ _ _ _ p)
  (values (GAv _ _ _ _ ph a) $ GLAv _ _ _ _ pa a))

(def-fns _ $ (erased guard-fn : (erased (Bool) uq) (erased (Term) l) (erased (List $ Entry) ps) (erased (List $ Entry) rs) (erased (List $ Nat) seen) (erased (Guard (TFn uq l ps rs) seen) g) -> (erased (Guard l seen) gl) (erased (GuardT ps seen) gp) (erased (GuardT rs seen) gr))
  (let-match erased g (GAv _ _ _ _ p a) ((GTop _) (values (GTop _) (GTTop _) $ GTTop _)))
  (let ((erased pl) (erased pp) (erased pr)) (fr-fn _ _ _ _ _ _ p))
  (values (GAv _ _ _ _ pl a) (GTAv _ _ _ _ pp a) $ GTAv _ _ _ _ pr a))

(def-fns _ $ (erased guard-tyctor : (erased (List $ Entry) ps) (erased (List $ Nat) seen) (erased (Guard (TTyCtor ps) seen) g) -> (erased (GuardT ps seen) gp))
  (match erased g _
    ((GTop _) (GTTop _))
    ((GAv _ _ n f p a) (GTAv _ _ _ _ (fr-tyctor n f ps p) a))))

(def-fns _ $ (erased guard-valctor : (erased (List $ Entry) ps) (erased (Term) ret) (erased (List $ Nat) seen) (erased (Guard (TValCtor ps ret) seen) g) -> (erased (GuardT ps seen) gp) (erased (Guard ret seen) gr))
  (let-match erased g (GAv _ _ _ _ p a) ((GTop _) (values (GTTop _) $ GTop _)))
  (let ((erased pp) (erased pr)) $ fr-valctor _ _ _ _ p)
  (values (GTAv _ _ _ _ pp a) $ GAv _ _ _ _ pr a))

(def-fns _ $ (erased guard-matchable : (erased (Disc) d) (erased (Bool) nt) (erased (Bool) ex) (erased (Term) ty) (erased (List $ MCtor) cs) (erased (List $ Nat) seen) (erased (Guard (TMatchable d nt ex ty cs) seen) g) -> (erased (Guard ty seen) gt) (erased (GuardM cs seen) gc))
  (let-match erased g (GAv _ _ _ _ p a) ((GTop _) (values (GTop _) $ GMTop _)))
  (let ((erased pt) (erased pc)) (fr-matchable _ _ _ _ _ _ _ p))
  (values (GAv _ _ _ _ pt a) $ GMAv _ _ _ _ pc a))



(def-fns _ $ (erased guardl-cons : (erased (Term) t) (erased (List $ Term) rest) (erased (List $ Nat) seen) (erased (GuardL (Cons (Term) t rest) seen) g) -> (erased (Guard t seen) gt) (erased (GuardL rest seen) gr))
  (let-match erased g (GLAv _ _ _ _ p a) ((GLTop _) (values (GTop _) $ GLTop _)))
  (let ((erased pt) (erased pr)) $ frl-cons _ _ _ _ p)
  (values (GAv _ _ _ _ pt a) $ GLAv _ _ _ _ pr a))

(def-fns _ $ (erased guardt-cons : (erased (Maybe $ String) nm) (erased (Bool) s) (erased (Mult) mu) (erased (Sg) sg) (erased (Maybe $ Term) place) (erased (Maybe $ Loc) site) (erased (List $ Entry) rest) (erased (List $ Nat) seen) (erased (GuardT (Cons (Entry) (MkEntry nm s mu sg place site) rest) seen) g) -> (erased (GuardS sg seen) gs) (erased (GuardT rest seen) gr))
  (let-match erased g (GTAv _ _ _ _ p a) ((GTTop _) (values (GSTop _) $ GTTop _)))
  (let ((erased ps) (erased pr)) (frt-cons _ _ _ _ _ _ _ _ _ p))
  (values (GSAv _ _ _ _ ps a) $ GTAv _ _ _ _ pr a))

(def-fns _ $ (erased guards-ty : (erased (Term) t) (erased (List $ Nat) seen) (erased (GuardS (SgTy t) seen) g) -> (erased (Guard t seen) gt))
  (match erased g _
    ((GSTop _) (GTop _))
    ((GSAv _ _ n f p a) (GAv _ _ _ _ (frs-ty n f t p) a))))

(def-fns _ $ (erased guards-is : (erased (Term) t) (erased (Term) ty) (erased (List $ Nat) seen) (erased (GuardS (SgIs t ty) seen) g) -> (erased (Guard t seen) gt))
  (match erased g _
    ((GSTop _) (GTop _))
    ((GSAv _ _ n f p a) (GAv _ _ _ _ (frs-is n f t ty p) a))))

(def-fns _ $ (erased guardm-cons : (erased (Mult) mu) (erased (Term) c) (erased (List $ MCtor) rest) (erased (List $ Nat) seen) (erased (GuardM (Cons (MCtor) (MkMCtor mu c) rest) seen) g) -> (erased (Guard c seen) gc) (erased (GuardM rest seen) gr))
  (let-match erased g (GMAv _ _ _ _ p a) ((GMTop _) (values (GTop _) $ GMTop _)))
  (let ((erased pc) (erased pr)) $ frm-cons _ _ _ _ _ p)
  (values (GAv _ _ _ _ pc a) $ GMAv _ _ _ _ pr a))

; ---- The order of the rules list and the position of a chase in it.

(def-adts
  ((Ord : ((List $ Nat) seen) ((List $ Rule) rules) -> Type)
    enum
    (many OrdNil : (erased (List $ Nat) seen) -> (Ord seen $ Nil $ Rule))
    (many OrdCons : (erased (List $ Nat) seen) (erased (Nat) x) (erased (Term) t) (erased (List $ Rule) rest) (erased (Guard t $ Cons (Nat) x seen) g) (erased (Ord (Cons (Nat) x seen) rest) o) -> (Ord seen $ Cons (Rule) (MkRule x t) rest)))
  ((Prefix : ((List $ Nat) seen) ((List $ Rule) whole) ((List $ Rule) after) -> Type)
    enum
    (many PNil : (erased (List $ Rule) whole) -> (Prefix (Nil $ Nat) whole whole))
    (many PCons : (erased (List $ Nat) seen) (erased (List $ Rule) whole) (erased (Nat) x) (erased (Term) t) (erased (List $ Rule) after) (erased (Prefix seen whole $ Cons (Rule) (MkRule x t) after) p) -> (Prefix (Cons (Nat) x seen) whole after)))
  ((RuleFound : ((List $ Nat) seen) ((List $ Rule) whole) ((List $ Rule) after) ((Term) t) -> Type)
    enum
    (many MkRuleFound : (erased (List $ Nat) seen) (erased (List $ Rule) whole) (erased (List $ Rule) after) (erased (Term) t) (erased (List $ Rule) after2) (erased (List $ Nat) seen2)
       (erased (Prefix seen2 whole after2) pre) (erased (Ord seen2 after2) ord) (erased (Guard t seen2) g) (erased (Subterm (List $ Rule) after2 (List $ Rule) after) sbt) -> (RuleFound seen whole after t))))

(def-fns _ $ (erased ord-snoc : (erased (List $ Nat) seen) (erased (List $ Rule) rules) (subterm erased (Ord seen rules) o) (erased (List $ Nat) ks) (erased (Keys seen rules ks) k) (erased (Nat) x) (erased (Term) t) (erased (List $ Rule) res) (erased (AppendR rules (MkRule x t) res) ap) (erased (Guard t $ Cons (Nat) x ks) g) -> (erased (Ord seen res) o2))
  (match erased o _
    ((OrdNil _)
      (let-match erased k (KNil s1))
      (let-match erased ap (ApNil r))
      (OrdCons _ _ _ _ g $ OrdNil $ Cons (Nat) _ _))
    ((OrdCons _ _ _ rest g1 o1)
      (let-match erased k (KCons s1 y1 u1 rest1 ks1 k1))
      (let-match erased ap (ApCons a rest2 r res2 ap2))
      (OrdCons _ _ _ _ g1 $ ord-snoc (Cons (Nat) _ _) rest o1 ks k1 x t res2 ap2 g))))

(def-fns _ $ (erased guard-weaken : (erased (Term) t) (erased (Nat) x) (erased (List $ Nat) seen) (erased (Guard t $ Cons (Nat) x seen) g) -> (erased (Guard t seen) g2))
  (let-match erased g (GAv t0 s n f p a))
  (let-match erased a (ARCons z ks n1 f1 r rest))
  (GAv _ _ _ _ p rest))

(def-fns _ $ (erased absurd guard-clash : (erased (Nat) v) (erased (List $ Nat) seen) (erased (Guard (TVar v) $ Cons (Nat) v seen) g) -> (erased (False) r))
  (let-match erased g (GAv t0 s n f p a))
  (let-match erased a (ARCons z ks n1 f1 r rest))
  (in-ruled-clash _ _ _ (fr-var n f v p) r))

; A ruled variable met inside a rule's term has its rule after that rule: the guard rules it out of the
; keys before, and agreement puts it somewhere.
(def-fns _ $ (erased mem-after : (erased (List $ Nat) seen) (erased (List $ Rule) whole) (erased (List $ Rule) after) (subterm erased (Prefix seen whole after) pre) (erased (Nat) v) (erased (Term) t) (erased (MemRule v t whole) m) (erased (Guard (TVar v) seen) g) -> (erased (MemRule v t after) m2))
  (let-match erased pre (PCons s _ x _ _ pre1) ((PNil _) m))
  (match erased (mem-after _ _ _ pre1 _ _ m $ guard-weaken (TVar _) x s g) _
    (absurd (MRHere _ _ _) (guard-clash _ _ g))
    ((MRThere _ _ _ _ m1) m1)))

(def-fns _ $ (erased find-rule : (erased (List $ Rule) after) (erased (Nat) x) (erased (List $ Nat) seen) (erased (List $ Rule) whole) (erased (Prefix seen whole after) pre) (erased (Ord seen after) ord) (erased (Term) t) (subterm erased (MemRule x t after) m) -> (erased (RuleFound seen whole after t) r))
  (match erased m _
    ((MRHere _ _ rest)
      (let-match erased ord (OrdCons s1 y1 t2 r1 g o))
      (MkRuleFound _ _ _ _ rest _ (PCons _ _ _ _ _ pre) o g $ prove-subterm rest after))
    ((MRThere _ _ _ rest m2)
      (let-match erased ord (OrdCons s1 y1 t2 r1 g o))
      (match erased (find-rule rest x _ _ (PCons _ _ _ _ _ pre) o _ m2) _
        ((MkRuleFound _ _ _ _ after3 _ pre3 ord3 g3 sub2) (MkRuleFound _ _ _ _ after3 _ pre3 ord3 g3 $ subterm-trans sub2 $ prove-subterm rest after))))))
; ---- Canonicalization (sections 5, 18): a chase continues along the rules after the one followed, the
; guard and the agreement proofs saying the rule is there; the result comes with its freshness.

(def-fns _
  ((many canon : (subterm erased (List $ Rule) after) (subterm many (Term) t) (erased (Nat) n) (many (Facts n) f) (erased (List $ Rule) whole) (erased (List $ Nat) seen) (erased (Prefix seen whole after) pre) (erased (Ord seen after) ord) (erased (Guard t seen) g) (erased (C1 (Nil $ Digit) n f whole) c) ->
      (many (Term) r) (erased (Fr n f r) fr))
    (match many t _
      ((TVar x)
        (match many (facts-lookup x _ f _ _ (WNil x) _ c) _
          ((LNone _ _ _ _ _)
            (let ((many msg)) $ str-cat "no fact for " $ nat-str x)
            (values (TErr msg) $ FrErr _ _ _))
          ((LFree _ _ _ _ _ _ p) (values t $ FrVar _ _ _ p))
          ((LRuled _ _ _ _ _ _ r0 m)
            (match erased (find-rule after x _ _ pre ord _ $ mem-after seen whole after pre x r0 m g) _
              ((MkRuleFound _ _ _ _ after2 seen2 pre2 ord2 g2 sub2) (tail $ canon (subterm sub2) after2 r0 n f whole seen2 pre2 ord2 g2 c))))))
      ((TBound _) (values t $ FrBound _ _ _))
      ((TApp h args)
        (let ((erased gh) (erased ga)) $ guard-app _ _ _ g)
        (let ((many h2) (erased fh)) $ notail $ canon after h _ f _ _ pre ord gh c)
        (let ((many args2) (erased fa)) $ notail $ canon-list after args _ f _ _ pre ord ga c)
        (values (TApp h2 args2) $ FrApp _ _ _ _ fh fa))
      ((TCell h args)
        (let ((erased gh) (erased ga)) $ guard-cell _ _ _ g)
        (let ((many h2) (erased fh)) $ notail $ canon after h _ f _ _ pre ord gh c)
        (let ((many args2) (erased fa)) $ notail $ canon-list after args _ f _ _ pre ord ga c)
        (values (TCell h2 args2) $ FrCell _ _ _ _ fh fa))
      ((TFn uq l ps rs)
        (let ((erased gl) (erased gp) (erased gr)) (guard-fn _ _ _ _ _ g))
        (let ((many l2) (erased fl)) $ notail $ canon after l _ f _ _ pre ord gl c)
        (let ((many ps2) (erased fp)) $ notail $ canon-tele after ps _ f _ _ pre ord gp c)
        (let ((many rs2) (erased frs)) $ notail $ canon-tele after rs _ f _ _ pre ord gr c)
        (values (TFn uq l2 ps2 rs2) (FrFn _ _ _ _ _ _ fl fp frs)))
      ((TTyCtor ps)
        (let ((erased gp)) $ guard-tyctor _ _ g)
        (let ((many ps2) (erased fp)) $ notail $ canon-tele after ps _ f _ _ pre ord gp c)
        (values (TTyCtor ps2) $ FrTyCtor _ _ _ fp))
      ((TValCtor ps ret)
        (let ((erased gp) (erased gr)) $ guard-valctor _ _ _ g)
        (let ((many ps2) (erased fp)) $ notail $ canon-tele after ps _ f _ _ pre ord gp c)
        (let ((many ret2) (erased fret)) $ notail $ canon after ret _ f _ _ pre ord gr c)
        (values (TValCtor ps2 ret2) $ FrValCtor _ _ _ _ fp fret))
      ((TMatchable d nt ex ty cs)
        (let ((erased gt) (erased gc)) (guard-matchable _ _ _ _ _ _ g))
        (let ((many ty2) (erased ft)) $ notail $ canon after ty _ f _ _ pre ord gt c)
        (let ((many cs2) (erased fc)) $ notail $ canon-mctors after cs _ f _ _ pre ord gc c)
        (values (TMatchable d nt ex ty2 cs2) (FrMatchable _ _ _ _ _ _ _ ft fc)))
      ((TSlotHolds cn) (values t $ FrSlotHolds _ _ cn))
      ((TErr _) (values t $ FrErr _ _ _))))
  ((many canon-list : (subterm erased (List $ Rule) after) (subterm many (List $ Term) ts) (erased (Nat) n) (many (Facts n) f) (erased (List $ Rule) whole) (erased (List $ Nat) seen) (erased (Prefix seen whole after) pre) (erased (Ord seen after) ord) (erased (GuardL ts seen) g) (erased (C1 (Nil $ Digit) n f whole) c) ->
      (many (List $ Term) r) (erased (FrL n f r) fr))
    (let-match many ts (Cons _ t rest) ((Nil _) (values ts $ FrLNil _ _)))
    (let ((erased gt) (erased gr)) $ guardl-cons _ _ _ g)
    (let ((many t2) (erased ft)) $ notail $ canon after t _ f _ _ pre ord gt c)
    (let ((many rest2) (erased frest)) $ notail $ canon-list after rest _ f _ _ pre ord gr c)
    (values (Cons _ t2 rest2) $ FrLCons _ _ _ _ ft frest))
  ((many canon-tele : (subterm erased (List $ Rule) after) (subterm many (List $ Entry) es) (erased (Nat) n) (many (Facts n) f) (erased (List $ Rule) whole) (erased (List $ Nat) seen) (erased (Prefix seen whole after) pre) (erased (Ord seen after) ord) (erased (GuardT es seen) g) (erased (C1 (Nil $ Digit) n f whole) c) ->
      (many (List $ Entry) r) (erased (FrT n f r) fr))
    (let-match many es (Cons _ e rest) ((Nil _) (values es $ FrTNil _ _)))
    (let-match many e (MkEntry nm s mu sg place site))
    (let ((erased gs) (erased gr)) (guardt-cons _ _ _ _ _ _ _ _ g))
    (let ((many sg2) (erased fs)) $ notail $ canon-sg after sg _ f _ _ pre ord gs c)
    (let ((many rest2) (erased frest)) $ notail $ canon-tele after rest _ f _ _ pre ord gr c)
    (values (Cons _ (MkEntry nm s mu sg2 place site) rest2) (FrTCons _ _ _ _ _ _ _ _ _ fs frest)))
  ((many canon-sg : (subterm erased (List $ Rule) after) (subterm many (Sg) sg) (erased (Nat) n) (many (Facts n) f) (erased (List $ Rule) whole) (erased (List $ Nat) seen) (erased (Prefix seen whole after) pre) (erased (Ord seen after) ord) (erased (GuardS sg seen) g) (erased (C1 (Nil $ Digit) n f whole) c) ->
      (many (Sg) r) (erased (FrS n f r) fr))
    (match many sg _
      ((SgTy t)
        (let ((erased gt)) $ guards-ty _ _ g)
        (let ((many t2) (erased ft)) $ notail $ canon after t _ f _ _ pre ord gt c)
        (values (SgTy t2) $ FrSTy _ _ _ ft))
      ((SgIs t ty)
        (let ((erased gt)) $ guards-is _ _ _ g)
        (let ((many t2) (erased ft)) $ notail $ canon after t _ f _ _ pre ord gt c)
        (values (SgIs t2 ty) $ FrSIs _ _ _ _ ft))))
  ((many canon-mctors : (subterm erased (List $ Rule) after) (subterm many (List $ MCtor) cs) (erased (Nat) n) (many (Facts n) f) (erased (List $ Rule) whole) (erased (List $ Nat) seen) (erased (Prefix seen whole after) pre) (erased (Ord seen after) ord) (erased (GuardM cs seen) g) (erased (C1 (Nil $ Digit) n f whole) c) ->
      (many (List $ MCtor) r) (erased (FrM n f r) fr))
    (let-match many cs (Cons _ mc rest) ((Nil _) (values cs $ FrMNil _ _)))
    (let-match many mc (MkMCtor mu t))
    (let ((erased gt) (erased gr)) $ guardm-cons _ _ _ _ g)
    (let ((many t2) (erased ft)) $ notail $ canon after t _ f _ _ pre ord gt c)
    (let ((many rest2) (erased frest)) $ notail $ canon-mctors after rest _ f _ _ pre ord gr c)
    (values (Cons _ (MkMCtor mu t2) rest2) $ FrMCons _ _ _ _ _ ft frest)))

; ---- The occurs check, as a freshness proof against the table with the variable ruled out.

(def-adts
  ((FrBox : ((Nat) n) ((Facts n) f) ((Term) t) -> Type)
    enum
    (many MkFrBox : (erased (Nat) n) (erased (Facts n) f) (erased (Term) t) (erased (Fr n f t) p) -> (FrBox n f t)))
  ((FrLBox : ((Nat) n) ((Facts n) f) ((List $ Term) ts) -> Type)
    enum
    (many MkFrLBox : (erased (Nat) n) (erased (Facts n) f) (erased (List $ Term) ts) (erased (FrL n f ts) p) -> (FrLBox n f ts)))
  ((FrTBox : ((Nat) n) ((Facts n) f) ((List $ Entry) es) -> Type)
    enum
    (many MkFrTBox : (erased (Nat) n) (erased (Facts n) f) (erased (List $ Entry) es) (erased (FrT n f es) p) -> (FrTBox n f es)))
  ((FrSBox : ((Nat) n) ((Facts n) f) ((Sg) sg) -> Type)
    enum
    (many MkFrSBox : (erased (Nat) n) (erased (Facts n) f) (erased (Sg) sg) (erased (FrS n f sg) p) -> (FrSBox n f sg)))
  ((FrMBox : ((Nat) n) ((Facts n) f) ((List $ MCtor) cs) -> Type)
    enum
    (many MkFrMBox : (erased (Nat) n) (erased (Facts n) f) (erased (List $ MCtor) cs) (erased (FrM n f cs) p) -> (FrMBox n f cs))))

(def-fns _
  ((many refresh : (subterm many (Term) t) (erased (Nat) n) (many (Facts n) f) (erased (List $ Rule) rules) (erased (C1 (Nil $ Digit) n f rules) c) -> (many (Maybe $ FrBox n f t) r))
    (match many t _
      ((TVar x)
        (match many (facts-lookup x _ f _ _ (WNil x) _ c) _
          ((LFree _ _ _ _ _ _ p) (Some _ $ MkFrBox _ _ _ $ FrVar n f x p)) (else (None $ FrBox n f t))))
      ((TBound k) (Some _ $ MkFrBox _ _ _ $ FrBound n f k))
      ((TApp h args)
        (let-match many (notail $ refresh h _ f _ c) (Some _ bh) ((None _) (None _)))
        (match many (notail $ refresh-list args _ f _ c) _
          ((None _) (None _))
          ((Some _ ba)
            (match many bh _ ((MkFrBox _ _ _ ph) (match many ba _ ((MkFrLBox _ _ _ pa) (Some _ $ MkFrBox _ _ _ $ FrApp n f h args ph pa))))))))
      ((TCell h args)
        (let-match many (notail $ refresh h _ f _ c) (Some _ bh) ((None _) (None _)))
        (match many (notail $ refresh-list args _ f _ c) _
          ((None _) (None _))
          ((Some _ ba)
            (match many bh _ ((MkFrBox _ _ _ ph) (match many ba _ ((MkFrLBox _ _ _ pa) (Some _ $ MkFrBox _ _ _ $ FrCell n f h args ph pa))))))))
      ((TFn uq l ps rs)
        (let-match many (notail $ refresh l _ f _ c) (Some _ bl) ((None _) (None _)))
        (let-match many (notail $ refresh-tele ps _ f _ c) (Some _ bp) ((None _) (None _)))
        (match many (notail $ refresh-tele rs _ f _ c) _
          ((None _) (None _))
          ((Some _ br)
            (match many bl _ ((MkFrBox _ _ _ pl) (match many bp _ ((MkFrTBox _ _ _ pp) (match many br _ ((MkFrTBox _ _ _ pr) (Some _ $ MkFrBox _ _ _ (FrFn n f uq l ps rs pl pp pr)))))))))))
      ((TTyCtor ps)
        (match many (notail $ refresh-tele ps _ f _ c) _
          ((None _) (None _))
          ((Some _ bp) (match many bp _ ((MkFrTBox _ _ _ pp) (Some _ $ MkFrBox _ _ _ $ FrTyCtor n f ps pp))))))
      ((TValCtor ps ret)
        (let-match many (notail $ refresh-tele ps _ f _ c) (Some _ bp) ((None _) (None _)))
        (match many (notail $ refresh ret _ f _ c) _
          ((None _) (None _))
          ((Some _ bret)
            (match many bp _ ((MkFrTBox _ _ _ pp) (match many bret _ ((MkFrBox _ _ _ pr) (Some _ $ MkFrBox _ _ _ $ FrValCtor n f ps ret pp pr))))))))
      ((TMatchable d nt ex ty cs)
        (let-match many (notail $ refresh ty _ f _ c) (Some _ bt) ((None _) (None _)))
        (match many (notail $ refresh-mctors cs _ f _ c) _
          ((None _) (None _))
          ((Some _ bc)
            (match many bt _ ((MkFrBox _ _ _ pt) (match many bc _ ((MkFrMBox _ _ _ pc) (Some _ $ MkFrBox _ _ _ (FrMatchable n f d nt ex ty cs pt pc)))))))))
      ((TSlotHolds cn) (Some _ $ MkFrBox _ _ _ $ FrSlotHolds _ _ cn))
      ((TErr m) (Some _ $ MkFrBox _ _ _ $ FrErr n f m))))
  ((many refresh-list : (subterm many (List $ Term) ts) (erased (Nat) n) (many (Facts n) f) (erased (List $ Rule) rules) (erased (C1 (Nil $ Digit) n f rules) c) -> (many (Maybe $ FrLBox n f ts) r))
    (let-match many ts (Cons _ t rest) ((Nil _) (Some _ $ MkFrLBox _ _ _ $ FrLNil n f)))
    (let-match many (notail $ refresh t _ f _ c) (Some _ bt) ((None _) (None _)))
    (match many (notail $ refresh-list rest _ f _ c) _
      ((None _) (None _))
      ((Some _ br)
        (match many bt _ ((MkFrBox _ _ _ pt) (match many br _ ((MkFrLBox _ _ _ pr) (Some _ $ MkFrLBox _ _ _ $ FrLCons n f t rest pt pr))))))))
  ((many refresh-tele : (subterm many (List $ Entry) es) (erased (Nat) n) (many (Facts n) f) (erased (List $ Rule) rules) (erased (C1 (Nil $ Digit) n f rules) c) -> (many (Maybe $ FrTBox n f es) r))
    (let-match many es (Cons _ e rest) ((Nil _) (Some _ $ MkFrTBox _ _ _ $ FrTNil n f)))
    (let-match many e (MkEntry nm s mu sg place site))
    (let-match many (notail $ refresh-sg sg _ f _ c) (Some _ bs) ((None _) (None _)))
    (match many (notail $ refresh-tele rest _ f _ c) _
      ((None _) (None _))
      ((Some _ br)
        (match many bs _ ((MkFrSBox _ _ _ ps) (match many br _ ((MkFrTBox _ _ _ pr) (Some _ $ MkFrTBox _ _ _ (FrTCons n f nm s mu sg place site rest ps pr)))))))))
  ((many refresh-sg : (subterm many (Sg) sg) (erased (Nat) n) (many (Facts n) f) (erased (List $ Rule) rules) (erased (C1 (Nil $ Digit) n f rules) c) -> (many (Maybe $ FrSBox n f sg) r))
    (match many sg _
      ((SgTy t)
        (match many (notail $ refresh t _ f _ c) _
          ((None _) (None _))
          ((Some _ bt) (match many bt _ ((MkFrBox _ _ _ pt) (Some _ $ MkFrSBox _ _ _ $ FrSTy n f t pt))))))
      ((SgIs t t-ty)
        (match many (notail $ refresh t _ f _ c) _
          ((None _) (None _))
          ((Some _ bt) (match many bt _ ((MkFrBox _ _ _ pt) (Some _ $ MkFrSBox _ _ _ $ FrSIs n f t t-ty pt))))))))
  ((many refresh-mctors : (subterm many (List $ MCtor) cs) (erased (Nat) n) (many (Facts n) f) (erased (List $ Rule) rules) (erased (C1 (Nil $ Digit) n f rules) c) -> (many (Maybe $ FrMBox n f cs) r))
    (let-match many cs (Cons _ mc rest) ((Nil _) (Some _ $ MkFrMBox _ _ _ $ FrMNil n f)))
    (let-match many mc (MkMCtor mu t))
    (let-match many (notail $ refresh t _ f _ c) (Some _ bt) ((None _) (None _)))
    (match many (notail $ refresh-mctors rest _ f _ c) _
      ((None _) (None _))
      ((Some _ br)
        (match many bt _ ((MkFrBox _ _ _ pt) (match many br _ ((MkFrMBox _ _ _ pr) (Some _ $ MkFrMBox _ _ _ $ FrMCons n f mu t rest pt pr)))))))))

; ---- A fresh variable's own rule: freshness before the variable was inserted survives its insertion and
; its ruling out, since no path of the term's variables is the new one's.

(def-fns _ $ (erased in-ins-out : (erased (Nat) z) (erased (Nat) x) (erased (Term) t) (erased (Nat) n0) (erased (Facts n0) f0) (erased (Nat) n1) (erased (Facts n1) f1) (erased (Nat) k) (erased (Facts k) f2)
    (subterm erased (Ins x n0 f0 n1 f1) i) (erased (Out x t n1 f1 k f2) o) (erased (In z n0 f0) p) -> (erased (In z k f2) q))
  (match erased i _
    (absurd (InsLeaf _ _) p)
    (absurd (InsGrow1 _ _ _ _ _ _) p)
    (absurd (InsGrow2 _ _ _ _ _ _) p)
    ((InsHere _ _ _ _ _ _ _)
      (let-match erased o (OutHere a1 a2 a3 ty0 t0 one0 two0 p0))
      (match erased p _
        ((In1 _ _ ddz _ _ _ _ _ _ _ _ q1) (In1 _ _ ddz _ _ _ _ _ _ _ _ q1))
        ((In2 _ _ ddz _ _ _ _ _ _ _ _ q1) (In2 _ _ ddz _ _ _ _ _ _ _ _ q1))))
    ((Ins1 x1 d1 dd1 _ n1b _ _ _ one _ _ k1 _ one2 _ q1)
      (let-match erased o (Out1 x2 _ dd2 _ _ _ _ _ _ _ _ _ k3 _ one3 _ q2)
        (absurd (Out2 x2 d2 dd2 _ _ _ _ _ _ _ _ _ _ _ _ _ _) (double-parity x1 x2 d2 dd1 dd2)))
      (match erased p _
        ((InHere _ _ _ _ _ _ _) (InHere _ _ _ _ _ _ _))
        ((In1 z1 _ ddz _ _ _ _ _ _ _ _ q3)
          (match erased (double-inj x2 x1 d1 dd2 dd1) _ ((Refl _ _) (In1 _ _ ddz _ _ _ _ _ _ _ _ $ in-ins-out z1 x1 t n1b one k1 one2 k3 one3 q1 q2 q3))))
        ((In2 _ _ ddz _ _ _ _ _ _ _ _ q3) (In2 _ _ ddz _ _ _ _ _ _ _ _ q3))))
    ((Ins2 x1 d1 dd1 _ _ a2 _ _ _ two _ k2 _ two2 _ q1)
      (let-match erased o (Out2 x2 _ dd2 _ _ _ _ _ _ _ _ _ k3 _ two3 _ q2)
        (absurd (Out1 x2 _ dd2 _ _ _ _ _ _ _ _ _ _ _ _ _ _) (double-parity x2 x1 d1 dd2 dd1)))
      (match erased p _
        ((InHere _ _ _ _ _ _ _) (InHere _ _ _ _ _ _ _))
        ((In1 _ _ ddz _ _ _ _ _ _ _ _ q3) (In1 _ _ ddz _ _ _ _ _ _ _ _ q3))
        ((In2 z1 _ ddz _ _ _ _ _ _ _ _ q3)
          (match erased (double-inj x2 x1 d1 dd2 dd1) _ ((Refl _ _) (In2 _ _ ddz _ _ _ _ _ _ _ _ $ in-ins-out z1 x1 t a2 two k2 two2 k3 two3 q1 q2 q3))))))))

(def-fns _
  ((erased fresh-ins-out : (erased (Nat) x) (erased (Term) t) (erased (Nat) n0) (erased (Facts n0) f0) (erased (Nat) n1) (erased (Facts n1) f1) (erased (Nat) k) (erased (Facts k) f2) (erased (Ins x n0 f0 n1 f1) i) (erased (Out x t n1 f1 k f2) o) (erased (Term) u) (subterm erased (Fr n0 f0 u) p) -> (erased (Fr k f2 u) q))
    (match erased p _
      ((FrVar _ _ z pz) (FrVar _ _ _ $ in-ins-out z x t n0 f0 n1 f1 k f2 i o pz))
      ((FrBound _ _ _) (FrBound _ _ _))
      ((FrApp _ _ h args ph pa) (FrApp _ _ _ _ (fresh-ins-out x t n0 f0 n1 f1 k f2 i o h ph) $ fresh-ins-out-list x t n0 f0 n1 f1 k f2 i o args pa))
      ((FrCell _ _ h args ph pa) (FrCell _ _ _ _ (fresh-ins-out x t n0 f0 n1 f1 k f2 i o h ph) $ fresh-ins-out-list x t n0 f0 n1 f1 k f2 i o args pa))
      ((FrFn _ _ _ l ps rs pl pp pr) (FrFn _ _ _ _ _ _ (fresh-ins-out x t n0 f0 n1 f1 k f2 i o l pl) (fresh-ins-out-tele x t n0 f0 n1 f1 k f2 i o ps pp) (fresh-ins-out-tele x t n0 f0 n1 f1 k f2 i o rs pr)))
      ((FrTyCtor _ _ ps pp) (FrTyCtor _ _ _ $ fresh-ins-out-tele x t n0 f0 n1 f1 k f2 i o ps pp))
      ((FrValCtor _ _ ps ret pp pr) (FrValCtor _ _ _ _ (fresh-ins-out-tele x t n0 f0 n1 f1 k f2 i o ps pp) $ fresh-ins-out x t n0 f0 n1 f1 k f2 i o ret pr))
      ((FrMatchable _ _ _ _ _ ty cs pt pc) (FrMatchable _ _ _ _ _ _ _ (fresh-ins-out x t n0 f0 n1 f1 k f2 i o ty pt) (fresh-ins-out-mctors x t n0 f0 n1 f1 k f2 i o cs pc)))
      ((FrSlotHolds _ _ cn) (FrSlotHolds _ _ cn))
      ((FrErr _ _ _) (FrErr _ _ _))))
  ((erased fresh-ins-out-list : (erased (Nat) x) (erased (Term) t) (erased (Nat) n0) (erased (Facts n0) f0) (erased (Nat) n1) (erased (Facts n1) f1) (erased (Nat) k) (erased (Facts k) f2) (erased (Ins x n0 f0 n1 f1) i) (erased (Out x t n1 f1 k f2) o) (erased (List $ Term) us) (subterm erased (FrL n0 f0 us) p) -> (erased (FrL k f2 us) q))
    (match erased p _
      ((FrLNil _ _) (FrLNil _ _))
      ((FrLCons _ _ u rest pu pr) (FrLCons _ _ _ _ (fresh-ins-out x t n0 f0 n1 f1 k f2 i o u pu) $ fresh-ins-out-list x t n0 f0 n1 f1 k f2 i o rest pr))))
  ((erased fresh-ins-out-tele : (erased (Nat) x) (erased (Term) t) (erased (Nat) n0) (erased (Facts n0) f0) (erased (Nat) n1) (erased (Facts n1) f1) (erased (Nat) k) (erased (Facts k) f2) (erased (Ins x n0 f0 n1 f1) i) (erased (Out x t n1 f1 k f2) o) (erased (List $ Entry) es) (subterm erased (FrT n0 f0 es) p) -> (erased (FrT k f2 es) q))
    (match erased p _
      ((FrTNil _ _) (FrTNil _ _))
      ((FrTCons _ _ _ _ _ sg _ _ rest ps pr) (FrTCons _ _ _ _ _ _ _ _ _ (fresh-ins-out-sg x t n0 f0 n1 f1 k f2 i o sg ps) (fresh-ins-out-tele x t n0 f0 n1 f1 k f2 i o rest pr)))))
  ((erased fresh-ins-out-sg : (erased (Nat) x) (erased (Term) t) (erased (Nat) n0) (erased (Facts n0) f0) (erased (Nat) n1) (erased (Facts n1) f1) (erased (Nat) k) (erased (Facts k) f2) (erased (Ins x n0 f0 n1 f1) i) (erased (Out x t n1 f1 k f2) o) (erased (Sg) sg) (subterm erased (FrS n0 f0 sg) p) -> (erased (FrS k f2 sg) q))
    (match erased p _
      ((FrSTy _ _ u pu) (FrSTy _ _ _ $ fresh-ins-out x t n0 f0 n1 f1 k f2 i o u pu))
      ((FrSIs _ _ u _ pu) (FrSIs _ _ _ _ $ fresh-ins-out x t n0 f0 n1 f1 k f2 i o u pu))))
  ((erased fresh-ins-out-mctors : (erased (Nat) x) (erased (Term) t) (erased (Nat) n0) (erased (Facts n0) f0) (erased (Nat) n1) (erased (Facts n1) f1) (erased (Nat) k) (erased (Facts k) f2) (erased (Ins x n0 f0 n1 f1) i) (erased (Out x t n1 f1 k f2) o) (erased (List $ MCtor) cs) (subterm erased (FrM n0 f0 cs) p) -> (erased (FrM k f2 cs) q))
    (match erased p _
      ((FrMNil _ _) (FrMNil _ _))
      ((FrMCons _ _ _ cn rest pc pr) (FrMCons _ _ _ _ _ (fresh-ins-out x t n0 f0 n1 f1 k f2 i o cn pc) $ fresh-ins-out-mctors x t n0 f0 n1 f1 k f2 i o rest pr)))))

(def-adts $ (OpenKind : -> Type)
  enum
  (many OKMatchable : -> (OpenKind)) (many OKNone : -> (OpenKind)))

(def-fns _ $ (many open-kind-code : (many (OpenKind) k) -> (many (Nat) n))
  (match many k _ ((OKMatchable) 0) ((OKNone) 2)))

; An opened Matchable or Newtype (section 19): its entry, its kind, and the names its type holds canonically,
; the type constructor first.
(def-adts $ (Opened : -> Type)
  enum
  (many MkOpened : (many (Nat) x) (many (OpenKind) kind) (many (List $ Nat) names) -> (Opened)))

(def-fns _ $ (many opened-x : (many (Opened) o) -> (many (Nat) x))
  (match many o _ ((MkOpened x _ _) x)))

(def-fns _ $ (many opened-names : (many (Opened) o) -> (many (List $ Nat) ns))
  (match many o _ ((MkOpened _ _ ns) ns)))

; The opened objects of a table, newest first, indexed by the names they hold, and those [touched] since the
; elaborator last restored section 19's invariant. Indexed by the table's facts: only opens-inserted,
; opens-out, table-open, table-unopen, table-settled and empty-table below mint one, so an Opens sits in
; the table its names are canonical under, refreshed where a variable is ruled out (rule-into).
(def-adts $ (Opens : ((Nat) n) ((Facts n) f) -> Type)
  enum
  (many MkOpens : (erased (Nat) n) (erased (Facts n) f) (many (List $ Opened) list) (many (IdMap $ List $ Nat) index) (many (List $ Nat) touched) -> (Opens n f)))

(def-fns _ $ (many nats-share : (subterm many (List $ Nat) xs) (many (List $ Nat) ys) -> (many (Bool) r))
  (match many xs _ ((Nil _) (BFalse)) ((Cons _ x rest) (or (list-mem-bin ys x) $ notail $ nats-share rest ys))))

(def-fns _ $ (many nats-remove : (subterm many (List $ Nat) xs) (many (Nat) x) -> (many (List $ Nat) r))
  (match many xs _
    ((Nil _) (Nil _))
    ((Cons _ y rest) (match many (nat-eq x y) _ ((BTrue) (tail $ nats-remove rest x)) ((BFalse) (Cons _ y $ notail $ nats-remove rest x))))))

(def-fns _ $ (many nats-dup : (subterm many (List $ Nat) xs) -> (many (Maybe $ Nat) r))
  (match many xs _
    ((Nil _) (None _))
    ((Cons _ x rest) (match many (list-mem-bin rest x) _ ((BTrue) (Some _ x)) ((BFalse) (tail $ nats-dup rest))))))

(def-fns _ $ (many index-of : (many (Nat) n) (many (IdMap $ List $ Nat) ix) -> (many (List $ Nat) r))
  (match many (idmap-get _ n ix) _ ((Hit _ _ _ os _) os) ((Miss _ _ _ _) (Nil _))))

(def-fns _ $ (many index-add : (subterm many (List $ Nat) names) (many (Nat) o) (many (IdMap $ List $ Nat) ix) -> (many (IdMap $ List $ Nat) r))
  (match many names _
    ((Nil _) ix)
    ((Cons _ n rest) (tail $ index-add rest o $ idmap-set _ n (Cons _ o $ index-of n ix) ix))))

(def-fns _ $ (many index-drop : (subterm many (List $ Nat) names) (many (Nat) o) (many (IdMap $ List $ Nat) ix) -> (many (IdMap $ List $ Nat) r))
  (match many names _
    ((Nil _) ix)
    ((Cons _ n rest) (tail $ index-drop rest o $ idmap-set _ n (nats-remove (index-of n ix) o) ix))))

; The object of id x replaced, with the names it held.
(def-fns _ $ (many opened-swap : (subterm many (List $ Opened) os) (many (Opened) o) -> (many (List $ Opened) r) (many (List $ Nat) old))
  (let-match many os (Cons _ p rest) ((Nil _) (values (Nil _) (Nil _))))
  (let-match many (nat-eq (opened-x p) $ opened-x o) (BFalse) ((BTrue) (values (Cons _ o rest) $ opened-names p)))
  (let ((many r) (many old)) $ notail $ opened-swap rest o)
  (values (Cons _ p r) old))

(def-fns _ $ (many opened-take : (subterm many (List $ Opened) os) (many (Nat) x) -> (many (List $ Opened) r) (many (List $ Nat) names))
  (let-match many os (Cons _ p rest) ((Nil _) (values (Nil _) (Nil _))))
  (let-match many (nat-eq (opened-x p) x) (BFalse) ((BTrue) (values rest $ opened-names p)))
  (let ((many r) (many names)) $ notail $ opened-take rest x)
  (values (Cons _ p r) names))

; ---- The table: the facts, the rules, the opened objects, and the erased invariants that make canonicalization complete.

(def-adts
  ((Table : ((Nat) n) ((Facts n) f) ((Nat) c) -> Type)
    enum
    (many MkTable : (erased (Nat) n) (many (Facts n) f) (erased (Nat) c) (erased (List $ Rule) ru) (erased (List $ Nat) ks) (erased (Ord (Nil $ Nat) ru) ord) (erased (Keys (Nil $ Nat) ru ks) keys) (erased (AllRuled ks n f) ar) (erased (C1 (Nil $ Digit) n f ru) c1) (erased (Above (Nil $ Digit) c n f) ab) (many (Opens n f) opens) -> (Table n f c)))
  ((Added : ((Nat) n) ((Facts n) f) ((Nat) c) -> Type)
    enum
    (many MkAdded : (erased (Nat) k) (erased (Facts $ Succ k) f) (erased (Facts k) f2) (erased (Nat) c) (many (Table k f2 c) tb) -> (Added (Succ k) f c))))

(let ((many empty-table)) $ MkTable _ (FEmpty) _ (Nil _) _ (OrdNil $ Nil $ Nat) (KNil $ Nil $ Nat) (ARNil (Zero) $ FEmpty) (C1Empty (Nil $ Digit) $ Nil $ Rule) (AbEmpty (Nil $ Digit) $ Zero) $ MkOpens _ _ (Nil _) (MEmpty _) $ Nil _)

(def-fns _ $ (many canon-in : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) bnd) (many (Table n f bnd) tb) (many (Term) t) -> (many (Term) r) (erased (Fr n f r) fr))
  (match many tb _
    ((MkTable _ f0 _ ru _ ord _ _ c1 _ _) (canon ru t _ f0 _ _ (PNil ru) ord (GTop t) c1))))
(def-fns _ $ (many canon-list-in : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) bnd) (many (Table n f bnd) tb) (many (List $ Term) ts) -> (many (List $ Term) r) (erased (FrL n f r) fr))
  (match many tb _
    ((MkTable _ f0 _ ru _ ord _ _ c1 _ _) (canon-list ru ts _ f0 _ _ (PNil ru) ord (GLTop ts) c1))))
(def-fns _ $ (many canon-tele-in : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) bnd) (many (Table n f bnd) tb) (many (List $ Entry) es) -> (many (List $ Entry) r) (erased (FrT n f r) fr))
  (match many tb _
    ((MkTable _ f0 _ ru _ ord _ _ c1 _ _) (canon-tele ru es _ f0 _ _ (PNil ru) ord (GTTop es) c1))))
(def-fns _ $ (many canon-mctors-in : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) bnd) (many (Table n f bnd) tb) (many (List $ MCtor) cs) -> (many (List $ MCtor) r) (erased (FrM n f r) fr))
  (match many tb _
    ((MkTable _ f0 _ ru _ ord _ _ c1 _ _) (canon-mctors ru cs _ f0 _ _ (PNil ru) ord (GMTop cs) c1))))


(def-fns _ $ (many fact-in : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) bnd) (many (Table n f bnd) tb) (many (Nat) x) -> (many (Term) ty) (many (Maybe $ Term) rule))
  (let-match many tb (MkTable _ f0 _ _ _ _ _ _ c1 _ _))
  (match many (facts-lookup x _ f0 _ _ (WNil x) _ c1) _
    ((LNone _ _ _ _ _) (values (TErr $ str-cat "no fact for " $ nat-str x) $ None _))
    ((LRuled _ _ _ _ _ ty t _) (values ty $ Some _ t))
    ((LFree _ _ _ _ _ ty _) (values ty $ None _))))

(def-fns _ $ (many type-in : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) bnd) (many (Table n f bnd) tb) (many (Nat) x) -> (many (Term) r))
  (let ((many ty) (many rule)) $ fact-in _ _ bnd tb x)
  (let ((many r) (erased fr)) $ canon-in _ _ bnd tb ty)
  r)

(def-fns _ $ (many var-id : (many (Term) t) -> (many (Nat) r))
  (match many t _ ((TVar x) x) (else 0)))

(def-fns _ $ (many mctor-ids : (subterm many (List $ MCtor) cs) -> (many (List $ Nat) r))
  (match many cs _
    ((Nil _) (Nil _))
    ((Cons _ mc rest) (match many mc _ ((MkMCtor _ t) (Cons _ (var-id t) $ notail $ mctor-ids rest))))))

; The kind of an opened object and the type constructor and constructors it names, canonically.
(def-fns _ $ (many open-names : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) bnd) (many (Table n f bnd) tb) (many (Nat) x) -> (many (OpenKind) k) (many (List $ Nat) names))
  (match many (type-in _ _ bnd tb x) _
    ((TMatchable _ _ _ t cs) (values (OKMatchable) $ Cons _ (var-id t) $ mctor-ids cs))
    ((TSlotHolds _) (values (OKNone) $ Nil _))
    (else (values (OKNone) $ Nil _))))

(def-fns _ $ (many opened-in : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) bnd) (many (Table n f bnd) tb) (many (Nat) x) -> (many (Opened) o))
  (let ((many k) (many names)) $ open-names _ _ bnd tb x)
  (MkOpened x k names))


; The opened objects transported across a change of the facts, each by the proof the change produces: a
; fresh entry inserted names nothing opened, and a variable ruled out is canonical no longer, so rule-into
; refreshes the objects naming it after this.
(def-fns _ $ (many opens-inserted : (erased (Nat) x) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) n2) (erased (Facts n2) f2) (erased (Ins x n f n2 f2) i) (many (Opens n f) o) -> (many (Opens n2 f2) r))
  (match many o _ ((MkOpens _ _ l ix tc) (MkOpens _ _ l ix tc))))

(def-fns _ $ (many opens-out : (erased (Nat) x) (erased (Term) t) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) k) (erased (Facts k) f2) (erased (Out x t n f k f2) o) (many (Opens n f) os) -> (many (Opens k f2) r))
  (match many os _ ((MkOpens _ _ l ix tc) (MkOpens _ _ l ix tc))))

; Each of [xs] reads its names again under the table, is indexed by them, and is touched.
(def-fns _ $ (many refresh-named : (subterm many (List $ Nat) xs) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) bnd) (many (Table n f bnd) tb) (many (List $ Opened) os) (many (IdMap $ List $ Nat) ix) (many (List $ Nat) tc) ->
    (many (List $ Opened) os2) (many (IdMap $ List $ Nat) ix2) (many (List $ Nat) tc2))
  (let-match many xs (Cons _ x rest) ((Nil _) (values os ix tc)))
  (let ((many o)) $ opened-in _ _ bnd tb x)
  (let ((many os2) (many old)) $ opened-swap os o)
  (tail $ refresh-named rest _ _ bnd tb os2 (index-add (opened-names o) x $ index-drop old x ix) $ Cons _ x tc))

; The table with the objects naming v refreshed, once v is ruled out.
(def-fns _ $ (many table-refresh : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) c) (many (Table n f c) tb) (many (Nat) v) -> (many (Table n f c) r))
  (let-match many tb (MkTable _ f0 _ ru _ ord keys ar c1 ab op))
  (let-match many op (MkOpens _ _ os ix tc))
  (let ((many os2) (many ix2) (many tc2)) $ refresh-named (index-of v ix) _ _ c tb os ix tc)
  (MkTable _ f0 _ ru _ ord keys ar c1 ab $ MkOpens _ _ os2 ix2 tc2))

; Opens x: listed newest first, indexed by its names, and touched.
(def-fns _ $ (many table-open : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) c) (many (Table n f c) tb) (many (Nat) x) -> (many (Table n f c) r))
  (let ((many o)) $ opened-in _ _ c tb x)
  (let-match many tb (MkTable _ f0 _ ru _ ord keys ar c1 ab op))
  (match many op _
    ((MkOpens _ _ os ix tc) (MkTable _ f0 _ ru _ ord keys ar c1 ab $ MkOpens _ _ (Cons _ o os) (index-add (opened-names o) x ix) $ Cons _ x tc))))

(def-fns _ $ (many table-unopen : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) c) (many (Table n f c) tb) (many (Nat) x) -> (many (Table n f c) r))
  (let-match many tb (MkTable _ f0 _ ru _ ord keys ar c1 ab op))
  (let-match many op (MkOpens _ _ os ix tc))
  (let ((many os2) (many names)) $ opened-take os x)
  (MkTable _ f0 _ ru _ ord keys ar c1 ab $ MkOpens _ _ os2 (index-drop names x ix) $ nats-remove tc x))

; The invariant restored: nothing is touched.
(def-fns _ $ (many table-settled : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) c) (many (Table n f c) tb) -> (many (Table n f c) r))
  (match many tb _
    ((MkTable _ f0 _ ru _ ord keys ar c1 ab op)
      (match many op _ ((MkOpens _ _ os ix _) (MkTable _ f0 _ ru _ ord keys ar c1 ab $ MkOpens _ _ os ix $ Nil _))))))

(def-fns _ $ (many table-opens : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) c) (many (Table n f c) tb) -> (many (List $ Opened) os) (many (IdMap $ List $ Nat) ix) (many (List $ Nat) tc))
  (match many tb _ ((MkTable _ _ _ _ _ _ _ _ _ _ op) (match many op _ ((MkOpens _ _ os ix tc) (values os ix tc))))))

; The table after a variable is ruled out with a term fresh in the result: the rule is appended, the
; keys and the order extended, both agreements carried across, and the opened objects naming the variable
; refreshed.
(def-fns _ $ (many rule-into : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) c) (erased (Above (Nil $ Digit) c n f) ab) (erased (List $ Rule) ru) (erased (List $ Nat) ks) (erased (Ord (Nil $ Nat) ru) ord) (erased (Keys (Nil $ Nat) ru ks) keys) (erased (AllRuled ks n f) ar) (erased (C1 (Nil $ Digit) n f ru) c1)
    (many (Opens n f) op) (many (Nat) x) (many (Term) t) (erased (Nat) k) (many (Facts k) f2) (erased (Out x t n f k f2) o) (erased (Fr k f2 t) ft) -> (many (Table k f2 c) tb))
  (let ((erased ru2) (erased ap)) $ append-rule ru $ MkRule x t)
  (let ((erased ar2)) $ ARCons _ _ _ _ (ruledin-out-new x t n f k f2 o) $ allruled-out ks x t n f k f2 o ar)
  (table-refresh _ _ c
    (MkTable _ f2 _ ru2 _
      (ord-snoc (Nil $ Nat) ru ord ks keys x t ru2 ap $ GAv t (Cons (Nat) _ _) k f2 ft ar2)
      (keys-snoc (Nil $ Nat) ru ks keys x t ru2 ap)
      ar2
      (c1-out (Nil $ Digit) x x (WNil x) t n f k f2 o ru c1 ru2 ap)
      (above-out (Nil $ Digit) c x t n f k f2 ab o)
      $ opens-out _ _ _ _ _ _ o op)
    x))

; Unification's binding: rule the variable out, and the occurs check is the term still being fresh.
(def-fns _ $ (many rule-out-refresh : (erased (Nat) n) (erased (Facts n) f) (many (Nat) bnd) (many (Table n f bnd) tb) (many (Nat) x) (erased (In x n f) p) (many (Term) t) -> (many (Maybe $ Added n f bnd) r))
  (let-match many tb (MkTable _ f0 _ ru _ ord keys ar c1 ab op))
  (let-match many (facts-rule-out _ f0 x p t) (MkRemoved _ _ _ _ f2 o))
  (let ((erased ru2) (erased ap)) $ append-rule ru $ MkRule x t)
  (let ((erased c2)) $ c1-out _ _ _ (WNil x) _ _ _ _ _ o _ c1 _ ap)
  (let-match many (refresh t _ f2 _ c2) (Some _ box) ((None _) (None _)))
  (match many box _
    ((MkFrBox _ _ _ ft) (Some _ $ MkAdded _ _ _ _ $ rule-into _ _ _ ab ru _ ord keys ar c1 op x t _ f2 o ft))))

; A new entry, rule-free, at the fresh id x above every key of the table: the count grows.
(def-fns _ $ (many table-insert : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) c) (many (Table n f c) tb) (many (Nat) x) (erased (Lt c x) lt) (many (Term) ty) -> (erased (Nat) n2) (erased (Facts n2) f2) (many (Table n2 f2 x) tb2))
  (let-match many tb (MkTable _ f0 _ ru ks ord keys ar c1 ab op))
  (let-match many (facts-insert x _ f0 ty) (IGrew _ _ _ f1 i _)
    (absurd (IKept _ _ _ q) (le-lt-absurd _ _ (above-taken c n f0 x ab q) lt)))
  (values (Succ n) f1 (MkTable _ f1 _ ru _ ord keys (allruled-ins ks x n f0 (Succ _) f1 i ar) (c1-ins (Nil $ Digit) x n f0 (Succ _) f1 i ru c1)
                         (above-ins (Nil $ Digit) x n f0 (Succ _) f1 x x (above-weaken (Nil $ Digit) c x n f0 ab $ lt-weaken c x lt) i (WNil x) $ lt-succ x)
                         $ opens-inserted _ _ _ _ _ i op)))

; A new entry with a rule, its term canonical: inserted rule-free and ruled out at once.
(def-fns _ $ (many table-insert-ruled : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) c) (many (Table n f c) tb) (many (Nat) x) (erased (Lt c x) lt) (many (Term) ty) (many (Term) t) (erased (Fr n f t) ft) -> (erased (Nat) n2) (erased (Facts n2) f2) (many (Table n2 f2 x) tb2))
  (let-match many tb (MkTable _ f0 _ ru ks ord keys ar c1 ab op))
  (let-match many (facts-insert x _ f0 ty) (IGrew _ _ _ f1 i q)
    (absurd (IKept _ _ _ q) (le-lt-absurd _ _ (above-taken c n f0 x ab q) lt)))
  (let-match many (facts-rule-out _ f1 x q t) (MkRemoved _ _ k _ f2 o))
  (values k f2 (rule-into _ _ _ (above-ins (Nil $ Digit) x n f0 (Succ _) f1 x x (above-weaken (Nil $ Digit) c x n f0 ab $ lt-weaken c x lt) i (WNil x) $ lt-succ x)
                  ru _ ord keys (allruled-ins ks x n f0 (Succ _) f1 i ar) (c1-ins (Nil $ Digit) x n f0 (Succ _) f1 i ru c1)
                  (opens-inserted _ _ _ _ _ i op) x t _ f2 o $ fresh-ins-out x t n f0 (Succ _) f1 k f2 i o t ft)))

(def-fns _ $ (many table-weaken : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) c) (erased (Nat) c2) (many (Table n f c) tb) (erased (Lt c (Succ c2)) le) -> (many (Table n f c2) tb2))
  (match many tb _
    ((MkTable n0 f0 _ ru _ ord keys ar c1 ab op) (MkTable _ f0 _ ru _ ord keys ar c1 (above-weaken (Nil $ Digit) c c2 n0 f0 ab le) op))))

; Two distinct variables: ruling the newer out leaves the older rule-free, so the alias is fresh.
(def-fns _ $ (erased in-out-neq : (erased (Nat) z) (erased (Nat) x) (erased (Term) t) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) k) (erased (Facts k) f2) (subterm erased (Out x t n f k f2) o) (erased (Neq z x) ne) (erased (In z n f) p) -> (erased (In z k f2) q))
  (match erased o _
    ((OutHere _ _ _ _ _ _ _ _)
      (match erased p _
        (absurd (InHere _ _ _ _ _ _ _) (neq-irrefl _ ne))
        ((In1 _ _ ddz _ _ _ _ _ _ _ _ q1) (In1 _ _ ddz _ _ _ _ _ _ _ _ q1))
        ((In2 _ _ ddz _ _ _ _ _ _ _ _ q1) (In2 _ _ ddz _ _ _ _ _ _ _ _ q1))))
    ((Out1 x1 dx ddx t0 _ n1 _ _ _ one _ _ k1 _ one2 _ q)
      (match erased p _
        ((InHere _ _ _ _ _ _ _) (InHere _ _ _ _ _ _ _))
        ((In1 z1 dz ddz _ _ _ _ _ _ _ _ q1)
          (In1 _ _ ddz _ _ _ _ _ _ _ _ $ in-out-neq z1 x1 t0 n1 one k1 one2 q (neq-half z1 dz x1 dx ddz ddx $ neq-pred dz dx ne) q1))
        ((In2 _ _ ddz _ _ _ _ _ _ _ _ q1) (In2 _ _ ddz _ _ _ _ _ _ _ _ q1))))
    ((Out2 x1 dx ddx t0 _ _ a2 _ _ _ two _ k2 _ two2 _ q)
      (match erased p _
        ((InHere _ _ _ _ _ _ _) (InHere _ _ _ _ _ _ _))
        ((In1 _ _ ddz _ _ _ _ _ _ _ _ q1) (In1 _ _ ddz _ _ _ _ _ _ _ _ q1))
        ((In2 z1 dz ddz _ _ _ _ _ _ _ _ q1)
          (In2 _ _ ddz _ _ _ _ _ _ _ _ $ in-out-neq z1 x1 t0 a2 two k2 two2 q (neq-half z1 dz x1 dx ddz ddx $ neq-pred dz dx $ neq-pred (Succ dz) (Succ dx) ne) q1))))))

(def-fns _ $ (many rule-out-var : (erased (Nat) n) (erased (Facts n) f) (many (Nat) bnd) (many (Table n f bnd) tb) (many (Nat) newer) (many (Nat) older) (erased (In newer n f) pn) (erased (In older n f) po) (erased (Neq older newer) ne) -> (many (Added n f bnd) r))
  (let-match many tb (MkTable _ f0 _ ru _ ord keys ar c1 ab op))
  (match many (facts-rule-out _ f0 newer pn $ TVar older) _
    ((MkRemoved _ _ k _ f2 o)
      (MkAdded _ _ _ _ $ rule-into _ _ _ ab ru _ ord keys ar c1 op newer (TVar older) _ f2 o $ FrVar k f2 older $ in-out-neq older newer (TVar _) n f0 k f2 o ne po))))



; ---- The scope environment (section 3) and fact table (section 18); [hl] the ghost history every
; Const's value was allocated into, [store] the next stamp, and [entries] and [finals] hold its references.

(def-adts
  ((Use : -> Type) enum (many UseShared : (many (Loc) loc) -> (Use)) (many UseConsumed : (many (Loc) loc) -> (Use)))
  ((Warned : -> Type) enum (many MkWarned : (many (Nat) id) (many (Loc) site) (many (String) msg) -> (Warned)))
  ((Pragmas : -> Type) enum (many MkPragmas : (many (List $ Warned) warned) (many (List $ Region) regions) -> (Pragmas)))
  ((Said : -> Type) enum (many SaidWarning : (many (String) text) -> (Said)) (many SaidError : (many (String) text) -> (Said)) (many SaidSilenced : (many (Nat) region) -> (Said)))
  ((UniqueState : -> Type) enum
    (many MkUniqueState : (many (IdMap $ Nat) locations) (many (IdMap $ Use) uses) (many (List $ Nat) captures)
      (many (Bool) usage-erased) (many (Bool) in-extern) (many (List $ Nat) signature)
      (many (List $ Nat) words) (many (List $ Nat) temporary) (many (Pragmas) pragmas) (many (IdMap $ Nat) aliases) -> (UniqueState))))
; An interned literal: its entry, its Numeral proof where it has one, and the spelling it reads back as.
(def-adts $ (LitEntry : -> Type)
  enum
  (many MkLitEntry : (many (Nat) id) (many (Maybe $ Nat) proof) (many (String) spelling) -> (LitEntry)))

(let ((many unique-empty)) (MkUniqueState (MEmpty _) (MEmpty _) (Nil _) (BFalse) (BFalse) (Nil _) (Nil _) (Nil _) (MkPragmas (Nil _) (Nil _)) (MEmpty _)))

(def-adts $ (Scope : -> Type)
  enum
  (many MkScope : (many (NameMap $ Nat) names) (many (List $ Nat) ids) -> (Scope)))
(def-fns _ $ (many scope-names : (many (Scope) s) -> (many (NameMap $ Nat) r)) (match many s _ ((MkScope n _) n)))
(def-fns _ $ (many scope-ids : (many (Scope) s) -> (many (List $ Nat) r)) (match many s _ ((MkScope _ ids) ids)))
(let ((many scope-empty)) (MkScope (nm-empty _) (Nil _)))

(def-adts
  ((Env : -> Type)
    enum
    (many MkEnv : (erased (Hist Block) hl) (many (Store Block hl) store) (many (Scope) scope) (many (IdMap $ EInfo hl) entries) (erased (Nat) nfree) (erased (Facts nfree) ffacts) (many (Nat) fresh) (many (Table nfree ffacts fresh) table)
       (many (Bool) run-pos) (many (List $ Nat) objects)
       (many (NameMap $ Nat) literals) (many (List $ Pair (Ref Block hl) $ Term) finals)
       (many (Maybe $ Nat) level) (many (List $ Nat) subterms) (many (List $ Pair (String) $ Loc) claimed) (many (List $ Said) diagnostics)
       (many (List $ LitEntry) lits) (many (Loc) loc) (many (Scope) prelude) (many (UniqueState) us) (many (List $ String) help) -> (Env)))
  ((EInfo : ((Hist Block) l) -> Type)
    enum
    (many MkEInfo : (erased (Hist Block) l) (many (Maybe $ String) name) (many (Mult) mult) (many (State l) state) (many (Bool) minted) (many (Bool) meta) (many (Maybe $ Loc) site) -> (EInfo l)))
  ((State : ((Hist Block) l) -> Type)
    enum
    (many SConst : (erased (Hist Block) l) (many (Ref Block l) v) -> (State l))
    (many SDyn : (erased (Hist Block) l) -> (State l))))

(def-fns _ $ (erased state-widen : (erased (Hist Block) b) (erased (Hist Block) c) (erased (Suffix Block c b) le) (erased (State b) s) -> (erased (State c) s2) (erased (Coercible (Shared) (State b) s (Shared) (State c) s2) p))
  (let-match erased s (SConst _ v) ((SDyn _) (values (SDyn _) (coercible-ctor (Shared) SDyn b c))))
  (let ((erased v2) (erased pv)) (ref-widen _ b c le v))
  (values (SConst _ v2) (coercible-ctor (Shared) SConst b c pv)))

(def-fns _ $ (erased einfo-widen : (erased (Hist Block) b) (erased (Hist Block) c) (erased (Suffix Block c b) le) (erased (EInfo b) e) -> (erased (EInfo c) e2) (erased (Coercible (Shared) (EInfo b) e (Shared) (EInfo c) e2) p))
  (let-match erased e (MkEInfo _ n m s mi me site))
  (let ((erased s2) (erased ps)) (state-widen b c le s))
  (values (MkEInfo _ n m s2 mi me site) (coercible-ctor (Shared) MkEInfo b c (coercible-refl (Shared) n) (coercible-refl (Shared) m) ps (coercible-refl (Shared) mi) (coercible-refl (Shared) me) (coercible-refl (Shared) site))))

(def-fns _ $ (erased maybe-einfo-widen : (erased (Hist Block) b) (erased (Hist Block) c) (erased (Suffix Block c b) le) (erased (Maybe $ EInfo b) m) -> (erased (Maybe $ EInfo c) m2) (erased (Coercible (Shared) (Maybe $ EInfo b) m (Shared) (Maybe $ EInfo c) m2) p))
  (let-match erased m (Some _ x) ((None _) (values (None _) (coercible-ctor (Shared) None (EInfo b) (EInfo c)))))
  (let ((erased x2) (erased px)) (einfo-widen b c le x))
  (values (Some _ x2) (coercible-ctor (Shared) Some (EInfo b) (EInfo c) px)))

(def-fns _ $ (erased entries-widen : (erased (Hist Block) b) (erased (Hist Block) c) (erased (Suffix Block c b) le) (subterm erased (IdMap $ EInfo b) m) -> (erased (IdMap $ EInfo c) m2) (erased (Coercible (Shared) (IdMap $ EInfo b) m (Shared) (IdMap $ EInfo c) m2) p))
  (let-match erased m (MNode _ here one two)
    ((MEmpty _) (values (MEmpty _) (coercible-ctor (Shared) MEmpty (EInfo b) (EInfo c)))))
  (let ((erased here2) (erased ph)) (maybe-einfo-widen b c le here))
  (let ((erased one2) (erased p1)) (entries-widen b c le one))
  (let ((erased two2) (erased p2)) (entries-widen b c le two))
  (values (MNode _ here2 one2 two2) (coercible-ctor (Shared) MNode (EInfo b) (EInfo c) ph p1 p2)))

(def-fns _ $ (erased finals-widen : (erased (Hist Block) b) (erased (Hist Block) c) (erased (Suffix Block c b) le) (subterm erased (List $ Pair (Ref Block b) $ Term) xs) -> (erased (List $ Pair (Ref Block c) $ Term) ys) (erased (Coercible (Shared) (List $ Pair (Ref Block b) $ Term) xs (Shared) (List $ Pair (Ref Block c) $ Term) ys) p))
  (let-match erased xs (Cons _ x rest)
    ((Nil _) (values (Nil _) (coercible-ctor (Shared) Nil (Pair (Ref Block b) $ Term) (Pair (Ref Block c) $ Term)))))
  (let ((erased rest2) (erased pr)) (finals-widen b c le rest))
  (let-match erased x (MkPair _ _ v ty))
  (let ((erased v2) (erased pv)) (ref-widen _ b c le v))
  (values (Cons _ (MkPair _ _ v2 ty) rest2) (coercible-ctor (Shared) Cons (Pair (Ref Block b) $ Term) (Pair (Ref Block c) $ Term) (coercible-ctor (Shared) MkPair (Ref Block b) (Ref Block c) (Term) (Term) pv (coercible-refl (Shared) ty)) pr)))

; The store with what holds its addresses, and the same put back; the caller keeps them consistent.
(def-fns _ $ (many env-store : (many (Env) e) -> (erased (Hist Block) hl) (many (Store Block hl) hp) (many (IdMap $ EInfo hl) en) (many (List $ Pair (Ref Block hl) $ Term) fi))
  (match many e _ ((MkEnv hs hp _ en _ _ _ _ _ _ _ fi _ _ _ _ _ _ _ _ _) (values hs hp en fi))))
(def-fns _ $ (many env-with-store : (many (Env) e) (erased (Hist Block) hl2) (many (Store Block hl2) hp2) (many (IdMap $ EInfo hl2) en2) (many (List $ Pair (Ref Block hl2) $ Term) fi2) -> (many (Env) r))
  (match many e _ ((MkEnv _ _ sc _ _ _ fr tb rp ob li _ lv st cl wa lt lo pr us hn) (MkEnv _ hp2 sc en2 _ _ fr tb rp ob li fi2 lv st cl wa lt lo pr us hn))))
(def-fns _ $ (many store-grow : (erased (Hist Block) hl) (erased (Hist Block) hl2) (erased (Suffix Block hl2 hl) le) (many (IdMap $ EInfo hl) en) (many (List $ Pair (Ref Block hl) $ Term) fi) -> (many (IdMap $ EInfo hl2) en2) (many (List $ Pair (Ref Block hl2) $ Term) fi2))
  (let ((erased en2) (erased pe)) (entries-widen hl hl2 le en))
  (let ((erased fi2) (erased pf)) (finals-widen hl hl2 le fi))
  (values (coerce en pe) (coerce fi pf)))

(def-fns _ $ (many entries-set-state : (erased (Hist Block) hl) (many (IdMap $ EInfo hl) en) (many (Nat) x) (many (State hl) st) -> (many (IdMap $ EInfo hl) r))
  (match many (idmap-get _ x en) _
    ((Miss _ _ _ _) (idmap-set _ x (MkEInfo _ (None _) (Many) st (BFalse) (BFalse) (None _)) en))
    ((Hit _ _ _ info _) (match many info _ ((MkEInfo _ n m _ mi me site) (idmap-set _ x (MkEInfo _ n m st mi me site) en))))))

; A closed block, one holding no reference, allocated as the value of [x]: a descriptor, a payload, the token.
(def-fns _ $ (many set-state-closed : (many (Env) e) (many (Nat) x) (many (Block (Ref Block (HEmpty Block))) b) -> (many (Env) r))
  (let ((erased hl) (many hp) (many en) (many fi)) $ env-store e)
  (let ((erased wb0) (erased pb0)) (block-widen _ _ (empty-suffix _ hl) b))
  (let ((erased hl2) (many hp2) (erased sf) (many a)) $ alloc Block _ hp (coerce b pb0))
  (let ((many en2) (many fi2)) $ store-grow _ _ sf en fi)
  (env-with-store e _ hp2 (entries-set-state _ en2 x $ SConst _ a) fi2))

(def-fns _ $ (many env-scope : (many (Env) e) -> (many (Scope) r))
  (match many e _ ((MkEnv _ _ sc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) sc)))
(def-fns _ $ (many env-entries : (many (Env) e) -> (erased (Hist Block) hs) (many (IdMap $ EInfo hs) r))
  (match many e _ ((MkEnv hs _ _ en _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (values hs en))))
(def-fns _ $ (many env-table : (many (Env) e) -> (erased (Nat) n) (erased (Facts n) f) (many (Nat) bnd) (many (Table n f bnd) tb))
  (match many e _ ((MkEnv _ _ _ _ nf ff fr tb _ _ _ _ _ _ _ _ _ _ _ _ _) (values nf ff fr tb))))
(def-fns _ $ (many env-fresh-bound : (many (Env) e) -> (many (Nat) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ fr _ _ _ _ _ _ _ _ _ _ _ _ _ _) fr)))
(def-fns _ $ (many env-facts : (many (Env) e) -> (erased (Nat) n) (many (Facts n) f))
  (let ((erased n) (erased f) (many bnd) (many tb)) $ env-table e)
  (match many tb _ ((MkTable n0 f0 _ _ _ _ _ _ _ _ _) (values n0 f0))))
(def-fns _ $ (many env-run-pos : (many (Env) e) -> (many (Bool) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ _ _ rp _ _ _ _ _ _ _ _ _ _ _ _) rp)))
(def-fns _ $ (many env-objects : (many (Env) e) -> (many (List $ Nat) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ _ _ _ ob _ _ _ _ _ _ _ _ _ _ _) ob)))
(def-fns _ $ (many env-opens : (many (Env) e) -> (many (List $ Opened) r))
  (let ((erased n) (erased f) (many bnd) (many tb)) $ env-table e)
  (let ((many os) (many ix) (many tc)) $ table-opens _ _ bnd tb)
  os)
(def-fns _ $ (many env-index : (many (Env) e) -> (many (IdMap $ List $ Nat) r))
  (let ((erased n) (erased f) (many bnd) (many tb)) $ env-table e)
  (let ((many os) (many ix) (many tc)) $ table-opens _ _ bnd tb)
  ix)
(def-fns _ $ (many env-touched : (many (Env) e) -> (many (List $ Nat) r))
  (let ((erased n) (erased f) (many bnd) (many tb)) $ env-table e)
  (let ((many os) (many ix) (many tc)) $ table-opens _ _ bnd tb)
  tc)
(def-fns _ $ (many env-open : (many (Env) e) (many (Nat) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa lt lo pr us hn) (MkEnv _ hp sc en _ _ fr (table-open _ _ fr tb x) rp ob li fi lv st cl wa lt lo pr us hn))))
(def-fns _ $ (many env-unopen : (many (Env) e) (many (Nat) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa lt lo pr us hn) (MkEnv _ hp sc en _ _ fr (table-unopen _ _ fr tb x) rp ob li fi lv st cl wa lt lo pr us hn))))
(def-fns _ $ (many env-settled : (many (Env) e) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa lt lo pr us hn) (MkEnv _ hp sc en _ _ fr (table-settled _ _ fr tb) rp ob li fi lv st cl wa lt lo pr us hn))))
(def-fns _ $ (many env-literals : (many (Env) e) -> (many (NameMap $ Nat) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ _ _ _ _ li _ _ _ _ _ _ _ _ _ _) li)))

(def-fns _ $ (many env-level : (many (Env) e) -> (many (Maybe $ Nat) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ _ _ _ _ _ _ lv _ _ _ _ _ _ _ _) lv)))
(def-fns _ $ (many env-subterms : (many (Env) e) -> (many (List $ Nat) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ _ _ _ _ _ _ _ st _ _ _ _ _ _ _) st)))
(def-fns _ $ (many env-claimed : (many (Env) e) -> (many (List $ Pair (String) $ Loc) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ cl _ _ _ _ _ _) cl)))
(def-fns _ $ (many said-silenced : (subterm many (List $ Said) ss) -> (many (List $ Nat) r))
  (match many ss _
    ((Nil _) (Nil _))
    ((Cons _ x rest) (match many x _ ((SaidSilenced k) (Cons _ k $ notail $ said-silenced rest)) (else (tail $ said-silenced rest))))))
(def-fns _ $ (many said-without-silenced : (subterm many (List $ Said) ss) -> (many (List $ Said) r))
  (match many ss _
    ((Nil _) ss)
    ((Cons _ x rest) (match many x _ ((SaidSilenced _) (tail $ said-without-silenced rest)) (else (Cons _ x $ notail $ said-without-silenced rest))))))
(def-fns _ $ (many env-silenced : (many (Env) e) -> (many (List $ Nat) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ wa _ _ _ _ _) (said-silenced wa))))
(def-fns _ $ (many env-set-said : (many (Env) e) (many (List $ Said) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl _ lt lo pr us hn) (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl x lt lo pr us hn))))
(def-fns _ $ (many env-said : (many (Env) e) -> (many (List $ Said) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ wa _ _ _ _ _) wa)))
(def-fns _ $ (many said-failed : (subterm many (List $ Said) ss) -> (many (Bool) r))
  (let-match many ss (Cons _ x rest) ((Nil _) (BFalse)))
  (match many x _ ((SaidError _) (BTrue)) (else (tail $ said-failed rest))))
(def-fns _ $ (many env-failed : (many (Env) e) -> (many (Bool) r))
  (said-failed $ env-said e))
(def-fns _ $ (many env-lits : (many (Env) e) -> (many (List $ LitEntry) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lt _ _ _ _) lt)))
(def-fns _ $ (many env-enter-body : (many (Env) e) (many (Nat) level) (many (List $ Nat) subterms) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb _ ob li fi _ _ cl wa lt lo pr us hn) (MkEnv _ hp sc en _ _ fr tb (BFalse) ob li fi (Some _ level) subterms cl wa lt lo pr us hn))))
; Where a claimed name was bound, which the second claim's note names.
(def-fns _ $ (many claimed-at : (subterm many (List $ Pair (String) $ Loc) cl) (many (String) name) ->
    (many (Maybe $ Loc) r))
  (let-match many cl (Cons _ p rest) ((Nil _) (None _)))
  (let-match many p (MkPair _ _ n l))
  (match many (str-eq n name) (((Maybe $ Loc) _))
    ((BTrue) (Some _ l))
    ((BFalse) (tail $ claimed-at rest name))))
(def-fns _ $ (many env-claim : (many (Env) e) (many (String) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa lt lo pr us hn) (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st (Cons _ (MkPair _ _ x lo) cl) wa lt lo pr us hn))))
(def-fns _ $ (many env-warn : (many (Env) e) (many (String) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa lt lo pr us hn) (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl (Cons _ (SaidWarning x) wa) lt lo pr us hn))))
(def-fns _ $ (many env-warn-all : (many (Env) e) (subterm many (List $ String) xs) -> (many (Env) r))
  (match many xs _
    ((Nil _) e)
    ((Cons _ x rest) (tail $ env-warn-all (env-warn e x) rest))))
(def-fns _ $ (many env-push-lit : (many (Env) e) (many (Nat) x) (many (Maybe $ Nat) proof) (many (String) spelling) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa lt lo pr us hn) (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa (Cons _ (MkLitEntry x proof spelling) lt) lo pr us hn))))
(def-fns _ $ (many env-set-scope : (many (Env) e) (many (Scope) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp _ en _ _ fr tb rp ob li fi lv st cl wa lt lo pr us hn) (MkEnv _ hp x en _ _ fr tb rp ob li fi lv st cl wa lt lo pr us hn))))
(def-fns _ $ (many env-set-table : (many (Env) e) (erased (Nat) n) (erased (Facts n) f) (many (Nat) c) (many (Table n f c) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ _ _ rp ob li fi lv st cl wa lt lo pr us hn) (MkEnv _ hp sc en _ _ c x rp ob li fi lv st cl wa lt lo pr us hn))))
(def-fns _ $ (many env-set-run-pos : (many (Env) e) (many (Bool) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb _ ob li fi lv st cl wa lt lo pr us hn) (MkEnv _ hp sc en _ _ fr tb x ob li fi lv st cl wa lt lo pr us hn))))
(def-fns _ $ (many env-set-literals : (many (Env) e) (many (NameMap $ Nat) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob _ fi lv st cl wa lt lo pr us hn) (MkEnv _ hp sc en _ _ fr tb rp ob x fi lv st cl wa lt lo pr us hn))))
(def-fns _ $ (many env-prelude : (many (Env) e) -> (many (Scope) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pr _ _) pr)))
; The scope the prelude left, which generated forms elaborate in (lib/elab.ml's in_prelude).
(def-fns _ $ (many env-set-prelude : (many (Env) e) (many (Scope) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa lt lo _ us hn) (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa lt lo x us hn))))
(def-fns _ $ (many env-help : (many (Env) e) -> (many (List $ String) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn) hn)))
(def-fns _ $ (many env-set-help : (many (Env) e) (many (String) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa lt lo pr us _) (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa lt lo pr us $ split-on x 10))))
; The next id, above every key of the table.
(def-fns _ $ (many env-fresh-id : (many (Env) e) -> (many (Env) r) (many (Nat) x))
  (let-match many e (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa lt lo pr us hn))
  (let ((many x) (erased ltp)) (values (Succ fr) (lt-succ fr)))
  (values (MkEnv _ hp sc en _ _ x (table-weaken _ _ _ _ tb $ lt-weaken fr x ltp) rp ob li fi lv st cl wa lt lo pr us hn) x))
(def-fns _ $ (many env-loc : (many (Env) e) -> (many (Loc) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo _ _ _) lo)))
(def-fns _ $ (many env-at-loc : (many (Env) e) (many (Loc) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa lt _ pr us hn) (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa lt x pr us hn))))
; A position in the file the environment is reading, as a Loc a message can point at.
(def-fns _ $ (many loc-in : (many (Env) e) (many (Pos) pos) -> (many (Loc) l))
  (match many (env-loc e) _ ((MkLoc f _) (MkLoc f pos))))
(def-fns _ $ (many env-at : (many (Env) e) (many (Pos) pos) -> (many (Env) r))
  (match many (env-loc e) _ ((MkLoc f _) (env-at-loc e $ MkLoc f pos))))
; Restores [outer]'s position in [inner], on leaving the form that set it.
(def-fns _ $ (many env-back : (many (Env) outer) (many (Env) inner) -> (many (Env) r))
  (env-at-loc inner $ env-loc outer))
; A message with the file and position in force, in the reference's format.
(def-fns _ $ (many located : (many (Env) e) (many (String) kind) (many (String) x) -> (many (String) r))
  (let-match many (env-loc e) (MkLoc f p))
  (match many p (((String) _))
    ((MkPos l c)
      (str-cat3 f ":" $ str-cat3 (nat-str l) ":" $ str-cat3 (nat-str c) kind x))))
; Where a position is, in the reference's format, or nothing for none (lib/reader.ml's where).
(def-fns _ $ (many loc-str : (many (Maybe $ Loc) site) -> (many (String) r))
  (let-match many site (Some _ l) ((None _) ""))
  (let-match many l (MkLoc f p))
  (let-match many p (MkPos ln c))
  (match many ln _
    ((Zero) "")
    (else (str-cat3 f ":" $ str-cat3 (nat-str ln) ":" $ nat-str c))))

; An unsolved meta is printed as a marker holding its id and where its `_` was written (name-of), so that the
; message it lands in can number the metas it mentions, in order, and name each one's `_` in a note of its own
; (lib/env.ml's metas_in).
(def-adts $ (MsgMeta : -> Type)
  enum
  (many MkMsgMeta : (many (String) id) (many (Nat) n) (many (String) where) -> (MsgMeta)))

(def-fns _ $ (many meta-find : (subterm many (List $ MsgMeta) ms) (many (String) id) -> (many (Maybe $ Nat) n))
  (match many ms _
    ((Nil _) (None _))
    ((Cons _ m rest) (match many m _ ((MkMsgMeta i n _) (match many (str-eq i id) _ ((BTrue) (Some _ n)) ((BFalse) (tail (meta-find rest id)))))))))

(def-fns _ $ (many meta-number : (many (String) id) (many (String) where) (many (List $ MsgMeta) seen) -> (many (Nat) n) (many (List $ MsgMeta) r))
  (let-match many (meta-find seen id) (None _) ((Some _ n) (values n seen)))
  (let ((many n)) $ Succ $ list-length _ seen)
  (let ((many seen2) (erased _)) $ list-append _ seen $ Cons _ (MkMsgMeta id n where) $ Nil _)
  (values n seen2))

; [mode] is 0 in the text, 1 in a marker's id and 2 in its position.
(def-fns _ $ (many meta-scan : (subterm many (String) s) (many (Nat) mode) (many (Rope) out) (many (Rope) id) (many (Rope) where) (many (List $ MsgMeta) seen) ->
    (many (Rope) r) (many (List $ MsgMeta) seen2))
  (let-match many s (SCons c rest) ((SNil) (values out seen)))
  (let-match many (char-is c 1) (BFalse)
    ((BTrue) (match many mode _ ((Zero) (tail (meta-scan rest 1 out (REmpty) (REmpty) seen))) (else (tail (meta-scan rest 2 out id where seen))))))
  (match many (char-is c 2) _
    ((BTrue)
      (let ((many n) (many seen2)) $ meta-number (rope-str id) (rope-str where) seen)
      (tail (meta-scan rest 0 (rcat3 out (RStr "?") $ RStr $ nat-str n) (REmpty) (REmpty) seen2)))
    ((BFalse)
      (let-match many mode (Succ m) ((Zero) (tail (meta-scan rest mode (rcat out $ RChar c) id where seen))))
      (match many m _
        ((Zero) (tail (meta-scan rest mode out (rcat id $ RChar c) where seen)))
        (else (tail (meta-scan rest mode out id (rcat where $ RChar c) seen)))))))

(def-fns _ $ (many meta-notes : (many (Env) e) (subterm many (List $ MsgMeta) ms) -> (many (List $ String) r))
  (let-match many ms (Cons _ m rest) ((Nil _) (Nil _)))
  (let-match many m (MkMsgMeta _ n where))
  (Cons _ (match many (str-is-empty where) (((String) _))
            ((BTrue) (located e ": note: " $ str-cat3 "`?" (nat-str n) "` is a `_` the elaborator supplied, not one written in the source"))
            ((BFalse) (str-cat3 where ": note: " $ str-cat3 "`?" (nat-str n) "` is the `_` written here")))
    $ notail $ meta-notes e rest))

; A message with its metas numbered, and the notes naming where each one's `_` was written.
(def-fns _ $ (many metas-in : (many (Env) e) (many (String) x) -> (many (String) r) (many (List $ String) notes))
  (let ((many out) (many seen)) $ meta-scan x 0 (REmpty) (REmpty) (REmpty) (Nil _))
  (values (rope-str out) (meta-notes e seen)))

(def-fns _ $ (many note-lines : (many (Env) e) (subterm many (List $ Pair (Loc) $ String) notes) (many (List $ String) rest) -> (many (List $ String) r))
  (let-match many notes (Cons _ n more) ((Nil _) rest))
  (let-match many n (MkPair _ _ l m))
  (Cons _ (located (env-at-loc e l) ": note: " m) $ notail $ note-lines e more rest))
(def-fns _ $ (many diagnostic : (many (Env) e) (many (String) kind) (many (List $ Pair (Loc) $ String) notes) (many (String) x) -> (many (String) r))
  (let ((many msg) (many mnotes)) $ metas-in e x)
  (join-strs (Cons _ (located e kind msg) $ note-lines e notes mnotes) "\n"))
(def-fns _ $ (many env-fail : (many (Env) e) (many (String) text) -> (many (Env) r))
  (env-set-said e $ Cons _ (SaidError text) $ env-said e))
(def-fns _ $ (many env-error-with : (many (Env) e) (many (List $ Pair (Loc) $ String) notes) (many (String) x) -> (many (Env) r))
  (env-fail e $ diagnostic e ": error: " notes x))
(def-fns _ $ (many env-error : (many (Env) e) (many (String) x) -> (many (Env) r))
  (env-error-with e (Nil _) x))
; An error about two places names both: the note is a second location, written under the message as a
; warning's note is, rather than described in the message's prose (ASSUMPTIONS 194).
(def-fns _ $ (many env-warn-with : (many (Env) e) (many (Loc) l) (many (List $ Pair (Loc) $ String) notes) (many (String) x) -> (many (Env) r))
  (env-warn e $ diagnostic (env-at-loc e l) ": warning: " notes x))
(def-fns _ $ (many env-warn-at : (many (Env) e) (many (Loc) l) (many (String) x) -> (many (Env) r))
  (env-warn-with e l (Nil _) x))

; The names of the entries minted after [stop], up to [x], dropped (lib/env.ml's hide).
(def-fns _ $ (many entries-anonymize : (erased (Hist Block) hs) (many (IdMap $ EInfo hs) en) (subterm many (Nat) x) (many (Nat) stop) -> (many (IdMap $ EInfo hs) r))
  (let-match many x (Succ p) ((Zero) en))
  (let-match many (nat-lt stop x) (BTrue) ((BFalse) en))
  (let ((many (IdMap $ EInfo hs) en2))
    (match many (idmap-get _ x en) _
      ((Miss _ _ _ _) en)
      ((Hit _ _ _ info _) (match many info (((IdMap $ EInfo hs) _)) ((MkEInfo _ _ m st mi me site) (idmap-set _ x (MkEInfo _ (None _) m st mi me site) en))))))
  (tail $ entries-anonymize _ en2 p stop))

; Leaves a telescope: keeps [inner]'s facts, opens, store, literals, fresh ids, finals and errors, restoring
; [outer]'s scope and objects; run position is [outer]'s.
(def-fns _ $ (many unique-restore : (many (UniqueState) outer) (many (UniqueState) inner) -> (many (UniqueState) r))
  (match many outer _ ((MkUniqueState _ _ caps ue ie sig _ _ _ _)
    (match many inner _ ((MkUniqueState loc2 uses2 _ _ _ _ words2 temp2 wd2 al2)
      (MkUniqueState loc2 uses2 caps ue ie sig words2 temp2 wd2 al2))))))

(def-fns _ $ (many env-restore : (many (Env) outer) (many (Env) inner) -> (many (Env) r))
  (let-match many outer (MkEnv _ _ sc _ _ _ _ _ rp ob _ _ lv st _ _ _ lo pr us hn))
  (match many inner _
    ((MkEnv _ hp2 _ en2 _ _ fr2 tb2 _ _ li2 fi2 _ _ cl2 wa2 lt2 _ _ us2 _) (MkEnv _ hp2 sc en2 _ _ fr2 tb2 rp ob li2 fi2 lv st cl2 wa2 lt2 lo pr (unique-restore us us2) hn))))

; Leaves a let's right-hand side: as env-restore, but the objects stay [inner]'s and the entries it added
; keep their ids in scope with their names dropped (section 16, lib/env.ml's hide).
(def-fns _ $ (many hide-words : (subterm many (List $ Nat) words) (many (List $ Nat) temp) (many (Nat) bound) -> (many (List $ Nat) r))
  (match many words _ ((Nil _) words) ((Cons _ x rest)
    (match many (nat-lt bound x) _
      ((BFalse) words)
      ((BTrue) (match many (list-mem-bin temp x) _ ((BTrue) (tail $ hide-words rest temp bound)) ((BFalse) (Cons _ x $ notail $ hide-words rest temp bound))))))))
(def-fns _ $ (many unique-hide : (many (Nat) bound) (many (UniqueState) state) -> (many (UniqueState) r))
  (match many state _ ((MkUniqueState loc uses caps ue ie sig words temp wd al)
    (MkUniqueState loc uses caps ue ie sig (hide-words words temp bound) temp wd al))))

(def-fns _ $ (many env-hide : (many (Env) outer) (many (Env) inner) -> (many (Env) r))
  (let-match many outer (MkEnv _ _ sc _ _ _ fr _ rp _ _ _ lv st _ _ _ lo pr us hn))
  (match many inner _
    ((MkEnv _ hp2 sc2 en2 _ _ fr2 tb2 _ ob2 li2 fi2 _ _ cl2 wa2 lt2 _ _ us2 _)
      (MkEnv _ hp2 (MkScope (scope-names sc) $ scope-ids sc2) (entries-anonymize _ en2 fr2 fr) _ _ fr2 tb2 rp ob2 li2 fi2 lv st cl2 wa2 lt2 lo pr (unique-hide fr (unique-restore us us2)) hn))))

; Leaves a match branch or a body: the entries (whose names the extractor prints), the store, the id
; supply, finals and errors survive; scope, facts, opens and objects are the outer ones again.
(def-fns _ $ (many env-discard : (many (Env) outer) (many (Env) inner) -> (many (Env) r))
  (let-match many outer (MkEnv _ _ sc _ nf ff fr tb rp ob li _ lv st _ _ _ lo pr us hn))
  (let-match many inner (MkEnv _ hp2 _ en2 _ _ fr2 _ _ _ _ fi2 _ _ cl2 wa2 lt2 _ _ _ _))
  (match many (nat-cmp fr fr2) _
    ((CLt _ _ _ _ p) (MkEnv _ hp2 sc en2 _ _ fr2 (table-weaken _ _ _ _ tb $ lt-weaken fr fr2 p) rp ob li fi2 lv st cl2 wa2 lt2 lo pr us hn)) (else (MkEnv _ hp2 sc en2 nf ff fr tb rp ob li fi2 lv st cl2 wa2 lt2 lo pr us hn))))

(def-fns _ $ (many entry : (many (Env) env) (many (Nat) x) -> (erased (Hist Block) hs) (many (EInfo hs) r))
  (let ((erased hs) (many en)) $ env-entries env)
  (match many (idmap-get _ x en) _
    ((Miss _ _ _ _) (values hs $ MkEInfo _ (None _) (Many) (SDyn _) (BFalse) (BFalse) (None _)))
    ((Hit _ _ _ e _) (values hs e))))

(def-fns _ $ (many env-entry-name : (many (Env) env) (many (Nat) x) -> (many (Maybe $ String) r))
  (let ((erased hs) (many e)) $ entry env x)
  (match many e _ ((MkEInfo _ n _ _ _ _ _) n)))

(def-fns _ $ (many env-entry-at : (many (Env) env) (many (Nat) x) -> (many (Maybe $ Loc) r))
  (let ((erased hs) (many e)) $ entry env x)
  (match many e _ ((MkEInfo _ _ _ _ _ _ site) site)))

(def-fns _ $ (many entry-mult-of : (many (Env) env) (many (Nat) x) -> (many (Mult) r))
  (let ((erased hs) (many e)) $ entry env x)
  (match many e _ ((MkEInfo _ _ m _ _ _ _) m)))

(def-fns _ $ (many entry-state : (many (Env) env) (many (Nat) x) -> (erased (Hist Block) hs) (many (State hs) r))
  (let ((erased hs) (many e)) $ entry env x)
  (match many e _ ((MkEInfo _ _ _ s _ _ _) (values hs s))))

(def-fns _ $ (many is-const : (many (Env) env) (many (Nat) x) -> (many (Bool) r))
  (let ((erased hs) (many s)) $ entry-state env x)
  (match many s _ ((SConst _ _) (BTrue)) ((SDyn _) (BFalse))))

(def-fns _ $ (many entry-minted : (many (Env) env) (many (Nat) x) -> (many (Bool) r))
  (let ((erased hs) (many e)) $ entry env x)
  (match many e _ ((MkEInfo _ _ _ _ mi _ _) mi)))

(def-fns _ $ (many is-meta : (many (Env) env) (many (Nat) x) -> (many (Bool) r))
  (let ((erased hs) (many e)) $ entry env x)
  (match many e _ ((MkEInfo _ _ _ _ _ me _) me)))

(def-fns _ $ (many mark-minted : (many (Env) e) (many (Nat) x) -> (many (Env) r))
  (let-match many e (MkEnv hs hp sc en _ _ fr tb rp ob li fi lv st cl wa lt lo pr us hn))
  (let ((many (EInfo hs) info))
    (match many (idmap-get _ x en) _
      ((Miss _ _ _ _) (MkEInfo _ (None _) (Erased) (SDyn _) (BTrue) (BFalse) (None _)))
      ((Hit _ _ _ i _) (match many i (((EInfo hs) _)) ((MkEInfo _ n m s _ me site) (MkEInfo _ n m s (BTrue) me site))))))
  (MkEnv _ hp sc (idmap-set _ x info en) _ _ fr tb rp ob li fi lv st cl wa lt lo pr us hn))

; An entry given a name for display only, the scope untouched.
(def-fns _ $ (many env-name-entry : (many (Env) e) (many (Nat) x) (many (String) n) -> (many (Env) r))
  (let-match many e (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa lt lo pr us hn))
  (let-match many (idmap-get _ x en) (Hit _ _ _ i _) ((Miss _ _ _ _) e))
  (match many i _
    ((MkEInfo _ _ m s mi me site) (MkEnv _ hp sc (idmap-set _ x (MkEInfo _ (Some _ n) m s mi me site) en) _ _ fr tb rp ob li fi lv st cl wa lt lo pr us hn))))

(def-fns _ $ (many name-of : (many (Env) env) (many (Nat) x) -> (many (String) r))
  (let ((erased hs) (many e)) $ entry env x)
  (let-match many e (MkEInfo _ n _ _ _ me site))
  (let-match many n (None _) ((Some _ s2) s2))
  (match many me _
    ((BTrue) (rope-str $ rcat4 (RChar #\x01) (RStr $ nat-str x) (RChar #\x01) $ rcat (RStr $ loc-str site) (RChar #\x02)))
    ((BFalse) (str-cat "_" $ nat-str x))))

; A name or term in a message is set off in backticks; a literal already reads as one and is left bare.
(def-fns _ $ (many tick : (many (String) s) -> (many (String) r))
  (match many (or (is-literal-name s) $ match many s (((Bool) _)) ((SNil) (BFalse)) ((SCons c _) (char-is c 34))) _
    ((BTrue) s)
    ((BFalse) (str-cat3 "`" s "`"))))

(def-fns _ $ (many qname : (many (Env) env) (many (Nat) x) -> (many (String) r))
  (tick $ name-of env x))

; The block a Const entry's value is, read through its reference.
(def-fns _ $ (many env-block : (many (Env) e) (many (Nat) x) -> (erased (Hist Block) a) (many (Maybe $ Block (Ref Block a)) r))
  (let ((erased hs) (many hp) (many en) (many fi)) $ env-store e)
  (let-match many (idmap-get _ x en) (Hit _ _ _ info _) ((Miss _ _ _ _) (values (HEmpty Block) $ None _)))
  (let-match many info (MkEInfo _ _ _ s _ _ _))
  (let-match many s (SConst _ v) ((SDyn _) (values (HEmpty Block) $ None _)))
  (let ((erased a) (many b) (erased sf)) (store-read Block _ hp v))
  (values a $ Some _ b))

; Forwards [y]'s state to [x] (section 9's state-forwarding let).
(def-fns _ $ (many forward-state : (many (Env) e) (many (Nat) x) (many (Nat) y) -> (many (Env) r))
  (let-match many e (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa lt lo pr us hn))
  (let-match many (idmap-get _ y en) (Hit _ _ _ info _) ((Miss _ _ _ _) e))
  (match many info _
    ((MkEInfo _ _ _ s _ _ _) (MkEnv _ hp sc (entries-set-state _ en x s) _ _ fr tb rp ob li fi lv st cl wa lt lo pr us hn))))

(def-fns _ $ (many fact-at : (many (Env) env) (many (Nat) x) -> (many (Term) ty) (many (Maybe $ Term) rule))
  (let ((erased n) (erased f) (many bnd) (many tb)) $ env-table env)
  (fact-in _ _ bnd tb x))

(def-fns _ $ (many env-unique : (many (Env) env) -> (many (UniqueState) r))
  (match many env _ ((MkEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ us hn) us)))
(def-fns _ $ (many env-set-unique : (many (Env) env) (many (UniqueState) state) -> (many (Env) r))
  (match many env _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa lt lo pr _ hn) (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa lt lo pr state hn))))
(def-fns _ $ (many env-locations : (many (Env) env) -> (many (IdMap $ Nat) r))
  (match many (env-unique env) _ ((MkUniqueState locations _ _ _ _ _ _ _ _ al) locations)))
(def-fns _ $ (many env-set-locations : (many (Env) env) (many (IdMap $ Nat) x) -> (many (Env) r))
  (match many (env-unique env) _ ((MkUniqueState _ uses captures ue ie sig words temp wd al) (env-set-unique env (MkUniqueState x uses captures ue ie sig words temp wd al)))))
(def-fns _ $ (many env-uses : (many (Env) env) -> (many (IdMap $ Use) r))
  (match many (env-unique env) _ ((MkUniqueState _ uses _ _ _ _ _ _ _ al) uses)))
(def-fns _ $ (many env-set-uses : (many (Env) env) (many (IdMap $ Use) x) -> (many (Env) r))
  (match many (env-unique env) _ ((MkUniqueState locations _ captures ue ie sig words temp wd al) (env-set-unique env (MkUniqueState locations x captures ue ie sig words temp wd al)))))
(def-fns _ $ (many env-captures : (many (Env) env) -> (many (List $ Nat) r))
  (match many (env-unique env) _ ((MkUniqueState _ _ captures _ _ _ _ _ _ al) captures)))
(def-fns _ $ (many env-set-captures : (many (Env) env) (many (List $ Nat) x) -> (many (Env) r))
  (match many (env-unique env) _ ((MkUniqueState locations uses _ ue ie sig words temp wd al) (env-set-unique env (MkUniqueState locations uses x ue ie sig words temp wd al)))))
(def-fns _ $ (many env-usage-erased : (many (Env) env) -> (many (Bool) r))
  (match many (env-unique env) _ ((MkUniqueState _ _ _ ue _ _ _ _ _ al) ue)))
(def-fns _ $ (many env-set-usage-erased : (many (Env) env) (many (Bool) x) -> (many (Env) r))
  (match many (env-unique env) _ ((MkUniqueState locations uses captures _ ie sig words temp wd al) (env-set-unique env (MkUniqueState locations uses captures x ie sig words temp wd al)))))
(def-fns _ $ (many env-in-extern : (many (Env) env) -> (many (Bool) r))
  (match many (env-unique env) _ ((MkUniqueState _ _ _ _ ie _ _ _ _ al) ie)))
(def-fns _ $ (many env-set-in-extern : (many (Env) env) (many (Bool) x) -> (many (Env) r))
  (match many (env-unique env) _ ((MkUniqueState locations uses captures ue _ sig words temp wd al) (env-set-unique env (MkUniqueState locations uses captures ue x sig words temp wd al)))))
(def-fns _ $ (many env-signature : (many (Env) env) -> (many (List $ Nat) r))
  (match many (env-unique env) _ ((MkUniqueState _ _ _ _ _ sig _ _ _ al) sig)))
(def-fns _ $ (many env-set-signature : (many (Env) env) (many (List $ Nat) x) -> (many (Env) r))
  (match many (env-unique env) _ ((MkUniqueState locations uses captures ue ie _ words temp wd al) (env-set-unique env (MkUniqueState locations uses captures ue ie x words temp wd al)))))
(def-fns _ $ (many env-words : (many (Env) env) -> (many (List $ Nat) r))
  (match many (env-unique env) _ ((MkUniqueState _ _ _ _ _ _ words _ _ al) words)))
(def-fns _ $ (many env-set-words : (many (Env) env) (many (List $ Nat) x) -> (many (Env) r))
  (match many (env-unique env) _ ((MkUniqueState locations uses captures ue ie sig _ temp wd al) (env-set-unique env (MkUniqueState locations uses captures ue ie sig x temp wd al)))))
(def-fns _ $ (many env-temporary : (many (Env) env) -> (many (List $ Nat) r))
  (match many (env-unique env) _ ((MkUniqueState _ _ _ _ _ _ _ temp _ al) temp)))
(def-fns _ $ (many env-set-temporary : (many (Env) env) (many (List $ Nat) x) -> (many (Env) r))
  (match many (env-unique env) _ ((MkUniqueState locations uses captures ue ie sig words _ wd al) (env-set-unique env (MkUniqueState locations uses captures ue ie sig words x wd al)))))

(def-fns _ $ (many env-aliases : (many (Env) env) -> (many (IdMap $ Nat) r))
  (match many (env-unique env) _ ((MkUniqueState _ _ _ _ _ _ _ _ _ al) al)))
(def-fns _ $ (many env-set-aliases : (many (Env) env) (many (IdMap $ Nat) x) -> (many (Env) r))
  (match many (env-unique env) _ ((MkUniqueState locations uses captures ue ie sig words temp wd _) (env-set-unique env (MkUniqueState locations uses captures ue ie sig words temp wd x)))))

(def-fns _ $ (many env-pragmas : (many (Env) env) -> (many (Pragmas) r))
  (match many (env-unique env) _ ((MkUniqueState _ _ _ _ _ _ _ _ pg al) pg)))
(def-fns _ $ (many env-set-pragmas : (many (Env) env) (many (Pragmas) x) -> (many (Env) r))
  (match many (env-unique env) _ ((MkUniqueState locations uses captures ue ie sig words temp _ al) (env-set-unique env (MkUniqueState locations uses captures ue ie sig words temp x al)))))
(def-fns _ $ (many env-warned : (many (Env) env) -> (many (List $ Warned) r))
  (match many (env-pragmas env) _ ((MkPragmas ws _) ws)))
(def-fns _ $ (many env-set-warned : (many (Env) env) (many (List $ Warned) x) -> (many (Env) r))
  (match many (env-pragmas env) _ ((MkPragmas _ rs) (env-set-pragmas env $ MkPragmas x rs))))
(def-fns _ $ (many env-regions : (many (Env) env) -> (many (List $ Region) r))
  (match many (env-pragmas env) _ ((MkPragmas _ rs) rs)))
(def-fns _ $ (many env-set-regions : (many (Env) env) (many (List $ Region) x) -> (many (Env) r))
  (match many (env-pragmas env) _ ((MkPragmas ws _) (env-set-pragmas env $ MkPragmas ws x))))

(def-fns _ $ (many entry-word : (many (Env) env) (many (Nat) x) -> (many (Bool) r))
  (list-mem-bin (env-words env) x))
(def-fns _ $ (many insert-desc : (many (Nat) x) (subterm many (List $ Nat) xs) -> (many (List $ Nat) r))
  (match many xs _
    ((Nil _) (Cons _ x xs))
    ((Cons _ y rest) (match many (nat-lt y x) _ ((BTrue) (Cons _ x xs)) ((BFalse) (Cons _ y $ notail $ insert-desc x rest))))))
(def-fns _ $ (many mark-word : (many (Env) env) (many (Nat) x) (many (Bool) temporary) -> (many (Env) r))
  (let ((many env2)) (env-set-words env $ insert-desc x $ env-words env))
  (match many temporary _ ((BFalse) env2) ((BTrue) (env-set-temporary env2 $ insert-desc x $ env-temporary env2))))
(def-fns _ $ (many location-root : (subterm many (Nat) x) (many (IdMap $ Nat) locations) -> (many (Nat) r))
  (let-match many (idmap-get _ x locations) (Hit _ _ _ y _) ((Miss _ _ _ _) x))
  (match many (nat-cmp y x) _
    ((CLt _ _ _ _ lt) (tail $ location-root (subterm (lt-subterm y x lt)) y locations))
    (else x)))
(def-fns _ $ (many location-term : (many (Env) env) (many (Term) t) -> (many (Term) r))
  (let ((many resolved))
    (match many t (((Term) _))
      ((TVar x) (match many (is-meta env x) _ ((BFalse) t) ((BTrue)
        (let ((erased n) (erased f) (many bnd) (many tb)) (env-table env))
        (let ((many out) (erased pf)) (canon-in _ _ bnd tb t)) out)))
      (else t)))
  (match many resolved _ ((TVar x) (TVar $ location-root x $ env-locations env)) (else resolved)))
(def-fns _ $ (many location-same : (many (Term) a) (many (Term) b) -> (many (Bool) r))
  (match many a _
    ((TVar x) (match many b _ ((TVar y) (nat-eq x y)) (else (BFalse))))
    ((TBound x) (match many b _ ((TBound y) (nat-eq x y)) (else (BFalse))))
    (else (BFalse))))
(def-fns _ $ (many at-equal : (many (Env) env) (many (Term) a) (many (Term) b) -> (many (Bool) r))
  (location-same (location-term env a) $ location-term env b))
(def-fns _ $ (many at-merge : (many (Env) env) (many (Term) a) (many (Term) b) -> (many (Env) r))
  (let ((many a2)) (location-term env a))
  (let ((many b2)) (location-term env b))
  (let-match many (location-same a2 b2) (BFalse) ((BTrue) env))
  (let-match many a2 (TVar x) (else (env-error env "locations must be variables")))
  (let-match many b2 (TVar y) (else (env-error env "locations must be variables")))
  (match many (nat-cmp x y) _
    ((CLt _ _ _ _ _) (env-set-locations env $ idmap-set _ y x $ env-locations env))
    (else (env-set-locations env $ idmap-set _ x y $ env-locations env))))
(def-fns _ $ (many use-max : (many (Use) a) (many (Use) b) -> (many (Use) r))
  (match many a _ ((UseConsumed _) a) ((UseShared _) b)))
(def-fns _ $ (many use-insert : (many (IdMap $ Use) uses) (many (Nat) x) (many (Use) state) -> (many (IdMap $ Use) r))
  (match many (idmap-get _ x uses) _
    ((Miss _ _ _ _) (idmap-set _ x state uses))
    ((Hit _ _ _ old _) (idmap-set _ x (use-max old state) uses))))
(def-fns _ $ (many uses-join-at : (subterm many (IdMap $ Use) a) (many (IdMap $ Use) b) (many (Nat) offset) (many (Nat) stride) -> (many (IdMap $ Use) r))
  (let-match many a (MNode _ here one two) ((MEmpty _) b))
  (let ((many b1)) (match many here (((IdMap $ Use) _)) ((None _) b) ((Some _ state) (use-insert b offset state))))
  (let ((many stride2)) (nat-add stride stride))
  (tail $ uses-join-at two (notail $ uses-join-at one b1 (nat-add offset stride) stride2) (nat-add offset stride2) stride2))
(def-fns _ $ (many uses-join : (many (IdMap $ Use) a) (many (IdMap $ Use) b) -> (many (IdMap $ Use) r))
  (uses-join-at a b 0 1))
(def-fns _ $ (many misuse : (many (Mult) demand) (many (Mult) supply) -> (many (Maybe $ String) r))
  (match many supply _
    ((Erased) (match many (mult-is-many demand) _ ((BTrue) (Some _ "used in a non-erased position")) ((BFalse) (None _))))
    ((Many) (match many demand _ ((Once) (Some _ "used at unique")) (else (None _))))
    ((Once) (match many demand _ ((Many) (Some _ "used at many without `share`")) (else (None _))))))

(def-fns _ $ (many check-mult : (many (Env) env) (many (List $ Pair (Loc) $ String) notes) (many (String) what) (many (Mult) demand) (many (Mult) supply) -> (many (Env) r) (many (Bool) bad))
  (let-match many (env-usage-erased env) (BFalse) ((BTrue) (values env $ BFalse)))
  (let-match many (misuse demand supply) (Some _ how) ((None _) (values env $ BFalse)))
  (values (env-error-with env notes $ str-cat3 what ", " how) $ BTrue))

(def-fns _ $ (many declared : (many (Env) env) (many (String) how) (many (Nat) x) -> (many (List $ Pair (Loc) $ String) r))
  (match many (env-entry-at env x) _
    ((None _) (Nil _))
    ((Some _ l) (Cons _ (MkPair _ _ l $ str-cat3 (qname env x) " is declared" $ str-cat how " here") $ Nil _))))

(def-fns _ $ (many use-entry : (many (Env) env) (many (Mult) pos) (many (Nat) x) (many (Bool) sharing) -> (many (Env) r))
  (let-match many (and (mult-is-many pos) $ not $ env-usage-erased env) (BTrue) ((BFalse) env))
  (let ((many m)) (entry-mult-of env x))
  (let ((many supply)) $ match many (and sharing $ not $ mult-is-once pos) (((Mult) _)) ((BTrue) (Many)) ((BFalse) m))
  (let ((many env1) (many _)) $ check-mult env (declared env "" x) (str-cat3 (qname env x) ", declared " $ tick $ mult-name m) pos supply)
  (let-match many m (Once) (else env1))
  (let ((many env2)) (match many (and (mult-is-once pos) $ list-mem-bin (env-captures env) x) (((Env) _)) ((BFalse) env1) ((BTrue) (env-error env1 $ str-cat3 "`def-fns` cannot capture " (qname env x) " at unique"))))
  (let ((many (Maybe $ Pair (Loc) $ String) conflict))
    (match many (idmap-get _ x $ env-uses env2) (((Maybe $ Pair (Loc) $ String) _))
      ((Miss _ _ _ _) (None _))
      ((Hit _ _ _ prior _)
        (let-match many prior (UseShared la) ((UseConsumed la) (Some _ $ MkPair _ _ la "already used at unique here")))
        (match many (mult-is-once pos) (((Maybe $ Pair (Loc) $ String) _))
          ((BTrue) (Some _ $ MkPair _ _ la "already shared here"))
          ((BFalse) (None _))))))
  (let ((many env3))
    (match many conflict (((Env) _))
      ((None _) env2)
      ((Some _ p)
        (match many p (((Env) _))
          ((MkPair _ _ la why)
            (env-error-with env2 (Cons _ (MkPair _ _ la why) $ Nil _) $ str-cat3 "unique value " (qname env x) " has conflicting non-erased uses"))))))
  (env-set-uses env3 $ idmap-set _ x (match many (mult-is-once pos) (((Use) _)) ((BTrue) (UseConsumed $ env-loc env3)) ((BFalse) (UseShared $ env-loc env3))) $ env-uses env3))
(def-fns _ $ (many set-entry-mult : (many (Env) env) (many (Nat) x) (many (Mult) mult) -> (many (Env) r))
  (let ((erased hs) (many hp) (many en) (many fi)) (env-store env))
  (let-match many (idmap-get _ x en) (Hit _ _ _ e _) ((Miss _ _ _ _) env))
  (match many e _
    ((MkEInfo _ name _ state minted meta site)
      (env-with-store env _ hp (idmap-set _ x (MkEInfo _ name mult state minted meta site) en) fi))))

(def-fns _ $ (many lookup : (many (Env) env) (many (String) name) -> (many (Maybe $ Nat) r))
  (match many (nm-get _ name $ scope-names $ env-scope env) _ ((NHit _ _ _ x _) (Some _ x)) ((NMiss _ _ _ _) (None _))))

(def-fns _ $ (many visible-names : (many (Env) env) (subterm many (List $ Nat) xs) -> (many (List $ String) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (Nil _)))
  (let ((many names)) (notail $ visible-names env rest))
  (let ((erased hs) (many e)) $ entry env x)
  (let-match many e (MkEInfo _ n _ _ _ _ _))
  (let-match many n (Some _ s) ((None _) names))
  (match many (lookup env s) _
    ((Some _ y) (match many (nat-eq x y) _ ((BTrue) (Cons _ s names)) ((BFalse) names)))
    ((None _) names)))

(def-fns _ $ (many nearest-names : (many (String) name) (subterm many (List $ String) xs) -> (many (Maybe $ Nat) best) (many (List $ String) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (values (None _) (Nil _))))
  (let ((many best) (many ties)) (notail $ nearest-names name rest))
  (let ((many d)) (distance name x))
  (let-match many best (Some _ b) ((None _) (values (Some _ d) $ list1 _ x)))
  (match many (nat-lt d b) _
    ((BTrue) (values (Some _ d) $ list1 _ x))
    ((BFalse) (values best $ match many (nat-eq d b) (((List $ String) _)) ((BTrue) (Cons _ x ties)) ((BFalse) ties)))))

(def-fns _ $ (many hint : (many (Env) env) (many (String) name) -> (many (String) r))
  (let ((many best) (many ties)) $ nearest-names name $ visible-names env $ scope-ids $ env-scope env)
  (match many ties _ ((Nil _) "") ((Cons _ _ _) (str-cat "\nhint: nearest in scope: " $ join-strs ties " "))))

(def-fns _ $ (many is-prelude : (many (Env) env) (many (Nat) x) -> (many (Bool) r))
  (list-mem-bin (scope-ids $ env-prelude env) x))


; Whether a type is one the fetching forms look for in ambient scope (sections 19, 38).
(def-fns _ $ (many is-object-type : (many (Term) ty) (many (Nat) objid) -> (many (Bool) r))
  (match many ty _
    ((TMatchable _ _ _ _ _) (BTrue))
    ((TSlotHolds _) (BFalse))
    ((TApp h _) (match many h _ ((TVar x) (nat-eq x objid)) (else (BFalse))))
    ((TCell _ _) (BFalse)) (else (BFalse))))

(def-fns _
  ((many canon-locations : (subterm many (Term) t) (many (Env) env) -> (many (Term) r))
    (match many t _
      ((TSlotHolds x) (TSlotHolds $ location-term env x))
      ((TApp h xs) (TApp (notail $ canon-locations h env) $ notail $ canon-locations-list xs env))
      ((TCell h xs) (TCell (notail $ canon-locations h env) $ notail $ canon-locations-list xs env))
      ((TFn uq l ps rs) (TFn uq (notail $ canon-locations l env) (notail $ canon-locations-tele ps env) (notail $ canon-locations-tele rs env)))
      ((TTyCtor ps) (TTyCtor $ notail $ canon-locations-tele ps env))
      ((TValCtor ps ret) (TValCtor (notail $ canon-locations-tele ps env) $ notail $ canon-locations ret env))
      ((TMatchable d nt ex ty cs) (TMatchable d nt ex (notail $ canon-locations ty env) $ notail $ canon-locations-mctors cs env))
      (else t)))
  ((many canon-locations-list : (subterm many (List $ Term) xs) (many (Env) env) -> (many (List $ Term) r))
    (match many xs _ ((Nil _) xs) ((Cons _ t rest) (Cons _ (notail $ canon-locations t env) $ notail $ canon-locations-list rest env))))
  ((many canon-locations-tele : (subterm many (List $ Entry) es) (many (Env) env) -> (many (List $ Entry) r))
    (let-match many es (Cons _ e rest) ((Nil _) es))
    (let-match many e (MkEntry name sub2 mu sg place site))
    (Cons _
      (MkEntry name sub2 mu
        (match many sg (((Sg) _)) ((SgTy t) (SgTy $ notail $ canon-locations t env)) ((SgIs t ty) (SgIs (notail $ canon-locations t env) ty)))
        (match many place (((Maybe $ Term) _)) ((None _) (None _)) ((Some _ at2) (Some _ $ notail $ canon-locations at2 env)))
        site)
      (notail $ canon-locations-tele rest env)))
  ((many canon-locations-mctors : (subterm many (List $ MCtor) cs) (many (Env) env) -> (many (List $ MCtor) r))
    (match many cs _ ((Nil _) cs) ((Cons _ c rest) (match many c _ ((MkMCtor m t) (Cons _ (MkMCtor m $ notail $ canon-locations t env) $ notail $ canon-locations-mctors rest env)))))))

(def-fns _ $ (many canon-env : (many (Env) env) (many (Term) t) -> (many (Term) r))
  (let ((erased n) (erased f) (many bnd) (many tb)) $ env-table env)
  (let ((many r) (erased fr)) $ canon-in _ _ bnd tb t)
  (canon-locations r env))

(def-fns _ $ (many canon-env-tele : (many (Env) env) (many (List $ Entry) es) -> (many (List $ Entry) r))
  (let ((erased n) (erased f) (many bnd) (many tb)) $ env-table env)
  (let ((many r) (erased fr)) $ canon-tele-in _ _ bnd tb es)
  (canon-locations-tele r env))

; The variables a term mentions, onto [acc], each place it occurs.
(def-fns _
  ((many term-vars : (subterm many (Term) t) (many (List $ Nat) acc) -> (many (List $ Nat) r))
    (match many t _
      ((TVar x) (Cons _ x acc))
      ((TApp h args) (tail $ term-vars h $ notail $ term-vars-list args acc))
      ((TCell h args) (tail $ term-vars h $ notail $ term-vars-list args acc))
      ((TFn _ l ps rs) (tail $ term-vars l $ notail $ term-vars-tele ps $ notail $ term-vars-tele rs acc))
      ((TTyCtor ps) (tail $ term-vars-tele ps acc))
      ((TValCtor ps ret) (tail $ term-vars-tele ps $ notail $ term-vars ret acc))
      ((TMatchable _ _ _ ty cs) (tail $ term-vars ty $ notail $ term-vars-mctors cs acc))
      ((TSlotHolds c) (tail $ term-vars c acc)) (else acc)))
  ((many term-vars-list : (subterm many (List $ Term) ts) (many (List $ Nat) acc) -> (many (List $ Nat) r))
    (match many ts _
      ((Nil _) acc)
      ((Cons _ t rest) (tail $ term-vars t $ notail $ term-vars-list rest acc))))
  ((many term-vars-mctors : (subterm many (List $ MCtor) cs) (many (List $ Nat) acc) -> (many (List $ Nat) r))
    (match many cs _
      ((Nil _) acc)
      ((Cons _ c rest) (match many c _ ((MkMCtor _ t) (tail $ term-vars t $ notail $ term-vars-mctors rest acc))))))
  ((many term-vars-tele : (subterm many (List $ Entry) es) (many (List $ Nat) acc) -> (many (List $ Nat) r))
    (let-match many es (Cons _ e rest) ((Nil _) acc))
    (let-match many e (MkEntry _ _ _ sg place _))
    (let ((many acc2)) $ notail $ term-vars-tele rest acc)
    (let ((many acc3)) $ match many place (((List $ Nat) _)) ((None _) acc2) ((Some _ p) (notail $ term-vars p acc2)))
    (match many sg _ ((SgTy t) (tail $ term-vars t acc3)) ((SgIs t _) (tail $ term-vars t acc3)))))

(def-fns _ $ (many any-meta : (many (Env) env) (subterm many (List $ Nat) xs) -> (many (Bool) r))
  (match many xs _ ((Nil _) (BFalse)) ((Cons _ x rest) (or (is-meta env x) $ notail $ any-meta env rest))))

; Whether a canonical term still mentions an unsolved meta.
(def-fns _ $ (many has-meta : (many (Term) t) (many (Env) env) -> (many (Bool) r))
  (any-meta env $ term-vars t $ Nil _))

(def-fns _ $ (many has-meta-env : (many (Env) env) (many (Term) t) -> (many (Bool) r))
  (has-meta (canon-env env t) env))

; The ids below are fixed by the order of the binds that follow; [bind-builtin] mints in that order.
(let ((many univ-id)) (Succ (Zero)))
(let ((many type-id)) (Succ univ-id))
(let ((many level-id)) (Succ type-id))
(let ((many slot-id)) (Succ level-id))
(let ((many null-id)) (Succ slot-id))
(let ((many predates-id)) (Succ null-id))
(let ((many subterm-id)) (Succ predates-id))
(let ((many sharing-id)) (Succ subterm-id))
(let ((many unique-id)) (Succ sharing-id))
(let ((many shared-id)) (Succ unique-id))
(let ((many sharing-matchable-id)) (Succ shared-id))
(let ((many coercible-id)) (Succ sharing-matchable-id))
(let ((many delegate-id)) (Succ coercible-id))
(let ((many special-id)) (Succ delegate-id))
(let ((many type-term)) $ TApp (TVar univ-id) $ Nil _)
(let ((many level-term)) $ TApp (TVar level-id) $ Nil _)
(let ((many special-term)) $ TApp (TVar special-id) $ Nil _)
(let ((many slot-term)) $ TApp (TVar slot-id) $ Nil _)
(let ((many sharing-term)) $ TApp (TVar sharing-id) $ Nil _)
(let ((many unique-term)) $ TApp (TVar unique-id) $ Nil _)
(let ((many shared-term)) $ TApp (TVar shared-id) $ Nil _)


; ---- Printing terms and values, for diagnostics and the final value (lib/term.ml's to_string, lib/value.ml's show)

(def-fns _
  ((many show-term : (subterm many (Term) t) (many (Env) env) (many (List $ Maybe $ String) bound) -> (many (Rope) r))
    (match many t _
      ((TVar x) (RStr $ name-of env x))
      ((TBound k)
        (RStr $ match many (list-nth _ bound k) (((String) _))
          ((NthHit _ _ _ n _) (match many n (((String) _)) ((Some _ s) s) ((None _) (str-cat "#" $ nat-str k))))
          ((NthMiss _ _ _ _) (str-cat "#" $ nat-str k))))
      ((TApp h args) (rcat4 (RStr "(") (notail $ show-term h env bound) (notail $ show-terms args env bound) $ RStr ")"))
      ((TCell h args) (rcat4 (RStr "(Cell ") (notail $ show-term h env bound) (notail $ show-terms args env bound) $ RStr ")"))
      ((TFn uq l ps rs)
        (let ((many psr) (many b2)) $ notail $ show-tele ps env bound (BTrue))
        (let ((many rsr) (many b3)) $ notail $ show-tele rs env b2 (BTrue))
        (rcat5 (RStr $ match many uq (((String) _)) ((BTrue) "(UniqueFn ") ((BFalse) "(Fn ")) (notail $ show-term l env bound) psr (rcat (RStr " ->") rsr) $ RStr ")"))
      ((TTyCtor ps)
        (let ((many psr) (many b2)) $ notail $ show-tele ps env bound (BFalse))
        (rwrap "(TyCtor" psr " -> Type)"))
      ((TValCtor ps ret)
        (let ((many psr) (many b2)) $ notail $ show-tele ps env bound (BTrue))
        (rcat4 (RStr "(ValCtor") psr (rcat (RStr " -> ") $ notail $ show-term ret env b2) $ RStr ")"))
      ((TMatchable d nt ex ty cs)
        (let ((many marks)) (str-cat (match many nt (((String) _)) ((BTrue) "newtype ") ((BFalse) "")) (match many ex (((String) _)) ((BTrue) "extern ") ((BFalse) ""))))
        (rcat5 (RStr $ match many d (((String) _)) ((DEnum) "(Matchable enum ") ((DUnion) "(Matchable union ")) (RStr marks) (notail $ show-term ty env bound) (notail $ show-mctors cs env bound) $ RStr ")"))
      ((TSlotHolds c)
        (match many c (((Rope) _))
          ((TVar x) (match many (nat-eq x null-id) (((Rope) _)) ((BTrue) (RStr "(SlotVacant)")) ((BFalse) (rwrap "(SlotHolds " (RStr $ name-of env x) ")"))))
          (else (rwrap "(SlotHolds " (notail $ show-term c env bound) ")"))))
      ((TErr m) (rwrap "<error: " (RStr m) ">"))))
  ((many show-terms : (subterm many (List $ Term) ts) (many (Env) env) (many (List $ Maybe $ String) bound) -> (many (Rope) r))
    (match many ts _
      ((Nil _) (REmpty))
      ((Cons _ t rest) (rcat3 (RStr " ") (notail $ show-term t env bound) $ notail $ show-terms rest env bound))))
  ((many show-mctors : (subterm many (List $ MCtor) cs) (many (Env) env) (many (List $ Maybe $ String) bound) -> (many (Rope) r))
    (let-match many cs (Cons _ c rest) ((Nil _) (REmpty)))
    (match many c _
      ((MkMCtor m t) (rcat5 (RStr " (") (RStr $ mult-name m) (rcat (RStr " ") $ notail $ show-term t env bound) (RStr ")") $ notail $ show-mctors rest env bound))))
  ((many show-tele : (subterm many (List $ Entry) es) (many (Env) env) (many (List $ Maybe $ String) bound) (many (Bool) marked) -> (many (Rope) r) (many (List $ Maybe $ String) bound2))
    (let-match many es (Cons _ e rest) ((Nil _) (values (REmpty) bound)))
    (let-match many e (MkEntry n s m sg place _))
    (let ((many (String) nm)) $ match many n _ ((None _) "_") ((Some _ x) x))
    (let ((many (String) marks))
      (match many marked _
        ((BFalse) "")
        ((BTrue) (str-cat3 (match many s (((String) _)) ((BTrue) "subterm ") ((BFalse) "")) (mult-name m) " "))))
    (let ((many (Rope) body)) (match many sg _
                       ((SgTy t) (rcat3 (notail $ show-term t env bound) (RStr " ") $ RStr nm))
                       ((SgIs t _) (rcat3 (notail $ show-term t env bound) (RStr " is ") $ RStr nm))))
    (let ((many body2)) (match many place (((Rope) _))
      ((None _) body)
      ((Some _ p) (match many p _
        ((TSlotHolds loc) (rcat3 body (RStr " at ") (notail $ show-term loc env bound)))
        (else (rcat3 body (RStr " at ") (notail $ show-term p env bound)))))))
    (let ((many restr) (many b2)) $ notail $ show-tele rest env (Cons _ n bound) marked)
    (values (rcat5 (RStr " (") (RStr marks) body2 (RStr ")") restr) b2)))

; Shadowing is legal (section 9) and warns at every binder that hides a name already in scope
; (ASSUMPTIONS 195). Only a binder the source wrote carries a position, and only such a binder warns;
; the entry it hides carries one too unless the built-ins minted it, which is what the other message says.
(def-fns _ $ (many warn-shadow : (many (Env) env) (many (Maybe $ String) name) (many (Maybe $ Loc) site) (many (Bool) written) -> (many (Env) r))
  (let-match many written (BTrue) ((BFalse) env))
  (let-match many site (Some _ l) ((None _) env))
  (let-match many name (Some _ n) ((None _) env))
  (let-match many (lookup env n) (Some _ prior) ((None _) env))
  (let-match many (str-eq n "_") (BFalse) ((BTrue) env))
  (match many (env-entry-at env prior) (((Env) _))
    ((Some _ pl)
      (env-warn-with env l (Cons _ (MkPair _ _ pl "shadowed binder is here") $ Nil _) $ str-cat3 "declaration of " (tick n) " shadows a previous binder"))
    ((None _)
      (env-warn-at env l $ str-cat3 "declaration of " (tick n) " shadows a built-in"))))

; Mints an entry: a fresh id, its name in scope, its state, its type and optional rule (section 3). A meta,
; standing for a `_` argument (SUGAR.md 6), enters neither the scope nor the objects: nothing reaches it by
; name or by type, and unification alone solves it. No other entry's type or rule may mention one still
; unsolved -- the invariant behind the sugar -- except while a telescope with holes is being built [holes].
(def-fns _ $ (many bind-as : (many (Env) env) (many (Bool) meta) (many (Bool) holes) (many (Maybe $ String) name) (many (Maybe $ Loc) site) (many (Bool) written) (many (Mult) mult) (many (Term) ty) (many (Maybe $ Term) rule) (many (Nat) objid) ->
    (many (Env) r) (many (Nat) x))
  ; before the entry is minted, while the scope still holds what it hides
  (let ((many (Env) envs)) (warn-shadow env name site written))
  (let ((many (Env) envl)) $ match many name _ ((None _) envs) ((Some _ n) (match many (is-literal-name n) (((Env) _)) ((BTrue) (env-error envs $ str-cat n " is a literal, not a name")) ((BFalse) envs))))
  (let ((many (Maybe $ Term) open))
    (match many (or meta holes) _
      ((BTrue) (None _))
      ((BFalse)
        (match many (has-meta-env envl ty) _
          ((BTrue) (Some _ ty))
          ((BFalse) (match many rule _ ((None _) (None _)) ((Some _ t) (match many (has-meta-env envl t) _ ((BTrue) (Some _ t)) ((BFalse) (None _))))))))))
  (let ((many (Env) envw)) $ match many open _ ((None _) envl) ((Some _ t) (env-error envl $ str-cat "cannot infer the `_` in " $ tick $ rope-str $ show-term t envl $ Nil _)))
  (let-match many envw (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv sts cl wa lt lo pr us hn))
  (let ((many x) (erased ltp)) (values (Succ fr) (lt-succ fr)))
  (let ((many (Scope) sc2))
    (match many meta _
      ((BTrue) sc)
      ((BFalse) (match many sc _ ((MkScope names ids) (MkScope (match many name (((NameMap $ Nat) _)) ((None _) names) ((Some _ n) (nm-set _ n x names))) $ Cons _ x ids))))))
  (let ((many en2)) $ idmap-set _ x (MkEInfo _ name mult (SDyn _) (BFalse) meta site) en)
  (let ((erased (Nat) nf2) (erased (Facts nf2) ff2) (many (Table nf2 ff2 x) tb2))
    (match many rule _
      ((None _) (table-insert _ _ _ tb x ltp ty))
      ((Some _ t)
        (let-match many tb (MkTable _ f0 _ ru _ ord _ _ c1 _ _))
        (let ((many t2) (erased ft)) $ canon ru t _ f0 _ _ (PNil ru) ord (GTop t) c1)
        (table-insert-ruled _ _ _ tb x ltp ty t2 ft))))
  (let ((many (List $ Nat) ob2)) $ match many (and (not meta) $ is-object-type ty objid) _ ((BTrue) (Cons _ x ob)) ((BFalse) ob))
  (values (MkEnv _ hp sc2 en2 _ _ x tb2 rp ob2 li fi lv sts cl wa lt lo pr us hn) x))

(def-fns _ $ (many bind : (many (Env) env) (many (Maybe $ String) name) (many (Maybe $ Loc) site) (many (Bool) written) (many (Mult) mult) (many (Term) ty) (many (Maybe $ Term) rule) (many (Nat) objid) ->
    (many (Env) r) (many (Nat) x))
  (bind-as env (BFalse) (BFalse) name site written mult ty rule objid))

; A binder that is Const at once: over a closed block, over the token, or over the token only in run
; position (section 34).
(def-fns _ $ (many bind-closed : (many (Env) env) (many (Maybe $ String) name) (many (Maybe $ Loc) site) (many (Bool) written) (many (Mult) mult) (many (Block (Ref Block (HEmpty Block))) b) (many (Term) ty) (many (Maybe $ Term) rule) (many (Nat) objid) ->
    (many (Env) r) (many (Nat) x))
  (let ((many env2) (many x)) $ bind env name site written mult ty rule objid)
  (values (set-state-closed env2 x b) x))

(def-fns _ $ (many bind-token : (many (Env) env) (many (Maybe $ String) name) (many (Maybe $ Loc) site) (many (Bool) written) (many (Mult) mult) (many (Term) ty) (many (Maybe $ Term) rule) (many (Nat) objid) ->
    (many (Env) r) (many (Nat) x))
  (bind-closed env name site written mult (BToken _) ty rule objid))

(def-fns _ $ (many bind-erased : (many (Env) env) (many (Maybe $ String) name) (many (Maybe $ Loc) site) (many (Bool) written) (many (Mult) mult) (many (Term) ty) (many (Maybe $ Term) rule) (many (Nat) objid) ->
    (many (Env) r) (many (Nat) x))
  (match many (env-run-pos env) _
    ((BTrue) (bind-token env name site written mult ty rule objid))
    ((BFalse) (bind env name site written mult ty rule objid))))


; ---- Instantiation and abstraction over de Bruijn binders (lib/term.ml)

(def-adts $ (VOp : -> Type)
  enum
  (many OpInst : (many (List $ Term) args) -> (VOp))
  (many OpAbs : (many (List $ Nat) ids) -> (VOp))
  (many OpMeta : (many (Env) env) -> (VOp))
  (many OpWild : (many (Nat) fresh) -> (VOp)))

; [args] are closed terms, innermost binder first; [ids] likewise, the head becoming Bound 0.
(def-fns _ $ (many op-leaf : (many (VOp) op) (many (Nat) d) (many (Term) t) -> (many (Term) r))
  (match many op _
    ((OpInst args)
      (let-match many t (TBound k) (else t))
      (let-match many (nat-lt k d) (BFalse) ((BTrue) t))
      (let ((many n)) $ list-length _ args)
      (match many (list-nth _ args $ nat-sub k d) _
        ((NthHit _ _ _ s _) s)
        ((NthMiss _ _ _ _) (TBound $ nat-sub k n))))
    ((OpAbs ids)
      (let-match many t (TVar x) (else t))
      (match many (index-of-bin ids x 0) _
        ((Some _ i) (TBound $ nat-add i d))
        ((None _) t)))
    ((OpMeta env)
      (let-match many t (TVar x) (else t))
      (let ((many ty) (many rule)) $ fact-at env x)
      (match many rule _
        ((None _) t)
        ((Some _ _) (match many (is-meta env x) _ ((BTrue) (canon-env env t)) ((BFalse) t)))))
    ((OpWild f)
      (match many t _
        ((TVar x) (match many (nat-lt x f) _ ((BTrue) t) ((BFalse) (TVar (Zero))))) (else t)))))

(def-fns _
  ((many mapv : (subterm many (Term) t) (many (VOp) op) (many (Nat) d) -> (many (Term) r))
    (match many t _
      ((TApp h args) (TApp (notail $ mapv h op d) $ notail $ mapv-list args op d))
      ((TCell h args) (TCell (notail $ mapv h op d) $ notail $ mapv-list args op d))
      ((TFn uq l ps rs)
        (let ((many d2) (many ps2)) $ notail $ mapv-tele ps op d)
        (let ((many d3) (many rs2)) $ notail $ mapv-tele rs op d2)
        (TFn uq (notail $ mapv l op d) ps2 rs2))
      ((TTyCtor ps)
        (let ((many d2) (many ps2)) $ notail $ mapv-tele ps op d)
        (TTyCtor ps2))
      ((TValCtor ps ret)
        (let ((many d2) (many ps2)) $ notail $ mapv-tele ps op d)
        (TValCtor ps2 $ notail $ mapv ret op d2))
      ((TMatchable disc nt ex ty cs) (TMatchable disc nt ex (notail $ mapv ty op d) (notail $ mapv-mctors cs op d)))
      ((TSlotHolds c) (TSlotHolds $ notail $ mapv c op d))
      (else (op-leaf op d t))))
  ((many mapv-list : (subterm many (List $ Term) ts) (many (VOp) op) (many (Nat) d) -> (many (List $ Term) r))
    (match many ts _
      ((Nil _) (Nil _))
      ((Cons _ t rest) (Cons _ (notail $ mapv t op d) $ notail $ mapv-list rest op d))))
  ((many mapv-mctors : (subterm many (List $ MCtor) cs) (many (VOp) op) (many (Nat) d) -> (many (List $ MCtor) r))
    (let-match many cs (Cons _ c rest) ((Nil _) (Nil _)))
    (match many c _
      ((MkMCtor m t) (Cons _ (MkMCtor m $ notail $ mapv t op d) $ notail $ mapv-mctors rest op d))))
  ; Each entry is mapped at the depth of the entries before it; returns the depth after the telescope.
  ((many mapv-tele : (subterm many (List $ Entry) es) (many (VOp) op) (many (Nat) d) -> (many (Nat) d2) (many (List $ Entry) r))
    (let-match many es (Cons _ e rest) ((Nil _) (values d $ Nil _)))
    (let ((many (Entry) e2)) (match many e _
                     ((MkEntry n s m sg place site)
                       (MkEntry n s m (match many sg (((Sg) _)) ((SgTy t) (SgTy $ notail $ mapv t op d)) ((SgIs t ty) (SgIs (notail $ mapv t op d) $ notail $ mapv ty op d))) (match many place (((Maybe $ Term) _)) ((None _) (None _)) ((Some _ p) (Some _ $ notail $ mapv p op d))) site))))
    (let ((many d3) (many rest2)) $ notail $ mapv-tele rest op $ Succ d)
    (values d3 $ Cons _ e2 rest2)))

(def-fns _ $ (many instantiate : (many (List $ Term) args) (many (Term) t) -> (many (Term) r))
  (mapv t (OpInst args) 0))

(def-fns _ $ (many instantiate-tele : (many (List $ Term) args) (many (List $ Entry) tele) -> (many (List $ Entry) r))
  (let ((many d) (many r)) $ mapv-tele tele (OpInst args) 0)
  r)

(def-fns _ $ (many abstract : (many (List $ Nat) ids) (many (Term) t) -> (many (Term) r))
  (mapv t (OpAbs ids) 0))

; Every solved meta replaced by its solution, the rest of the term as written.
(def-fns _ $ (many metaless : (many (Env) env) (many (Term) t) -> (many (Term) r))
  (mapv t (OpMeta env) 0))

(def-fns _ $ (many abstract-sg : (many (List $ Nat) ids) (many (Sg) sg) -> (many (Sg) r))
  (match many sg _
    ((SgTy t) (SgTy $ abstract ids t))
    ((SgIs t ty) (SgIs (abstract ids t) $ abstract ids ty))))


(def-fns _ $ (many type-of : (many (Env) env) (many (Nat) x) -> (many (Term) r))
  (let ((erased n) (erased f) (many bnd) (many tb)) $ env-table env)
  (type-in _ _ bnd tb x))

; An entry read through its alias rule (section 9).
(def-fns _ $ (many resolve : (many (Env) env) (many (Nat) x) -> (many (Nat) r))
  (match many (canon-env env $ TVar x) _
    ((TVar y) y) (else x)))

; ---- The built-in entries (lib/prelude.ml): Univ, Type, Level, the proof types, Special and its forms

(def-fns _ $ (many ty-entry : (many (String) name) (many (Term) t) -> (many (Entry) e))
  (MkEntry (Some _ name) (BFalse) (Erased) (SgTy t) (None _) (None _)))

(let ((many empty-env)) (MkEnv _ (store-empty Block) scope-empty (MEmpty _) _ _ (Zero) empty-table (BTrue) (Nil _) (nm-empty _) (Nil _) (None _) (Nil _) (Nil _) (Nil _) (Nil _) (MkLoc "" (MkPos 0 0)) scope-empty unique-empty (Nil _)))

(def-fns _ $ (many bind-builtin : (many (Env) env) (many (String) name) (many (Term) ty) (many (Maybe $ Term) rule) -> (many (Env) r))
  (let ((many env2) (many x)) $ bind-token env (Some _ name) (None _) (BFalse) (Erased) ty rule delegate-id)
  env2)

(let ((many special-adt-stub)) (MkAdt "Special" (BTrue) (Nil _) (None _) (BFalse)))

; Binds each form's %-constructor (ASSUMPTIONS 5) and the form's own entry holding that constructor's value;
; returns the constructors for the Special Matchable.
(def-fns _ $ (many bind-specials : (subterm many (List $ SpEntry) sps) (many (Env) env) (many (Nat) index) (many (List $ Nat) shape) -> (many (Env) r) (many (List $ Ctor) ctors) (many (List $ MCtor) mctors))
  (let-match many sps (Cons _ sp rest) ((Nil _) (values env (Nil _) $ Nil _)))
  (let-match many sp (MkSpEntry name _))
  (let ((many cname)) $ str-cat "%" name)
  (let ((many env2) (many c)) $ bind env (Some _ cname) (None _) (BFalse) (Many) (TValCtor (Nil _) special-term) (None _) delegate-id)
  (let ((many ctor)) (MkCtor cname c index 0 (BTrue) (None _) shape (BFalse)))
  (let ((many env3)) $ set-state-closed env2 c $ BCtorFn _ ctor)
  (let ((many env4) (many ctors) (many mctors)) $ notail $ bind-specials rest env3 (Succ index) shape)
  (values env4 (Cons _ ctor ctors) $ Cons _ (MkMCtor (Many) $ TVar c) mctors))

(def-fns _ $ (many bind-special-names : (subterm many (List $ SpEntry) sps) (many (List $ Ctor) ctors) (many (Env) env) -> (many (Env) r))
  (let-match many sps (Cons _ sp rest) ((Nil _) env))
  (let-match many ctors (Cons _ ctor crest) ((Nil _) env))
  (let-match many sp (MkSpEntry name _))
  (let-match many ctor (MkCtor _ c _ _ _ _ _ _))
  (let ((many env2) (many x)) $ bind-closed env (Some _ name) (None _) (BFalse) (Many) (BTag _ ctor $ Nil _) special-term (Some _ $ TApp (TVar c) $ Nil _) delegate-id)
  (tail $ bind-special-names rest crest env2))

(def-fns _ $ (many make-builtins : -> (many (Env) env))
  (let ((many hetero)) (Cons _ (ty-entry "A" type-term) $ Cons _ (ty-entry "a" $ TBound 0) $
                      Cons _ (ty-entry "B" type-term) $ Cons _ (ty-entry "b" $ TBound 0) (Nil _)))
  (let ((many e1)) $ bind-builtin empty-env "Univ" (TTyCtor $ Nil _) $ None _)
  (let ((many e2)) $ bind-builtin e1 "Type" type-term $ Some _ type-term)
  (let ((many e3)) $ bind-builtin e2 "Level" (TTyCtor $ Nil _) $ None _)
  (let ((many eslot)) (bind-builtin e3 "Slot" (TTyCtor $ Nil _) $ None _))
  (let ((many enull) (many null)) (bind-token eslot (None _) (None _) (BFalse) (Many) type-term (None _) delegate-id))
  (let ((many e4)) (bind-builtin (mark-word enull null (BFalse)) "Predates"
                   (TTyCtor (Cons _ (ty-entry "A" type-term) $ Cons _ (ty-entry "a" $ TBound 0) $
                             Cons _ (ty-entry "l" level-term) (Nil _))) $ None _))
  (let ((many e5)) $ bind-builtin e4 "Subterm" (TTyCtor hetero) $ None _)
  (let ((many esharing)) (bind-builtin e5 "Sharing" (TTyCtor $ Nil _) $ None _))
  (let ((many ushape)) (Cons _ 0 $ Cons _ 0 $ Nil _))
  (let ((many uc)) (MkCtor "Unique" unique-id 0 0 (BTrue) (None _) ushape (BFalse)))
  (let ((many sc)) (MkCtor "Shared" shared-id 1 0 (BTrue) (None _) ushape (BFalse)))
  (let ((many eu) (many ui)) (bind-closed esharing (Some _ "Unique") (None _) (BFalse) (Many) (BCtorFn _ uc) (TValCtor (Nil _) sharing-term) (None _) delegate-id))
  (let ((many es) (many si)) (bind-closed eu (Some _ "Shared") (None _) (BFalse) (Many) (BCtorFn _ sc) (TValCtor (Nil _) sharing-term) (None _) delegate-id))
  (let ((many ucs)) (Cons _ uc $ Cons _ sc $ Nil _))
  (let ((many umcs)) (Cons _ (MkMCtor (Many) $ TVar ui) $ Cons _ (MkMCtor (Many) $ TVar si) $ Nil _))
  (let ((many em) (many mid)) (bind-closed es (None _) (None _) (BFalse) (Many) (BMat _ $ MkAdt "Sharing" (BTrue) ucs (None _) (BFalse)) (TMatchable (DEnum) (BFalse) (BFalse) (TVar sharing-id) umcs) (None _) delegate-id))
  (let ((many coercible-tele)) (Cons _ (ty-entry "sa" sharing-term) $ Cons _ (ty-entry "A" type-term) $ Cons _ (ty-entry "a" $ TBound 0) $ Cons _ (ty-entry "sb" sharing-term) $ Cons _ (ty-entry "B" type-term) $ Cons _ (ty-entry "b" $ TBound 0) $ Nil _))
  (let ((many e6)) (bind-builtin (env-settled $ env-open em mid) "Coercible" (TTyCtor coercible-tele) $ None _))
  (let ((many delegate-tele)) (Cons _ (ty-entry "sg" sharing-term) $ Cons _ (ty-entry "G" type-term) $ Cons _ (ty-entry "g" $ TBound 0) $ Cons _ (ty-entry "sf" sharing-term) $ Cons _ (ty-entry "F" type-term) $ Cons _ (ty-entry "f" $ TBound 0) $ Nil _))
  (let ((many edel)) (bind-builtin e6 "Delegate" (TTyCtor delegate-tele) $ None _))
  (let ((many e7)) $ bind-builtin edel "Special" (TTyCtor $ Nil _) $ None _)
  (let ((many e8) (many ctors) (many mctors)) $ bind-specials sp-table e7 0 $ list-replicate _ (list-length _ sp-table) 0)
  (let ((many adt)) (MkAdt "Special" (BTrue) ctors (None _) (BFalse)))
  (let ((many e9) (many m)) $ bind-closed e8 (None _) (None _) (BFalse) (Many) (BMat _ adt) (TMatchable (DEnum) (BFalse) (BFalse) (TVar special-id) mctors) (None _) delegate-id)
  (bind-special-names sp-table ctors $ env-settled $ env-open e9 m))


; ---- Inference over the grammar (lib/elab.ml's infer)

; The head type constructor of a canonical type, if any.
(def-fns _ $ (many type-head : (many (Env) env) (many (Term) ty) -> (many (Maybe $ Nat) r))
  (match many (canon-env env ty) _
    ((TApp h _) (match many h _ ((TVar x) (Some _ x)) (else (None $ Nat))))
    ((TCell _ _) (None _)) (else (None $ Nat))))

(def-fns _ $ (many bool-eq : (many (Bool) a) (many (Bool) b) -> (many (Bool) r))
  (match many a _ ((BTrue) b) ((BFalse) (not b))))

; ---- Structural identity of canonical terms (section 5's canonicalize-then-compare)

(def-fns _ $ (many mult-eq : (many (Mult) a) (many (Mult) b) -> (many (Bool) r))
  (and (bool-eq (mult-is-many a) $ mult-is-many b) $ bool-eq (mult-is-once a) $ mult-is-once b))

(def-fns _ $ (many disc-eq : (many (Disc) a) (many (Disc) b) -> (many (Bool) r))
  (match many a _
    ((DEnum) (match many b _ ((DEnum) (BTrue)) ((DUnion) (BFalse))))
    ((DUnion) (match many b _ ((DEnum) (BFalse)) ((DUnion) (BTrue))))))

(def-fns _
  ((many term-eq : (subterm many (Term) a) (many (Term) b) -> (many (Bool) r))
    (match many a _
      ((TVar x) (match many b _ ((TVar y) (nat-eq x y)) (else (BFalse))))
      ((TBound k) (match many b _ ((TBound j) (nat-eq k j)) (else (BFalse))))
      ((TApp h as) (match many b _
                     ((TApp h2 as2) (and (notail $ term-eq h h2) $ notail $ terms-eq as as2)) (else (BFalse))))
      ((TCell h as) (match many b _
                     ((TCell h2 as2) (and (notail $ term-eq h h2) $ notail $ terms-eq as as2)) (else (BFalse))))
      ((TFn uq l p r) (match many b _
                     ((TFn uq2 l2 p2 r2) (and (bool-eq uq uq2) $ and (notail $ term-eq l l2) $ and (notail $ tele-eq p p2) $ notail $ tele-eq r r2)) (else (BFalse))))
      ((TTyCtor p) (match many b _
                     ((TTyCtor p2) (tail $ tele-eq p p2)) (else (BFalse))))
      ((TValCtor p r) (match many b _
                        ((TValCtor p2 r2) (and (notail $ tele-eq p p2) $ notail $ term-eq r r2)) (else (BFalse))))
      ((TMatchable d nt ex t c) (match many b _
                            ((TMatchable d2 nt2 ex2 t2 c2) (and (bool-eq nt nt2) $ and (bool-eq ex ex2) $ and (disc-eq d d2) $ and (notail $ term-eq t t2) $ notail $ mctors-eq c c2)) (else (BFalse))))
      ((TSlotHolds c) (match many b _ ((TSlotHolds c2) (tail $ term-eq c c2)) (else (BFalse))))
      ((TErr _) (BFalse))))
  ((many places-eq : (subterm many (Maybe $ Term) a) (many (Maybe $ Term) b) -> (many (Bool) r))
    (match many a _ ((None _) (match many b _ ((None _) (BTrue)) ((Some _ _) (BFalse))))
      ((Some _ x) (match many b _ ((None _) (BFalse)) ((Some _ y) (tail $ term-eq x y))))))
  ((many terms-eq : (subterm many (List $ Term) as) (many (List $ Term) bs) -> (many (Bool) r))
    (let-match many as (Cons _ a rest) ((Nil _) (list-is-empty _ bs)))
    (match many bs _
      ((Nil _) (BFalse))
      ((Cons _ b rest2) (and (notail $ term-eq a b) $ notail $ terms-eq rest rest2))))
  ((many tele-eq : (subterm many (List $ Entry) as) (many (List $ Entry) bs) -> (many (Bool) r))
    (let-match many as (Cons _ a rest) ((Nil _) (list-is-empty _ bs)))
    (let-match many bs (Cons _ b rest2) ((Nil _) (BFalse)))
    (let-match many a (MkEntry _ s m sg place _))
    (let-match many b (MkEntry _ s2 m2 sg2 place2 _))
    (let ((many t2)) $ sg-term sg2)
    (let ((many (Bool) same)) $ match many sg _ ((SgTy t) (notail $ term-eq t t2)) ((SgIs t _) (notail $ term-eq t t2)))
    (and (mult-eq m m2) $ and (bool-eq s s2)
      $ and (notail $ places-eq place place2) $ and same $ notail $ tele-eq rest rest2))
  ((many mctors-eq : (subterm many (List $ MCtor) as) (many (List $ MCtor) bs) -> (many (Bool) r))
    (let-match many as (Cons _ a rest) ((Nil _) (list-is-empty _ bs)))
    (let-match many bs (Cons _ b rest2) ((Nil _) (BFalse)))
    (let-match many a (MkMCtor m t))
    (match many b _
      ((MkMCtor m2 t2) (and (mult-eq m m2) $ and (notail $ term-eq t t2) $ notail $ mctors-eq rest rest2)))))

(def-fns _ $ (many equal-env : (many (Env) env) (many (Term) a) (many (Term) b) -> (many (Bool) r))
  (term-eq (canon-env env a) $ canon-env env b))

; ---- Forced unification (section 18): records the facts a branch forces, or reports the contradiction
; that refutes it (lib/env.ml's unify). The measure is the table's count of rule-free entries: a step is
; structural on canonical terms while no binding happens, and after a binding, which rules an entry out,
; the rest is re-canonicalized at the smaller count.

(def-adts
  ((Clash : -> Type)
    enum
    (many CText : (many (String) s) -> (Clash))
    (many CTerm : (many (Term) t) -> (Clash))
    (many CName : (many (Nat) x) -> (Clash))
    (many CCat : (many (Clash) a) (many (Clash) b) -> (Clash)))
  ((UnifyRes : -> Type)
    enum
    (many UOk : (many (Env) env) -> (UnifyRes))
    (many UContra : (many (Clash) msg) -> (UnifyRes)))
  ((Outcome : ((Nat) n) ((Nat) c) -> Type)
    enum
    (many Same : (erased (Nat) n) (erased (Nat) c) (many (Env) env) -> (Outcome n c))
    (many Less : (erased (Nat) n) (erased (Nat) c) (erased (Nat) k) (erased (Facts k) f2) (many (Table k f2 c) tb) (many (Env) env) (erased (Subterm (Nat) k (Nat) n) p) -> (Outcome n c))
    (many Contra : (erased (Nat) n) (erased (Nat) c) (many (Clash) msg) -> (Outcome n c))))

(def-fns _ $ (many unify-place : (many (Env) env) (many (Maybe $ Term) a) (many (Maybe $ Term) b) (many (Bool) force) -> (many (UnifyRes) r))
  (match many a _
    ((None _) (match many b _ ((None _) (UOk env)) ((Some _ _) (UContra $ CText "at annotation mismatch"))))
    ((Some _ x) (match many b _
      ((None _) (UContra $ CText "at annotation mismatch"))
      ((Some _ y) (match many x _
        ((TSlotHolds v) (match many y _
          ((TSlotHolds w) (match many (at-equal env v w) _
            ((BTrue) (UOk env)) ((BFalse) (match many force _ ((BFalse) (UContra $ CText "at annotation mismatch")) ((BTrue) (UOk $ at-merge env v w))))))
          (else (UContra $ CText "malformed at annotation"))))
        (else (UContra $ CText "malformed at annotation"))))))))

(def-fns _ $ (many lift : (erased (Nat) n) (many (Nat) bnd) (erased (Nat) k) (erased (Facts k) f2) (many (Table k f2 bnd) tb) (many (Env) env) (erased (Subterm (Nat) k (Nat) n) p) (many (Outcome k bnd) o) -> (many (Outcome n bnd) r))
  (match many o _
    ((Same _ _ env3) (Less _ _ _ _ tb env3 p))
    ((Less _ _ _ _ tb2 env2 q) (Less _ _ _ _ tb2 env2 $ subterm-trans q p))
    ((Contra _ _ m) (Contra _ _ m))))

(def-fns _ $ (many mctors-list : (subterm many (List $ MCtor) cs) (many (Nat) x) -> (many (Bool) r))
  (let-match many cs (Cons _ c rest) ((Nil _) (BFalse)))
  (let-match many c (MkMCtor _ t))
  (match many t _
    ((TVar y) (or (nat-eq x y) $ notail $ mctors-list rest x)) (else (tail $ mctors-list rest x))))

; Constructors one opened Matchable lists are distinct (section 19), first-class ones included: the objects
; naming x, found through the index, are those whose canonical constructors, the names after the type
; constructor, may hold both (ASSUMPTIONS 139).
(def-fns _ $ (many listed-in : (subterm many (List $ Opened) os) (many (List $ Nat) cands) (many (Nat) x) (many (Nat) y) -> (many (Bool) r))
  (let-match many os (Cons _ o rest) ((Nil _) (BFalse)))
  (let-match many o (MkOpened ox k names))
  (let ((many (Bool) here))
    (match many (and (list-mem-bin cands ox) $ nat-eq (open-kind-code k) 0) _
      ((BFalse) (BFalse))
      ((BTrue) (match many names (((Bool) _)) ((Nil _) (BFalse)) ((Cons _ _ ctors) (and (list-mem-bin ctors x) $ list-mem-bin ctors y))))))
  (match many here _
    ((BTrue) (BTrue))
    ((BFalse) (tail $ listed-in rest cands x y))))

(def-fns _ $ (many listed : (many (Env) env) (many (Nat) x) (many (Nat) y) -> (many (Bool) r))
  (listed-in (env-opens env) (index-of x $ env-index env) x y))

(def-fns _ $ (many signature-of : (many (Env) env) (many (Nat) z) -> (many (Maybe $ Term) r))
  (match many (type-of env z) _
    ((TTyCtor p) (Some _ $ TTyCtor p))
    ((TValCtor p r) (Some _ $ TValCtor p r)) (else (None $ Term))))

; Whether a term mentions a binder no telescope of its own binds (a dangling de Bruijn index) at depth d.
(def-fns _
  ((many dangling : (subterm many (Term) t) (many (Nat) d) -> (many (Bool) r))
    (match many t _
      ((TBound k) (not $ nat-lt k d))
      ((TApp h args) (or (notail $ dangling h d) $ notail $ dangling-list args d))
      ((TCell h args) (or (notail $ dangling h d) $ notail $ dangling-list args d))
      ((TFn _ l ps rs) (or (notail $ dangling l d) $ or (notail $ dangling-tele ps d) $ notail $ dangling-tele rs $ nat-add d $ list-length _ ps))
      ((TTyCtor ps) (tail $ dangling-tele ps d))
      ((TValCtor ps ret) (or (notail $ dangling-tele ps d) $ notail $ dangling ret $ nat-add d $ list-length _ ps))
      ((TMatchable _ _ _ ty cs) (or (notail $ dangling ty d) $ notail $ dangling-mctors cs d))
      ((TSlotHolds c) (tail $ dangling c d)) (else (BFalse))))
  ((many dangling-list : (subterm many (List $ Term) ts) (many (Nat) d) -> (many (Bool) r))
    (match many ts _
      ((Nil _) (BFalse))
      ((Cons _ t rest) (or (notail $ dangling t d) $ notail $ dangling-list rest d))))
  ((many dangling-mctors : (subterm many (List $ MCtor) cs) (many (Nat) d) -> (many (Bool) r))
    (match many cs _
      ((Nil _) (BFalse))
      ((Cons _ c rest) (match many c _ ((MkMCtor _ t) (or (notail $ dangling t d) $ notail $ dangling-mctors rest d))))))
  ((many dangling-tele : (subterm many (List $ Entry) es) (many (Nat) d) -> (many (Bool) r))
    (let-match many es (Cons _ e rest) ((Nil _) (BFalse)))
    (let-match many e (MkEntry _ _ _ sg place _))
    (or (match many sg (((Bool) _)) ((SgTy t) (notail $ dangling t d)) ((SgIs t _) (notail $ dangling t d)))
      $ or (match many place (((Bool) _)) ((None _) (BFalse)) ((Some _ p) (notail $ dangling p d))) $ notail $ dangling-tele rest $ Succ d)))

(def-fns _ $ (many contradiction : (erased (Nat) n) (many (Nat) bnd) (many (Term) a) (many (Term) b) -> (many (Outcome n bnd) r))
  (Contra _ _ $ CCat (CTerm a) $ CCat (CText " vs ") $ CTerm b))

; A variable against a term: a dangling binder refutes, and so does the variable occurring in the term,
; which is the term not being fresh once the variable is ruled out (section 18).
(def-fns _ $ (many bind-var : (erased (Nat) n) (erased (Facts n) f) (many (Nat) bnd) (many (Table n f bnd) tb) (many (Env) env) (many (Nat) x) (erased (In x n f) p) (many (Term) t) (many (Term) a) (many (Term) b) (many (Bool) force) -> (many (Outcome n bnd) r))
  (let-match many (or (dangling t 0) $ not $ or force $ is-meta env x) (BFalse) ((BTrue) (contradiction _ bnd a b)))
  (let-match many (rule-out-refresh _ _ bnd tb x p t) (Some _ added)
    ((None _) (Contra _ _ $ CCat (CName x) $ CCat (CText " occurs in ") $ CTerm t)))
  (match many added _
    ((MkAdded k _ _ _ tb2) (Less _ _ _ _ tb2 (env-set-table env _ _ bnd tb2) $ prove-subterm k n))))

(def-fns _
  ((many unify : (subterm erased (Nat) n) (erased (Facts n) f) (many (Nat) bnd) (many (Table n f bnd) tb) (subterm many (Term) a) (erased (Fr n f a) pa) (many (Term) b) (erased (Fr n f b) pb) (many (Env) env) (many (Bool) force) -> (many (Outcome n bnd) r))
    (let-match many (term-eq a b) (BFalse) ((BTrue) (Same _ _ env)))
    (match many a _
      ((TVar x)
        (match many b _
          ((TVar y)
            (let ((erased px)) $ fr-var _ _ _ pa)
            (let ((erased py)) $ fr-var _ _ _ pb)
            (let-match many (nat-eq-dec x y) (BNo _ _ ne) ((BYes _ _ _) (Same _ _ env)))
            (let ((many (Nat) newer) (many (Nat) older) (erased (In newer n f) pn) (erased (In older n f) po) (erased (Neq older newer) neq))
              (match many (nat-lt x y) _
                ((BTrue) (values y x py px ne))
                ((BFalse) (values x y px py $ neq-sym _ _ ne))))
            (match many (or (is-meta env x) $ is-meta env y) _
              ((BTrue)
                (let ((many (Nat) m) (many (Nat) o) (erased (In m n f) pm) (erased (In o n f) po2) (erased (Neq o m) neq2))
                  (match many (and (is-meta env x) $ or (not $ is-meta env y) $ nat-eq x newer) _
                    ((BTrue) (values x y px py $ neq-sym _ _ ne))
                    ((BFalse) (values y x py px ne))))
                (match many (rule-out-var _ _ bnd tb m o pm po2 neq2) _
                  ((MkAdded k _ _ _ tb2) (Less _ _ _ _ tb2 (env-set-table env _ _ bnd tb2) $ prove-subterm k n))))
              ((BFalse)
                (let-match many (or (not force) $ listed env x y) (BFalse) ((BTrue) (contradiction _ bnd a b)))
                (let ((many sx)) $ signature-of env newer)
                (let ((many sy)) $ signature-of env older)
                (let-match many (rule-out-var _ _ bnd tb newer older pn po neq) (MkAdded k _ _ _ tb2))
                (let ((many env2)) $ env-set-table env _ _ bnd tb2)
                (let ((erased p)) $ prove-subterm k n)
                (let ((many (Outcome k bnd) after-sig))
                  (match many sx _
                    ((None _) (Same _ _ env))
                    ((Some _ s)
                      (let-match many sy (Some _ s2) ((None _) (Same _ _ env)))
                      (let ((many s3) (erased ps3)) $ canon-in _ _ bnd tb2 s)
                      (let ((many s4) (erased ps4)) $ canon-in _ _ bnd tb2 s2)
                      (notail $ unify _ _ bnd tb2 s3 ps3 s4 ps4 env2 force))))
                (match many after-sig _
                  ((Contra _ _ m) (Contra _ _ m))
                  ((Same _ _ _) (Less _ _ _ _ tb2 env2 p))
                  ((Less _ _ _ _ tb3 env3 q) (Less _ _ _ _ tb3 env3 $ subterm-trans q p))))))
          ((TBound _) (contradiction _ bnd a b))
          ((TErr m) (Contra _ _ $ CText m)) (else (bind-var n f bnd tb env x (fr-var n f x pa) b a b force))))
      ((TBound _) (contradiction _ bnd a b))
      ((TErr m) (Contra _ _ $ CText m))
      (else
        (match many b _
          ((TVar y) (bind-var _ _ bnd tb env y (fr-var n f y pb) a a b force))
          ((TErr m) (Contra _ _ $ CText m))
          (else
            (match many a _
              ((TApp h as)
                (let-match many b (TApp h2 as2) (else (contradiction n bnd a b)))
                (let-match many (nat-cmp (list-length _ as) $ list-length _ as2) (CEq _ _ _) (else (contradiction _ bnd a b)))
                (let ((erased ph) (erased pas)) $ fr-app _ _ _ _ pa)
                (let ((erased ph2) (erased pas2)) $ fr-app _ _ _ _ pb)
                (let-match many (notail $ unify _ _ bnd tb h ph h2 ph2 env force) (Less _ _ k f2 tb2 env2 p)
                  ((Same _ _ env4) (tail $ unify-list _ _ bnd tb as pas as2 pas2 env4 force))
                  ((Contra _ _ m) (Contra _ _ m)))
                (let ((many as3) (erased pas3)) $ canon-list-in _ _ bnd tb2 as)
                (let ((many bs3) (erased pbs3)) $ canon-list-in _ _ bnd tb2 as2)
                (lift _ bnd _ _ tb2 env2 p $ notail $ unify-list (subterm p) k f2 bnd tb2 as3 pas3 bs3 pbs3 env2 force))
              ((TCell h as)
                (let-match many b (TCell h2 as2) (else (contradiction n bnd a b)))
                (let-match many (nat-cmp (list-length _ as) $ list-length _ as2) (CEq _ _ _) (else (contradiction _ bnd a b)))
                (let ((erased ph) (erased pas)) $ fr-cell _ _ _ _ pa)
                (let ((erased ph2) (erased pas2)) $ fr-cell _ _ _ _ pb)
                (let-match many (notail $ unify _ _ bnd tb h ph h2 ph2 env force) (Less _ _ k f2 tb2 env2 p)
                  ((Same _ _ env4) (tail $ unify-list _ _ bnd tb as pas as2 pas2 env4 force))
                  ((Contra _ _ m) (Contra _ _ m)))
                (let ((many as3) (erased pas3)) $ canon-list-in _ _ bnd tb2 as)
                (let ((many bs3) (erased pbs3)) $ canon-list-in _ _ bnd tb2 as2)
                (lift _ bnd _ _ tb2 env2 p $ notail $ unify-list (subterm p) k f2 bnd tb2 as3 pas3 bs3 pbs3 env2 force))
              ((TFn uq l ps rs)
                (let-match many b (TFn uq2 l2 ps2 rs2) (else (contradiction n bnd a b)))
                (match many (bool-eq uq uq2) _ ((BFalse) (contradiction _ bnd a b)) ((BTrue)
                  (let ((erased pl) (erased pps) (erased prs)) (fr-fn _ _ _ _ _ _ pa))
                  (let ((erased pl2) (erased pps2) (erased prs2)) (fr-fn _ _ _ _ _ _ pb))
                  (match many (notail $ unify _ _ bnd tb l pl l2 pl2 env force) _
                    ((Contra _ _ m) (Contra _ _ m))
                    ((Same _ _ env5)
                      (let-match many (notail $ unify-tele _ _ bnd tb ps pps ps2 pps2 env5 a b force) (Less _ _ k f2 tb2 env2 p)
                        ((Contra _ _ m) (Contra _ _ m))
                        ((Same _ _ env4) (tail $ unify-tele _ _ bnd tb rs prs rs2 prs2 env4 a b force)))
                      (let ((many rs3) (erased prs3)) $ canon-tele-in _ _ bnd tb2 rs)
                      (let ((many rs4) (erased prs4)) $ canon-tele-in _ _ bnd tb2 rs2)
                      (lift _ bnd _ _ tb2 env2 p $ notail $ unify-tele (subterm p) k f2 bnd tb2 rs3 prs3 rs4 prs4 env2 a b force))
                    ((Less _ _ k f2 tb2 env2 p)
                      (let ((many ps3) (erased pps3)) $ canon-tele-in _ _ bnd tb2 ps)
                      (let ((many ps4) (erased pps4)) $ canon-tele-in _ _ bnd tb2 ps2)
                      (match many (notail $ unify-tele (subterm p) k f2 bnd tb2 ps3 pps3 ps4 pps4 env2 a b force) _
                        ((Contra _ _ m) (Contra _ _ m))
                        ((Same _ _ _)
                          (let ((many rs3) (erased prs3)) $ canon-tele-in _ _ bnd tb2 rs)
                          (let ((many rs4) (erased prs4)) $ canon-tele-in _ _ bnd tb2 rs2)
                          (lift _ bnd _ _ tb2 env2 p $ notail $ unify-tele (subterm p) k f2 bnd tb2 rs3 prs3 rs4 prs4 env2 a b force))
                        ((Less _ _ j f3 tb3 env3 q)
                          (let ((many rs3) (erased prs3)) $ canon-tele-in _ _ bnd tb3 rs)
                          (let ((many rs4) (erased prs4)) $ canon-tele-in _ _ bnd tb3 rs2)
                          (lift _ bnd _ _ tb3 env3 (subterm-trans q p) $ notail $ unify-tele (subterm (subterm-trans q p)) j f3 bnd tb3 rs3 prs3 rs4 prs4 env3 a b force))))))))
              ((TTyCtor ps)
                (match many b _
                  ((TTyCtor ps2) (tail $ unify-tele _ _ bnd tb ps (fr-tyctor n f ps pa) ps2 (fr-tyctor n f ps2 pb) env a b force))
                  (else (contradiction n bnd a b))))
              ((TValCtor ps ret)
                (let-match many b (TValCtor ps2 ret2) (else (contradiction n bnd a b)))
                (let ((erased pps) (erased pret)) $ fr-valctor _ _ _ _ pa)
                (let ((erased pps2) (erased pret2)) $ fr-valctor _ _ _ _ pb)
                (let-match many (notail $ unify-tele _ _ bnd tb ps pps ps2 pps2 env a b force) (Less _ _ k f2 tb2 env2 p)
                  ((Contra _ _ m) (Contra _ _ m))
                  ((Same _ _ env4) (tail $ unify _ _ bnd tb ret pret ret2 pret2 env4 force)))
                (let ((many ret3) (erased pret3)) $ canon-in _ _ bnd tb2 ret)
                (let ((many ret4) (erased pret4)) $ canon-in _ _ bnd tb2 ret2)
                (lift _ bnd _ _ tb2 env2 p $ notail $ unify (subterm p) k f2 bnd tb2 ret3 pret3 ret4 pret4 env2 force))
              ((TMatchable d nt ex t cs)
                (let-match many b (TMatchable d2 nt2 ex2 t2 cs2) (else (contradiction n bnd a b)))
                (let-match many (and (bool-eq nt nt2) $ and (bool-eq ex ex2) $ and (disc-eq d d2) $ nat-eq (list-length _ cs) $ list-length _ cs2) (BTrue)
                  ((BFalse) (contradiction _ bnd a b)))
                (let ((erased pt) (erased pcs)) (fr-matchable _ _ _ _ _ _ _ pa))
                (let ((erased pt2) (erased pcs2)) (fr-matchable _ _ _ _ _ _ _ pb))
                (let-match many (notail $ unify _ _ bnd tb t pt t2 pt2 env force) (Less _ _ k f2 tb2 env2 p)
                  ((Contra _ _ m) (Contra _ _ m))
                  ((Same _ _ env4) (tail $ unify-mctors _ _ bnd tb cs pcs cs2 pcs2 env4 a b force)))
                (let ((many cs3) (erased pcs3)) $ canon-mctors-in _ _ bnd tb2 cs)
                (let ((many cs4) (erased pcs4)) $ canon-mctors-in _ _ bnd tb2 cs2)
                (lift _ bnd _ _ tb2 env2 p $ notail $ unify-mctors (subterm p) k f2 bnd tb2 cs3 pcs3 cs4 pcs4 env2 a b force))
              ((TSlotHolds cn)
                (let-match many b (TSlotHolds cn2) (else (contradiction _ bnd a b)))
                (match many (at-equal env cn cn2) _
                  ((BTrue) (Same _ _ env))
                  ((BFalse) (match many force _ ((BTrue) (Same _ _ $ at-merge env cn cn2)) ((BFalse) (contradiction _ bnd a b))))))
              (else (contradiction n bnd a b))))))))

  ((many unify-list : (subterm erased (Nat) n) (erased (Facts n) f) (many (Nat) bnd) (many (Table n f bnd) tb) (subterm many (List $ Term) as) (erased (FrL n f as) pas) (many (List $ Term) bs) (erased (FrL n f bs) pbs) (many (Env) env) (many (Bool) force) -> (many (Outcome n bnd) r))
    (let-match many as (Cons _ a rest) ((Nil _) (Same _ _ env)))
    (let-match many bs (Cons _ b rest2) ((Nil _) (Same _ _ env)))
    (let ((erased pa) (erased prest)) $ frl-cons _ _ _ _ pas)
    (let ((erased pb) (erased prest2)) $ frl-cons _ _ _ _ pbs)
    (let-match many (notail $ unify _ _ bnd tb a pa b pb env force) (Less _ _ k f2 tb2 env2 p)
      ((Contra _ _ m) (Contra _ _ m))
      ((Same _ _ env4) (tail $ unify-list _ _ bnd tb rest prest rest2 prest2 env4 force)))
    (let ((many rest3) (erased prest3)) $ canon-list-in _ _ bnd tb2 rest)
    (let ((many rest4) (erased prest4)) $ canon-list-in _ _ bnd tb2 rest2)
    (lift _ bnd _ _ tb2 env2 p $ notail $ unify-list (subterm p) k f2 bnd tb2 rest3 prest3 rest4 prest4 env2 force))

  ; Telescopes unify entry by entry; a different length, multiplicity or subterm mark is a mismatch of shape.
  ((many unify-tele : (subterm erased (Nat) n) (erased (Facts n) f) (many (Nat) bnd) (many (Table n f bnd) tb) (subterm many (List $ Entry) as) (erased (FrT n f as) pas) (many (List $ Entry) bs) (erased (FrT n f bs) pbs) (many (Env) env) (many (Term) wa) (many (Term) wb) (many (Bool) force) -> (many (Outcome n bnd) r))
    (let-match many as (Cons _ a rest)
      ((Nil _) (match many bs _ ((Nil _) (Same _ _ env)) ((Cons _ _ _) (contradiction _ bnd wa wb)))))
    (let-match many bs (Cons _ b rest2) ((Nil _) (contradiction _ bnd wa wb)))
    (let-match many a (MkEntry _ s m sg place _))
    (let-match many b (MkEntry _ s2 m2 sg2 place2 _))
    (let-match many (and (mult-eq m m2) $ bool-eq s s2) (BTrue) ((BFalse) (contradiction _ bnd wa wb)))
    (let-match many (unify-place env place place2 force) (UOk env5) ((UContra msg) (Contra _ _ msg)))
    (let ((erased psg) (erased prest)) (frt-cons _ _ _ _ _ _ _ _ _ pas))
    (let ((erased psg2) (erased prest2)) (frt-cons _ _ _ _ _ _ _ _ _ pbs))
    (let-match many (notail $ unify-sg _ _ bnd tb sg psg sg2 psg2 env5 force) (Less _ _ k f2 tb2 env2 p)
      ((Contra _ _ msg) (Contra _ _ msg))
      ((Same _ _ env4) (tail $ unify-tele _ _ bnd tb rest prest rest2 prest2 env4 wa wb force)))
    (let ((many rest3) (erased prest3)) $ canon-tele-in _ _ bnd tb2 rest)
    (let ((many rest4) (erased prest4)) $ canon-tele-in _ _ bnd tb2 rest2)
    (lift _ bnd _ _ tb2 env2 p $ notail $ unify-tele (subterm p) k f2 bnd tb2 rest3 prest3 rest4 prest4 env2 wa wb force))

  ((many unify-sg : (subterm erased (Nat) n) (erased (Facts n) f) (many (Nat) bnd) (many (Table n f bnd) tb) (subterm many (Sg) sg) (erased (FrS n f sg) psg) (many (Sg) sg2) (erased (FrS n f sg2) psg2) (many (Env) env) (many (Bool) force) -> (many (Outcome n bnd) r))
    (match many sg _
      ((SgTy t)
        (match many sg2 _
          ((SgTy t2) (tail $ unify _ _ bnd tb t (frs-ty n f t psg) t2 (frs-ty n f t2 psg2) env force))
          ((SgIs t2 ty2) (tail $ unify _ _ bnd tb t (frs-ty n f t psg) t2 (frs-is n f t2 ty2 psg2) env force))))
      ((SgIs t ty)
        (match many sg2 _
          ((SgTy t2) (tail $ unify _ _ bnd tb t (frs-is n f t ty psg) t2 (frs-ty n f t2 psg2) env force))
          ((SgIs t2 ty2) (tail $ unify _ _ bnd tb t (frs-is n f t ty psg) t2 (frs-is n f t2 ty2 psg2) env force))))))

  ((many unify-mctors : (subterm erased (Nat) n) (erased (Facts n) f) (many (Nat) bnd) (many (Table n f bnd) tb) (subterm many (List $ MCtor) as) (erased (FrM n f as) pas) (many (List $ MCtor) bs) (erased (FrM n f bs) pbs) (many (Env) env) (many (Term) wa) (many (Term) wb) (many (Bool) force) -> (many (Outcome n bnd) r))
    (let-match many as (Cons _ a rest) ((Nil _) (Same _ _ env)))
    (let-match many bs (Cons _ b rest2) ((Nil _) (Same _ _ env)))
    (let-match many a (MkMCtor m t))
    (let-match many b (MkMCtor m2 t2))
    (let-match many (mult-eq m m2) (BTrue) ((BFalse) (contradiction _ bnd wa wb)))
    (let ((erased pt) (erased prest)) $ frm-cons _ _ _ _ _ pas)
    (let ((erased pt2) (erased prest2)) $ frm-cons _ _ _ _ _ pbs)
    (let-match many (notail $ unify _ _ bnd tb t pt t2 pt2 env force) (Less _ _ k f2 tb2 env2 p)
      ((Contra _ _ msg) (Contra _ _ msg))
      ((Same _ _ env4) (tail $ unify-mctors _ _ bnd tb rest prest rest2 prest2 env4 wa wb force)))
    (let ((many rest3) (erased prest3)) $ canon-mctors-in _ _ bnd tb2 rest)
    (let ((many rest4) (erased prest4)) $ canon-mctors-in _ _ bnd tb2 rest2)
    (lift _ bnd _ _ tb2 env2 p $ notail $ unify-mctors (subterm p) k f2 bnd tb2 rest3 prest3 rest4 prest4 env2 wa wb force)))

; Unification against the environment's table: solving, for a check; forcing, for a branch entry or an open,
; through unify-force alone.
(def-fns _ $ (many unify-in : (many (Env) env) (many (Term) a) (many (Term) b) (many (Bool) force) -> (many (UnifyRes) r))
  (let ((erased n) (erased f) (many bnd) (many tb)) $ env-table env)
  (let ((many a1) (erased pa)) $ canon-in _ _ bnd tb a)
  (let ((many b1) (erased pb)) $ canon-in _ _ bnd tb b)
  (match many (unify _ _ bnd tb a1 pa b1 pb env force) _
    ((Same _ _ env3) (UOk env3))
    ((Less _ _ _ _ _ env2 _) (UOk env2))
    ((Contra _ _ m) (UContra m))))

(def-fns _ $ (many unify-solve : (many (Env) env) (many (Term) a) (many (Term) b) -> (many (UnifyRes) r))
  (unify-in env a b $ BFalse))

; A forcing (section 18) leaves the opened objects it touched to be merged (section 19), so its environment
; is handed back as Forced, which only the restorers, merge-all and merge-opens, read an environment out of;
; a contradiction is carried along, and the next forcing is on the Forced.
(def-adts $ (Forced : -> Type)
  enum
  (many Forcing : (many (Env) e) -> (Forced))
  (many Refuted : (many (Clash) m) -> (Forced)))

(def-fns _ $ (many unify-force : (many (Forced) fe) (many (Term) a) (many (Term) b) -> (many (Forced) r))
  (match many fe _
    ((Refuted _) fe)
    ((Forcing env) (match many (unify-in env a b $ BTrue) _ ((UOk env2) (Forcing env2)) ((UContra m) (Refuted m))))))

(let ((many nat-adt)) (MkAdt "Nat" (BTrue) (Nil _) (Some _ (ExtNat)) (BFalse)))
(let ((many str-adt)) (MkAdt "String" (BTrue) (Nil _) (Some _ (ExtString)) (BFalse)))
