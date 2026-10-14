; self/core.sl -- the compiler's data: the restricted type grammar (DESIGN.md section 9) as terms with de
; Bruijn telescopes, the special-form registry (section 54), runtime values and post-erasure code, the
; scope environment with its fact table (sections 5, 7), canonicalization, instantiation and the part of
; forced unification a trusting compiler needs. Mirrors lib/term.ml, lib/value.ml and lib/env.ml.

(let ((many many-one)) $ Cons _ (Many) $ Nil _)

; The entries of [xs] sit at the many positions of [ms], in order.
(def-adts
  ((Picked : (Type A) ((List $ Multiplicity) ms) ((List A) xs) -> Type)
    enum
    (many PkNil : (erased Type A) -> (Picked A (Nil (Multiplicity)) (Nil A)))
    (many PkMany : (erased Type A) (erased (List $ Multiplicity) ms) (erased A x) (erased (List A) xs) (erased (Picked A ms xs) p) -> (Picked A (Cons (Multiplicity) (Many) ms) (Cons A x xs)))
    (many PkOnce : (erased Type A) (erased (List $ Multiplicity) ms) (erased A x) (erased (List A) xs) (erased (Picked A ms xs) p) -> (Picked A (Cons (Multiplicity) (Once) ms) (Cons A x xs)))
    (many PkErased : (erased Type A) (erased (List $ Multiplicity) ms) (erased (List A) xs) (erased (Picked A ms xs) p) -> (Picked A (Cons (Multiplicity) (Erased) ms) xs))))

(def-fns _ $ (many picked-of : (erased Type A) (subterm many (List $ Multiplicity) ms) (many (List A) xs) (erased (Lockstep (Multiplicity) A ms xs) lock) -> (many (List A) r) (erased (Picked A ms r) pk))
  (let-match many ms (Cons _ m rest) ((Nil _) (values (Nil _) (PkNil _))))
  (let-match erased lock (LsCons ta tb x0 y0 xs0 ys0 p))
  (let-match many xs (Cons b x xrest))
  (let ((many r) (erased pk)) $ notail $ picked-of _ rest xrest p)
  (match many m _
    ((Many) (values (Cons _ x r) (PkMany _ rest x r pk)))
    ((Once) (values (Cons _ x r) (PkOnce _ rest x r pk)))
    ((Erased) (values r (PkErased _ rest r pk)))))

(def-fns _ $ (erased picked-along : (erased Type A) (erased Type B) (erased (List $ Multiplicity) ms) (erased (List A) xs) (erased (List B) ys) (subterm erased (Picked A ms xs) p) (erased (Lockstep A B xs ys) q) -> (erased (Picked B ms ys) r))
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
(def-fns _ $ (erased picked-lockstep : (erased Type A) (erased Type B) (erased (List $ Multiplicity) ms) (erased (List A) xs) (erased (List B) ys) (subterm erased (Picked A ms xs) p) (erased (Picked B ms ys) q) -> (erased (Lockstep A B xs ys) lk))
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
(def-adts $ (ManySame : ((List $ Multiplicity) a) ((List $ Multiplicity) b) -> Type)
  enum
  (many MsNil : -> (ManySame (Nil (Multiplicity)) (Nil (Multiplicity))))
  (many MsMany : (erased (List $ Multiplicity) a) (erased (List $ Multiplicity) b) (erased (ManySame a b) p) -> (ManySame (Cons (Multiplicity) (Many) a) (Cons (Multiplicity) (Many) b)))
  (many MsOnce : (erased (List $ Multiplicity) a) (erased (List $ Multiplicity) b) (erased (ManySame a b) p) -> (ManySame (Cons (Multiplicity) (Once) a) (Cons (Multiplicity) (Once) b)))
  (many MsManyOnce : (erased (List $ Multiplicity) a) (erased (List $ Multiplicity) b) (erased (ManySame a b) p) -> (ManySame (Cons (Multiplicity) (Many) a) (Cons (Multiplicity) (Once) b)))
  (many MsOnceMany : (erased (List $ Multiplicity) a) (erased (List $ Multiplicity) b) (erased (ManySame a b) p) -> (ManySame (Cons (Multiplicity) (Once) a) (Cons (Multiplicity) (Many) b)))
  (many MsErasedL : (erased (List $ Multiplicity) a) (erased (List $ Multiplicity) b) (erased (ManySame a b) p) -> (ManySame (Cons (Multiplicity) (Erased) a) b))
  (many MsErasedR : (erased (List $ Multiplicity) a) (erased (List $ Multiplicity) b) (erased (ManySame a b) p) -> (ManySame a (Cons (Multiplicity) (Erased) b))))

(def-fns _ $ (erased picked-same : (erased Type A) (erased (List $ Multiplicity) a) (erased (List $ Multiplicity) b) (erased (List A) xs) (subterm erased (ManySame a b) p) (erased (Picked A a xs) q) -> (erased (Picked A b xs) r))
  (match erased p _
    ((MsNil) q)
    ((MsMany _ b2 p2) (let-match erased q (PkMany t a3 x xs2 q2)) (PkMany _ b2 x xs2 $ picked-same _ _ _ _ p2 q2))
    ((MsOnce _ b2 p2) (let-match erased q (PkOnce t a3 x xs2 q2)) (PkOnce _ b2 x xs2 $ picked-same _ _ _ _ p2 q2))
    ((MsManyOnce _ b2 p2) (let-match erased q (PkMany t a3 x xs2 q2)) (PkOnce _ b2 x xs2 $ picked-same _ _ _ _ p2 q2))
    ((MsOnceMany _ b2 p2) (let-match erased q (PkOnce t a3 x xs2 q2)) (PkMany _ b2 x xs2 $ picked-same _ _ _ _ p2 q2))
    ((MsErasedL _ _ p2) (let-match erased q (PkErased t a3 xs2 q2)) (picked-same _ _ _ _ p2 q2))
    ((MsErasedR _ b2 p2) (PkErased _ b2 xs $ picked-same _ _ _ _ p2 q))))

(def-fns _ $ (many mults-same : (subterm many (List $ Multiplicity) a) (subterm many (List $ Multiplicity) b) -> (many (Maybe $ ManySame a b) r))
  (match many a _
    ((Nil _)
      (let-match many b (Cons _ n br) ((Nil _) (Some _ (MsNil))))
      (let-match many n (Erased)
        ((Many) (None _)) ((Once) (None _)))
      (match many (notail $ mults-same a br) _ ((Some _ p) (Some _ $ MsErasedR _ _ p)) ((None _) (None _))))
    ((Cons _ m ar)
      (match many m _
        ((Erased) (match many (notail $ mults-same ar b) _ ((Some _ p) (Some _ $ MsErasedL _ _ p)) ((None _) (None _))))
        ((Many)
          (let-match many b (Cons _ n br) ((Nil _) (None _)))
          (match many n _
            ((Many) (match many (notail $ mults-same ar br) _ ((Some _ p) (Some _ $ MsMany _ _ p)) ((None _) (None _))))
            ((Once) (match many (notail $ mults-same ar br) _ ((Some _ p) (Some _ $ MsManyOnce _ _ p)) ((None _) (None _))))
            ((Erased) (match many (notail $ mults-same a br) _ ((Some _ p) (Some _ $ MsErasedR _ _ p)) ((None _) (None _))))))
        ((Once)
          (let-match many b (Cons _ n br) ((Nil _) (None _)))
          (match many n _
            ((Many) (match many (notail $ mults-same ar br) _ ((Some _ p) (Some _ $ MsOnceMany _ _ p)) ((None _) (None _))))
            ((Once) (match many (notail $ mults-same ar br) _ ((Some _ p) (Some _ $ MsOnce _ _ p)) ((None _) (None _))))
            ((Erased) (match many (notail $ mults-same a br) _ ((Some _ p) (Some _ $ MsErasedR _ _ p)) ((None _) (None _))))))))))

(def-adts $ (Disc : -> Type)
  enum
  (many DEnum : -> (Disc))
  (many DUnion : -> (Disc)))

; Where a message points: the file and the position within it (ASSUMPTIONS 194).
(def-adts $ (Loc : -> Type)
  enum
  (many MkLoc : (many (String) file) (many (Spot) pos) -> (Loc)))

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
    (many TSlotOf : (many (Term) c) -> (Term))
    (many TErr : (many (String) msg) -> (Term)))
  ((Entry : -> Type)
    enum
    (many MkEntry : (many (Maybe $ Name) name) (many (Bool) is-sub) (many (Multiplicity) mult) (many (Sg) sg) (many (Maybe $ Term) place) (many (Maybe $ Loc) site) -> (Entry)))
  ((Sg : -> Type)
    enum
    (many SgTy : (many (Term) t) -> (Sg))
    (many SgIs : (many (Term) t) (many (Term) ty) -> (Sg)))
  ((MCtor : -> Type)
    enum
    (many MkMCtor : (many (Multiplicity) m) (many (Term) c) -> (MCtor))))

; The ids below are fixed by the order of the binds that follow; [bind-builtin] mints in that order, each
; entry followed by its automatic slot (section 35), so the ids step by two.
(let ((many univ-id)) (Succ (Zero)))
(let ((many type-id)) (Succ $ Succ univ-id))
(let ((many level-id)) (Succ $ Succ type-id))
(let ((many slot-id)) (Succ $ Succ level-id))
(let ((many null-id)) (Succ $ Succ slot-id))
(let ((many world-id)) (Succ $ Succ null-id))
(let ((many predates-id)) (Succ $ Succ world-id))
(let ((many subterm-id)) (Succ $ Succ predates-id))
(let ((many sharing-id)) (Succ $ Succ subterm-id))
(let ((many unique-id)) (Succ $ Succ sharing-id))
(let ((many shared-id)) (Succ $ Succ unique-id))
(let ((many sharing-matchable-id)) (Succ $ Succ shared-id))
(let ((many coercible-id)) (Succ $ Succ sharing-matchable-id))
(let ((many delegate-id)) (Succ $ Succ coercible-id))
(let ((many atfn-id)) (Succ $ Succ delegate-id))
(let ((many special-id)) (Succ $ Succ atfn-id))
(let ((many type-term)) $ TApp (TVar univ-id) $ Nil _)
(let ((many universe-key)) "(Univ)")
(let ((many level-term)) $ TApp (TVar level-id) $ Nil _)
(let ((many special-term)) $ TApp (TVar special-id) $ Nil _)
(let ((many slot-term)) $ TApp (TVar slot-id) $ Nil _)
(let ((many world-term)) $ TApp (TVar world-id) $ Nil _)
(let ((many sharing-term)) $ TApp (TVar sharing-id) $ Nil _)
(let ((many unique-term)) $ TApp (TVar unique-id) $ Nil _)
(let ((many shared-term)) $ TApp (TVar shared-id) $ Nil _)

(def-fns _ $ (many entry-place : (many (Entry) e) -> (many (Maybe $ Term) p))
  (match many e _ ((MkEntry _ _ _ _ place _) place)))

(def-fns _ $ (many sg-term : (many (Sg) sg) -> (many (Term) t))
  (match many sg _ ((SgTy t) t) ((SgIs t _) t)))

(def-fns _ $ (many sg-ty : (many (Sg) sg) -> (many (Term) t))
  (match many sg _ ((SgTy t) t) ((SgIs _ ty) ty)))

(def-fns _ $ (many entry-mult : (many (Entry) e) -> (many (Multiplicity) m))
  (match many e _ ((MkEntry _ _ m _ _ _) m)))

(def-fns _ $ (many entry-sg : (many (Entry) e) -> (many (Sg) sg))
  (match many e _ ((MkEntry _ _ _ sg _ _) sg)))

(def-fns _ $ (many entry-name : (many (Entry) e) -> (many (Maybe $ Name) n))
  (match many e _ ((MkEntry n _ _ _ _ _) n)))

(def-fns _ $ (many entry-sub : (many (Entry) e) -> (many (Bool) s))
  (match many e _ ((MkEntry _ s _ _ _ _) s)))

(def-fns _ $ (many mult-name : (many (Multiplicity) m) -> (many (String) s))
  (match many m _ ((Erased) "erased") ((Many) "many") ((Once) "unique")))

(def-fns _ $ (many mult-is-many : (many (Multiplicity) m) -> (many (Bool) r))
  (match many m _ ((Erased) (BFalse)) ((Many) (BTrue)) ((Once) (BTrue))))

(def-fns _ $ (many under : (many (Multiplicity) pos) (many (Multiplicity) m) -> (many (Multiplicity) r))
  (match many pos _ ((Erased) (Erased)) ((Many) m) ((Once) m)))

; The position of a list of expected multiplicities: erased when the list is non-empty and every entry is.
(def-adts $ (PosOf : ((List $ Multiplicity) ms) ((Multiplicity) pos) -> Type)
  enum
  (many PoNil : -> (PosOf (Nil (Multiplicity)) (Many)))
  (many PoMany : (erased (List $ Multiplicity) rest) -> (PosOf (Cons (Multiplicity) (Many) rest) (Many)))
  (many PoOnce : (erased (List $ Multiplicity) rest) -> (PosOf (Cons (Multiplicity) (Once) rest) (Many)))
  (many PoOnly : -> (PosOf (Cons (Multiplicity) (Erased) (Nil (Multiplicity))) (Erased)))
  (many PoErased : (erased (Multiplicity) m) (erased (List $ Multiplicity) rest) (erased (Multiplicity) p) (erased (PosOf (Cons (Multiplicity) m rest) p) q) -> (PosOf (Cons (Multiplicity) (Erased) (Cons (Multiplicity) m rest)) p)))

(def-fns _ $ (many pos-of : (subterm many (List $ Multiplicity) ms) -> (many (Multiplicity) r) (erased (PosOf ms r) pf))
  (let-match many ms (Cons _ m rest) ((Nil _) (values (Many) (PoNil))))
  (let-match many m (Erased) ((Many) (values (Many) (PoMany _))) ((Once) (values (Many) (PoOnce _))))
  (let-match many rest (Cons _ _ _) ((Nil _) (values (Erased) (PoOnly))))
  (let ((many p) (erased q)) $ tail $ pos-of rest)
  (values p (PoErased _ _ _ q)))

(def-fns _ $ (many pos-mult : (many (List $ Multiplicity) ms) -> (many (Multiplicity) r))
  (let-match many ms (Cons _ m rest)
    ((Nil _) (Many)))
  (match many m _ ((Once) (match many rest _ ((Nil _) (Once)) ((Cons _ _ _) (Many)))) (else (let ((many r) (erased pf)) (pos-of ms)) r)))

(def-fns _ $ (many mult-is-once : (many (Multiplicity) m) -> (many (Bool) r))
  (match many m _ ((Once) (BTrue)) (else (BFalse))))

(def-fns _ $ (many field-under : (many (Multiplicity) pos) (many (Multiplicity) m) -> (many (Multiplicity) r))
  (let-match many pos (Many) ((Erased) (Erased)) ((Once) m))
  (match many m _ ((Once) (Many)) (else m)))

(def-fns _ $ (many many-count : (subterm many (List $ Entry) es) -> (many (Nat) n))
  (let-match many es (Cons _ e rest) ((Nil _) (Zero)))
  (match many (entry-mult e) _
    ((Many) (Succ $ notail $ many-count rest))
    ((Once) (Succ $ notail $ many-count rest))
    ((Erased) (tail $ many-count rest))))

(def-fns _ $ (many entry-stored : (many (Entry) e) -> (many (Bool) r))
  (and (mult-is-many $ entry-mult e) $ not $ is-some _ $ entry-place e))

(def-fns _ $ (many stored-count : (subterm many (List $ Entry) es) -> (many (Nat) n))
  (let-match many es (Cons _ e rest) ((Nil _) (Zero)))
  (match many (entry-stored e) _
    ((BTrue) (Succ $ notail $ stored-count rest))
    ((BFalse) (tail $ stored-count rest))))

(def-fns _ $ (many tele-mults : (subterm many (List $ Entry) es) -> (many (List $ Multiplicity) ms))
  (match many es _
    ((Nil _) (Nil _))
    ((Cons _ e rest) (Cons _ (entry-mult e) $ notail $ tele-mults rest))))

; ---- The special-form registry (section 54), grouped by where each is dispatched.

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
    (many StOpenAdt : -> (StmtK)) (many StDumpContext : -> (StmtK)) (many StSlotSelf : -> (StmtK)) (many StOpenAtFn : -> (StmtK))
    (many StCompileError : -> (StmtK)) (many StCompileWarn : -> (StmtK)) (many StDefOpaque : -> (StmtK)) (many StDefPrim : -> (StmtK)))
  ((FormerK : -> Type)
    enum
    (many FoFn : -> (FormerK)) (many FoTyCtor : -> (FormerK)) (many FoValCtor : -> (FormerK))
    (many FoMatchable : -> (FormerK)) (many FoUniqueFn : -> (FormerK)) (many FoCell : -> (FormerK)))
  ((ExprK : -> Type)
    enum
    (many ExMatch : -> (ExprK)) (many ExMatchableOf : -> (ExprK)) (many ExSlotOf : -> (ExprK)) (many ExAtFnOf : -> (ExprK)) (many ExShare : -> (ExprK)) (many ExCellAlloc : -> (ExprK)) (many ExCellWrite : -> (ExprK)) (many ExCellMatch : -> (ExprK)) (many ExCoercibleShare : -> (ExprK))
    (many ExNumeralOf : -> (ExprK)) (many ExLevelOf : -> (ExprK)) (many ExProveSubterm : -> (ExprK))
    (many ExProvePredates : -> (ExprK)) (many ExValues : -> (ExprK)) (many ExPredatesTrans : -> (ExprK))
    (many ExSubtermTrans : -> (ExprK)) (many ExPredatesSubterm : -> (ExprK)) (many ExCoerce : -> (ExprK))
    (many ExCoercibleRefl : -> (ExprK)) (many ExCoercibleSym : -> (ExprK)) (many ExCoercibleTrans : -> (ExprK))
    (many ExCoercibleWrap : -> (ExprK)) (many ExCoercibleCtor : -> (ExprK)) (many ExCoercibleOf : -> (ExprK)) (many ExDelegateOf : -> (ExprK))
    (many ExProveLiteralLt : -> (ExprK)) (many ExOpenAbsurd : -> (ExprK)) (many ExWorldDo : -> (ExprK)) (many ExGensym : -> (ExprK)) (many ExGensymUnique : -> (ExprK)) (many ExSettledOf : -> (ExprK))
    (many ExSettledType : -> (ExprK)) (many ExSettledErase : -> (ExprK)) (many ExResolve : -> (ExprK)) (many ExReadFile : -> (ExprK)) (many ExSettledEq : -> (ExprK)) (many ExSettledMult : -> (ExprK)) (many ExSettledValue : -> (ExprK)) (many ExInternNat : -> (ExprK)) (many ExInternChar : -> (ExprK)) (many ExInternString : -> (ExprK)) (many ExMintSettled : -> (ExprK)) (many ExMintSettledErased : -> (ExprK))
    (many ExPlaceAt : -> (ExprK)) (many ExPlaceAtMany : -> (ExprK)) (many ExUnplaceAt : -> (ExprK)) (many ExUnplaceAtMany : -> (ExprK)) (many ExPlacedSlot : -> (ExprK)) (many ExPlacedEq : -> (ExprK)))
  ((MarkK : -> Type)
    enum
    (many MkErased : -> (MarkK)) (many MkMany : -> (MarkK)) (many MkUnique : -> (MarkK)) (many MkAt : -> (MarkK)) (many MkColon : -> (MarkK)) (many MkIs : -> (MarkK))
    (many MkArrow : -> (MarkK)) (many MkSubterm : -> (MarkK)) (many MkEnum : -> (MarkK)) (many MkUnion : -> (MarkK))
    (many MkTail : -> (MarkK)) (many MkDelegate : -> (MarkK)) (many MkPredates : -> (MarkK)) (many MkAbsurd : -> (MarkK))
    (many MkNewtypeMark : -> (MarkK)) (many MkExtern : -> (MarkK)) (many MkElse : -> (MarkK)) (many MkNoTail : -> (MarkK))))

(def-fns _ $ (many stmt-code : (many (StmtK) k) -> (many (Nat) n))
  (match many k _ ((StLet) 0) ((StDefLvl) 1) ((StDefFns) 2) ((StDefAdts) 3) ((StComptimeMatch) 4) ((StLetMatch) 5) ((StUnary) 6) ((StOpenAdt) 7) ((StDefUnique) 8) ((StDumpContext) 9) ((StSlotSelf) 10) ((StOpenAtFn) 11) ((StCompileError) 12) ((StCompileWarn) 13) ((StDefOpaque) 14) ((StDefPrim) 15)))

(def-fns _ $ (many former-code : (many (FormerK) k) -> (many (Nat) n))
  (match many k _ ((FoFn) 0) ((FoTyCtor) 1) ((FoValCtor) 2) ((FoMatchable) 3) ((FoUniqueFn) 4) ((FoCell) 5)))

(def-fns _ $ (many expr-code : (many (ExprK) k) -> (many (Nat) n))
  (match many k _
    ((ExMatch) 0) ((ExMatchableOf) 1) ((ExSlotOf) 2) ((ExAtFnOf) 20) ((ExShare) 21) ((ExCellAlloc) 22) ((ExCellWrite) 23) ((ExCellMatch) 24) ((ExCoercibleShare) 25) ((ExNumeralOf) 3) ((ExLevelOf) 4) ((ExProveSubterm) 5)
    ((ExProvePredates) 6) ((ExValues) 7) ((ExPredatesTrans) 8) ((ExSubtermTrans) 9) ((ExPredatesSubterm) 10)
    ((ExCoerce) 11) ((ExCoercibleRefl) 12) ((ExCoercibleSym) 13) ((ExCoercibleTrans) 14) ((ExCoercibleWrap) 15)
    ((ExCoercibleCtor) 16) ((ExCoercibleOf) 17) ((ExProveLiteralLt) 18) ((ExOpenAbsurd) 19) ((ExDelegateOf) 26) ((ExWorldDo) 27) ((ExGensym) 28) ((ExGensymUnique) 29) ((ExSettledOf) 30)
    ((ExSettledMult) 31) ((ExSettledValue) 32) ((ExInternNat) 33) ((ExInternChar) 34) ((ExInternString) 35) ((ExSettledType) 36) ((ExSettledEq) 37) ((ExSettledErase) 38) ((ExResolve) 39) ((ExReadFile) 40)
    ((ExPlaceAt) 41) ((ExPlaceAtMany) 42) ((ExUnplaceAt) 43) ((ExUnplaceAtMany) 44) ((ExPlacedSlot) 45) ((ExPlacedEq) 46) ((ExMintSettled) 47) ((ExMintSettledErased) 48)))

(def-fns _ $ (many mark-code : (many (MarkK) k) -> (many (Nat) n))
  (match many k _
    ((MkErased) 0) ((MkMany) 1) ((MkColon) 2) ((MkIs) 3) ((MkArrow) 4) ((MkSubterm) 5) ((MkEnum) 6) ((MkUnion) 7)
    ((MkTail) 8) ((MkDelegate) 9) ((MkPredates) 10) ((MkAbsurd) 11) ((MkNewtypeMark) 12) ((MkExtern) 13) ((MkElse) 14) ((MkUnique) 15) ((MkAt) 16) ((MkNoTail) 17)))

(def-fns _ $ (many sp-arity : (many (Sp) sp) -> (many (Maybe $ Nat) n))
  (match many sp _
    ((SpMark k) (match many k _ ((MkTail) (Some _ 1)) ((MkNoTail) (Some _ 1)) ((MkDelegate) (Some _ 1)) (else (None _))))
    ((SpExpr k)
      (match many k _
        ((ExMatchableOf) (Some _ 1)) ((ExSlotOf) (Some _ 1)) ((ExAtFnOf) (Some _ 1)) ((ExNumeralOf) (Some _ 1)) ((ExLevelOf) (Some _ 1)) ((ExCoercibleSym) (Some _ 1)) ((ExCoercibleShare) (Some _ 1)) ((ExCoercibleOf) (Some _ 1)) ((ExDelegateOf) (Some _ 1)) ((ExSettledOf) (Some _ 2))
        ((ExProveSubterm) (Some _ 2)) ((ExProvePredates) (Some _ 2)) ((ExProveLiteralLt) (Some _ 2)) ((ExPredatesTrans) (Some _ 2)) ((ExSubtermTrans) (Some _ 2)) ((ExPredatesSubterm) (Some _ 2)) ((ExCoerce) (Some _ 2)) ((ExCoercibleRefl) (Some _ 2)) ((ExCoercibleTrans) (Some _ 2))
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
  sp-cons "let-match" (SpStmt $ StLetMatch) $ sp-cons "unary" (SpStmt $ StUnary) $ sp-cons "prove-literal-lt" (SpExpr $ ExProveLiteralLt) $
  sp-cons "open-adt" (SpStmt $ StOpenAdt) $ sp-cons "open-absurd" (SpExpr $ ExOpenAbsurd) $
  sp-cons "Fn" (SpFormer $ FoFn) $ sp-cons "UniqueFn" (SpFormer $ FoUniqueFn) $ sp-cons "TyCtor" (SpFormer $ FoTyCtor) $ sp-cons "ValCtor" (SpFormer $ FoValCtor) $
  sp-cons "Matchable" (SpFormer $ FoMatchable) $
  sp-cons "cell-alloc" (SpExpr $ ExCellAlloc) $ sp-cons "cell-write" (SpExpr $ ExCellWrite) $ sp-cons "cell-match" (SpExpr $ ExCellMatch) $ sp-cons "Cell" (SpFormer $ FoCell) $ sp-cons "slot-of" (SpExpr $ ExSlotOf) $ sp-cons "slot-self" (SpStmt $ StSlotSelf) $ sp-cons "at-fn-of" (SpExpr $ ExAtFnOf) $ sp-cons "open-at-fn" (SpStmt $ StOpenAtFn) $ sp-cons "at" (SpMark $ MkAt) $ sp-cons "share" (SpExpr $ ExShare) $ sp-cons "match" (SpExpr $ ExMatch) $ sp-cons "matchable-of" (SpExpr $ ExMatchableOf) $
  sp-cons "numeral-of" (SpExpr $ ExNumeralOf) $ sp-cons "level-of" (SpExpr $ ExLevelOf) $ sp-cons "prove-subterm" (SpExpr $ ExProveSubterm) $
  sp-cons "prove-predates" (SpExpr $ ExProvePredates) $ sp-cons "values" (SpExpr $ ExValues) $
  sp-cons "predates-trans" (SpExpr $ ExPredatesTrans) $ sp-cons "subterm-trans" (SpExpr $ ExSubtermTrans) $
  sp-cons "predates-subterm" (SpExpr $ ExPredatesSubterm) $
  sp-cons "coerce" (SpExpr $ ExCoerce) $ sp-cons "coercible-refl" (SpExpr $ ExCoercibleRefl) $ sp-cons "coercible-sym" (SpExpr $ ExCoercibleSym) $
  sp-cons "coercible-trans" (SpExpr $ ExCoercibleTrans) $ sp-cons "coercible-wrap" (SpExpr $ ExCoercibleWrap) $
  sp-cons "coercible-ctor" (SpExpr $ ExCoercibleCtor) $ sp-cons "coercible-of" (SpExpr $ ExCoercibleOf) $ sp-cons "delegate-of" (SpExpr $ ExDelegateOf) $ sp-cons "coercible-share" (SpExpr $ ExCoercibleShare) $ sp-cons "dump-context" (SpStmt $ StDumpContext) $ sp-cons "compile-error" (SpStmt $ StCompileError) $ sp-cons "compile-warn" (SpStmt $ StCompileWarn) $ sp-cons "world-do" (SpExpr $ ExWorldDo) $ sp-cons "gensym" (SpExpr $ ExGensym) $ sp-cons "gensym-unique" (SpExpr $ ExGensymUnique) $ sp-cons "settled-of" (SpExpr $ ExSettledOf) $ sp-cons "settled-type" (SpExpr $ ExSettledType) $ sp-cons "settled-erase" (SpExpr $ ExSettledErase) $ sp-cons "settled-eq" (SpExpr $ ExSettledEq) $ sp-cons "resolve" (SpExpr $ ExResolve) $ sp-cons "read-file" (SpExpr $ ExReadFile) $ sp-cons "settled-mult" (SpExpr $ ExSettledMult) $ sp-cons "settled-value" (SpExpr $ ExSettledValue) $ sp-cons "intern-nat" (SpExpr $ ExInternNat) $ sp-cons "intern-char" (SpExpr $ ExInternChar) $ sp-cons "intern-string" (SpExpr $ ExInternString) $ sp-cons "mint-settled" (SpExpr $ ExMintSettled) $ sp-cons "mint-settled-erased" (SpExpr $ ExMintSettledErased) $ sp-cons "def-opaque" (SpStmt $ StDefOpaque) $ sp-cons "def-prim" (SpStmt $ StDefPrim) $
  sp-cons "place-at" (SpExpr $ ExPlaceAt) $ sp-cons "place-at-many" (SpExpr $ ExPlaceAtMany) $ sp-cons "unplace-at" (SpExpr $ ExUnplaceAt) $ sp-cons "unplace-at-many" (SpExpr $ ExUnplaceAtMany) $ sp-cons "placed-slot" (SpExpr $ ExPlacedSlot) $ sp-cons "placed-eq" (SpExpr $ ExPlacedEq) $
  sp-cons "erased" (SpMark $ MkErased) $ sp-cons "many" (SpMark $ MkMany) $ sp-cons "unique" (SpMark $ MkUnique) $ sp-cons ":" (SpMark $ MkColon) $
  sp-cons "is" (SpMark $ MkIs) $ sp-cons "->" (SpMark $ MkArrow) $ sp-cons "subterm" (SpMark $ MkSubterm) $
  sp-cons "enum" (SpMark $ MkEnum) $ sp-cons "union" (SpMark $ MkUnion) $ sp-cons "tail" (SpMark $ MkTail) $ sp-cons "notail" (SpMark $ MkNoTail) $
  sp-cons "delegate" (SpMark $ MkDelegate) $ sp-cons "predates" (SpMark $ MkPredates) $ sp-cons "absurd" (SpMark $ MkAbsurd) $
  sp-cons "newtype" (SpMark $ MkNewtypeMark) $ sp-cons "extern" (SpMark $ MkExtern) $ sp-cons "else" (SpMark $ MkElse) (Nil _))

(def-fns _ $ (many sp-name-in : (subterm many (List $ SpEntry) es) (many (Sp) sp) -> (many (String) name))
  (let-match many es (Cons _ e rest)
    ((Nil _) "?"))
  (let-match many e (MkSpEntry n s))
  (match many (sp-eq s sp) _ ((BTrue) n) ((BFalse) (tail $ sp-name-in rest sp))))

(def-fns _ $ (many sp-name : (many (Sp) sp) -> (many (String) name))
  (sp-name-in sp-table sp))

(let ((many sp-index)) $ idmap-of-list _ sp-table 0 $ MEmpty _)

(def-fns _ $ (many sp-of-index : (many (Nat) i) -> (many (Maybe $ Sp) r))
  (let-match many (idmap-get _ i sp-index) (Hit _ _ _ e _)
    ((Miss _ _ _ _) (None _)))
  (match many e _ ((MkSpEntry _ sp) (Some _ sp))))

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
  (let-match many (at-dec x f) (None _)
    ((Some _ p) (Some _ $ MHere _ _ _ p)))
  (match many (notail $ mem-dec x rest) _ ((Some _ p) (Some _ $ MThere _ _ _ p)) ((None _) (None _))))

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

; ---- The FFI's types and functions (section 42; lib/ffi.ml), each decided from its name once, at its extern mark.

(def-adts
  ((Extern : ((Nat) arity) -> Type)
    enum
    (many ExArrayNew : -> (Extern 1)) (many ExArraySwap : -> (Extern 3)) (many ExArrayPluck : -> (Extern 2)) (many ExArrayPlace : -> (Extern 3))
    (many ExArraySwapImm : -> (Extern 3)) (many ExArrayPlaceImm : -> (Extern 3)) (many ExArrayLength : -> (Extern 1)) (many ExListToArray : -> (Extern 1)) (many ExArrayMake : -> (Extern 2))
    (many ExAdd : -> (Extern 2)) (many ExSub : -> (Extern 2)) (many ExMul : -> (Extern 2)) (many ExDiv : -> (Extern 2)) (many ExDivmod : -> (Extern 2)) (many ExNatCmp : -> (Extern 2)) (many ExNatMod : -> (Extern 2)) (many ExAppend : -> (Extern 2))
    (many ExShl : -> (Extern 2)) (many ExShr : -> (Extern 2)) (many ExU62Shl : -> (Extern 2)) (many ExU62Shr : -> (Extern 2))
    (many ExNatAnd : -> (Extern 2)) (many ExNatOr : -> (Extern 2)) (many ExNatXor : -> (Extern 2)) (many ExU62And : -> (Extern 2)) (many ExU62Or : -> (Extern 2)) (many ExU62Xor : -> (Extern 2)) (many ExU62Inc : -> (Extern 1)) (many ExU62Dec : -> (Extern 1))
    (many ExNatHalve : -> (Extern 1)) (many ExTrim : -> (Extern 1)) (many ExFlatten : -> (Extern 1))
    (many ExStrCmp : -> (Extern 2)) (many ExStrLength : -> (Extern 1)) (many ExStrSplit : -> (Extern 2)) (many ExNatStr : -> (Extern 1))
    (many ExU62Add : -> (Extern 2)) (many ExU62Sub : -> (Extern 2)) (many ExU62Mul : -> (Extern 2)) (many ExU62Div : -> (Extern 2)) (many ExU62Divmod : -> (Extern 2)) (many ExU62Mod : -> (Extern 2)) (many ExU62Cmp : -> (Extern 2))
    (many ExLtDec : -> (Extern 2)) (many ExU62LtDec : -> (Extern 2)) (many ExArrayGet : -> (Extern 2))
    (many ExArrayGetMany : -> (Extern 2)) (many ExArrayLengthMany : -> (Extern 1))
    (many ExBytesMake : -> (Extern 2)) (many ExBytesGet : -> (Extern 2)) (many ExBytesGetMany : -> (Extern 2)) (many ExBytesSet : -> (Extern 3))
    (many ExBytesLength : -> (Extern 1)) (many ExBytesLengthMany : -> (Extern 1)) (many ExStrBytesCopy : -> (Extern 1)) (many ExBytesStr : -> (Extern 1))
    (many ExBytesCopy : -> (Extern 1)) (many ExArrayCopy : -> (Extern 1))
    (many ExBytesSub : -> (Extern 3)) (many ExBytesBlit : -> (Extern 5)) (many ExArraySub : -> (Extern 3)) (many ExArrayBlit : -> (Extern 5)))
  ((SomeExtern : -> Type)
    enum
    (many MkSomeExtern : (erased (Nat) n) (many (Extern n) e) -> (SomeExtern))))

; The shape an implementation's view has (lib/ffi_core.ml), which its model must have too: the many-field
; arities of the non-phantom constructors in order, every one of them tagged. An extern function that builds
; a plain type's values records that type's shape the same way; one that builds none records nothing.
(def-fns _ $ (many ext-result-shape : (erased (Nat) n) (many (Extern n) e) -> (many (Maybe $ List $ Nat) s))
  (let ((many (List $ Nat) cmp)) (Cons _ 0 $ Cons _ 0 $ Cons _ 0 $ Nil _))
  (let ((many (List $ Nat) dec)) (Cons _ 0 $ Cons _ 0 $ Nil _))
  (match many e _
    ((ExArrayNew) (None _)) ((ExArraySwap) (None _)) ((ExArrayPluck) (None _)) ((ExArrayPlace) (None _))
    ((ExArraySwapImm) (None _)) ((ExArrayPlaceImm) (None _)) ((ExArrayLength) (None _)) ((ExListToArray) (None _)) ((ExArrayMake) (None _))
    ((ExNatCmp) (Some _ cmp)) ((ExStrCmp) (Some _ cmp))
    ((ExAdd) (None _)) ((ExSub) (None _)) ((ExMul) (None _)) ((ExDiv) (None _)) ((ExDivmod) (None _))
    ((ExNatMod) (None _)) ((ExAppend) (None _)) ((ExShl) (None _)) ((ExShr) (None _)) ((ExU62Shl) (None _)) ((ExU62Shr) (None _)) ((ExNatAnd) (None _)) ((ExNatOr) (None _)) ((ExNatXor) (None _)) ((ExU62And) (None _)) ((ExU62Or) (None _)) ((ExU62Xor) (None _)) ((ExU62Inc) (None _)) ((ExU62Dec) (None _)) ((ExNatHalve) (None _)) ((ExTrim) (None _))
    ((ExFlatten) (None _)) ((ExStrLength) (None _)) ((ExStrSplit) (None _)) ((ExNatStr) (None _))
    ((ExU62Add) (None _)) ((ExU62Sub) (None _)) ((ExU62Mul) (None _)) ((ExU62Div) (None _)) ((ExU62Divmod) (None _)) ((ExU62Mod) (None _)) ((ExU62Cmp) (Some _ cmp))
    ((ExLtDec) (Some _ dec)) ((ExU62LtDec) (Some _ dec)) ((ExArrayGet) (None _))
    ((ExArrayGetMany) (None _)) ((ExArrayLengthMany) (None _))
    ((ExBytesMake) (None _)) ((ExBytesGet) (None _)) ((ExBytesGetMany) (None _)) ((ExBytesSet) (None _))
    ((ExBytesLength) (None _)) ((ExBytesLengthMany) (None _)) ((ExStrBytesCopy) (None _)) ((ExBytesStr) (None _)) ((ExBytesCopy) (None _)) ((ExArrayCopy) (None _))
    ((ExBytesSub) (None _)) ((ExBytesBlit) (None _)) ((ExArraySub) (None _)) ((ExArrayBlit) (None _))))

(def-fns _ $ (many ext-arity : (erased (Nat) n) (many (Extern n) e) -> (many n is m))
  (match many e _
    ((ExArrayNew) 1) ((ExArraySwap) 3) ((ExArrayPluck) 2) ((ExArrayPlace) 3)
    ((ExArraySwapImm) 3) ((ExArrayPlaceImm) 3) ((ExArrayLength) 1) ((ExListToArray) 1) ((ExArrayMake) 2)
    ((ExAdd) 2) ((ExSub) 2) ((ExMul) 2) ((ExDiv) 2) ((ExDivmod) 2) ((ExNatCmp) 2) ((ExNatMod) 2) ((ExAppend) 2) ((ExShl) 2) ((ExShr) 2) ((ExU62Shl) 2) ((ExU62Shr) 2) ((ExNatAnd) 2) ((ExNatOr) 2) ((ExNatXor) 2) ((ExU62And) 2) ((ExU62Or) 2) ((ExU62Xor) 2) ((ExU62Inc) 1) ((ExU62Dec) 1)
    ((ExNatHalve) 1) ((ExTrim) 1) ((ExFlatten) 1) ((ExStrCmp) 2) ((ExStrLength) 1) ((ExStrSplit) 2) ((ExNatStr) 1)
    ((ExU62Add) 2) ((ExU62Sub) 2) ((ExU62Mul) 2) ((ExU62Div) 2) ((ExU62Divmod) 2) ((ExU62Mod) 2) ((ExU62Cmp) 2)
    ((ExLtDec) 2) ((ExU62LtDec) 2) ((ExArrayGet) 2) ((ExArrayGetMany) 2) ((ExArrayLengthMany) 1)
    ((ExBytesMake) 2) ((ExBytesGet) 2) ((ExBytesGetMany) 2) ((ExBytesSet) 3) ((ExBytesLength) 1) ((ExBytesLengthMany) 1) ((ExStrBytesCopy) 1) ((ExBytesStr) 1) ((ExBytesCopy) 1) ((ExArrayCopy) 1) ((ExBytesSub) 3) ((ExBytesBlit) 5) ((ExArraySub) 3) ((ExArrayBlit) 5)))

(def-fns _ $ (many ext-twin : (erased (Nat) n) (many (Extern n) e) -> (many (Extern n) r))
  (match many e _
    ((ExU62Add) (ExAdd)) ((ExU62Sub) (ExSub)) ((ExU62Mul) (ExMul)) ((ExU62Div) (ExDiv)) ((ExU62Divmod) (ExDivmod))
    ((ExU62Mod) (ExNatMod)) ((ExU62Shl) (ExShl)) ((ExU62Shr) (ExShr)) ((ExU62And) (ExNatAnd)) ((ExU62Or) (ExNatOr)) ((ExU62Xor) (ExNatXor)) ((ExU62Cmp) (ExNatCmp)) ((ExU62LtDec) (ExLtDec)) ((ExArrayGet) (ExArrayPluck))
    ((ExArrayGetMany) (ExArrayPluck)) ((ExArrayLengthMany) (ExArrayLength)) ((ExBytesGetMany) (ExBytesGet)) ((ExBytesLengthMany) (ExBytesLength))
    ((ExArraySwapImm) (ExArraySwap)) ((ExArrayPlaceImm) (ExArrayPlace))
    (else e)))

(def-fns _ $ (many ext-name : (erased (Nat) n) (many (Extern n) e) -> (many (String) s))
  (match many e _
    ((ExArrayNew) "array-new") ((ExArraySwap) "array-swap") ((ExArrayPluck) "array-pluck") ((ExArrayPlace) "array-place")
    ((ExArraySwapImm) "array-swap-imm") ((ExArrayPlaceImm) "array-place-imm") ((ExArrayLength) "array-length") ((ExListToArray) "list-to-array") ((ExArrayMake) "array-make")
    ((ExAdd) "add") ((ExSub) "sub") ((ExMul) "mul") ((ExDiv) "div") ((ExDivmod) "divmod") ((ExNatCmp) "nat-cmp") ((ExNatMod) "nat-mod") ((ExAppend) "append")
    ((ExShl) "shl") ((ExShr) "shr") ((ExU62Shl) "u62-shl") ((ExU62Shr) "u62-shr")
    ((ExNatAnd) "nat-and") ((ExNatOr) "nat-or") ((ExNatXor) "nat-xor") ((ExU62And) "u62-and") ((ExU62Or) "u62-or") ((ExU62Xor) "u62-xor") ((ExU62Inc) "u62-inc") ((ExU62Dec) "u62-dec")
    ((ExNatHalve) "nat-halve") ((ExTrim) "trim") ((ExFlatten) "flatten")
    ((ExStrCmp) "str-cmp") ((ExStrLength) "str-length") ((ExStrSplit) "str-split") ((ExNatStr) "nat-str")
    ((ExU62Add) "u62-add") ((ExU62Sub) "u62-sub") ((ExU62Mul) "u62-mul") ((ExU62Div) "u62-div") ((ExU62Divmod) "u62-divmod") ((ExU62Mod) "u62-mod") ((ExU62Cmp) "u62-cmp")
    ((ExLtDec) "lt-dec") ((ExU62LtDec) "u62-lt-dec") ((ExArrayGet) "array-get")
    ((ExArrayGetMany) "array-get-many") ((ExArrayLengthMany) "array-length-many")
    ((ExBytesMake) "bytes-make") ((ExBytesGet) "bytes-get") ((ExBytesGetMany) "bytes-get-many") ((ExBytesSet) "bytes-set")
    ((ExBytesLength) "bytes-length") ((ExBytesLengthMany) "bytes-length-many") ((ExStrBytesCopy) "str-bytes-copy") ((ExBytesStr) "bytes-str") ((ExBytesCopy) "bytes-copy") ((ExArrayCopy) "array-copy")
    ((ExBytesSub) "bytes-sub") ((ExBytesBlit) "bytes-blit") ((ExArraySub) "array-sub") ((ExArrayBlit) "array-blit")))

(let ((many externs))
  $ Cons _ (MkSomeExtern _ $ ExArrayNew) $ Cons _ (MkSomeExtern _ $ ExArraySwap) $ Cons _ (MkSomeExtern _ $ ExArrayPluck) $ Cons _ (MkSomeExtern _ $ ExArrayPlace) $ Cons _ (MkSomeExtern _ $ ExArraySwapImm) $ Cons _ (MkSomeExtern _ $ ExArrayPlaceImm) $
  Cons _ (MkSomeExtern _ $ ExArrayLength) $ Cons _ (MkSomeExtern _ $ ExListToArray) $ Cons _ (MkSomeExtern _ $ ExArrayMake) $ Cons _ (MkSomeExtern _ $ ExAdd) $ Cons _ (MkSomeExtern _ $ ExSub) $ Cons _ (MkSomeExtern _ $ ExMul) $ Cons _ (MkSomeExtern _ $ ExDiv) $ Cons _ (MkSomeExtern _ $ ExDivmod) $ Cons _ (MkSomeExtern _ $ ExNatCmp) $ Cons _ (MkSomeExtern _ $ ExNatMod) $ Cons _ (MkSomeExtern _ $ ExAppend) $
  Cons _ (MkSomeExtern _ $ ExShl) $ Cons _ (MkSomeExtern _ $ ExShr) $ Cons _ (MkSomeExtern _ $ ExU62Shl) $ Cons _ (MkSomeExtern _ $ ExU62Shr) $
  Cons _ (MkSomeExtern _ $ ExNatAnd) $ Cons _ (MkSomeExtern _ $ ExNatOr) $ Cons _ (MkSomeExtern _ $ ExNatXor) $ Cons _ (MkSomeExtern _ $ ExU62And) $ Cons _ (MkSomeExtern _ $ ExU62Or) $ Cons _ (MkSomeExtern _ $ ExU62Xor) $ Cons _ (MkSomeExtern _ $ ExU62Inc) $ Cons _ (MkSomeExtern _ $ ExU62Dec) $
  Cons _ (MkSomeExtern _ $ ExNatHalve) $ Cons _ (MkSomeExtern _ $ ExTrim) $ Cons _ (MkSomeExtern _ $ ExFlatten) $
  Cons _ (MkSomeExtern _ $ ExStrCmp) $ Cons _ (MkSomeExtern _ $ ExStrLength) $ Cons _ (MkSomeExtern _ $ ExStrSplit) $ Cons _ (MkSomeExtern _ $ ExNatStr) $
  Cons _ (MkSomeExtern _ $ ExU62Add) $ Cons _ (MkSomeExtern _ $ ExU62Sub) $ Cons _ (MkSomeExtern _ $ ExU62Mul) $ Cons _ (MkSomeExtern _ $ ExU62Div) $ Cons _ (MkSomeExtern _ $ ExU62Divmod) $ Cons _ (MkSomeExtern _ $ ExU62Mod) $ Cons _ (MkSomeExtern _ $ ExU62Cmp) $
  Cons _ (MkSomeExtern _ $ ExLtDec) $ Cons _ (MkSomeExtern _ $ ExU62LtDec) $ Cons _ (MkSomeExtern _ $ ExArrayGet) $
  Cons _ (MkSomeExtern _ $ ExArrayGetMany) $ Cons _ (MkSomeExtern _ $ ExArrayLengthMany) $
  Cons _ (MkSomeExtern _ $ ExBytesMake) $ Cons _ (MkSomeExtern _ $ ExBytesGet) $ Cons _ (MkSomeExtern _ $ ExBytesGetMany) $ Cons _ (MkSomeExtern _ $ ExBytesSet) $
  Cons _ (MkSomeExtern _ $ ExBytesLength) $ Cons _ (MkSomeExtern _ $ ExBytesLengthMany) $ Cons _ (MkSomeExtern _ $ ExStrBytesCopy) $ Cons _ (MkSomeExtern _ $ ExBytesStr) $
  Cons _ (MkSomeExtern _ $ ExBytesCopy) $ Cons _ (MkSomeExtern _ $ ExArrayCopy) $
  Cons _ (MkSomeExtern _ $ ExBytesSub) $ Cons _ (MkSomeExtern _ $ ExBytesBlit) $ Cons _ (MkSomeExtern _ $ ExArraySub) $ Cons _ (MkSomeExtern _ $ ExArrayBlit) (Nil _))

(def-fns _ $ (many extern-named : (subterm many (List $ SomeExtern) es) (many (String) name) -> (many (Maybe $ SomeExtern) r))
  (let-match many es (Cons _ e rest) ((Nil _) (None _)))
  (match many (match many e (((Bool) _)) ((MkSomeExtern _ x) (str-eq name $ ext-name _ x))) _
    ((BTrue) (Some _ e))
    ((BFalse) (tail $ extern-named rest name))))

(def-fns _ $ (many extern-of : (many (String) name) -> (many (Maybe $ SomeExtern) r))
  (extern-named externs name))

; ---- Blocks, frames and post-erasure code (lib/value.ml): a value is an address into self/heap.sl's
; store, and a block holds section 33's representation with every address in it below its own.

(def-adts
  ((Payload : -> Type)
    enum
    (many PNat : (many (Nat) n) -> (Payload))
    (many PHalf : (many (Nat) n) -> (Payload))
    (many PStr : (many (String) s) -> (Payload))
    (many PBytes : (many (String) s) -> (Payload))
    (many PRaw : (many (String) file) (many (Syn) r) -> (Payload))
    (many PHandle : (many (Nat) id) (many (Reading) rd) (many (Multiplicity) m) (many (String) shown) -> (Payload)))
  ((ExtType : -> Type)
    enum
    (many ExtArray : -> (ExtType)) (many ExtNat : -> (ExtType)) (many ExtHalf : -> (ExtType)) (many ExtString : -> (ExtType)) (many ExtBytes : -> (ExtType))
    (many ExtRaw : (many (Ctor) nopos) (many (Ctor) mkpos) (many (Ctor) nil) (many (Ctor) cons) (many (Ctor) sname) (many (Ctor) sgen) -> (ExtType)))
  ; [tagged]: an enum with more than one non-phantom constructor (section 33); [ctors]: the non-phantom
  ; ones at their discriminants; [ext]: the extern type's name where the FFI holds it (section 42); a
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
  ; read off the model's return type at the extern mark (section 42).
  ((Impl : -> Type)
    enum
    (many MkImpl : (many (SomeExtern) e) (many (List $ Ctor) cs) -> (Impl)))
  ((Func : ((List $ Nat) gids) ((List $ List $ Nat) ctx) -> Type)
    enum
    (many MkFunc : (erased (List $ Nat) gids) (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) rets) (many (String) name) (many (Nat) id) (many (List $ Nat) params) (many (Code (Cons (List (Nat)) params (Cons (List (Nat)) gids ctx)) rets) body) (many (Maybe $ Impl) impl) (many (Bool) top) -> (Func gids ctx))
    (many MkAlias : (erased (List $ Nat) gids) (erased (List $ List $ Nat) ctx) (many (String) name) (many (Nat) id) (many (Code (Cons (List (Nat)) gids ctx) many-one) target) -> (Func gids ctx)))
  ; [ctx]: the frames in scope; [ms]: the multiplicities of the values the code produces, the many ones being
  ; what runs (section 27); a node that has to make values on its own holds them as data. A Settled entry is
  ; named by its id and read from the store when the code runs (section 29); a value elaboration embeds is
  ; a closed block, allocated when reached.
  ((Code : ((List $ List $ Nat) ctx) ((List $ Multiplicity) ms) -> Type)
    enum
    (many CVar : (erased (List $ List $ Nat) ctx) (many (Nat) id) (many (Mem id ctx) p) -> (Code ctx many-one))
    (many CConst : (erased (List $ List $ Nat) ctx) (many (Nat) id) -> (Code ctx many-one))
    (many CValue : (erased (List $ List $ Nat) ctx) (many (Block (Ref Block (HEmpty Block))) v) -> (Code ctx many-one))
    (many CErased : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ms) -> (Code ctx ms))
    (many CValues : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ms) (many (List $ Code ctx many-one) cs) (erased (Picked (Code ctx many-one) ms cs) pk) -> (Code ctx ms))
    (many CApp : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ms) (many (Code ctx many-one) f) (many (List $ Code ctx many-one) args) (many (CC) cc) -> (Code ctx ms))
    (many CLet : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ms) (erased (List $ Multiplicity) ns) (many (List $ Nat) ids) (erased (Picked (Nat) ms ids) pk) (many (Code ctx ms) rhs) (many (Code (Cons (List (Nat)) ids ctx) ns) rest) -> (Code ctx ns))
    (many CLetRec : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ns) (erased (List $ Nat) gids) (many (Group gids ctx) g) (many (Code (Cons (List (Nat)) gids ctx) ns) rest) -> (Code ctx ns))
    (many CMatch : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ns) (many (Code ctx many-one) scrut) (many (Shape ctx) shape) (many (List $ Branch ctx ns) branches) (many (Maybe $ Code (Cons (List (Nat)) (Nil (Nat)) ctx) ns) dflt) (many (List $ Nat) live) -> (Code ctx ns))
    (many CCellAlloc : (erased (List $ List $ Nat) ctx) (many (Ctor) ctor) (many (List $ Code ctx many-one) slots) -> (Code ctx many-one))
    (many CCellWrite : (erased (List $ List $ Nat) ctx) (many (Ctor) ctor) (many (Code ctx many-one) cell) (many (List $ Pair (Nat) $ Code ctx many-one) slots) -> (Code ctx many-one))
    (many CCellCopy : (erased (List $ List $ Nat) ctx) (many (Ctor) ctor) (many (Code ctx many-one) cell) (many (List $ Pair (Nat) $ Code ctx many-one) slots) -> (Code ctx many-one))
    (many CCellRead : (erased (List $ List $ Nat) ctx) (many (Ctor) ctor) (many (Nat) index) (many (Code ctx many-one) cell) -> (Code ctx many-one))
    (many CWorldDo : (erased (List $ List $ Nat) ctx) (many (Code ctx many-one) req) -> (Code ctx many-one))
    (many CPrim : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ms) (many (Sp) prim) (many (List $ Code ctx many-one) args) -> (Code ctx ms))
    (many CAbsurd : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ms) -> (Code ctx ms))
    (many CError : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ms) (many (String) msg) -> (Code ctx ms)))
  ((CC : -> Type)
    enum
    (many CCPlain : -> (CC)) (many CCTail : -> (CC)) (many CCDelegate : -> (CC)) (many CCCtor : -> (CC)) (many CCNoTail : -> (CC))
    ; a same-level call in a non-erased position carrying no mark, where the tail-position check warns
    (many CCSame : (many (Loc) site) (many (String) callee) -> (CC)))
  ((Shape : ((List $ List $ Nat) ctx) -> Type)
    enum
    (many ShKnown : (erased (List $ List $ Nat) ctx) (many (Adt) adt) -> (Shape ctx))
    (many ShHeld : (erased (List $ List $ Nat) ctx) (many (Code ctx many-one) c) (many (Adt) adt) -> (Shape ctx))
    (many ShNone : (erased (List $ List $ Nat) ctx) -> (Shape ctx)))
  ((Branch : ((List $ List $ Nat) ctx) ((List $ Multiplicity) ns) -> Type)
    enum
    (many MkBranch : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ns) (many (Nat) disc) (many (List $ Nat) ids) (many (Code (Cons (List (Nat)) ids ctx) ns) body) -> (Branch ctx ns))))

(def-fns _ $ (many ext-type-name : (many (ExtType) t) -> (many (String) s))
  (match many t _ ((ExtArray) "Array") ((ExtNat) "Nat") ((ExtHalf) "Half") ((ExtString) "String") ((ExtBytes) "Bytes") ((ExtRaw _ _ _ _ _ _) "Raw")))

(def-fns _ $ (many ext-type-shape : (many (ExtType) t) -> (many (List $ Nat) s))
  (match many t _
    ((ExtArray) (Cons _ 0 $ Cons _ 2 $ Nil _))
    ((ExtNat) (Cons _ 0 $ Cons _ 1 $ Nil _))
    ((ExtHalf) (Cons _ 0 $ Cons _ 1 $ Cons _ 1 $ Nil _))
    ((ExtString) (Cons _ 0 $ Cons _ 2 $ Nil _))
    ((ExtBytes) (Cons _ 0 $ Cons _ 2 $ Nil _))
    ((ExtRaw _ _ _ _ _ _) (Cons _ 2 $ Cons _ 1 $ Cons _ 2 $ Cons _ 2 $ Nil _))))

(def-fns _ $ (many ext-type-of : (many (String) name) -> (many (Maybe $ ExtType) r))
  (let-match many (str-eq name "Nat") (BFalse) ((BTrue) (Some _ $ ExtNat)))
  (let-match many (str-eq name "Half") (BFalse) ((BTrue) (Some _ $ ExtHalf)))
  (let-match many (str-eq name "String") (BFalse) ((BTrue) (Some _ $ ExtString)))
  (let-match many (str-eq name "Array") (BFalse) ((BTrue) (Some _ $ ExtArray)))
  (match many (str-eq name "Bytes") _ ((BTrue) (Some _ $ ExtBytes)) ((BFalse) (None _))))

; Widening the bound of every holder of addresses is a coerce (section 33).

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
  ((many recast : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ns) (many (List $ Multiplicity) ms) (erased (ManySame ms ns) same) (subterm many (Code ctx ms) c) -> (many (Code ctx ns) r))
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
      ((CCellCopy _ _ _ _) (CValues _ ns (Cons _ c $ Nil _) $ picked-same _ _ _ _ same $ PkMany _ (Nil _) c (Nil _) $ PkNil _))
      ((CCellRead _ _ _ _) (CValues _ ns (Cons _ c $ Nil _) $ picked-same _ _ _ _ same $ PkMany _ (Nil _) c (Nil _) $ PkNil _))
      ((CWorldDo _ _) (CValues _ ns (Cons _ c $ Nil _) $ picked-same _ _ _ _ same $ PkMany _ (Nil _) c (Nil _) $ PkNil _))
      ((CPrim _ _ p args) (CPrim _ ns p args))
      ((CAbsurd _ _) (CAbsurd _ ns))
      ((CError _ _ m) (CError _ ns m)))
    (CMatch _ ns scrut shape (notail $ recast-branches _ ns ms same branches)
      (match many dfl (((Maybe $ Code (Cons (List (Nat)) (Nil (Nat)) ctx) ns) _)) ((Some _ d) (Some _ $ notail $ recast _ ns ms same d)) ((None _) (None _))) live))
  ((many recast-branches : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ns) (many (List $ Multiplicity) ms) (erased (ManySame ms ns) same) (subterm many (List $ Branch ctx ms) bs) -> (many (List $ Branch ctx ns) r))
    (let-match many bs (Cons _ b rest)
      ((Nil _) (Nil _)))
    (match many b _ ((MkBranch _ _ d ids body) (Cons _ (MkBranch _ _ d ids $ notail $ recast _ ns ms same body) $ notail $ recast-branches _ ns ms same rest)))))

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
    (many FrSlotOf : (erased (Nat) n) (erased (Facts n) f) (erased (Term) c) -> (Fr n f $ TSlotOf c))
    (many FrErr : (erased (Nat) n) (erased (Facts n) f) (erased (String) m) -> (Fr n f $ TErr m)))
  ((FrL : ((Nat) n) ((Facts n) f) ((List $ Term) ts) -> Type)
    enum
    (many FrLNil : (erased (Nat) n) (erased (Facts n) f) -> (FrL n f $ Nil $ Term))
    (many FrLCons : (erased (Nat) n) (erased (Facts n) f) (erased (Term) t) (erased (List $ Term) rest) (erased (Fr n f t) p) (erased (FrL n f rest) q) -> (FrL n f $ Cons (Term) t rest)))
  ((FrT : ((Nat) n) ((Facts n) f) ((List $ Entry) es) -> Type)
    enum
    (many FrTNil : (erased (Nat) n) (erased (Facts n) f) -> (FrT n f $ Nil $ Entry))
    (many FrTCons : (erased (Nat) n) (erased (Facts n) f) (erased (Maybe $ Name) nm) (erased (Bool) s) (erased (Multiplicity) mu) (erased (Sg) sg) (erased (Maybe $ Term) place) (erased (Maybe $ Loc) site) (erased (List $ Entry) rest) (erased (FrS n f sg) p) (erased (FrP n f place) pp) (erased (FrT n f rest) q) -> (FrT n f $ Cons (Entry) (MkEntry nm s mu sg place site) rest)))
  ((FrP : ((Nat) n) ((Facts n) f) ((Maybe $ Term) p) -> Type)
    enum
    (many FrPNone : (erased (Nat) n) (erased (Facts n) f) -> (FrP n f $ None $ Term))
    (many FrPSome : (erased (Nat) n) (erased (Facts n) f) (erased (Term) t) (erased (Fr n f t) p) -> (FrP n f $ Some (Term) t)))
  ((FrS : ((Nat) n) ((Facts n) f) ((Sg) sg) -> Type)
    enum
    (many FrSTy : (erased (Nat) n) (erased (Facts n) f) (erased (Term) t) (erased (Fr n f t) p) -> (FrS n f $ SgTy t))
    (many FrSIs : (erased (Nat) n) (erased (Facts n) f) (erased (Term) t) (erased (Term) ty) (erased (Fr n f t) p) -> (FrS n f $ SgIs t ty)))
  ((FrM : ((Nat) n) ((Facts n) f) ((List $ MCtor) cs) -> Type)
    enum
    (many FrMNil : (erased (Nat) n) (erased (Facts n) f) -> (FrM n f $ Nil $ MCtor))
    (many FrMCons : (erased (Nat) n) (erased (Facts n) f) (erased (Multiplicity) mu) (erased (Term) c) (erased (List $ MCtor) rest) (erased (Fr n f c) p) (erased (FrM n f rest) q) -> (FrM n f $ Cons (MCtor) (MkMCtor mu c) rest))))

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
  ((GuardP : ((Maybe $ Term) p) ((List $ Nat) seen) -> Type)
    enum
    (many GPTop : (erased (Maybe $ Term) p) -> (GuardP p $ Nil $ Nat))
    (many GPAv : (erased (Maybe $ Term) p) (erased (List $ Nat) seen) (erased (Nat) n) (erased (Facts n) f) (erased (FrP n f p) q) (erased (AllRuled seen n f) a) -> (GuardP p seen)))
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

(def-fns _ $ (erased frt-cons : (erased (Nat) n) (erased (Facts n) f) (erased (Maybe $ Name) nm) (erased (Bool) s) (erased (Multiplicity) mu) (erased (Sg) sg) (erased (Maybe $ Term) place) (erased (Maybe $ Loc) site) (erased (List $ Entry) rest) (erased (FrT n f $ Cons (Entry) (MkEntry nm s mu sg place site) rest) p) -> (erased (FrS n f sg) ps) (erased (FrP n f place) pp) (erased (FrT n f rest) pr))
  (let-match erased p (FrTCons a b c d e g _ _ h ps pp pr))
  (values ps pp pr))

(def-fns _ $ (erased frp-some : (erased (Nat) n) (erased (Facts n) f) (erased (Term) t) (erased (FrP n f $ Some (Term) t) p) -> (erased (Fr n f t) pt))
  (let-match erased p (FrPSome a b c pt))
  pt)

(def-fns _ $ (erased frs-ty : (erased (Nat) n) (erased (Facts n) f) (erased (Term) t) (erased (FrS n f $ SgTy t) p) -> (erased (Fr n f t) pt))
  (let-match erased p (FrSTy a b c pt))
  pt)

(def-fns _ $ (erased frs-is : (erased (Nat) n) (erased (Facts n) f) (erased (Term) t) (erased (Term) ty) (erased (FrS n f $ SgIs t ty) p) -> (erased (Fr n f t) pt))
  (let-match erased p (FrSIs a b c d pt))
  pt)

(def-fns _ $ (erased frm-cons : (erased (Nat) n) (erased (Facts n) f) (erased (Multiplicity) mu) (erased (Term) c) (erased (List $ MCtor) rest) (erased (FrM n f $ Cons (MCtor) (MkMCtor mu c) rest) p) -> (erased (Fr n f c) pc) (erased (FrM n f rest) pr))
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

(def-fns _ $ (erased guardt-cons : (erased (Maybe $ Name) nm) (erased (Bool) s) (erased (Multiplicity) mu) (erased (Sg) sg) (erased (Maybe $ Term) place) (erased (Maybe $ Loc) site) (erased (List $ Entry) rest) (erased (List $ Nat) seen) (erased (GuardT (Cons (Entry) (MkEntry nm s mu sg place site) rest) seen) g) -> (erased (GuardS sg seen) gs) (erased (GuardP place seen) gp) (erased (GuardT rest seen) gr))
  (let-match erased g (GTAv _ _ _ _ p a) ((GTTop _) (values (GSTop _) (GPTop _) $ GTTop _)))
  (let ((erased ps) (erased pp) (erased pr)) (frt-cons _ _ _ _ _ _ _ _ _ p))
  (values (GSAv _ _ _ _ ps a) (GPAv _ _ _ _ pp a) $ GTAv _ _ _ _ pr a))

(def-fns _ $ (erased guardp-some : (erased (Term) t) (erased (List $ Nat) seen) (erased (GuardP (Some (Term) t) seen) g) -> (erased (Guard t seen) gt))
  (match erased g _
    ((GPTop _) (GTop _))
    ((GPAv _ _ n f p a) (GAv _ _ _ _ (frp-some n f t p) a))))

(def-fns _ $ (erased guards-ty : (erased (Term) t) (erased (List $ Nat) seen) (erased (GuardS (SgTy t) seen) g) -> (erased (Guard t seen) gt))
  (match erased g _
    ((GSTop _) (GTop _))
    ((GSAv _ _ n f p a) (GAv _ _ _ _ (frs-ty n f t p) a))))

(def-fns _ $ (erased guards-is : (erased (Term) t) (erased (Term) ty) (erased (List $ Nat) seen) (erased (GuardS (SgIs t ty) seen) g) -> (erased (Guard t seen) gt))
  (match erased g _
    ((GSTop _) (GTop _))
    ((GSAv _ _ n f p a) (GAv _ _ _ _ (frs-is n f t ty p) a))))

(def-fns _ $ (erased guardm-cons : (erased (Multiplicity) mu) (erased (Term) c) (erased (List $ MCtor) rest) (erased (List $ Nat) seen) (erased (GuardM (Cons (MCtor) (MkMCtor mu c) rest) seen) g) -> (erased (Guard c seen) gc) (erased (GuardM rest seen) gr))
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
; ---- Canonicalization (sections 7, 9): a chase continues along the rules after the one followed, the
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
      ((TSlotOf cn) (values t $ FrSlotOf _ _ cn))
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
    (let ((erased gs) (erased gp) (erased gr)) (guardt-cons _ _ _ _ _ _ _ _ g))
    (let ((many sg2) (erased fs)) $ notail $ canon-sg after sg _ f _ _ pre ord gs c)
    (let ((many place2) (erased fp)) $ notail $ canon-place after place _ f _ _ pre ord gp c)
    (let ((many rest2) (erased frest)) $ notail $ canon-tele after rest _ f _ _ pre ord gr c)
    (values (Cons _ (MkEntry nm s mu sg2 place2 site) rest2) (FrTCons _ _ _ _ _ _ _ _ _ fs fp frest)))
  ((many canon-place : (subterm erased (List $ Rule) after) (subterm many (Maybe $ Term) place) (erased (Nat) n) (many (Facts n) f) (erased (List $ Rule) whole) (erased (List $ Nat) seen) (erased (Prefix seen whole after) pre) (erased (Ord seen after) ord) (erased (GuardP place seen) g) (erased (C1 (Nil $ Digit) n f whole) c) ->
      (many (Maybe $ Term) r) (erased (FrP n f r) fr))
    (let-match many place (Some _ p) ((None _) (values place $ FrPNone _ _)))
    (let ((many p2) (erased fp)) $ notail $ canon after p _ f _ _ pre ord (guardp-some _ _ g) c)
    (values (Some _ p2) $ FrPSome _ _ _ fp))
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
  ((FrPBox : ((Nat) n) ((Facts n) f) ((Maybe $ Term) p) -> Type)
    enum
    (many MkFrPBox : (erased (Nat) n) (erased (Facts n) f) (erased (Maybe $ Term) p) (erased (FrP n f p) q) -> (FrPBox n f p)))
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
        (let-match many (notail $ refresh-list args _ f _ c) (Some _ ba)
          ((None _) (None _)))
        (let-match many bh (MkFrBox _ _ _ ph))
        (match many ba _ ((MkFrLBox _ _ _ pa) (Some _ $ MkFrBox _ _ _ $ FrApp n f h args ph pa))))
      ((TCell h args)
        (let-match many (notail $ refresh h _ f _ c) (Some _ bh) ((None _) (None _)))
        (let-match many (notail $ refresh-list args _ f _ c) (Some _ ba)
          ((None _) (None _)))
        (let-match many bh (MkFrBox _ _ _ ph))
        (match many ba _ ((MkFrLBox _ _ _ pa) (Some _ $ MkFrBox _ _ _ $ FrCell n f h args ph pa))))
      ((TFn uq l ps rs)
        (let-match many (notail $ refresh l _ f _ c) (Some _ bl) ((None _) (None _)))
        (let-match many (notail $ refresh-tele ps _ f _ c) (Some _ bp) ((None _) (None _)))
        (let-match many (notail $ refresh-tele rs _ f _ c) (Some _ br)
          ((None _) (None _)))
        (let-match many bl (MkFrBox _ _ _ pl))
        (let-match many bp (MkFrTBox _ _ _ pp))
        (match many br _ ((MkFrTBox _ _ _ pr) (Some _ $ MkFrBox _ _ _ (FrFn n f uq l ps rs pl pp pr)))))
      ((TTyCtor ps)
        (let-match many (notail $ refresh-tele ps _ f _ c) (Some _ bp)
          ((None _) (None _)))
        (match many bp _ ((MkFrTBox _ _ _ pp) (Some _ $ MkFrBox _ _ _ $ FrTyCtor n f ps pp))))
      ((TValCtor ps ret)
        (let-match many (notail $ refresh-tele ps _ f _ c) (Some _ bp) ((None _) (None _)))
        (let-match many (notail $ refresh ret _ f _ c) (Some _ bret)
          ((None _) (None _)))
        (let-match many bp (MkFrTBox _ _ _ pp))
        (match many bret _ ((MkFrBox _ _ _ pr) (Some _ $ MkFrBox _ _ _ $ FrValCtor n f ps ret pp pr))))
      ((TMatchable d nt ex ty cs)
        (let-match many (notail $ refresh ty _ f _ c) (Some _ bt) ((None _) (None _)))
        (let-match many (notail $ refresh-mctors cs _ f _ c) (Some _ bc)
          ((None _) (None _)))
        (let-match many bt (MkFrBox _ _ _ pt))
        (match many bc _ ((MkFrMBox _ _ _ pc) (Some _ $ MkFrBox _ _ _ (FrMatchable n f d nt ex ty cs pt pc)))))
      ((TSlotOf cn) (Some _ $ MkFrBox _ _ _ $ FrSlotOf _ _ cn))
      ((TErr m) (Some _ $ MkFrBox _ _ _ $ FrErr n f m))))
  ((many refresh-list : (subterm many (List $ Term) ts) (erased (Nat) n) (many (Facts n) f) (erased (List $ Rule) rules) (erased (C1 (Nil $ Digit) n f rules) c) -> (many (Maybe $ FrLBox n f ts) r))
    (let-match many ts (Cons _ t rest) ((Nil _) (Some _ $ MkFrLBox _ _ _ $ FrLNil n f)))
    (let-match many (notail $ refresh t _ f _ c) (Some _ bt) ((None _) (None _)))
    (let-match many (notail $ refresh-list rest _ f _ c) (Some _ br)
      ((None _) (None _)))
    (let-match many bt (MkFrBox _ _ _ pt))
    (match many br _ ((MkFrLBox _ _ _ pr) (Some _ $ MkFrLBox _ _ _ $ FrLCons n f t rest pt pr))))
  ((many refresh-tele : (subterm many (List $ Entry) es) (erased (Nat) n) (many (Facts n) f) (erased (List $ Rule) rules) (erased (C1 (Nil $ Digit) n f rules) c) -> (many (Maybe $ FrTBox n f es) r))
    (let-match many es (Cons _ e rest) ((Nil _) (Some _ $ MkFrTBox _ _ _ $ FrTNil n f)))
    (let-match many e (MkEntry nm s mu sg place site))
    (let-match many (notail $ refresh-sg sg _ f _ c) (Some _ bs) ((None _) (None _)))
    (let-match many (notail $ refresh-place place _ f _ c) (Some _ bp) ((None _) (None _)))
    (let-match many (notail $ refresh-tele rest _ f _ c) (Some _ br)
      ((None _) (None _)))
    (let-match many bs (MkFrSBox _ _ _ ps))
    (let-match many bp (MkFrPBox _ _ _ pp))
    (match many br _ ((MkFrTBox _ _ _ pr) (Some _ $ MkFrTBox _ _ _ (FrTCons n f nm s mu sg place site rest ps pp pr)))))
  ((many refresh-place : (subterm many (Maybe $ Term) place) (erased (Nat) n) (many (Facts n) f) (erased (List $ Rule) rules) (erased (C1 (Nil $ Digit) n f rules) c) -> (many (Maybe $ FrPBox n f place) r))
    (let-match many place (Some _ p) ((None _) (Some _ $ MkFrPBox _ _ _ $ FrPNone n f)))
    (let-match many (notail $ refresh p _ f _ c) (Some _ bp) ((None _) (None _)))
    (match many bp _ ((MkFrBox _ _ _ pp) (Some _ $ MkFrPBox _ _ _ $ FrPSome n f p pp))))
  ((many refresh-sg : (subterm many (Sg) sg) (erased (Nat) n) (many (Facts n) f) (erased (List $ Rule) rules) (erased (C1 (Nil $ Digit) n f rules) c) -> (many (Maybe $ FrSBox n f sg) r))
    (match many sg _
      ((SgTy t)
        (let-match many (notail $ refresh t _ f _ c) (Some _ bt)
          ((None _) (None _)))
        (match many bt _ ((MkFrBox _ _ _ pt) (Some _ $ MkFrSBox _ _ _ $ FrSTy n f t pt))))
      ((SgIs t t-ty)
        (let-match many (notail $ refresh t _ f _ c) (Some _ bt)
          ((None _) (None _)))
        (match many bt _ ((MkFrBox _ _ _ pt) (Some _ $ MkFrSBox _ _ _ $ FrSIs n f t t-ty pt))))))
  ((many refresh-mctors : (subterm many (List $ MCtor) cs) (erased (Nat) n) (many (Facts n) f) (erased (List $ Rule) rules) (erased (C1 (Nil $ Digit) n f rules) c) -> (many (Maybe $ FrMBox n f cs) r))
    (let-match many cs (Cons _ mc rest) ((Nil _) (Some _ $ MkFrMBox _ _ _ $ FrMNil n f)))
    (let-match many mc (MkMCtor mu t))
    (let-match many (notail $ refresh t _ f _ c) (Some _ bt) ((None _) (None _)))
    (let-match many (notail $ refresh-mctors rest _ f _ c) (Some _ br)
      ((None _) (None _)))
    (let-match many bt (MkFrBox _ _ _ pt))
    (match many br _ ((MkFrMBox _ _ _ pr) (Some _ $ MkFrMBox _ _ _ $ FrMCons n f mu t rest pt pr)))))

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
      (let-match erased p (In1 z1 _ ddz _ _ _ _ _ _ _ _ q3)
        ((InHere _ _ _ _ _ _ _) (InHere _ _ _ _ _ _ _))
        ((In2 _ _ ddz _ _ _ _ _ _ _ _ q3) (In2 _ _ ddz _ _ _ _ _ _ _ _ q3)))
      (match erased (double-inj x2 x1 d1 dd2 dd1) _ ((Refl _ _) (In1 _ _ ddz _ _ _ _ _ _ _ _ $ in-ins-out z1 x1 t n1b one k1 one2 k3 one3 q1 q2 q3))))
    ((Ins2 x1 d1 dd1 _ _ a2 _ _ _ two _ k2 _ two2 _ q1)
      (let-match erased o (Out2 x2 _ dd2 _ _ _ _ _ _ _ _ _ k3 _ two3 _ q2)
        (absurd (Out1 x2 _ dd2 _ _ _ _ _ _ _ _ _ _ _ _ _ _) (double-parity x2 x1 d1 dd2 dd1)))
      (let-match erased p (In2 z1 _ ddz _ _ _ _ _ _ _ _ q3)
        ((InHere _ _ _ _ _ _ _) (InHere _ _ _ _ _ _ _))
        ((In1 _ _ ddz _ _ _ _ _ _ _ _ q3) (In1 _ _ ddz _ _ _ _ _ _ _ _ q3)))
      (match erased (double-inj x2 x1 d1 dd2 dd1) _ ((Refl _ _) (In2 _ _ ddz _ _ _ _ _ _ _ _ $ in-ins-out z1 x1 t a2 two k2 two2 k3 two3 q1 q2 q3))))))

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
      ((FrSlotOf _ _ cn) (FrSlotOf _ _ cn))
      ((FrErr _ _ _) (FrErr _ _ _))))
  ((erased fresh-ins-out-list : (erased (Nat) x) (erased (Term) t) (erased (Nat) n0) (erased (Facts n0) f0) (erased (Nat) n1) (erased (Facts n1) f1) (erased (Nat) k) (erased (Facts k) f2) (erased (Ins x n0 f0 n1 f1) i) (erased (Out x t n1 f1 k f2) o) (erased (List $ Term) us) (subterm erased (FrL n0 f0 us) p) -> (erased (FrL k f2 us) q))
    (match erased p _
      ((FrLNil _ _) (FrLNil _ _))
      ((FrLCons _ _ u rest pu pr) (FrLCons _ _ _ _ (fresh-ins-out x t n0 f0 n1 f1 k f2 i o u pu) $ fresh-ins-out-list x t n0 f0 n1 f1 k f2 i o rest pr))))
  ((erased fresh-ins-out-tele : (erased (Nat) x) (erased (Term) t) (erased (Nat) n0) (erased (Facts n0) f0) (erased (Nat) n1) (erased (Facts n1) f1) (erased (Nat) k) (erased (Facts k) f2) (erased (Ins x n0 f0 n1 f1) i) (erased (Out x t n1 f1 k f2) o) (erased (List $ Entry) es) (subterm erased (FrT n0 f0 es) p) -> (erased (FrT k f2 es) q))
    (match erased p _
      ((FrTNil _ _) (FrTNil _ _))
      ((FrTCons _ _ _ _ _ sg place _ rest ps pp pr) (FrTCons _ _ _ _ _ _ _ _ _ (fresh-ins-out-sg x t n0 f0 n1 f1 k f2 i o sg ps) (fresh-ins-out-place x t n0 f0 n1 f1 k f2 i o place pp) (fresh-ins-out-tele x t n0 f0 n1 f1 k f2 i o rest pr)))))
  ((erased fresh-ins-out-place : (erased (Nat) x) (erased (Term) t) (erased (Nat) n0) (erased (Facts n0) f0) (erased (Nat) n1) (erased (Facts n1) f1) (erased (Nat) k) (erased (Facts k) f2) (erased (Ins x n0 f0 n1 f1) i) (erased (Out x t n1 f1 k f2) o) (erased (Maybe $ Term) place) (subterm erased (FrP n0 f0 place) p) -> (erased (FrP k f2 place) q))
    (match erased p _
      ((FrPNone _ _) (FrPNone _ _))
      ((FrPSome _ _ u pu) (FrPSome _ _ _ $ fresh-ins-out x t n0 f0 n1 f1 k f2 i o u pu))))
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
  (many OKMatchable : -> (OpenKind)) (many OKAtFn : -> (OpenKind)) (many OKNone : -> (OpenKind)))

(def-fns _ $ (many open-kind-code : (many (OpenKind) k) -> (many (Nat) n))
  (match many k _ ((OKMatchable) 0) ((OKAtFn) 1) ((OKNone) 2)))

; An opened Matchable or Newtype (section 8): its entry, its kind, and the names its type holds canonically,
; the type constructor first.
(def-adts $ (Opened : -> Type)
  enum
  (many MkOpened : (many (Nat) x) (many (OpenKind) kind) (many (List $ Nat) names) -> (Opened)))

(def-fns _ $ (many opened-x : (many (Opened) o) -> (many (Nat) x))
  (match many o _ ((MkOpened x _ _) x)))

(def-fns _ $ (many opened-names : (many (Opened) o) -> (many (List $ Nat) ns))
  (match many o _ ((MkOpened _ _ ns) ns)))

; The opened objects of a table, newest first, indexed by the names they hold, and those [touched] since the
; elaborator last restored section 8's invariant. Indexed by the table's facts: only opens-inserted,
; opens-out, table-open, table-unopen, table-settled and empty-table below mint one, so an Opens sits in
; the table its names are canonical under, refreshed where a variable is ruled out (rule-into).
(def-adts $ (Opens : ((Nat) n) ((Facts n) f) -> Type)
  enum
  (many MkOpens : (erased (Nat) n) (erased (Facts n) f) (many (List $ Opened) list) (many (IdMap $ List $ Nat) index) (many (List $ Nat) touched) -> (Opens n f)))

(def-fns _ $ (many nats-share : (subterm many (List $ Nat) xs) (many (List $ Nat) ys) -> (many (Bool) r))
  (match many xs _ ((Nil _) (BFalse)) ((Cons _ x rest) (or (list-mem-bin ys x) $ notail $ nats-share rest ys))))

(def-fns _ $ (many nats-remove : (subterm many (List $ Nat) xs) (many (Nat) x) -> (many (List $ Nat) r))
  (let-match many xs (Cons _ y rest)
    ((Nil _) (Nil _)))
  (match many (nat-eq x y) _ ((BTrue) (tail $ nats-remove rest x)) ((BFalse) (Cons _ y $ notail $ nats-remove rest x))))

(def-fns _ $ (many nats-dup : (subterm many (List $ Nat) xs) -> (many (Maybe $ Nat) r))
  (let-match many xs (Cons _ x rest)
    ((Nil _) (None _)))
  (match many (list-mem-bin rest x) _ ((BTrue) (Some _ x)) ((BFalse) (tail $ nats-dup rest))))

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

(def-adts $ (SlotEntry : -> Type)
  enum
  (many EntrySlot : -> (SlotEntry))
  (many MetaSlot : -> (SlotEntry))
  (many SlotAtom : -> (SlotEntry)))

(def-adts $ (Slots : -> Type)
  enum
  (many MkSlots : (many (IdMap $ SlotEntry) kinds) (many (Nat) free-metas) -> (Slots)))

(def-adts
  ((Table : ((Nat) n) ((Facts n) f) ((Nat) c) -> Type)
    enum
    (many MkTable : (erased (Nat) n) (many (Facts n) f) (erased (Nat) c) (erased (List $ Rule) ru) (erased (List $ Nat) ks) (erased (Ord (Nil $ Nat) ru) ord) (erased (Keys (Nil $ Nat) ru ks) keys) (erased (AllRuled ks n f) ar) (erased (C1 (Nil $ Digit) n f ru) c1) (erased (Above (Nil $ Digit) c n f) ab) (many (Opens n f) opens) (many (Slots) slots) -> (Table n f c)))
  ((Added : ((Nat) n) ((Facts n) f) ((Nat) c) -> Type)
    enum
    (many MkAdded : (erased (Nat) k) (erased (Facts $ Succ k) f) (erased (Facts k) f2) (erased (Nat) c) (many (Table k f2 c) tb) -> (Added (Succ k) f c))))

(let ((many empty-table)) $ MkTable _ (FEmpty) _ (Nil _) _ (OrdNil $ Nil $ Nat) (KNil $ Nil $ Nat) (ARNil (Zero) $ FEmpty) (C1Empty (Nil $ Digit) $ Nil $ Rule) (AbEmpty (Nil $ Digit) $ Zero) (MkOpens _ _ (Nil _) (MEmpty _) $ Nil _) $ MkSlots (MEmpty _) 0)

; The automatic slot of [x], the next id (section 35), both entries already in the table; a slot is its own slot.
(def-fns _ $ (many table-add-slot : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) c) (many (Table n f c) tb) (many (Nat) x) (many (Bool) meta) -> (many (Table n f c) r))
  (let ((many e)) $ match many meta (((SlotEntry) e)) ((BTrue) (MetaSlot)) ((BFalse) (EntrySlot)))
  (let-match many tb (MkTable _ f0 _ ru _ ord keys ar c1 ab op sl))
  (let-match many sl (MkSlots kinds fm))
  (MkTable _ f0 _ ru _ ord keys ar c1 ab op $ MkSlots (idmap-set _ x e kinds) $ match many meta (((Nat) _)) ((BTrue) (Succ fm)) ((BFalse) fm)))

(def-fns _ $ (many table-slot-entry : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) c) (many (Table n f c) tb) (many (Nat) x) -> (many (Maybe $ SlotEntry) r))
  (let-match many tb (MkTable _ _ _ _ _ _ _ _ _ _ _ sl))
  (let-match many sl (MkSlots kinds _))
  (let-match many (idmap-get _ x kinds) (Miss _ _ _ _) ((Hit _ _ _ e _) (Some _ e)))
  (let-match many x (Succ p) ((Zero) (None _)))
  (match many (idmap-get _ p kinds) _ ((Hit _ _ _ _ _) (Some _ $ SlotAtom)) ((Miss _ _ _ _) (None _))))

(def-fns _ $ (many table-free-metas : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) c) (many (Table n f c) tb) -> (many (Nat) r))
  (let-match many tb (MkTable _ _ _ _ _ _ _ _ _ _ _ sl))
  (match many sl _ ((MkSlots _ fm) fm)))

(def-fns _ $ (many table-slot-of : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) c) (many (Table n f c) tb) (many (Nat) x) -> (many (Maybe $ Nat) r))
  (let-match many (table-slot-entry _ _ c tb x) (Some _ e) ((None _) (None _)))
  (match many e _ ((EntrySlot) (Some _ $ Succ x)) ((SlotAtom) (Some _ x)) ((MetaSlot) (None _))))

; The chase alone, from the top: what the rules say, with `(slot-of x)` left as written.
(def-fns _ $ (many chase-in : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) bnd) (many (Table n f bnd) tb) (many (Term) t) -> (many (Term) r) (erased (Fr n f r) fr))
  (match many tb _
    ((MkTable _ f0 _ ru _ ord _ _ c1 _ _ _) (canon ru t _ f0 _ _ (PNil ru) ord (GTop t) c1))))

(def-fns _ $ (many meta-slot-in : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) bnd) (many (Table n f bnd) tb) (many (Term) m) (many (Nat) s) -> (many (Term) r) (erased (Fr n f r) fr))
  (let ((many c) (erased _)) $ chase-in _ _ bnd tb m)
  (let-match many c (TVar y) (else (chase-in _ _ bnd tb $ TVar s)))
  (let-match many (table-slot-of _ _ bnd tb y) (Some _ sy) ((None _) (values (TSlotOf c) $ FrSlotOf _ _ c)))
  (chase-in _ _ bnd tb $ TVar sy))

; `(slot-of x)` resolved to x's automatic slot, by x's binder and never through x's rule (section 35,
; review item 28), and the slot then chased. This session reads the chase above as leaving the form as
; written, so that a rule's term, canonical when it was appended, holds no `(slot-of x)` of a slotted x and
; a chase's result needs this pass only where the term it was given did. A place is a slot term and is read
; the same way.
(def-fns _
  ((many slots-in : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) bnd) (many (Table n f bnd) tb) (subterm many (Term) t) (erased (Fr n f t) p) -> (many (Term) r) (erased (Fr n f r) fr))
    (match many t _
      ((TSlotOf c)
        (let ((many (Maybe $ SlotEntry) slot)) $ match many c (((Maybe $ SlotEntry) _)) ((TVar x) (table-slot-entry _ _ bnd tb x)) (else (None _)))
        (let-match many slot (None _) ((Some _ e) (let-match many c (TVar x) (else (values t $ FrSlotOf _ _ c)))
          (match many e _
            ((EntrySlot) (chase-in _ _ bnd tb $ TVar $ Succ x))
            ((SlotAtom) (chase-in _ _ bnd tb c))
            ((MetaSlot) (meta-slot-in _ _ bnd tb c $ Succ x)))))
        (let-match many c (TApp _ _) ((TCell _ _) (values t $ FrSlotOf _ _ c)) (else (values t $ FrSlotOf _ _ c)))
        (let-match many tb (MkTable _ f0 _ _ _ _ _ _ c1 _ _ _))
        (let-match many (refresh c _ f0 _ c1) (Some _ box) ((None _) (values t $ FrSlotOf _ _ c)))
        (let-match many box (MkFrBox _ _ _ fc))
        (let ((many c2) (erased _)) $ notail $ slots-in _ _ bnd tb c fc)
        (let ((many c3) (erased _)) $ chase-in _ _ bnd tb c2)
        (values (TSlotOf c3) $ FrSlotOf _ _ c3))
      ((TApp h args)
        (let ((erased ph) (erased pa)) $ fr-app _ _ _ _ p)
        (let ((many h2) (erased fh)) $ notail $ slots-in _ _ bnd tb h ph)
        (let ((many args2) (erased fa)) $ notail $ slots-in-list _ _ bnd tb args pa)
        (values (TApp h2 args2) $ FrApp _ _ _ _ fh fa))
      ((TCell h args)
        (let ((erased ph) (erased pa)) $ fr-cell _ _ _ _ p)
        (let ((many h2) (erased fh)) $ notail $ slots-in _ _ bnd tb h ph)
        (let ((many args2) (erased fa)) $ notail $ slots-in-list _ _ bnd tb args pa)
        (values (TCell h2 args2) $ FrCell _ _ _ _ fh fa))
      ((TFn uq l ps rs)
        (let ((erased pl) (erased pp) (erased pr)) (fr-fn _ _ _ _ _ _ p))
        (let ((many l2) (erased fl)) $ notail $ slots-in _ _ bnd tb l pl)
        (let ((many ps2) (erased fp)) $ notail $ slots-in-tele _ _ bnd tb ps pp)
        (let ((many rs2) (erased frs)) $ notail $ slots-in-tele _ _ bnd tb rs pr)
        (values (TFn uq l2 ps2 rs2) (FrFn _ _ _ _ _ _ fl fp frs)))
      ((TTyCtor ps)
        (let ((many ps2) (erased fp)) $ notail $ slots-in-tele _ _ bnd tb ps $ fr-tyctor _ _ _ p)
        (values (TTyCtor ps2) $ FrTyCtor _ _ _ fp))
      ((TValCtor ps ret)
        (let ((erased pp) (erased pr)) $ fr-valctor _ _ _ _ p)
        (let ((many ps2) (erased fp)) $ notail $ slots-in-tele _ _ bnd tb ps pp)
        (let ((many ret2) (erased fret)) $ notail $ slots-in _ _ bnd tb ret pr)
        (values (TValCtor ps2 ret2) $ FrValCtor _ _ _ _ fp fret))
      ((TMatchable d nt ex ty cs)
        (let ((erased pt) (erased pc)) (fr-matchable _ _ _ _ _ _ _ p))
        (let ((many ty2) (erased ft)) $ notail $ slots-in _ _ bnd tb ty pt)
        (let ((many cs2) (erased fc)) $ notail $ slots-in-mctors _ _ bnd tb cs pc)
        (values (TMatchable d nt ex ty2 cs2) (FrMatchable _ _ _ _ _ _ _ ft fc)))
      (else (values t p))))
  ((many slots-in-list : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) bnd) (many (Table n f bnd) tb) (subterm many (List $ Term) ts) (erased (FrL n f ts) p) -> (many (List $ Term) r) (erased (FrL n f r) fr))
    (let-match many ts (Cons _ t rest) ((Nil _) (values ts $ FrLNil _ _)))
    (let ((erased pt) (erased pr)) $ frl-cons _ _ _ _ p)
    (let ((many t2) (erased ft)) $ notail $ slots-in _ _ bnd tb t pt)
    (let ((many rest2) (erased frest)) $ notail $ slots-in-list _ _ bnd tb rest pr)
    (values (Cons _ t2 rest2) $ FrLCons _ _ _ _ ft frest))
  ((many slots-in-tele : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) bnd) (many (Table n f bnd) tb) (subterm many (List $ Entry) es) (erased (FrT n f es) p) -> (many (List $ Entry) r) (erased (FrT n f r) fr))
    (let-match many es (Cons _ e rest) ((Nil _) (values es $ FrTNil _ _)))
    (let-match many e (MkEntry nm s mu sg place site))
    (let ((erased ps) (erased pp) (erased pr)) (frt-cons _ _ _ _ _ _ _ _ _ p))
    (let ((many sg2) (erased fs)) $ notail $ slots-in-sg _ _ bnd tb sg ps)
    (let ((many (Maybe $ Term) place2) (erased (FrP n f place2) fp))
      (match many place _
        ((None _) (values (None _) $ FrPNone _ _))
        ((Some _ q)
          (let ((many q2) (erased fq)) $ notail $ slots-in _ _ bnd tb q $ frp-some _ _ _ pp)
          (let ((many q3) (erased fq3)) $ chase-in _ _ bnd tb q2)
          (values (Some _ q3) $ FrPSome _ _ _ fq3))))
    (let ((many rest2) (erased frest)) $ notail $ slots-in-tele _ _ bnd tb rest pr)
    (values (Cons _ (MkEntry nm s mu sg2 place2 site) rest2) (FrTCons _ _ _ _ _ _ _ _ _ fs fp frest)))
  ((many slots-in-sg : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) bnd) (many (Table n f bnd) tb) (subterm many (Sg) sg) (erased (FrS n f sg) p) -> (many (Sg) r) (erased (FrS n f r) fr))
    (match many sg _
      ((SgTy t)
        (let ((many t2) (erased ft)) $ notail $ slots-in _ _ bnd tb t $ frs-ty _ _ _ p)
        (values (SgTy t2) $ FrSTy _ _ _ ft))
      ((SgIs t ty)
        (let ((many t2) (erased ft)) $ notail $ slots-in _ _ bnd tb t $ frs-is _ _ _ _ p)
        (values (SgIs t2 ty) $ FrSIs _ _ _ _ ft))))
  ((many slots-in-mctors : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) bnd) (many (Table n f bnd) tb) (subterm many (List $ MCtor) cs) (erased (FrM n f cs) p) -> (many (List $ MCtor) r) (erased (FrM n f r) fr))
    (let-match many cs (Cons _ mc rest) ((Nil _) (values cs $ FrMNil _ _)))
    (let-match many mc (MkMCtor mu t))
    (let ((erased pt) (erased pr)) $ frm-cons _ _ _ _ _ p)
    (let ((many t2) (erased ft)) $ notail $ slots-in _ _ bnd tb t pt)
    (let ((many rest2) (erased frest)) $ notail $ slots-in-mctors _ _ bnd tb rest pr)
    (values (Cons _ (MkMCtor mu t2) rest2) $ FrMCons _ _ _ _ _ ft frest)))

(def-fns _ $ (many canon-in : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) bnd) (many (Table n f bnd) tb) (many (Term) t) -> (many (Term) r) (erased (Fr n f r) fr))
  (let ((many r) (erased fr)) $ chase-in _ _ bnd tb t)
  (slots-in _ _ bnd tb r fr))
(def-fns _ $ (many canon-list-in : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) bnd) (many (Table n f bnd) tb) (many (List $ Term) ts) -> (many (List $ Term) r) (erased (FrL n f r) fr))
  (let-match many tb (MkTable _ f0 _ ru _ ord _ _ c1 _ _ _))
  (let ((many r) (erased fr)) $ canon-list ru ts _ f0 _ _ (PNil ru) ord (GLTop ts) c1)
  (slots-in-list _ _ bnd tb r fr))
(def-fns _ $ (many canon-tele-in : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) bnd) (many (Table n f bnd) tb) (many (List $ Entry) es) -> (many (List $ Entry) r) (erased (FrT n f r) fr))
  (let-match many tb (MkTable _ f0 _ ru _ ord _ _ c1 _ _ _))
  (let ((many r) (erased fr)) $ canon-tele ru es _ f0 _ _ (PNil ru) ord (GTTop es) c1)
  (slots-in-tele _ _ bnd tb r fr))
(def-fns _ $ (many canon-sg-in : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) bnd) (many (Table n f bnd) tb) (many (Sg) sg) -> (many (Sg) r) (erased (FrS n f r) fr))
  (let-match many tb (MkTable _ f0 _ ru _ ord _ _ c1 _ _ _))
  (let ((many r) (erased fr)) $ canon-sg ru sg _ f0 _ _ (PNil ru) ord (GSTop sg) c1)
  (slots-in-sg _ _ bnd tb r fr))
(def-fns _ $ (many canon-mctors-in : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) bnd) (many (Table n f bnd) tb) (many (List $ MCtor) cs) -> (many (List $ MCtor) r) (erased (FrM n f r) fr))
  (let-match many tb (MkTable _ f0 _ ru _ ord _ _ c1 _ _ _))
  (let ((many r) (erased fr)) $ canon-mctors ru cs _ f0 _ _ (PNil ru) ord (GMTop cs) c1)
  (slots-in-mctors _ _ bnd tb r fr))

(def-fns _ $ (many fact-in : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) bnd) (many (Table n f bnd) tb) (many (Nat) x) -> (many (Term) ty) (many (Maybe $ Term) rule))
  (let-match many tb (MkTable _ f0 _ _ _ _ _ _ c1 _ _ _))
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
  (let-match many cs (Cons _ mc rest)
    ((Nil _) (Nil _)))
  (match many mc _ ((MkMCtor _ t) (Cons _ (var-id t) $ notail $ mctor-ids rest))))

; The kind of an opened object and the type constructor and constructors it names, canonically.
(def-fns _ $ (many open-names : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) bnd) (many (Table n f bnd) tb) (many (Nat) x) -> (many (OpenKind) k) (many (List $ Nat) names))
  (let-match many (type-in _ _ bnd tb x) (TApp h args)
    ((TMatchable _ _ _ t cs) (values (OKMatchable) $ Cons _ (var-id t) $ mctor-ids cs))
    (else (values (OKNone) $ Nil _)))
  (let-match many h (TVar c) (else (values (OKNone) $ Nil _)))
  (let-match many (and (nat-eq c atfn-id) $ nat-eq (list-length _ args) 2) (BTrue) ((BFalse) (values (OKNone) $ Nil _)))
  (let-match many (list-nth _ args 1) (NthHit _ _ _ g _) ((NthMiss _ _ _ _) (values (OKNone) $ Nil _)))
  (values (OKAtFn) $ Cons _ (var-id g) $ Nil _))

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
  (let-match many tb (MkTable _ f0 _ ru _ ord keys ar c1 ab op sl))
  (let-match many op (MkOpens _ _ os ix tc))
  (let ((many os2) (many ix2) (many tc2)) $ refresh-named (index-of v ix) _ _ c tb os ix tc)
  (MkTable _ f0 _ ru _ ord keys ar c1 ab (MkOpens _ _ os2 ix2 tc2) sl))

; Opens x: listed newest first, indexed by its names, and touched.
(def-fns _ $ (many table-open : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) c) (many (Table n f c) tb) (many (Nat) x) -> (many (Table n f c) r))
  (let ((many o)) $ opened-in _ _ c tb x)
  (let-match many tb (MkTable _ f0 _ ru _ ord keys ar c1 ab op sl))
  (match many op _
    ((MkOpens _ _ os ix tc) (MkTable _ f0 _ ru _ ord keys ar c1 ab (MkOpens _ _ (Cons _ o os) (index-add (opened-names o) x ix) $ Cons _ x tc) sl))))

(def-fns _ $ (many table-unopen : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) c) (many (Table n f c) tb) (many (Nat) x) -> (many (Table n f c) r))
  (let-match many tb (MkTable _ f0 _ ru _ ord keys ar c1 ab op sl))
  (let-match many op (MkOpens _ _ os ix tc))
  (let ((many os2) (many names)) $ opened-take os x)
  (MkTable _ f0 _ ru _ ord keys ar c1 ab (MkOpens _ _ os2 (index-drop names x ix) $ nats-remove tc x) sl))

; The invariant restored: nothing is touched.
(def-fns _ $ (many table-settled : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) c) (many (Table n f c) tb) -> (many (Table n f c) r))
  (let-match many tb (MkTable _ f0 _ ru _ ord keys ar c1 ab op sl))
  (match many op _ ((MkOpens _ _ os ix _) (MkTable _ f0 _ ru _ ord keys ar c1 ab (MkOpens _ _ os ix $ Nil _) sl))))

(def-fns _ $ (many table-opens : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) c) (many (Table n f c) tb) -> (many (List $ Opened) os) (many (IdMap $ List $ Nat) ix) (many (List $ Nat) tc))
  (let-match many tb (MkTable _ _ _ _ _ _ _ _ _ _ op _))
  (match many op _ ((MkOpens _ _ os ix tc) (values os ix tc))))

(def-fns _ $ (many slots-ruled : (many (Slots) sl) (many (Nat) x) -> (many (Slots) r))
  (let-match many sl (MkSlots kinds fm))
  (let-match many fm (Succ _) ((Zero) sl))
  (let-match many (idmap-get _ x kinds) (Hit _ _ _ e _) ((Miss _ _ _ _) sl))
  (match many e _ ((MetaSlot) (MkSlots kinds $ nat-pred fm)) (else sl)))

; The table after a variable is ruled out with a term fresh in the result: the rule is appended, the
; keys and the order extended, both agreements carried across, and the opened objects naming the variable
; refreshed.
(def-fns _ $ (many rule-into : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) c) (erased (Above (Nil $ Digit) c n f) ab) (erased (List $ Rule) ru) (erased (List $ Nat) ks) (erased (Ord (Nil $ Nat) ru) ord) (erased (Keys (Nil $ Nat) ru ks) keys) (erased (AllRuled ks n f) ar) (erased (C1 (Nil $ Digit) n f ru) c1)
    (many (Opens n f) op) (many (Slots) sl) (many (Nat) x) (many (Term) t) (erased (Nat) k) (many (Facts k) f2) (erased (Out x t n f k f2) o) (erased (Fr k f2 t) ft) -> (many (Table k f2 c) tb))
  (let ((erased ru2) (erased ap)) $ append-rule ru $ MkRule x t)
  (let ((erased ar2)) $ ARCons _ _ _ _ (ruledin-out-new x t n f k f2 o) $ allruled-out ks x t n f k f2 o ar)
  (table-refresh _ _ c
    (MkTable _ f2 _ ru2 _
      (ord-snoc (Nil $ Nat) ru ord ks keys x t ru2 ap $ GAv t (Cons (Nat) _ _) k f2 ft ar2)
      (keys-snoc (Nil $ Nat) ru ks keys x t ru2 ap)
      ar2
      (c1-out (Nil $ Digit) x x (WNil x) t n f k f2 o ru c1 ru2 ap)
      (above-out (Nil $ Digit) c x t n f k f2 ab o)
      (opens-out _ _ _ _ _ _ o op) (slots-ruled sl x))
    x))

; Unification's binding: rule the variable out, and the occurs check is the term still being fresh.
(def-fns _ $ (many rule-out-refresh : (erased (Nat) n) (erased (Facts n) f) (many (Nat) bnd) (many (Table n f bnd) tb) (many (Nat) x) (erased (In x n f) p) (many (Term) t) -> (many (Maybe $ Added n f bnd) r))
  (let-match many tb (MkTable _ f0 _ ru _ ord keys ar c1 ab op sl))
  (let-match many (facts-rule-out _ f0 x p t) (MkRemoved _ _ _ _ f2 o))
  (let ((erased ru2) (erased ap)) $ append-rule ru $ MkRule x t)
  (let ((erased c2)) $ c1-out _ _ _ (WNil x) _ _ _ _ _ o _ c1 _ ap)
  (let-match many (refresh t _ f2 _ c2) (Some _ box) ((None _) (None _)))
  (match many box _
    ((MkFrBox _ _ _ ft) (Some _ $ MkAdded _ _ _ _ $ rule-into _ _ _ ab ru _ ord keys ar c1 op sl x t _ f2 o ft))))

; A new entry, rule-free, at the fresh id x above every key of the table: the count grows.
(def-fns _ $ (many table-insert : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) c) (many (Table n f c) tb) (many (Nat) x) (erased (Lt c x) lt) (many (Term) ty) -> (erased (Nat) n2) (erased (Facts n2) f2) (many (Table n2 f2 x) tb2))
  (let-match many tb (MkTable _ f0 _ ru ks ord keys ar c1 ab op sl))
  (let-match many (facts-insert x _ f0 ty) (IGrew _ _ _ f1 i _)
    (absurd (IKept _ _ _ q) (le-lt-absurd _ _ (above-taken c n f0 x ab q) lt)))
  (values (Succ n) f1 (MkTable _ f1 _ ru _ ord keys (allruled-ins ks x n f0 (Succ _) f1 i ar) (c1-ins (Nil $ Digit) x n f0 (Succ _) f1 i ru c1)
                         (above-ins (Nil $ Digit) x n f0 (Succ _) f1 x x (above-weaken (Nil $ Digit) c x n f0 ab $ lt-weaken c x lt) i (WNil x) $ lt-succ x)
                         (opens-inserted _ _ _ _ _ i op) sl)))

; A new entry with a rule, its term canonical: inserted rule-free and ruled out at once.
(def-fns _ $ (many table-insert-ruled : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) c) (many (Table n f c) tb) (many (Nat) x) (erased (Lt c x) lt) (many (Term) ty) (many (Term) t) (erased (Fr n f t) ft) -> (erased (Nat) n2) (erased (Facts n2) f2) (many (Table n2 f2 x) tb2))
  (let-match many tb (MkTable _ f0 _ ru ks ord keys ar c1 ab op sl))
  (let-match many (facts-insert x _ f0 ty) (IGrew _ _ _ f1 i q)
    (absurd (IKept _ _ _ q) (le-lt-absurd _ _ (above-taken c n f0 x ab q) lt)))
  (let-match many (facts-rule-out _ f1 x q t) (MkRemoved _ _ k _ f2 o))
  (values k f2 (rule-into _ _ _ (above-ins (Nil $ Digit) x n f0 (Succ _) f1 x x (above-weaken (Nil $ Digit) c x n f0 ab $ lt-weaken c x lt) i (WNil x) $ lt-succ x)
                  ru _ ord keys (allruled-ins ks x n f0 (Succ _) f1 i ar) (c1-ins (Nil $ Digit) x n f0 (Succ _) f1 i ru c1)
                  (opens-inserted _ _ _ _ _ i op) sl x t _ f2 o $ fresh-ins-out x t n f0 (Succ _) f1 k f2 i o t ft)))

(def-fns _ $ (many table-reenter : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) c) (many (Table n f c) tb) (many (Nat) x) (erased (Lt x (Succ c)) le) (many (Term) ty) (many (Maybe $ Term) rule) -> (erased (Nat) n2) (erased (Facts n2) f2) (many (Table n2 f2 c) tb2))
  (let-match many tb (MkTable _ f0 _ ru ks ord keys ar c1 ab op sl))
  (let-match many (facts-insert x _ f0 ty) (IGrew _ _ _ f1 i q) ((IKept _ _ _ _) (values n f0 tb)))
  (let ((erased ab2)) $ above-ins (Nil $ Digit) c n f0 (Succ _) f1 x x ab i (WNil x) le)
  (let ((erased ar2)) $ allruled-ins ks x n f0 (Succ _) f1 i ar)
  (let ((erased c12)) $ c1-ins (Nil $ Digit) x n f0 (Succ _) f1 i ru c1)
  (let ((many op2)) $ opens-inserted _ _ _ _ _ i op)
  (let-match many rule (Some _ t) ((None _) (values (Succ n) f1 (MkTable _ f1 _ ru _ ord keys ar2 c12 ab2 op2 sl))))
  (let ((many t2) (erased ft)) $ canon-in _ _ _ tb t)
  (let-match many (facts-rule-out _ f1 x q t2) (MkRemoved _ _ k _ f2 o))
  (values k f2 (rule-into _ _ _ ab2 ru _ ord keys ar2 c12 op2 sl x t2 _ f2 o $ fresh-ins-out x t2 n f0 (Succ _) f1 k f2 i o t2 ft)))

(def-fns _ $ (many table-weaken : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) c) (erased (Nat) c2) (many (Table n f c) tb) (erased (Lt c (Succ c2)) le) -> (many (Table n f c2) tb2))
  (match many tb _
    ((MkTable n0 f0 _ ru _ ord keys ar c1 ab op sl) (MkTable _ f0 _ ru _ ord keys ar c1 (above-weaken (Nil $ Digit) c c2 n0 f0 ab le) op sl))))

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
  (let-match many tb (MkTable _ f0 _ ru _ ord keys ar c1 ab op sl))
  (match many (facts-rule-out _ f0 newer pn $ TVar older) _
    ((MkRemoved _ _ k _ f2 o)
      (MkAdded _ _ _ _ $ rule-into _ _ _ ab ru _ ord keys ar c1 op sl newer (TVar older) _ f2 o $ FrVar k f2 older $ in-out-neq older newer (TVar _) n f0 k f2 o ne po))))



; ---- The scope environment (section 5) and fact table (section 7); [hl] the ghost history every
; Settled's value was allocated into, [store] the next stamp, and [entries] and [finals] hold its references.

(def-adts $ (BinderKind : -> Type)
  enum
  (many BLet : (many (Nat) group) (many (Bool) single) -> (BinderKind))
  (many BParam : -> (BinderKind))
  (many BField : -> (BinderKind))
  (many BOptional : -> (BinderKind))
  (many BDefinition : -> (BinderKind)))

(def-adts $ (PrimSig : -> Type)
  enum
  (many MkPrimSig : (many (Sp) prim) (many (Multiplicity) mult) (many (List $ Entry) params) (many (List $ Entry) rets) -> (PrimSig)))

(def-adts $ (Macros : -> Type)
  enum
  (many MkMacros : (many (Nat) expansions) (many (Nat) gensyms) (many (List $ PrimSig) prims) (many (List $ String) sources) (many (Nat) fuel) -> (Macros)))

(def-adts $ (Tracked : -> Type)
  enum
  (many MkTracked : (many (Loc) site) (many (Name) name) (many (BinderKind) kind) (many (Multiplicity) mult) (many (Bool) scope-erased) -> (Tracked)))

(def-adts $ (RefState : -> Type)
  enum
  (many RefLevel : (many (Nat) level) -> (RefState))
  (many RefTo : (many (Nat) target) -> (RefState)))

(def-adts $ (Tracking : -> Type)
  enum
  (many MkTracking : (many (Bool) on) (many (IdMap $ Tracked) binders) (many (IdMap $ RefState) refs) -> (Tracking)))

(let ((many tracking-empty)) (MkTracking (BFalse) (MEmpty _) (MEmpty _)))

(def-adts
  ((Use : -> Type) enum (many UseShared : (many (Loc) loc) -> (Use)) (many UseConsumed : (many (Loc) loc) -> (Use)))
  ((Uses : -> Type) enum (many MkUses : (many (IdMap $ Use) map) (many (List $ Nat) dirty) -> (Uses)))
  ((Warned : -> Type) enum (many MkWarned : (many (Nat) id) (many (Loc) site) (many (String) msg) -> (Warned)))
  ((Pragmas : -> Type) enum (many MkPragmas : (many (List $ Warned) warned) (many (List $ Region) regions) (many (Bool) unwarned) -> (Pragmas)))
  ((Said : -> Type) enum (many SaidWarning : (many (Loc) here) (many (String) text) -> (Said)) (many SaidError : (many (Loc) here) (many (String) text) -> (Said)) (many SaidSilenced : (many (Nat) region) -> (Said)) (many SaidShadow : (many (Nat) x) (many (Nat) prior) (many (Loc) prior-at) (many (Name) name) (many (Loc) here) -> (Said)))
  ((UniqueState : -> Type) enum
    (many MkUniqueState : (many (List $ Nat) ctor-tele) (many (Uses) uses) (many (List $ Nat) captures)
      (many (Bool) usage-erased) (many (Bool) in-extern) (many (List $ Nat) signature)
      (many (List $ Nat) words) (many (List $ Nat) temporary) (many (Pragmas) pragmas) (many (IdMap $ Nat) aliases) (many (Bool) extern-ok) -> (UniqueState))))
; An entry outside every scope: an interned literal, with its Numeral proof where it has one and the spelling
; and node it reads back as, or a constant a macro minted, with neither; and the declaration facts of its
; entries, entered again into the table of a scope that dropped them (env-discard).
(def-adts
  ((LitFact : -> Type)
    enum
    (many MkLitFact : (many (Nat) id) (many (Term) ty) (many (Maybe $ Term) rule) -> (LitFact)))
  ((LitEntry : -> Type)
    enum
    (many MkLitEntry : (many (Nat) id) (many (Maybe $ Nat) proof) (many (Maybe $ Pair (String) (Syn)) lit) (many (List $ LitFact) facts) (many (Nat) ordinal) -> (LitEntry))))

(let ((many unique-empty)) (MkUniqueState (Nil _) (MkUses (MEmpty _) (Nil _)) (Nil _) (BFalse) (BFalse) (Nil _) (Nil _) (Nil _) (MkPragmas (Nil _) (Nil _) (BFalse)) (MEmpty _) (BFalse)))

(def-adts $ (Scope : -> Type)
  enum
  (many MkScope : (many (NameIndex $ Nat) names) (many (List $ Nat) ids) -> (Scope)))
(def-fns _ $ (many scope-names : (many (Scope) s) -> (many (NameIndex $ Nat) r)) (match many s _ ((MkScope n _) n)))
(def-fns _ $ (many scope-ids : (many (Scope) s) -> (many (List $ Nat) r)) (match many s _ ((MkScope _ ids) ids)))
(let ((many scope-empty)) (MkScope (name-index-empty _) (Nil _)))

(def-adts $ (Sink : -> Type)
  enum
  (many MkSink : (many (String) owner) (many (String) noun) (many (List $ Entry) tele) (many (List $ Syn) written) (many (List $ Pair (Loc) $ String) anchors) (many (Scope) scope) (many (Maybe $ Nat) function) -> (Sink)))

(def-adts $ (Enclosing : -> Type)
  enum
  (many MkEnclosing : (many (Maybe $ Nat) function) (many (List $ Nat) subterms) (many (Maybe $ Sink) sink) (many (Bool) final) -> (Enclosing)))

(def-adts $ (Trusted : -> Type)
  enum
  (many TrustHere : -> (Trusted))
  (many TrustThen : (erased (Nat) n) (erased (Facts n) f) (many (Nat) c) (many (Table n f c) tb) -> (Trusted)))

(def-fns _ $ (many trusted-at : (many (Bool) run) (erased (Nat) n) (erased (Facts n) f) (many (Nat) c) (many (Table n f c) tb) (many (Trusted) rp) -> (many (Trusted) r))
  (let-match many run (BFalse) ((BTrue) (TrustHere)))
  (match many rp _ ((TrustHere) (TrustThen _ _ c tb)) (else rp)))

(def-adts
  ((Env : -> Type)
    enum
    (many MkEnv : (erased (Hist Block) hl) (many (Store Block hl) store) (many (Scope) scope) (many (IdMap $ EInfo hl) entries) (erased (Nat) nfree) (erased (Facts nfree) ffacts) (many (Nat) fresh) (many (Table nfree ffacts fresh) table)
       (many (Trusted) run-pos) (many (List $ Nat) objects)
       (many (NameMap $ Nat) literals) (many (List $ Pair (Ref Block hl) $ Term) finals)
       (many (Maybe $ Nat) level) (many (Enclosing) enclosing) (many (List $ Pair (String) $ Loc) claimed) (many (List $ Said) diagnostics) (many (Tracking) tracking)
       (many (List $ LitEntry) lits) (many (Loc) loc) (many (Scope) prelude) (many (UniqueState) us) (many (NameMap $ List $ String) help) (many (Macros) expansions) -> (Env)))
  ((EInfo : ((Hist Block) l) -> Type)
    enum
    (many MkEInfo : (erased (Hist Block) l) (many (Maybe $ Name) name) (many (Multiplicity) mult) (many (State l) state) (many (Bool) minted) (many (Maybe $ Nat) introduced) (many (Bool) meta) (many (Maybe $ Loc) site) -> (EInfo l)))
  ((State : ((Hist Block) l) -> Type)
    enum
    (many SSettled : (erased (Hist Block) l) (many (Ref Block l) v) (many (Nat) minter) -> (State l))
    (many SHypothetical : (erased (Hist Block) l) -> (State l))))

(def-fns _ $ (erased state-widen : (erased (Hist Block) b) (erased (Hist Block) c) (erased (Suffix Block c b) le) (erased (State b) s) -> (erased (State c) s2) (erased (Coercible (Shared) (State b) s (Shared) (State c) s2) p))
  (let-match erased s (SSettled _ v m) ((SHypothetical _) (values (SHypothetical _) (coercible-ctor (Shared) SHypothetical b c))))
  (let ((erased v2) (erased pv)) (ref-widen _ b c le v))
  (values (SSettled _ v2 m) (coercible-ctor (Shared) SSettled b c pv (coercible-refl (Shared) m))))

(def-fns _ $ (erased einfo-widen : (erased (Hist Block) b) (erased (Hist Block) c) (erased (Suffix Block c b) le) (erased (EInfo b) e) -> (erased (EInfo c) e2) (erased (Coercible (Shared) (EInfo b) e (Shared) (EInfo c) e2) p))
  (let-match erased e (MkEInfo _ n m s mi io me site))
  (let ((erased s2) (erased ps)) (state-widen b c le s))
  (values (MkEInfo _ n m s2 mi io me site) (coercible-ctor (Shared) MkEInfo b c (coercible-refl (Shared) n) (coercible-refl (Shared) m) ps (coercible-refl (Shared) mi) (coercible-refl (Shared) io) (coercible-refl (Shared) me) (coercible-refl (Shared) site))))

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
  (match many e _ ((MkEnv hs hp _ en _ _ _ _ _ _ _ fi _ _ _ _ _ _ _ _ _ _ _) (values hs hp en fi))))
(def-fns _ $ (many env-with-store : (many (Env) e) (erased (Hist Block) hl2) (many (Store Block hl2) hp2) (many (IdMap $ EInfo hl2) en2) (many (List $ Pair (Ref Block hl2) $ Term) fi2) -> (many (Env) r))
  (match many e _ ((MkEnv _ _ sc _ _ _ fr tb rp ob li _ lv st cl wa tk lt lo pr us hn ex) (MkEnv _ hp2 sc en2 _ _ fr tb rp ob li fi2 lv st cl wa tk lt lo pr us hn ex))))
(def-fns _ $ (many store-grow : (erased (Hist Block) hl) (erased (Hist Block) hl2) (erased (Suffix Block hl2 hl) le) (many (IdMap $ EInfo hl) en) (many (List $ Pair (Ref Block hl) $ Term) fi) -> (many (IdMap $ EInfo hl2) en2) (many (List $ Pair (Ref Block hl2) $ Term) fi2))
  (let ((erased en2) (erased pe)) (entries-widen hl hl2 le en))
  (let ((erased fi2) (erased pf)) (finals-widen hl hl2 le fi))
  (values (coerce en pe) (coerce fi pf)))

; The store with the entries and finals that hold its addresses, threaded as one.
(def-adts $ (Heap : ((Hist Block) hl) -> Type)
  enum
  (many MkHeap : (erased (Hist Block) hl) (many (Store Block hl) st) (many (IdMap $ EInfo hl) en) (many (List $ Pair (Ref Block hl) $ Term) fi) (many (Maybe $ String) crash) -> (Heap hl)))

(def-fns _ $ (many env-heap : (many (Env) e) -> (erased (Hist Block) hl) (many (Heap hl) h))
  (let ((erased hl) (many hp) (many en) (many fi)) $ env-store e)
  (values hl $ MkHeap _ hp en fi $ None _))

(def-fns _ $ (many env-put-heap : (many (Env) e) (erased (Hist Block) hl) (many (Heap hl) h) -> (many (Env) r))
  (match many h _ ((MkHeap _ hp en fi _) (env-with-store e _ hp en fi))))

(def-fns _ $ (many heap-store : (erased (Hist Block) hl) (many (Heap hl) h) -> (many (Store Block hl) st))
  (match many h _ ((MkHeap _ st _ _ _) st)))

(def-fns _ $ (many heap-entries : (erased (Hist Block) hl) (many (Heap hl) h) -> (many (IdMap $ EInfo hl) en))
  (match many h _ ((MkHeap _ _ en _ _) en)))

(def-fns _ $ (many heap-finals : (erased (Hist Block) hl) (many (Heap hl) h) -> (many (List $ Pair (Ref Block hl) $ Term) fi))
  (match many h _ ((MkHeap _ _ _ fi _) fi)))

(def-fns _ $ (many heap-with-entries : (erased (Hist Block) hl) (many (Heap hl) h) (many (IdMap $ EInfo hl) en) -> (many (Heap hl) r))
  (match many h _ ((MkHeap _ st _ fi c) (MkHeap _ st en fi c))))

(def-fns _ $ (many heap-with-finals : (erased (Hist Block) hl) (many (Heap hl) h) (many (List $ Pair (Ref Block hl) $ Term) fi) -> (many (Heap hl) r))
  (match many h _ ((MkHeap _ st en _ c) (MkHeap _ st en fi c))))

(def-fns _ $ (many halloc : (erased (Hist Block) hl) (many (Heap hl) h) (many (Block (Ref Block hl)) b) ->
    (erased (Hist Block) hl2) (many (Heap hl2) h2) (erased (Suffix Block hl2 hl) sf) (many (Ref Block hl2) a))
  (let-match many h (MkHeap _ st en fi c))
  (let ((many c2)) $ match many c (((Maybe $ String) r)) ((Some _ _) c) ((None _) (match many b (((Maybe $ String) r)) ((BError _ m) (Some _ m)) (else (None _)))))
  (let ((erased hl2) (many st2) (erased sf) (many a)) $ alloc Block _ st b)
  (let ((many en2) (many fi2)) $ store-grow _ _ sf en fi)
  (values hl2 (MkHeap _ st2 en2 fi2 c2) sf a))

(def-fns _ $ (many hread : (erased (Hist Block) hl) (many (Heap hl) h) (many (Ref Block hl) r) ->
    (erased (Hist Block) s) (many (Block (Ref Block s)) body) (erased (Suffix Block hl s) sf))
  (store-read Block _ (heap-store _ h) r))

(def-fns _ $ (many hwrite : (erased (Hist Block) hl) (many (Heap hl) h) (many (Ref Block hl) r) (many (Block (Ref Block hl)) b) -> (many (Heap hl) h2))
  (match many h _ ((MkHeap _ st en fi c) (MkHeap _ (store-write Block _ st r b) en fi c))))

(def-fns _ $ (many hsize : (erased (Hist Block) hl) (many (Heap hl) h) -> (many (Nat) n))
  (store-size Block _ $ heap-store _ h))

(def-fns _ $ (many entries-set-state : (erased (Hist Block) hl) (many (IdMap $ EInfo hl) en) (many (Nat) x) (many (State hl) st) -> (many (IdMap $ EInfo hl) r))
  (let-match many (idmap-get _ x en) (Hit _ _ _ info _)
    ((Miss _ _ _ _) (idmap-set _ x (MkEInfo _ (None _) (Many) st (BFalse) (Some _ x) (BFalse) (None _)) en)))
  (match many info _ ((MkEInfo _ n m _ mi io me site) (idmap-set _ x (MkEInfo _ n m st mi io me site) en))))

; A closed block, one holding no reference, allocated as the value of [x]: a descriptor, a payload, the token.
(def-fns _ $ (many heap-set-closed : (erased (Hist Block) hl) (many (Heap hl) h) (many (Nat) x) (many (Block (Ref Block (HEmpty Block))) b) ->
    (erased (Hist Block) hl2) (many (Heap hl2) h2) (erased (Suffix Block hl2 hl) sf))
  (let ((erased wb0) (erased pb0)) (block-widen _ _ (empty-suffix _ hl) b))
  (let ((erased hl2) (many h2) (erased sf) (many a)) $ halloc _ h (coerce b pb0))
  (values hl2 (heap-with-entries _ h2 $ entries-set-state _ (heap-entries _ h2) x $ SSettled _ a x) sf))

(def-fns _ $ (many set-state-closed : (many (Env) e) (many (Nat) x) (many (Block (Ref Block (HEmpty Block))) b) -> (many (Env) r))
  (let ((erased hl) (many h)) $ env-heap e)
  (let ((erased hl2) (many h2) (erased sf)) $ heap-set-closed _ h x b)
  (env-put-heap e _ h2))

(def-fns _ $ (many env-scope : (many (Env) e) -> (many (Scope) r))
  (match many e _ ((MkEnv _ _ sc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) sc)))
(def-fns _ $ (many env-entries : (many (Env) e) -> (erased (Hist Block) hs) (many (IdMap $ EInfo hs) r))
  (match many e _ ((MkEnv hs _ _ en _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (values hs en))))
(def-fns _ $ (many env-table : (many (Env) e) -> (erased (Nat) n) (erased (Facts n) f) (many (Nat) bnd) (many (Table n f bnd) tb))
  (match many e _ ((MkEnv _ _ _ _ nf ff fr tb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (values nf ff fr tb))))
(def-fns _ $ (many env-fresh-bound : (many (Env) e) -> (many (Nat) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) fr)))
(def-fns _ $ (many env-facts : (many (Env) e) -> (erased (Nat) n) (many (Facts n) f))
  (let ((erased n) (erased f) (many bnd) (many tb)) $ env-table e)
  (match many tb _ ((MkTable n0 f0 _ _ _ _ _ _ _ _ _ _) (values n0 f0))))
(def-fns _ $ (many env-run-pos : (many (Env) e) -> (many (Bool) r))
  (let-match many e (MkEnv _ _ _ _ _ _ _ _ rp _ _ _ _ _ _ _ _ _ _ _ _ _ _))
  (match many rp _ ((TrustHere) (BTrue)) (else (BFalse))))
(def-fns _ $ (many trusted-type : (many (Env) e) (many (Nat) x) -> (many (Term) r))
  (let-match many e (MkEnv _ _ _ _ _ _ _ tb rp _ _ _ _ _ _ _ _ _ _ _ _ _ _))
  (match many rp _
    ((TrustHere) (type-in _ _ _ tb x))
    ((TrustThen _ _ _ tb0) (type-in _ _ _ tb0 x))))
(def-fns _ $ (many trusted-former : (many (Env) e) (many (Nat) x) -> (many (Bool) r))
  (let-match many e (MkEnv _ _ _ _ _ _ _ tb rp _ _ _ _ _ _ _ _ _ _ _ _ _ _))
  (let ((many ty) (many rule)) $ match many rp (((Term) _) ((Maybe $ Term) _)) ((TrustHere) (fact-in _ _ _ tb x)) ((TrustThen _ _ _ tb0) (fact-in _ _ _ tb0 x)))
  (match many ty _ ((TApp _ _) (BFalse)) ((TVar _) (BFalse)) (else (BTrue))))
(def-fns _ $ (many env-objects : (many (Env) e) -> (many (List $ Nat) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ _ _ _ ob _ _ _ _ _ _ _ _ _ _ _ _ _) ob)))
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
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex) (MkEnv _ hp sc en _ _ fr (table-open _ _ fr tb x) rp ob li fi lv st cl wa tk lt lo pr us hn ex))))
(def-fns _ $ (many env-unopen : (many (Env) e) (many (Nat) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex) (MkEnv _ hp sc en _ _ fr (table-unopen _ _ fr tb x) rp ob li fi lv st cl wa tk lt lo pr us hn ex))))
(def-fns _ $ (many env-settled : (many (Env) e) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex) (MkEnv _ hp sc en _ _ fr (table-settled _ _ fr tb) rp ob li fi lv st cl wa tk lt lo pr us hn ex))))
(def-fns _ $ (many env-literals : (many (Env) e) -> (many (NameMap $ Nat) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ _ _ _ _ li _ _ _ _ _ _ _ _ _ _ _ _) li)))

(def-fns _ $ (many env-level : (many (Env) e) -> (many (Maybe $ Nat) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ _ _ _ _ _ _ lv _ _ _ _ _ _ _ _ _ _) lv)))
(def-fns _ $ (many env-subterms : (many (Env) e) -> (many (List $ Nat) r))
  (let-match many e (MkEnv _ _ _ _ _ _ _ _ _ _ _ _ _ st _ _ _ _ _ _ _ _ _))
  (match many st _ ((MkEnclosing _ xs _ _) xs)))
(def-fns _ $ (many env-enclosing : (many (Env) e) -> (many (Maybe $ Nat) r))
  (let-match many e (MkEnv _ _ _ _ _ _ _ _ _ _ _ _ _ st _ _ _ _ _ _ _ _ _))
  (match many st _ ((MkEnclosing f _ _ _) f)))
(def-fns _ $ (many env-sink : (many (Env) e) -> (many (Maybe $ Sink) r))
  (let-match many e (MkEnv _ _ _ _ _ _ _ _ _ _ _ _ _ st _ _ _ _ _ _ _ _ _))
  (match many st _ ((MkEnclosing _ _ k _) k)))
(def-fns _ $ (many env-set-sink : (many (Env) e) (many (Maybe $ Sink) k) -> (many (Env) r))
  (let-match many e (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex))
  (match many st _ ((MkEnclosing f xs _ b) (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv (MkEnclosing f xs k b) cl wa tk lt lo pr us hn ex))))
(def-fns _ $ (many env-set-final : (many (Env) e) -> (many (Env) r))
  (let-match many e (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex))
  (match many st _ ((MkEnclosing f xs k _) (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv (MkEnclosing f xs k $ BTrue) cl wa tk lt lo pr us hn ex))))
(def-fns _ $ (many env-take-sink : (many (Env) e) -> (many (Env) r) (many (Maybe $ Sink) k) (many (Bool) final))
  (let-match many e (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex))
  (let-match many st (MkEnclosing f xs k b))
  (match many (or b $ is-some _ k) _
    ((BFalse) (values e k b))
    ((BTrue) (values (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv (MkEnclosing f xs (None _) (BFalse)) cl wa tk lt lo pr us hn ex) k b))))
(def-fns _ $ (many env-claimed : (many (Env) e) -> (many (List $ Pair (String) $ Loc) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ cl _ _ _ _ _ _ _ _) cl)))
(def-fns _ $ (many said-silenced : (subterm many (List $ Said) ss) -> (many (List $ Nat) r))
  (let-match many ss (Cons _ x rest)
    ((Nil _) (Nil _)))
  (match many x _ ((SaidSilenced k) (Cons _ k $ notail $ said-silenced rest)) (else (tail $ said-silenced rest))))
(def-fns _ $ (many said-without-silenced : (subterm many (List $ Said) ss) -> (many (List $ Said) r))
  (let-match many ss (Cons _ x rest)
    ((Nil _) ss))
  (match many x _ ((SaidSilenced _) (tail $ said-without-silenced rest)) (else (Cons _ x $ notail $ said-without-silenced rest))))
(def-fns _ $ (many env-silenced : (many (Env) e) -> (many (List $ Nat) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ wa tk _ _ _ _ _ _) (said-silenced wa))))
(def-fns _ $ (many env-set-said : (many (Env) e) (many (List $ Said) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl _ tk lt lo pr us hn ex) (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl x tk lt lo pr us hn ex))))
(def-fns _ $ (many env-said : (many (Env) e) -> (many (List $ Said) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ wa tk _ _ _ _ _ _) wa)))
(def-fns _ $ (many said-failed : (many (Bool) warnings) (subterm many (List $ Said) ss) -> (many (Bool) r))
  (let-match many ss (Cons _ x rest) ((Nil _) (BFalse)))
  (let-match many (match many x (((Bool) _)) ((SaidError _ _) (BTrue)) ((SaidWarning _ _) warnings) (else (BFalse))) (BFalse) ((BTrue) (BTrue)))
  (tail $ said-failed warnings rest))
(def-fns _ $ (many env-failed : (many (Env) e) -> (many (Bool) r))
  (said-failed (BFalse) $ env-said e))
(def-fns _ $ (many env-lits : (many (Env) e) -> (many (List $ LitEntry) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lt _ _ _ _ _) lt)))
(def-fns _ $ (many env-enter-body : (many (Env) e) (many (Nat) f) (many (Nat) level) (many (List $ Nat) subterms) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi _ _ cl wa tk lt lo pr us hn ex) (MkEnv _ hp sc en _ _ fr tb (trusted-at (BFalse) _ _ fr tb rp) ob li fi (Some _ level) (MkEnclosing (Some _ f) subterms (None _) (BFalse)) cl wa tk lt lo pr us hn ex))))
; Where a claimed name was bound, which the second claim's note names.
(def-fns _ $ (many claimed-at : (subterm many (List $ Pair (String) $ Loc) cl) (many (String) name) ->
    (many (Maybe $ Loc) r))
  (let-match many cl (Cons _ p rest) ((Nil _) (None _)))
  (let-match many p (MkPair _ _ n l))
  (match many (str-eq n name) (((Maybe $ Loc) _))
    ((BTrue) (Some _ l))
    ((BFalse) (tail $ claimed-at rest name))))
(def-fns _ $ (many env-claim : (many (Env) e) (many (String) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex) (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st (Cons _ (MkPair _ _ x lo) cl) wa tk lt lo pr us hn ex))))
(def-fns _ $ (many env-warn : (many (Env) e) (many (String) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex) (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl (Cons _ (SaidWarning lo x) wa) tk lt lo pr us hn ex))))
(def-fns _ $ (many env-warn-all : (many (Env) e) (subterm many (List $ String) xs) -> (many (Env) r))
  (match many xs _
    ((Nil _) e)
    ((Cons _ x rest) (tail $ env-warn-all (env-warn e x) rest))))
(def-fns _ $ (many lit-ordinal : (many (List $ LitEntry) lits) -> (many (Nat) r))
  (let-match many lits (Cons _ l _) ((Nil _) 0))
  (match many l _ ((MkLitEntry _ _ _ _ o) o)))

(def-fns _ $ (many lits-since : (subterm many (List $ LitEntry) lits) (many (Nat) bound) (many (List $ LitEntry) acc) -> (many (List $ LitEntry) r))
  (let-match many lits (Cons _ l rest) ((Nil _) acc))
  (match many (nat-lt bound $ lit-ordinal lits) _ ((BTrue) (tail $ lits-since rest bound $ Cons _ l acc)) ((BFalse) acc)))

(def-fns _ $ (many env-push-lit : (many (Env) e) (many (Nat) x) (many (Maybe $ Nat) proof) (many (Maybe $ Pair (String) (Syn)) lit) (many (List $ LitFact) facts) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex) (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk (Cons _ (MkLitEntry x proof lit facts (Succ $ lit-ordinal lt)) lt) lo pr us hn ex))))
(def-fns _ $ (many env-set-scope : (many (Env) e) (many (Scope) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp _ en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex) (MkEnv _ hp x en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex))))
(def-fns _ $ (many env-set-table : (many (Env) e) (erased (Nat) n) (erased (Facts n) f) (many (Nat) c) (many (Table n f c) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ _ _ rp ob li fi lv st cl wa tk lt lo pr us hn ex) (MkEnv _ hp sc en _ _ c x rp ob li fi lv st cl wa tk lt lo pr us hn ex))))
(def-fns _ $ (many env-set-run-pos : (many (Env) e) (many (Bool) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex) (MkEnv _ hp sc en _ _ fr tb (trusted-at x _ _ fr tb rp) ob li fi lv st cl wa tk lt lo pr us hn ex))))
(def-fns _ $ (many env-set-literals : (many (Env) e) (many (NameMap $ Nat) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob _ fi lv st cl wa tk lt lo pr us hn ex) (MkEnv _ hp sc en _ _ fr tb rp ob x fi lv st cl wa tk lt lo pr us hn ex))))
(def-fns _ $ (many env-prelude : (many (Env) e) -> (many (Scope) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pr _ _ _) pr)))
; The scope the prelude left, which generated forms elaborate in (lib/elab.ml's in_prelude).
(def-fns _ $ (many env-set-prelude : (many (Env) e) (many (Scope) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo _ us hn ex) (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo x us hn ex))))
(def-fns _ $ (many help-split : (subterm many (String) s) (many (Rope) acc) -> (many (Maybe $ Pair (String) (String)) r))
  (let-match many s (SCons c rest) ((SNil) (None _)))
  (let-match many rest (SCons d rest2) ((SNil) (None _)))
  (match many (and (char-is c 58) $ char-is d 32) _
    ((BTrue) (Some _ $ MkPair _ _ (rope-str $ rcat acc $ RStr ": ") rest2))
    ((BFalse) (tail $ help-split rest $ RCat acc $ RChar c))))

(def-fns _ $ (many help-index : (subterm many (List $ String) ls) (many (NameMap $ List $ String) m) -> (many (NameMap $ List $ String) r))
  (let-match many ls (Cons _ l rest) ((Nil _) m))
  (let-match many (help-split l $ REmpty) (Some _ p) ((None _) (tail $ help-index rest m)))
  (let-match many p (MkPair _ _ key text))
  (let ((many (List $ String) old)) $ match many (nm-get _ key m) _ ((NHit _ _ _ v _) v) ((NMiss _ _ _ _) (Nil _)))
  (tail $ help-index rest $ nm-set _ key (Cons _ text old) m))

(def-fns _ $ (many env-help : (many (Env) e) -> (many (NameMap $ List $ String) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn ex) hn)))
(def-fns _ $ (many env-set-help : (many (Env) e) (many (String) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us _ ex) (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us (help-index (list-rev _ $ split-on x 10) $ nm-empty _) ex))))
(def-fns _ $ (many env-macros : (many (Env) e) -> (many (Macros) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ex) ex)))
(def-fns _ $ (many env-set-macros : (many (Env) e) (many (Macros) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn _) (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn x))))
(def-fns _ $ (many env-expansions : (many (Env) e) -> (many (Nat) r))
  (match many (env-macros e) _ ((MkMacros n _ _ _ _) n)))
(def-fns _ $ (many env-set-expansions : (many (Env) e) (many (Nat) x) -> (many (Env) r))
  (match many (env-macros e) _ ((MkMacros _ g ps ss f) (env-set-macros e $ MkMacros x g ps ss f))))
(def-fns _ $ (many env-gensyms : (many (Env) e) -> (many (Nat) r))
  (match many (env-macros e) _ ((MkMacros _ g _ _ _) g)))
(def-fns _ $ (many env-set-gensyms : (many (Env) e) (many (Nat) x) -> (many (Env) r))
  (match many (env-macros e) _ ((MkMacros n _ ps ss f) (env-set-macros e $ MkMacros n x ps ss f))))
(def-fns _ $ (many env-prims : (many (Env) e) -> (many (List $ PrimSig) r))
  (match many (env-macros e) _ ((MkMacros _ _ ps _ _) ps)))
(def-fns _ $ (many env-add-prim : (many (Env) e) (many (PrimSig) p) -> (many (Env) r))
  (match many (env-macros e) _ ((MkMacros n g ps ss f) (env-set-macros e $ MkMacros n g (Cons _ p ps) ss f))))
(def-fns _ $ (many env-sources : (many (Env) e) -> (many (List $ String) r))
  (match many (env-macros e) _ ((MkMacros _ _ _ ss _) ss)))
(def-fns _ $ (many env-set-sources : (many (Env) e) (many (List $ String) ss) -> (many (Env) r))
  (match many (env-macros e) _ ((MkMacros n g ps _ f) (env-set-macros e $ MkMacros n g ps ss f))))
(def-fns _ $ (many env-fuel : (many (Env) e) -> (many (Nat) r))
  (match many (env-macros e) _ ((MkMacros _ _ _ _ f) f)))
(def-fns _ $ (many env-set-fuel : (many (Env) e) (many (Nat) f) -> (many (Env) r))
  (match many (env-macros e) _ ((MkMacros n g ps ss _) (env-set-macros e $ MkMacros n g ps ss f))))
; The next id, above every key of the table.
(def-fns _ $ (many env-fresh-id : (many (Env) e) -> (many (Env) r) (many (Nat) x))
  (let-match many e (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex))
  (let ((many x) (erased ltp)) (values (Succ fr) (lt-succ fr)))
  (values (MkEnv _ hp sc en _ _ x (table-weaken _ _ _ _ tb $ lt-weaken fr x ltp) rp ob li fi lv st cl wa tk lt lo pr us hn ex) x))
(def-fns _ $ (many env-loc : (many (Env) e) -> (many (Loc) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo _ _ _ _) lo)))
(def-fns _ $ (many env-at-loc : (many (Env) e) (many (Loc) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt _ pr us hn ex) (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt x pr us hn ex))))
; A position in the file the environment is reading, as a Loc a message can point at.
(def-fns _ $ (many loc-in : (many (Env) e) (many (Spot) pos) -> (many (Loc) l))
  (match many (env-loc e) _ ((MkLoc f _) (MkLoc f pos))))
(def-fns _ $ (many env-at : (many (Env) e) (many (Spot) pos) -> (many (Env) r))
  (match many (env-loc e) _ ((MkLoc f _) (env-at-loc e $ MkLoc f pos))))
; Restores [outer]'s position in [inner], on leaving the form that set it.
(def-fns _ $ (many env-back : (many (Env) outer) (many (Env) inner) -> (many (Env) r))
  (env-at-loc inner $ env-loc outer))
; A message with the file and position in force, in the reference's format.
(def-fns _ $ (many loc-here : (many (Loc) lo) -> (many (String) r))
  (let-match many lo (MkLoc f p))
  (let-match many p (MkSpot l c)
    ((PosSpot q) (match many q _ ((NoPos) "") ((MkPos f2 l c) (str-cat3 f2 ":" $ str-cat3 (nat-str l) ":" $ nat-str c)))))
  (str-cat3 f ":" $ str-cat3 (nat-str l) ":" $ nat-str c))
(def-fns _ $ (many labelled : (many (String) here) (many (String) kind) (many (String) x) -> (many (String) r))
  (let-match many here (SNil) (else (str-cat3 here kind x)))
  (let-match many kind (SCons _ k1) (else (str-cat kind x)))
  (let-match many k1 (SCons _ k2) (else (str-cat kind x)))
  (str-cat k2 x))
(def-fns _ $ (many located : (many (Env) e) (many (String) kind) (many (String) x) -> (many (String) r))
  (labelled (loc-here $ env-loc e) kind x))
; Where a position is, in the reference's format, or nothing for none (lib/reader.ml's where).
(def-fns _ $ (many loc-str : (many (Maybe $ Loc) site) -> (many (String) r))
  (let-match many site (Some _ l) ((None _) ""))
  (let-match many l (MkLoc f p))
  (let-match many p (MkSpot ln c) ((PosSpot _) (loc-here l)))
  (match many ln _
    ((Zero) "")
    (else (str-cat3 f ":" $ str-cat3 (nat-str ln) ":" $ nat-str c))))

; An unsolved meta or an anonymous entry is printed as a marker holding its kind, its id and where it was
; written (name-of). Markers are numbered when a message is printed, in order of first mention and once for the
; whole run, so a number names one thing in every message; each message names where each one stands in a note
; (lib/env.ml's resolve).
(def-adts $ (MsgMeta : -> Type)
  enum
  (many MkMsgMeta : (many (String) id) (many (Nat) n) (many (String) where) -> (MsgMeta)))

(def-fns _ $ (many meta-find : (subterm many (List $ MsgMeta) ms) (many (String) id) -> (many (Maybe $ Nat) n))
  (let-match many ms (Cons _ m rest)
    ((Nil _) (None _)))
  (let-match many m (MkMsgMeta i n _))
  (match many (str-eq i id) _ ((BTrue) (Some _ n)) ((BFalse) (tail (meta-find rest id)))))

(def-fns _ $ (many is-hole-key : (many (String) id) -> (many (Bool) r))
  (match many id _ ((SCons c _) (char-is c 63)) ((SNil) (BFalse))))

(def-fns _ $ (many key-count : (subterm many (List $ MsgMeta) ms) (many (Bool) hole) -> (many (Nat) n))
  (let-match many ms (Cons _ m rest) ((Nil _) (Zero)))
  (let-match many m (MkMsgMeta i _ _))
  (let ((many more)) $ notail $ key-count rest hole)
  (match many (match many hole (((Bool) _)) ((BTrue) (is-hole-key i)) ((BFalse) (not $ is-hole-key i))) _ ((BTrue) (Succ more)) ((BFalse) more)))

(def-fns _ $ (many meta-number : (many (String) id) (many (List $ MsgMeta) table) -> (many (Nat) n) (many (List $ MsgMeta) r))
  (let-match many (meta-find table id) (None _) ((Some _ n) (values n table)))
  (let ((many n)) $ Succ $ key-count table $ is-hole-key id)
  (values n $ Cons _ (MkMsgMeta id n "") table))

(def-fns _ $ (many is-kw-key : (many (String) id) -> (many (Bool) r))
  (match many id _ ((SCons c _) (char-is c 107)) ((SNil) (BFalse))))

(def-fns _ $ (many meta-shown : (many (String) id) (many (Nat) n) -> (many (String) r))
  (let-match many id (SCons c rest)
    ((SNil) (str-cat "__" $ nat-str n)))
  (match many (char-is c 107) _ ((BTrue) (str-cat "__" rest)) ((BFalse) (str-cat (match many (char-is c 63) (((String) _)) ((BTrue) "__?") ((BFalse) "__")) $ nat-str n))))

; [mode] is 0 in the text, 1 in a marker's id and 2 in its position.
(def-fns _ $ (many meta-scan : (subterm many (String) s) (many (Nat) mode) (many (Rope) out) (many (Rope) id) (many (Rope) where) (many (List $ MsgMeta) seen) (many (List $ MsgMeta) table) ->
    (many (Rope) r) (many (List $ MsgMeta) seen2) (many (List $ MsgMeta) table2))
  (let-match many s (SCons c rest) ((SNil) (values out seen table)))
  (let-match many (char-is c 1) (BFalse)
    ((BTrue) (match many mode _ ((Zero) (tail (meta-scan rest 1 out (REmpty) (REmpty) seen table))) (else (tail (meta-scan rest 2 out id where seen table))))))
  (match many (char-is c 2) _
    ((BTrue)
      (let ((many key)) $ rope-str id)
      (let ((many n) (many table2)) $ match many (is-kw-key key) (((Nat) _) ((List $ MsgMeta) _)) ((BTrue) (values 0 table)) ((BFalse) (meta-number key table)))
      (let ((many seen2)) $ match many (meta-find seen key) (((List $ MsgMeta) _))
        ((Some _ _) seen)
        ((None _) (let ((many l) (erased _)) (list-append _ seen $ Cons _ (MkMsgMeta key n $ rope-str where) $ Nil _)) l))
      (tail (meta-scan rest 0 (rcat out $ RStr $ meta-shown key n) (REmpty) (REmpty) seen2 table2)))
    ((BFalse)
      (let-match many mode (Succ m) ((Zero) (tail (meta-scan rest mode (rcat out $ RChar c) id where seen table))))
      (match many m _
        ((Zero) (tail (meta-scan rest mode out (rcat id $ RChar c) where seen table)))
        (else (tail (meta-scan rest mode out id (rcat where $ RChar c) seen table)))))))

(def-fns _ $ (many anon-note : (many (String) id) -> (many (String) r))
  (let-match many id (SCons c _) ((SNil) "anonymous, minted here"))
  (let-match many (char-is c 63) (BFalse) ((BTrue) "the `_` written here"))
  (let-match many (char-is c 109) (BFalse) ((BTrue) "the slot of the `_` written here"))
  (let-match many (char-is c 115) (BFalse) ((BTrue) "the slot of the entry bound here"))
  "anonymous, minted here")

(def-fns _ $ (many meta-notes : (many (String) here) (subterm many (List $ MsgMeta) ms) -> (many (List $ String) r))
  (let-match many ms (Cons _ m rest) ((Nil _) (Nil _)))
  (let-match many m (MkMsgMeta id n where))
  (let ((many shown)) $ str-cat3 "`" (meta-shown id n) "` is ")
  (let ((many hole)) $ is-hole-key id)
  (let-match many (is-kw-key id) (BFalse)
    ((BTrue)
      (let ((many b)) $ match many id (((String) _)) ((SCons _ r) r) ((SNil) ""))
      (Cons _ (match many (str-is-empty where) (((String) _))
                ((BTrue) (str-cat3 here ": note: " $ str-cat3 shown "`" $ str-cat b "`, shadowed"))
                ((BFalse) (str-cat3 where ": note: " $ str-cat3 shown "`" $ str-cat b "`, shadowed here")))
        $ notail $ meta-notes here rest)))
  (Cons _ (match many (str-is-empty where) (((String) _))
            ((BTrue) (str-cat3 here ": note: " $ str-cat shown $ match many hole (((String) _)) ((BTrue) "a `_` the elaborator supplied, not one written in the source") ((BFalse) "anonymous, minted by the elaborator rather than written in the source")))
            ((BFalse) (str-cat3 where ": note: " $ str-cat shown $ anon-note id)))
    $ notail $ meta-notes here rest))

; A message with its markers numbered against the run's [table], and the notes placing each one.
(def-fns _ $ (many resolve-lines : (many (Loc) lo) (subterm many (List $ String) lines) (many (List $ MsgMeta) seen) (many (List $ MsgMeta) table) -> (many (List $ String) r) (many (List $ MsgMeta) table2))
  (let-match many lines (Cons _ x rest) ((Nil _) (values (Nil _) table)))
  (let ((many out) (many seen2) (many table2)) $ meta-scan x 0 (REmpty) (REmpty) (REmpty) seen table)
  (let ((many more) (many table3)) $ notail $ resolve-lines lo rest seen2 table2)
  (let ((many line)) $ rope-str out)
  (let ((many mine)) $ meta-notes (loc-here lo) $ list-drop _ (list-length _ seen) seen2)
  (match many (and (not $ list-is-empty _ mine) $ or (str-starts "hint: " line) $ str-contains line ": hint: ") _
    ((BTrue) (let ((many notes) (erased _)) (list-append _ mine $ Cons _ line more)) (values notes table3))
    ((BFalse) (let ((many notes) (erased _)) (list-append _ mine more)) (values (Cons _ line notes) table3))))

(def-fns _ $ (many resolve-marks : (many (Loc) lo) (many (String) x) (many (List $ MsgMeta) table) -> (many (String) r) (many (List $ MsgMeta) table2))
  (let ((many ls) (many table2)) $ resolve-lines lo (split-on x 10) (Nil _) table)
  (values (join-strs ls "\n") table2))

(def-fns _ $ (many note-lines : (many (Env) e) (subterm many (List $ Pair (Loc) $ String) notes) (many (List $ String) rest) -> (many (List $ String) r))
  (let-match many notes (Cons _ n more) ((Nil _) rest))
  (let-match many n (MkPair _ _ l m))
  (Cons _ (located (env-at-loc e l) ": note: " m) $ notail $ note-lines e more rest))
(def-fns _ $ (many diagnostic : (many (Env) e) (many (String) kind) (many (List $ Pair (Loc) $ String) notes) (many (String) x) -> (many (String) r))
  (join-strs (Cons _ (located e kind x) $ note-lines e notes $ Nil _) "\n"))
(def-fns _ $ (many said-has : (subterm many (List $ Said) ss) (many (String) text) -> (many (Bool) r))
  (let-match many ss (Cons _ x rest) ((Nil _) (BFalse)))
  (let-match many x (SaidError _ t)
    (else (tail $ said-has rest text)))
  (match many (str-eq t text) _ ((BTrue) (BTrue)) ((BFalse) (tail $ said-has rest text))))
(def-fns _ $ (many env-fail : (many (Env) e) (many (String) text) -> (many (Env) r))
  (let ((many said)) $ env-said e)
  (match many (and (said-failed (BFalse) said) $ or (str-contains text "<error: ") $ said-has said text) _
    ((BTrue) e)
    ((BFalse) (env-set-said e $ Cons _ (SaidError (env-loc e) text) said))))
(def-fns _ $ (many env-error-with : (many (Env) e) (many (List $ Pair (Loc) $ String) notes) (many (String) x) -> (many (Env) r))
  (env-fail e $ diagnostic e ": error: " notes x))
(def-fns _ $ (many env-error-hinted : (many (Env) e) (many (List $ Pair (Loc) $ String) notes) (many (String) x) (many (String) hint) -> (many (Env) r))
  (env-fail e $ str-cat (diagnostic e ": error: " notes x) hint))
(def-fns _ $ (many env-error : (many (Env) e) (many (String) x) -> (many (Env) r))
  (env-error-with e (Nil _) x))
(def-fns _ $ (many env-with-heap : (many (Env) e) (erased (Hist Block) hl) (many (Heap hl) h) -> (many (Env) r))
  (let ((many e2)) $ env-put-heap e _ h)
  (let-match many h (MkHeap _ _ _ _ crash))
  (let-match many crash (Some _ m) ((None _) e2))
  (match many (env-failed e2) _ ((BTrue) e2) ((BFalse) (env-error e2 $ str-cat "compile-time evaluation failed: " m))))
; An error about two places names both: the note is a second location, written under the message as a
; warning's note is, rather than described in the message's prose (ASSUMPTIONS 194).
(def-fns _ $ (many env-warn-with : (many (Env) e) (many (Loc) l) (many (List $ Pair (Loc) $ String) notes) (many (String) x) -> (many (Env) r))
  (env-back e $ env-warn (env-at-loc e l) $ diagnostic (env-at-loc e l) ": warning: " notes x))
(def-fns _ $ (many env-warn-at : (many (Env) e) (many (Loc) l) (many (String) x) -> (many (Env) r))
  (env-warn-with e l (Nil _) x))

; The names of the entries minted after [stop], up to [x], dropped (lib/env.ml's hide).
(def-fns _ $ (many entries-anonymize : (erased (Hist Block) hs) (many (IdMap $ EInfo hs) en) (subterm many (Nat) x) (many (Nat) stop) -> (many (IdMap $ EInfo hs) r))
  (let-match many x (Succ p) ((Zero) en))
  (let-match many (nat-lt stop x) (BTrue) ((BFalse) en))
  (let ((many (IdMap $ EInfo hs) en2))
    (match many (idmap-get _ x en) _
      ((Miss _ _ _ _) en)
      ((Hit _ _ _ info _) (match many info (((IdMap $ EInfo hs) _)) ((MkEInfo _ _ m st mi io me site) (idmap-set _ x (MkEInfo _ (None _) m st mi io me site) en))))))
  (tail $ entries-anonymize _ en2 p stop))

; Leaves a telescope: keeps [inner]'s facts, opens, store, literals, fresh ids, finals and errors, restoring
; [outer]'s scope and objects; run position is [outer]'s.
(def-fns _ $ (many unique-restore : (many (UniqueState) outer) (many (UniqueState) inner) -> (many (UniqueState) r))
  (let-match many outer (MkUniqueState ct _ caps ue ie sig _ _ _ _ _))
  (match many inner _ ((MkUniqueState _ uses2 _ _ _ _ words2 temp2 wd2 al2 ex2)
    (MkUniqueState ct uses2 caps ue ie sig words2 temp2 wd2 al2 ex2))))

(def-fns _ $ (many env-restore : (many (Env) outer) (many (Env) inner) -> (many (Env) r))
  (let-match many outer (MkEnv _ _ sc _ _ _ _ _ rp ob _ _ lv st _ _ _ _ lo pr us hn _))
  (match many inner _
    ((MkEnv _ hp2 _ en2 _ _ fr2 tb2 _ _ li2 fi2 _ _ cl2 wa2 tk2 lt2 _ _ us2 _ ex2) (MkEnv _ hp2 sc en2 _ _ fr2 tb2 rp ob li2 fi2 lv st cl2 wa2 tk2 lt2 lo pr (unique-restore us us2) hn ex2))))

; Leaves a let's right-hand side: as env-restore, but the objects stay [inner]'s and the entries it added
; keep their ids in scope with their names dropped (section 27, lib/env.ml's hide).
(def-fns _ $ (many env-hide : (many (Env) outer) (many (Env) inner) -> (many (Env) r))
  (let-match many outer (MkEnv _ _ sc _ _ _ fr _ rp _ _ _ lv st _ _ _ _ lo pr us hn _))
  (match many inner _
    ((MkEnv _ hp2 sc2 en2 _ _ fr2 tb2 _ ob2 li2 fi2 _ _ cl2 wa2 tk2 lt2 _ _ us2 _ ex2)
      (MkEnv _ hp2 (MkScope (scope-names sc) $ scope-ids sc2) (entries-anonymize _ en2 fr2 fr) _ _ fr2 tb2 rp ob2 li2 fi2 lv st cl2 wa2 tk2 lt2 lo pr (unique-restore us us2) hn ex2))))

(def-fns _ $ (many reenter-facts : (subterm many (List $ LitFact) facts) (erased (Nat) n) (erased (Facts n) f) (many (Nat) bnd) (many (Table n f bnd) tb) -> (erased (Nat) n2) (erased (Facts n2) f2) (many (Table n2 f2 bnd) tb2))
  (let-match many facts (Cons _ fact rest) ((Nil _) (values n f tb)))
  (let-match many fact (MkLitFact x ty rule))
  (let-match many (nat-cmp x bnd) (CLt _ _ _ _ p) (else (tail $ reenter-facts rest _ _ bnd tb)))
  (let ((erased n1) (erased f1) (many tb1)) $ table-reenter _ _ _ tb x (lt-weaken x bnd p) ty rule)
  (let ((erased n2) (erased f2) (many tb2)) $ table-reenter _ _ _ tb1 (Succ x) (LtS x bnd p) slot-term (None _))
  (tail $ reenter-facts rest _ _ bnd $ table-add-slot _ _ _ tb2 x (BFalse)))

(def-fns _ $ (many reenter-lits : (subterm many (List $ LitEntry) lits) (erased (Nat) n) (erased (Facts n) f) (many (Nat) bnd) (many (Table n f bnd) tb) -> (erased (Nat) n2) (erased (Facts n2) f2) (many (Table n2 f2 bnd) tb2))
  (let-match many lits (Cons _ l rest) ((Nil _) (values n f tb)))
  (let-match many l (MkLitEntry _ _ _ facts _))
  (let ((erased n1) (erased f1) (many tb1)) $ reenter-facts facts _ _ bnd tb)
  (tail $ reenter-lits rest _ _ bnd tb1))

; Leaves a match branch or a body: the entries (whose names the extractor prints), the store, the id
; supply, finals, errors and the literal table survive; scope, facts, opens and objects are the outer ones
; again, with the declaration facts of the literals interned inside entered again (section 45).
(def-fns _ $ (many env-discard : (many (Env) outer) (many (Env) inner) -> (many (Env) r))
  (let-match many outer (MkEnv _ _ sc _ nf ff fr tb rp ob _ _ lv st _ _ _ lt lo pr us hn _))
  (let-match many inner (MkEnv _ hp2 _ en2 _ _ fr2 _ _ _ li2 fi2 _ _ cl2 wa2 tk2 lt2 _ _ _ _ ex2))
  (let ((many minted)) $ lits-since lt2 (lit-ordinal lt) $ Nil _)
  (let-match many (nat-cmp fr fr2) (CLt _ _ _ _ p)
    (else (MkEnv _ hp2 sc en2 nf ff fr tb rp ob li2 fi2 lv st cl2 wa2 tk2 lt2 lo pr us hn ex2)))
  (let ((erased n3) (erased f3) (many tb3)) $ reenter-lits minted _ _ fr2 $ table-weaken _ _ _ _ tb $ lt-weaken fr fr2 p)
  (MkEnv _ hp2 sc en2 _ _ fr2 tb3 rp ob li2 fi2 lv st cl2 wa2 tk2 lt2 lo pr us hn ex2))

(def-fns _ $ (many trusted-snapshot : (many (Env) env) -> (many (Env) r))
  (let ((erased n) (erased f) (many bnd) (many tb)) $ env-table env)
  (let-match many env (MkEnv _ _ _ _ _ _ _ _ rp _ _ _ _ _ _ _ _ _ _ _ _ _ _))
  (let ((erased n0) (erased f0) (many tb0)) $ match many rp (((Nat) n0) ((Facts n0) f0) ((Table n0 f0 bnd) _))
    ((TrustHere) (values n f tb))
    ((TrustThen tn tf c tb1) (match many (nat-cmp c bnd) (((Nat) n0) ((Facts n0) f0) ((Table n0 f0 bnd) _)) ((CLt _ _ _ _ p) (values tn tf $ table-weaken _ _ _ _ tb1 $ lt-weaken c bnd p)) (else (values n f tb)))))
  (let ((erased n2) (erased f2) (many tb2)) $ reenter-lits (env-lits env) _ _ bnd tb0)
  (env-set-run-pos (env-set-table env _ _ bnd tb2) (BTrue)))

(def-fns _ $ (many entry : (many (Env) env) (many (Nat) x) -> (erased (Hist Block) hs) (many (EInfo hs) r))
  (let ((erased hs) (many en)) $ env-entries env)
  (match many (idmap-get _ x en) _
    ((Miss _ _ _ _) (values hs $ MkEInfo _ (None _) (Many) (SHypothetical _) (BFalse) (Some _ x) (BFalse) (None _)))
    ((Hit _ _ _ e _) (values hs e))))

(def-fns _ $ (many env-entry-name : (many (Env) env) (many (Nat) x) -> (many (Maybe $ Name) r))
  (let ((erased hs) (many e)) $ entry env x)
  (match many e _ ((MkEInfo _ n _ _ _ _ _ _) n)))

(def-fns _ $ (many env-entry-at : (many (Env) env) (many (Nat) x) -> (many (Maybe $ Loc) r))
  (let ((erased hs) (many e)) $ entry env x)
  (match many e _ ((MkEInfo _ _ _ _ _ _ _ site) site)))

(def-fns _ $ (many entry-mult-of : (many (Env) env) (many (Nat) x) -> (many (Multiplicity) r))
  (let ((erased hs) (many e)) $ entry env x)
  (match many e _ ((MkEInfo _ _ m _ _ _ _ _) m)))

(def-fns _ $ (many entry-state : (many (Env) env) (many (Nat) x) -> (erased (Hist Block) hs) (many (State hs) r))
  (let ((erased hs) (many e)) $ entry env x)
  (match many e _ ((MkEInfo _ _ _ s _ _ _ _) (values hs s))))

(def-fns _ $ (many is-settled : (many (Env) env) (many (Nat) x) -> (many (Bool) r))
  (let ((erased hs) (many s)) $ entry-state env x)
  (match many s _ ((SSettled _ _ _) (BTrue)) ((SHypothetical _) (BFalse))))

(def-fns _ $ (many entry-minted : (many (Env) env) (many (Nat) x) -> (many (Bool) r))
  (let ((erased hs) (many e)) $ entry env x)
  (match many e _ ((MkEInfo _ _ _ _ mi _ _ _) mi)))

(def-fns _ $ (many entry-introduced : (many (Env) env) (many (Nat) x) -> (many (Maybe $ Nat) r))
  (let ((erased hs) (many e)) $ entry env x)
  (match many e _ ((MkEInfo _ _ _ _ _ io _ _) io)))

(def-fns _ $ (many is-literal : (many (Env) env) (many (Nat) x) -> (many (Bool) r))
  (match many (entry-introduced env x) _ ((None _) (BTrue)) ((Some _ _) (BFalse))))

(def-fns _ $ (many older-of : (many (Maybe $ Nat) iox) (many (Maybe $ Nat) ioy) (many (Nat) x) (many (Nat) y) -> (many (Bool) r))
  (match many iox _
    ((None _) (match many ioy _ ((None _) (nat-lt x y)) ((Some _ _) (BTrue))))
    ((Some _ _) (match many ioy _ ((None _) (BFalse)) ((Some _ _) (nat-lt x y))))))

(def-fns _ $ (many is-meta : (many (Env) env) (many (Nat) x) -> (many (Bool) r))
  (let ((erased hs) (many e)) $ entry env x)
  (match many e _ ((MkEInfo _ _ _ _ _ _ me _) me)))

(def-fns _ $ (many mark-minted : (many (Env) e) (many (Nat) x) -> (many (Env) r))
  (let-match many e (MkEnv hs hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex))
  (let ((many (EInfo hs) info))
    (match many (idmap-get _ x en) _
      ((Miss _ _ _ _) (MkEInfo _ (None _) (Erased) (SHypothetical _) (BTrue) (Some _ x) (BFalse) (None _)))
      ((Hit _ _ _ i _) (match many i (((EInfo hs) _)) ((MkEInfo _ n m s _ io me site) (MkEInfo _ n m s (BTrue) io me site))))))
  (MkEnv _ hp sc (idmap-set _ x info en) _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex))

; An entry given a name for display only, the scope untouched.
(def-fns _ $ (many env-name-entry : (many (Env) e) (many (Nat) x) (many (String) n) -> (many (Env) r))
  (let-match many e (MkEnv hs hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex))
  (let ((many (EInfo hs) i)) $ match many (idmap-get _ x en) _ ((Hit _ _ _ i _) i) ((Miss _ _ _ _) (MkEInfo _ (None _) (Many) (SHypothetical _) (BFalse) (Some _ x) (BFalse) (None _))))
  (match many i _
    ((MkEInfo _ _ m s mi io me site) (MkEnv _ hp sc (idmap-set _ x (MkEInfo _ (Some _ $ NSrc n) m s mi io me site) en) _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex))))

(def-fns _ $ (many anon-mark : (many (Env) env) (many (Nat) x) -> (many (String) r))
  (let ((erased hs) (many e)) $ entry env x)
  (let-match many e (MkEInfo _ _ _ _ _ _ me site))
  (let ((erased ho) (many o)) $ entry env $ nat-pred x)
  (let-match many o (MkEInfo _ _ _ _ _ _ ome osite))
  (let ((erased tn) (erased tf) (many bnd) (many tb)) $ env-table env)
  (let ((many owned)) $ and (match many (table-slot-of _ _ bnd tb x) (((Bool) _)) ((Some _ s) (nat-eq s x)) ((None _) (BFalse))) $ not $ str-is-empty $ loc-str osite)
  (let ((many kind) (many where)) $ match many owned (((String) _) ((String) _))
    ((BTrue) (values (match many ome (((String) _)) ((BTrue) "m") ((BFalse) "s")) $ loc-str osite))
    ((BFalse) (values (match many me (((String) _)) ((BTrue) "?") ((BFalse) "_")) $ loc-str site)))
  (rope-str $ rcat4 (RChar #\x01) (RStr $ str-cat kind $ nat-str x) (RChar #\x01) $ rcat (RStr where) (RChar #\x02)))

(def-fns _ $ (many entry-name-or-id : (many (Env) env) (many (Nat) x) -> (many (String) r))
  (let ((erased hs) (many e)) $ entry env x)
  (let-match many e (MkEInfo _ n _ _ _ _ _ _))
  (match many n _ ((None _) (str-cat "__" $ nat-str x)) ((Some _ s2) (spell-name s2))))

(def-fns _ $ (many named-as : (many (Env) env) (many (Nat) x) -> (many (String) r))
  (let ((erased hs) (many e)) $ entry env x)
  (let-match many e (MkEInfo _ n _ _ _ _ _ _))
  (match many n _ ((None _) (anon-mark env x)) ((Some _ s2) (name-text s2))))

(def-fns _ $ (many name-of : (many (Env) env) (many (Nat) x) -> (many (String) r))
  (let ((erased hs) (many e)) $ entry env x)
  (let-match many e (MkEInfo _ n _ _ _ _ _ _))
  (match many n _ ((None _) (anon-mark env x)) ((Some _ s2) (spell-name s2))))

; A name or term in a message is set off in backticks; a literal already reads as one and is left bare.
(def-fns _ $ (many tick : (many (String) s) -> (many (String) r))
  (match many (or (is-literal-name s) $ match many s (((Bool) _)) ((SNil) (BFalse)) ((SCons c _) (char-is c 34))) _
    ((BTrue) s)
    ((BFalse) (str-cat3 "`" s "`"))))

(def-fns _ $ (many spell-binder : (many (Maybe $ Name) n) -> (many (String) s))
  (match many n _ ((None _) "_") ((Some _ x) (spell-name x))))

(def-fns _ $ (many tick-name : (many (Name) n) -> (many (String) r))
  (tick $ spell-name n))

(def-fns _ $ (many qname : (many (Env) env) (many (Nat) x) -> (many (String) r))
  (tick $ name-of env x))

; The block a Settled entry's value is, read through its reference.
(def-fns _ $ (many env-block : (many (Env) e) (many (Nat) x) -> (erased (Hist Block) a) (many (Maybe $ Block (Ref Block a)) r))
  (let ((erased hs) (many hp) (many en) (many fi)) $ env-store e)
  (let-match many (idmap-get _ x en) (Hit _ _ _ info _) ((Miss _ _ _ _) (values (HEmpty Block) $ None _)))
  (let-match many info (MkEInfo _ _ _ s _ _ _ _))
  (let-match many s (SSettled _ v _) ((SHypothetical _) (values (HEmpty Block) $ None _)))
  (let ((erased a) (many b) (erased sf)) (store-read Block _ hp v))
  (values a $ Some _ b))

; Forwards [y]'s state to [x] (section 19's state-forwarding let).
(def-fns _ $ (many forward-state : (many (Env) e) (many (Nat) x) (many (Nat) y) -> (many (Env) r))
  (let-match many e (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex))
  (let-match many (idmap-get _ y en) (Hit _ _ _ info _) ((Miss _ _ _ _) e))
  (match many info _
    ((MkEInfo _ _ _ s _ _ _ _) (MkEnv _ hp sc (entries-set-state _ en x s) _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex))))

(def-fns _ $ (many set-hypothetical : (many (Env) e) (many (Nat) x) -> (many (Env) r))
  (let-match many e (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex))
  (MkEnv _ hp sc (entries-set-state _ en x $ SHypothetical _) _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex))

(def-fns _ $ (many minted-from : (many (Env) e) (many (Nat) x) (many (Nat) y) -> (many (Env) r))
  (let-match many e (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex))
  (let-match many (idmap-get _ y en) (Hit _ _ _ src _) ((Miss _ _ _ _) e))
  (let-match many (idmap-get _ x en) (Hit _ _ _ dst _) ((Miss _ _ _ _) e))
  (let-match many src (MkEInfo _ _ _ ss _ _ _ _))
  (let-match many dst (MkEInfo _ _ _ ds _ _ _ _))
  (let-match many ss (SSettled _ _ m) ((SHypothetical _) e))
  (let-match many ds (SSettled _ v _) ((SHypothetical _) e))
  (MkEnv _ hp sc (entries-set-state _ en x $ SSettled _ v m) _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex))

(def-fns _ $ (many forward-binder : (many (Env) e) (many (Nat) x) (many (Nat) y) (many (Multiplicity) mult) -> (many (Env) r))
  (let ((many run)) $ env-run-pos e)
  (let-match many (is-settled e y) (BTrue) ((BFalse) (match many run (((Env) _)) ((BTrue) e) ((BFalse) (forward-state e x y)))))
  (match many mult _
    ((Once) (match many run (((Env) _)) ((BTrue) e) ((BFalse) (set-hypothetical e x))))
    ((Many) (match many run (((Env) _)) ((BTrue) (minted-from e x y)) ((BFalse) (forward-state e x y))))
    ((Erased) (minted-from (match many run (((Env) _)) ((BTrue) e) ((BFalse) (set-state-closed e x $ BToken _))) x y))))

(def-fns _ $ (many forward-marks : (many (Env) e) (many (Nat) x) (many (Nat) y) -> (many (Env) r))
  (let-match many e (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex))
  (let ((erased hs) (many src)) $ entry e y)
  (let-match many (idmap-get _ x en) (Hit _ _ _ dst _) ((Miss _ _ _ _) e))
  (let-match many src (MkEInfo _ _ _ _ mi io _ _))
  (let-match many dst (MkEInfo _ n m s _ own me site))
  (MkEnv _ hp sc (idmap-set _ x (MkEInfo _ n m s mi (match many io (((Maybe $ Nat) _)) ((None _) own) (else io)) me site) en) _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr us hn ex))

(def-fns _ $ (many fact-at : (many (Env) env) (many (Nat) x) -> (many (Term) ty) (many (Maybe $ Term) rule))
  (let ((erased n) (erased f) (many bnd) (many tb)) $ env-table env)
  (fact-in _ _ bnd tb x))

(def-fns _ $ (many env-unique : (many (Env) env) -> (many (UniqueState) r))
  (match many env _ ((MkEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ us hn ex) us)))
(def-fns _ $ (many env-set-unique : (many (Env) env) (many (UniqueState) state) -> (many (Env) r))
  (match many env _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr _ hn ex) (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa tk lt lo pr state hn ex))))
(def-fns _ $ (many env-ctor-tele : (many (Env) env) -> (many (List $ Nat) r))
  (match many (env-unique env) _ ((MkUniqueState ct _ _ _ _ _ _ _ _ al ex) ct)))
(def-fns _ $ (many env-set-ctor-tele : (many (Env) env) (many (List $ Nat) x) -> (many (Env) r))
  (match many (env-unique env) _ ((MkUniqueState _ uses captures ue ie sig words temp wd al ex) (env-set-unique env (MkUniqueState x uses captures ue ie sig words temp wd al ex)))))
(def-fns _ $ (many env-uses : (many (Env) env) -> (many (Uses) r))
  (match many (env-unique env) _ ((MkUniqueState _ uses _ _ _ _ _ _ _ al ex) uses)))
(def-fns _ $ (many env-set-uses : (many (Env) env) (many (Uses) x) -> (many (Env) r))
  (match many (env-unique env) _ ((MkUniqueState ct _ captures ue ie sig words temp wd al ex) (env-set-unique env (MkUniqueState ct x captures ue ie sig words temp wd al ex)))))
(def-fns _ $ (many env-captures : (many (Env) env) -> (many (List $ Nat) r))
  (match many (env-unique env) _ ((MkUniqueState _ _ captures _ _ _ _ _ _ al ex) captures)))
(def-fns _ $ (many env-set-captures : (many (Env) env) (many (List $ Nat) x) -> (many (Env) r))
  (match many (env-unique env) _ ((MkUniqueState ct uses _ ue ie sig words temp wd al ex) (env-set-unique env (MkUniqueState ct uses x ue ie sig words temp wd al ex)))))
(def-fns _ $ (many env-usage-erased : (many (Env) env) -> (many (Bool) r))
  (match many (env-unique env) _ ((MkUniqueState _ _ _ ue _ _ _ _ _ al ex) ue)))
(def-fns _ $ (many env-set-usage-erased : (many (Env) env) (many (Bool) x) -> (many (Env) r))
  (match many (env-unique env) _ ((MkUniqueState ct uses captures _ ie sig words temp wd al ex) (env-set-unique env (MkUniqueState ct uses captures x ie sig words temp wd al ex)))))
(def-fns _ $ (many env-in-extern : (many (Env) env) -> (many (Bool) r))
  (match many (env-unique env) _ ((MkUniqueState _ _ _ _ ie _ _ _ _ al ex) ie)))
(def-fns _ $ (many env-set-in-extern : (many (Env) env) (many (Bool) x) -> (many (Env) r))
  (match many (env-unique env) _ ((MkUniqueState ct uses captures ue _ sig words temp wd al ex) (env-set-unique env (MkUniqueState ct uses captures ue x sig words temp wd al ex)))))
(def-fns _ $ (many env-signature : (many (Env) env) -> (many (List $ Nat) r))
  (match many (env-unique env) _ ((MkUniqueState _ _ _ _ _ sig _ _ _ al ex) sig)))
(def-fns _ $ (many env-set-signature : (many (Env) env) (many (List $ Nat) x) -> (many (Env) r))
  (match many (env-unique env) _ ((MkUniqueState ct uses captures ue ie _ words temp wd al ex) (env-set-unique env (MkUniqueState ct uses captures ue ie x words temp wd al ex)))))
(def-fns _ $ (many env-words : (many (Env) env) -> (many (List $ Nat) r))
  (match many (env-unique env) _ ((MkUniqueState _ _ _ _ _ _ words _ _ al ex) words)))
(def-fns _ $ (many env-set-words : (many (Env) env) (many (List $ Nat) x) -> (many (Env) r))
  (match many (env-unique env) _ ((MkUniqueState ct uses captures ue ie sig _ temp wd al ex) (env-set-unique env (MkUniqueState ct uses captures ue ie sig x temp wd al ex)))))
(def-fns _ $ (many env-temporary : (many (Env) env) -> (many (List $ Nat) r))
  (match many (env-unique env) _ ((MkUniqueState _ _ _ _ _ _ _ temp _ al ex) temp)))
(def-fns _ $ (many env-set-temporary : (many (Env) env) (many (List $ Nat) x) -> (many (Env) r))
  (match many (env-unique env) _ ((MkUniqueState ct uses captures ue ie sig words _ wd al ex) (env-set-unique env (MkUniqueState ct uses captures ue ie sig words x wd al ex)))))

(def-fns _ $ (many env-aliases : (many (Env) env) -> (many (IdMap $ Nat) r))
  (match many (env-unique env) _ ((MkUniqueState _ _ _ _ _ _ _ _ _ al ex) al)))
(def-fns _ $ (many env-set-aliases : (many (Env) env) (many (IdMap $ Nat) x) -> (many (Env) r))
  (match many (env-unique env) _ ((MkUniqueState ct uses captures ue ie sig words temp wd _ ex) (env-set-unique env (MkUniqueState ct uses captures ue ie sig words temp wd x ex)))))

(def-fns _ $ (many env-externs : (many (Env) env) -> (many (Bool) r))
  (match many (env-unique env) _ ((MkUniqueState _ _ _ _ _ _ _ _ _ _ ex) ex)))
(def-fns _ $ (many env-set-externs : (many (Env) env) (many (Bool) x) -> (many (Env) r))
  (match many (env-unique env) _ ((MkUniqueState ct uses captures ue ie sig words temp wd al _) (env-set-unique env (MkUniqueState ct uses captures ue ie sig words temp wd al x)))))

(def-fns _ $ (many env-pragmas : (many (Env) env) -> (many (Pragmas) r))
  (match many (env-unique env) _ ((MkUniqueState _ _ _ _ _ _ _ _ pg al ex) pg)))
(def-fns _ $ (many env-set-pragmas : (many (Env) env) (many (Pragmas) x) -> (many (Env) r))
  (match many (env-unique env) _ ((MkUniqueState ct uses captures ue ie sig words temp _ al ex) (env-set-unique env (MkUniqueState ct uses captures ue ie sig words temp x al ex)))))
(def-fns _ $ (many env-warned : (many (Env) env) -> (many (List $ Warned) r))
  (match many (env-pragmas env) _ ((MkPragmas ws _ _) ws)))
(def-fns _ $ (many env-set-warned : (many (Env) env) (many (List $ Warned) x) -> (many (Env) r))
  (match many (env-pragmas env) _ ((MkPragmas _ rs si) (env-set-pragmas env $ MkPragmas x rs si))))
(def-fns _ $ (many env-regions : (many (Env) env) -> (many (List $ Region) r))
  (match many (env-pragmas env) _ ((MkPragmas _ rs _) rs)))
(def-fns _ $ (many env-set-regions : (many (Env) env) (many (List $ Region) x) -> (many (Env) r))
  (match many (env-pragmas env) _ ((MkPragmas ws _ si) (env-set-pragmas env $ MkPragmas ws x si))))
(def-fns _ $ (many env-unwarned : (many (Env) env) -> (many (Bool) r))
  (match many (env-pragmas env) _ ((MkPragmas _ _ si) si)))
(def-fns _ $ (many env-set-unwarned : (many (Env) env) (many (Bool) x) -> (many (Env) r))
  (match many (env-pragmas env) _ ((MkPragmas ws rs _) (env-set-pragmas env $ MkPragmas ws rs x))))

(def-fns _ $ (many env-tracking : (many (Env) e) -> (many (Tracking) r))
  (match many e _ ((MkEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tk _ _ _ _ _ _) tk)))
(def-fns _ $ (many env-set-tracking : (many (Env) e) (many (Tracking) x) -> (many (Env) r))
  (match many e _ ((MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa _ lt lo pr us hn ex) (MkEnv _ hp sc en _ _ fr tb rp ob li fi lv st cl wa x lt lo pr us hn ex))))
(def-fns _ $ (many env-warn-unused : (many (Env) env) -> (many (Bool) r))
  (match many (env-tracking env) _ ((MkTracking on _ _) on)))
(def-fns _ $ (many env-set-warn-unused : (many (Env) env) (many (Bool) on) -> (many (Env) r))
  (env-set-tracking env $ MkTracking on (MEmpty _) (MEmpty _)))
(def-fns _ $ (many ref-level : (many (IdMap $ RefState) rf) (many (Nat) x) -> (many (Nat) r))
  (let-match many (idmap-get _ x rf) (Hit _ _ _ st _) ((Miss _ _ _ _) 0))
  (let-match many st (RefTo y) ((RefLevel n) n))
  (let-match many (idmap-get _ y rf) (Hit _ _ _ sy _) ((Miss _ _ _ _) 0))
  (match many sy _ ((RefLevel n) n) ((RefTo _) 0)))
(def-fns _ $ (many env-pend : (many (Env) env) (many (Nat) x) -> (many (Env) r))
  (let-match many (env-tracking env) (MkTracking on bs rf))
  (let-match many on (BTrue) ((BFalse) env))
  (match many (idmap-mem _ x rf) _ ((BTrue) env) ((BFalse) (env-set-tracking env $ MkTracking on bs $ idmap-set _ x (RefLevel 0) rf))))
(def-fns _ $ (many loc-place : (many (Loc) lo) -> (many (Maybe $ Pair (String) $ Pair (Nat) (Nat)) r))
  (let-match many lo (MkLoc f p))
  (let-match many p (PosSpot q) ((MkSpot l c) (Some _ $ MkPair _ _ f $ MkPair _ _ l c)))
  (match many q _ ((NoPos) (None _)) ((MkPos f2 l c) (Some _ $ MkPair _ _ f2 $ MkPair _ _ l c))))
(def-fns _ $ (many env-track : (many (Env) env) (many (BinderKind) kind) (many (Nat) x) -> (many (Env) r))
  (let-match many (env-tracking env) (MkTracking on bs rf))
  (let-match many on (BTrue) ((BFalse) env))
  (let-match many (env-entry-at env x) (Some _ l) ((None _) env))
  (let-match many (loc-place l) (Some _ _) ((None _) env))
  (let-match many (env-entry-name env x) (Some _ n) ((None _) env))
  (env-pend (env-set-tracking env $ MkTracking on (idmap-set _ x (MkTracked l n kind (entry-mult-of env x) $ env-usage-erased env) bs) rf) x))
(def-fns _ $ (many env-track-all : (many (Env) env) (many (BinderKind) kind) (subterm many (List $ Nat) xs) -> (many (Env) r))
  (let-match many xs (Cons _ x rest) ((Nil _) env))
  (tail $ env-track-all (env-track env kind x) kind rest))
(def-fns _ $ (many env-stand-for : (many (Env) env) (subterm many (List $ Nat) xs) (many (List $ Nat) ys) -> (many (Env) r))
  (let-match many (env-tracking env) (MkTracking on bs rf))
  (let-match many on (BTrue) ((BFalse) env))
  (let-match many xs (Cons _ x xrest) ((Nil _) env))
  (let-match many ys (Cons _ y yrest) ((Nil _) env))
  (let ((many n)) $ match many (nat-lt (ref-level rf x) (ref-level rf y)) (((Nat) _)) ((BTrue) (ref-level rf y)) ((BFalse) (ref-level rf x)))
  (tail $ env-stand-for (env-set-tracking env $ MkTracking on bs $ idmap-set _ x (RefTo y) $ idmap-set _ y (RefLevel n) rf) xrest yrest))
(def-fns _ $ (many env-refer : (many (Env) env) (many (Bool) live) (many (Nat) x0) -> (many (Env) r))
  (let-match many (env-tracking env) (MkTracking on bs rf))
  (let-match many on (BTrue) ((BFalse) env))
  (let-match many (idmap-get _ x0 rf) (Hit _ _ _ st _) ((Miss _ _ _ _) env))
  (let ((many x)) $ match many st (((Nat) _)) ((RefTo y) y) ((RefLevel _) x0))
  (let ((many want)) $ match many live (((Nat) _)) ((BTrue) 2) ((BFalse) 1))
  (match many (nat-lt (ref-level rf x) want) _
    ((BFalse) env)
    ((BTrue) (env-set-tracking env $ MkTracking on bs $ idmap-set _ x (RefLevel want) rf))))

(def-fns _ $ (many entry-word : (many (Env) env) (many (Nat) x) -> (many (Bool) r))
  (list-mem-bin (env-words env) x))
(def-fns _ $ (many insert-desc : (many (Nat) x) (subterm many (List $ Nat) xs) -> (many (List $ Nat) r))
  (let-match many xs (Cons _ y rest)
    ((Nil _) (Cons _ x xs)))
  (match many (nat-lt y x) _ ((BTrue) (Cons _ x xs)) ((BFalse) (Cons _ y $ notail $ insert-desc x rest))))
(def-fns _ $ (many mark-word : (many (Env) env) (many (Nat) x) (many (Bool) temporary) -> (many (Env) r))
  (let ((many env2)) (env-set-words env $ insert-desc x $ env-words env))
  (match many temporary _ ((BFalse) env2) ((BTrue) (env-set-temporary env2 $ insert-desc x $ env-temporary env2))))
(def-fns _ $ (many use-max : (many (Use) a) (many (Use) b) -> (many (Use) r))
  (match many a _ ((UseConsumed _) a) ((UseShared _) b)))
(def-fns _ $ (many uses-map : (many (Uses) u) -> (many (IdMap $ Use) r))
  (match many u _ ((MkUses m _) m)))
(def-fns _ $ (many uses-fork : (many (Uses) u) -> (many (Uses) r))
  (MkUses (uses-map u) (Nil _)))
(def-fns _ $ (many uses-set : (many (Uses) u) (many (Nat) x) (many (Use) state) -> (many (Uses) r))
  (match many u _ ((MkUses m d) (MkUses (idmap-set _ x state m) (Cons _ x d)))))
(def-fns _ $ (many uses-join-keys : (subterm many (List $ Nat) ks) (many (IdMap $ Use) from) (many (Uses) into) -> (many (Uses) r))
  (let-match many ks (Cons _ k rest) ((Nil _) into))
  (let-match many (idmap-get _ k from) (Hit _ _ _ state _) ((Miss _ _ _ _) (tail $ uses-join-keys rest from into)))
  (tail $ uses-join-keys rest from $ uses-set into k $ match many (idmap-get _ k $ uses-map into) (((Use) _)) ((Miss _ _ _ _) state) ((Hit _ _ _ old _) (use-max state old))))
(def-fns _ $ (many uses-join : (many (Uses) a) (many (Uses) b) -> (many (Uses) r))
  (match many b _ ((MkUses m d) (uses-join-keys d m a))))
(def-fns _ $ (many misuse : (many (Multiplicity) demand) (many (Multiplicity) supply) -> (many (Maybe $ String) r))
  (match many supply _
    ((Erased) (match many (mult-is-many demand) _ ((BTrue) (Some _ "used in a non-erased position")) ((BFalse) (None _))))
    ((Many) (match many demand _ ((Once) (Some _ "used at unique")) (else (None _))))
    ((Once) (match many demand _ ((Many) (Some _ "used at many without `share`")) (else (None _))))))

(def-fns _ $ (many lit-of : (subterm many (List $ LitEntry) ls) (many (Nat) x) -> (many (Maybe $ Pair (String) (Syn)) r))
  (let-match many ls (Cons _ l rest) ((Nil _) (None _)))
  (let-match many l (MkLitEntry y _ lit _ _))
  (match many (nat-eq x y) _ ((BTrue) lit) ((BFalse) (tail $ lit-of rest x))))

(def-fns _ $ (many spelling-of : (many (Maybe $ Pair (String) (Syn)) lit) -> (many (Maybe $ String) r))
  (let-match many lit (Some _ p) ((None _) (None _)))
  (match many p _ ((MkPair _ _ s _) (Some _ s))))

(def-fns _ $ (many lit-entry-spelling : (many (LitEntry) l) -> (many (Maybe $ String) r))
  (match many l _ ((MkLitEntry _ _ lit _ _) (spelling-of lit))))

(def-fns _ $ (many lit-spelling : (many (List $ LitEntry) ls) (many (Nat) x) -> (many (Maybe $ String) r))
  (spelling-of $ lit-of ls x))

(def-fns _ $ (many set-entry-mult : (many (Env) env) (many (Nat) x) (many (Multiplicity) mult) -> (many (Env) r))
  (let ((erased hs) (many hp) (many en) (many fi)) (env-store env))
  (let-match many (idmap-get _ x en) (Hit _ _ _ e _) ((Miss _ _ _ _) env))
  (match many e _
    ((MkEInfo _ name _ state minted io meta site)
      (env-with-store env _ hp (idmap-set _ x (MkEInfo _ name mult state minted io meta site) en) fi))))

(def-fns _ $ (many lookup : (many (Env) env) (many (Name) name) -> (many (Maybe $ Nat) r))
  (match many name _ ((NHandle x _ _ _) (Some _ x)) (else (name-index-get _ name $ scope-names $ env-scope env))))

(def-fns _ $ (many visible-names : (many (Env) env) (subterm many (List $ Nat) xs) -> (many (List $ String) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (Nil _)))
  (let ((many names)) (notail $ visible-names env rest))
  (let ((erased hs) (many e)) $ entry env x)
  (let-match many e (MkEInfo _ n _ _ _ _ _ _))
  (let-match many n (Some _ nm) ((None _) names))
  (let-match many nm (NSrc s) (else names))
  (let-match many (lookup env nm) (Some _ y)
    ((None _) names))
  (match many (nat-eq x y) _ ((BTrue) (Cons _ s names)) ((BFalse) names)))

(def-fns _ $ (many nearest-names : (many (String) name) (subterm many (List $ String) xs) -> (many (Maybe $ Nat) best) (many (List $ String) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (values (None _) (Nil _))))
  (let ((many best) (many ties)) (notail $ nearest-names name rest))
  (let ((many d)) (distance name x))
  (let-match many best (Some _ b) ((None _) (values (Some _ d) $ list1 _ x)))
  (match many (nat-lt d b) _
    ((BTrue) (values (Some _ d) $ list1 _ x))
    ((BFalse) (values best $ match many (nat-eq d b) (((List $ String) _)) ((BTrue) (Cons _ x ties)) ((BFalse) ties)))))

(def-fns _ $ (many hint : (many (Env) env) (many (Name) n) -> (many (String) r))
  (let-match many n (NSrc name) (else ""))
  (let ((many best) (many ties)) $ nearest-names name $ visible-names env $ scope-ids $ env-scope env)
  (match many ties _ ((Nil _) "") ((Cons _ _ _) (str-cat "\nhint: nearest in scope: " $ join-strs ties " "))))

(def-fns _ $ (many is-prelude : (many (Env) env) (many (Nat) x) -> (many (Bool) r))
  (list-mem-bin (scope-ids $ env-prelude env) x))


(def-fns _ $ (many canon-env : (many (Env) env) (many (Term) t) -> (many (Term) r))
  (let ((erased n) (erased f) (many bnd) (many tb)) $ env-table env)
  (let ((many r) (erased fr)) $ canon-in _ _ bnd tb t)
  r)

(def-fns _ $ (many canon-env-tele : (many (Env) env) (many (List $ Entry) es) -> (many (List $ Entry) r))
  (let ((erased n) (erased f) (many bnd) (many tb)) $ env-table env)
  (let ((many r) (erased fr)) $ canon-tele-in _ _ bnd tb es)
  r)

; The automatic slot an entry was minted with (section 35); `None` only for an id the table never bound.
(def-fns _ $ (many env-slot-of : (many (Env) env) (many (Nat) x) -> (many (Maybe $ Nat) r))
  (let ((erased n) (erased f) (many bnd) (many tb)) $ env-table env)
  (table-slot-of _ _ bnd tb x))

(def-fns _ $ (many slot-atom : (many (Nat) x) -> (many (Term) t))
  (TSlotOf $ TVar x))

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
      ((TSlotOf c) (tail $ term-vars c acc)) (else acc)))
  ((many term-vars-list : (subterm many (List $ Term) ts) (many (List $ Nat) acc) -> (many (List $ Nat) r))
    (match many ts _
      ((Nil _) acc)
      ((Cons _ t rest) (tail $ term-vars t $ notail $ term-vars-list rest acc))))
  ((many term-vars-mctors : (subterm many (List $ MCtor) cs) (many (List $ Nat) acc) -> (many (List $ Nat) r))
    (let-match many cs (Cons _ c rest)
      ((Nil _) acc))
    (match many c _ ((MkMCtor _ t) (tail $ term-vars t $ notail $ term-vars-mctors rest acc))))
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
  (let ((erased n) (erased f) (many bnd) (many tb)) $ env-table env)
  (let-match many (table-free-metas _ _ bnd tb) (Succ _) ((Zero) (BFalse)))
  (has-meta (canon-env env t) env))



; Whether a type is one the fetching forms look for in ambient scope (sections 8, 33).
(def-fns _ $ (many is-object-type : (many (Term) ty) (many (Nat) objid) -> (many (Bool) r))
  (let-match many ty (TApp h _)
    ((TMatchable _ _ _ _ _) (BTrue))
    ((TSlotOf _) (BFalse))
    ((TCell _ _) (BFalse)) (else (BFalse)))
  (match many h _ ((TVar x) (or (nat-eq x objid) $ nat-eq x atfn-id)) (else (BFalse))))

; ---- Printing terms and values, for diagnostics and the final value (lib/term.ml's to_string, lib/value.ml's show)

; The newest name in scope holding each special form a message spells (Env.speller), else `_` and its
; built-in name, as a marker the printed message notes.
(def-fns _ $ (many kw-find : (subterm many (List $ Pair (String) $ Pair (Nat) (String)) kws) (many (String) b) -> (many (Maybe $ Pair (Nat) (String)) r))
  (let-match many kws (Cons _ k rest) ((Nil _) (None _)))
  (let-match many k (MkPair _ _ b2 v))
  (match many (str-eq b b2) _ ((BTrue) (Some _ v)) ((BFalse) (tail $ kw-find rest b))))

(def-fns _ $ (many kw-spell : (many (List $ Pair (String) $ Pair (Nat) (String)) kws) (many (String) b) -> (many (String) r))
  (let-match many (kw-find kws b) (Some _ v)
    ((None _) (rope-str $ rcat4 (RChar #\x01) (RStr "k") (RStr b) $ rcat (RChar #\x01) (RChar #\x02))))
  (match many v _ ((MkPair _ _ _ n) n)))

(def-fns _ $ (many is-universe : (many (Term) h) (many (List $ Term) args) -> (many (Bool) r))
  (let-match many h (TVar u) (else (BFalse)))
  (and (nat-eq u univ-id) $ list-is-empty _ args))

(def-fns _ $ (many show-universe : (many (Env) env) (many (List $ Pair (String) $ Pair (Nat) (String)) kws) -> (many (String) r))
  (let-match many (kw-find kws universe-key) (Some _ v)
    ((None _) (str-cat3 "(" (name-of env univ-id) ")")))
  (match many v _ ((MkPair _ _ _ n) n)))

(def-fns _
  ((many show-term : (subterm many (Term) t) (many (Env) env) (many (List $ Pair (String) $ Pair (Nat) (String)) kws) (many (List $ Maybe $ Name) bound) -> (many (Rope) r))
    (match many t _
      ((TVar x) (RStr $ named-as env x))
      ((TBound k)
        (RStr $ match many (list-nth _ bound k) (((String) _))
          ((NthHit _ _ _ n _) (match many n (((String) _)) ((Some _ s) (spell-name s)) ((None _) (str-cat "#" $ nat-str k))))
          ((NthMiss _ _ _ _) (str-cat "#" $ nat-str k))))
      ((TApp h args)
        (match many (is-universe h args) _
          ((BTrue) (RStr $ show-universe env kws))
          ((BFalse) (rcat4 (RStr "(") (notail $ show-term h env kws bound) (notail $ show-terms args env kws bound) $ RStr ")"))))
      ((TCell h args) (rcat4 (RStr $ str-cat3 "(" (kw-spell kws "Cell") " ") (notail $ show-term h env kws bound) (notail $ show-terms args env kws bound) $ RStr ")"))
      ((TFn uq l ps rs)
        (let ((many psr) (many b2)) $ notail $ show-tele ps env kws bound (BTrue))
        (let ((many rsr) (many b3)) $ notail $ show-tele rs env kws b2 (BTrue))
        (rcat5 (RStr $ str-cat3 "(" (kw-spell kws $ match many uq (((String) _)) ((BTrue) "UniqueFn") ((BFalse) "Fn")) " ") (notail $ show-term l env kws bound) psr (rcat (RStr $ str-cat " " $ kw-spell kws "->") rsr) $ RStr ")"))
      ((TTyCtor ps)
        (let ((many psr) (many b2)) $ notail $ show-tele ps env kws bound (BFalse))
        (rwrap (str-cat "(" $ kw-spell kws "TyCtor") psr $ str-cat3 " " (kw-spell kws "->") $ str-cat3 " " (show-universe env kws) ")"))
      ((TValCtor ps ret)
        (let ((many psr) (many b2)) $ notail $ show-tele ps env kws bound (BTrue))
        (rcat4 (RStr $ str-cat "(" $ kw-spell kws "ValCtor") psr (rcat (RStr $ str-cat3 " " (kw-spell kws "->") " ") $ notail $ show-term ret env kws b2) $ RStr ")"))
      ((TMatchable d nt ex ty cs)
        (let ((many marks)) (str-cat (match many nt (((String) _)) ((BTrue) (str-cat (kw-spell kws "newtype") " ")) ((BFalse) "")) (match many ex (((String) _)) ((BTrue) (str-cat (kw-spell kws "extern") " ")) ((BFalse) ""))))
        (rcat5 (RStr $ str-cat3 "(" (kw-spell kws "Matchable") $ str-cat3 " " (kw-spell kws $ match many d (((String) _)) ((DEnum) "enum") ((DUnion) "union")) " ") (RStr marks) (notail $ show-term ty env kws bound) (notail $ show-mctors cs env kws bound) $ RStr ")"))
      ((TSlotOf c) (rwrap (str-cat3 "(" (kw-spell kws "slot-of") " ") (notail $ show-term c env kws bound) ")"))
      ((TErr m) (rwrap "<error: " (RStr m) ">"))))
  ((many show-terms : (subterm many (List $ Term) ts) (many (Env) env) (many (List $ Pair (String) $ Pair (Nat) (String)) kws) (many (List $ Maybe $ Name) bound) -> (many (Rope) r))
    (match many ts _
      ((Nil _) (REmpty))
      ((Cons _ t rest) (rcat3 (RStr " ") (notail $ show-term t env kws bound) $ notail $ show-terms rest env kws bound))))
  ((many show-mctors : (subterm many (List $ MCtor) cs) (many (Env) env) (many (List $ Pair (String) $ Pair (Nat) (String)) kws) (many (List $ Maybe $ Name) bound) -> (many (Rope) r))
    (let-match many cs (Cons _ c rest) ((Nil _) (REmpty)))
    (match many c _
      ((MkMCtor m t) (rcat5 (RStr " (") (RStr $ kw-spell kws $ mult-name m) (rcat (RStr " ") $ notail $ show-term t env kws bound) (RStr ")") $ notail $ show-mctors rest env kws bound))))
  ((many show-tele : (subterm many (List $ Entry) es) (many (Env) env) (many (List $ Pair (String) $ Pair (Nat) (String)) kws) (many (List $ Maybe $ Name) bound) (many (Bool) marked) -> (many (Rope) r) (many (List $ Maybe $ Name) bound2))
    (let-match many es (Cons _ e rest) ((Nil _) (values (REmpty) bound)))
    (let-match many e (MkEntry n s m sg place _))
    (let ((many (String) nm)) $ spell-binder n)
    (let ((many (String) marks))
      (match many marked _
        ((BFalse) "")
        ((BTrue) (str-cat3 (match many s (((String) _)) ((BTrue) (str-cat (kw-spell kws "subterm") " ")) ((BFalse) "")) (kw-spell kws $ mult-name m) " "))))
    (let ((many (Rope) body)) (match many sg _
                       ((SgTy t) (rcat3 (notail $ show-term t env kws bound) (RStr " ") $ RStr nm))
                       ((SgIs t _) (rcat3 (notail $ show-term t env kws bound) (RStr $ str-cat3 " " (kw-spell kws "is") " ") $ RStr nm))))
    (let ((many body2)) (match many place (((Rope) _))
      ((None _) body)
      ((Some _ p) (match many p _
        ((TSlotOf loc) (rcat3 body (RStr $ str-cat3 " " (kw-spell kws "at") " ") (notail $ show-term loc env kws bound)))
        (else (rcat3 body (RStr $ str-cat3 " " (kw-spell kws "at") " ") (notail $ show-term p env kws bound)))))))
    (let ((many restr) (many b2)) $ notail $ show-tele rest env kws (Cons _ n bound) marked)
    (values (rcat5 (RStr " (") (RStr marks) body2 (RStr ")") restr) b2)))

; Shadowing is legal (section 19) and warns at every binder that hides a name already in scope
; (ASSUMPTIONS 195). Only a binder the source wrote carries a position, and only such a binder warns;
; the entry it hides carries one too unless the built-ins minted it, which is what the other message says.
(def-fns _ $ (many warn-shadow : (many (Env) env) (many (Maybe $ Name) name) (many (Maybe $ Loc) site) (many (Bool) written) -> (many (Env) r))
  (let-match many written (BTrue) ((BFalse) env))
  (let-match many site (Some _ l) ((None _) env))
  (let-match many name (Some _ n) ((None _) env))
  (let-match many (lookup env n) (Some _ prior) ((None _) env))
  (let-match many env (MkEnv _ _ _ _ _ _ fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
  (match many (env-entry-at env prior) (((Env) _))
    ((Some _ pl) (env-set-said env $ Cons _ (SaidShadow (Succ fr) prior pl n l) $ env-said env))
    ((None _)
      (env-warn-at env l $ str-cat3 "declaration of " (tick-name n) " shadows a built-in"))))

; Mints an entry: a fresh id, its name in scope, its state, its type and optional rule (section 5). A meta,
; standing for a `_` argument (DESIGN.md section 50), enters neither the scope nor the objects: nothing reaches it by
; name or by type, and unification alone solves it. No other entry's type or rule may mention one still
; unsolved -- the invariant behind the sugar -- except while a telescope with holes is being built [holes].
; The term a binder's type or rule still holds an open meta in, the rule's first as the reference reports it;
; elab.sl's bind-as refuses it (lib/env.ml's bind).
(def-fns _ $ (many open-in : (many (Env) env) (many (Bool) meta) (many (Bool) holes) (many (Term) ty) (many (Maybe $ Term) rule) -> (many (Maybe $ Term) t))
  (let-match many (or meta holes) (BFalse) ((BTrue) (None _)))
  (let ((many (Maybe $ Term) in-rule)) $ match many rule _ ((None _) (None _)) ((Some _ t) (match many (has-meta-env env t) _ ((BTrue) (Some _ t)) ((BFalse) (None _)))))
  (let-match many in-rule (None _) ((Some _ t) (Some _ t)))
  (match many (has-meta-env env ty) _ ((BTrue) (Some _ ty)) ((BFalse) (None _))))

(def-fns _ $ (many bind-entry : (many (Env) env) (erased (Hist Block) hl) (many (IdMap $ EInfo hl) en) (many (Bool) meta) (many (Bool) holes) (many (Bool) literal) (many (Maybe $ Name) name) (many (Maybe $ Loc) site) (many (Bool) written) (many (Multiplicity) mult) (many (Term) ty) (many (Maybe $ Term) rule) (many (Nat) objid) ->
    (many (Env) r) (many (IdMap $ EInfo hl) en2) (many (Nat) x))
  ; before the entry is minted, while the scope still holds what it hides
  (let ((many (Env) envs)) (warn-shadow env name site written))
  (let-match many envs (MkEnv _ hp sc en0 _ _ fr tb rp ob li fi lv sts cl wa tk lt lo pr us hn ex))
  (let ((many x) (erased ltp)) (values (Succ fr) (lt-succ fr)))
  (let ((many (Scope) sc2))
    (match many (or meta literal) _
      ((BTrue) sc)
      ((BFalse) (match many sc _ ((MkScope names ids) (MkScope (match many name (((NameIndex $ Nat) _)) ((None _) names) ((Some _ n) (name-index-set _ n x names))) $ Cons _ x ids))))))
  (let ((many en2)) $ idmap-set _ x (MkEInfo _ name mult (SHypothetical _) (BFalse) (match many literal (((Maybe $ Nat) _)) ((BTrue) (None _)) ((BFalse) (Some _ x))) meta site) en)
  (let ((erased (Nat) nf2) (erased (Facts nf2) ff2) (many (Table nf2 ff2 x) tb2))
    (match many rule _
      ((None _) (table-insert _ _ _ tb x ltp ty))
      ((Some _ t)
        (let ((many t2) (erased ft)) $ canon-in _ _ _ tb t)
        (table-insert-ruled _ _ _ tb x ltp ty t2 ft))))
  ; every entry, erased or a meta included, is minted with its automatic slot, the next id (section 35)
  (let ((erased (Nat) nf3) (erased (Facts nf3) ff3) (many (Table nf3 ff3 (Succ x)) tb3)) $ table-insert _ _ _ tb2 (Succ x) (lt-succ x) slot-term)
  (let ((many (List $ Nat) ob2)) $ match many (and (not meta) $ is-object-type ty objid) _ ((BTrue) (Cons _ x ob)) ((BFalse) ob))
  (values (MkEnv _ hp sc2 en0 _ _ (Succ x) (table-add-slot _ _ _ tb3 x meta) rp ob2 li fi lv sts cl wa tk lt lo pr us hn ex) en2 x))

(def-fns _ $ (many bind-as-raw : (many (Env) env) (many (Bool) meta) (many (Bool) holes) (many (Bool) literal) (many (Maybe $ Name) name) (many (Maybe $ Loc) site) (many (Bool) written) (many (Multiplicity) mult) (many (Term) ty) (many (Maybe $ Term) rule) (many (Nat) objid) ->
    (many (Env) r) (many (Nat) x))
  (let ((erased hl) (many h)) $ env-heap env)
  (let ((many env2) (many en2) (many x)) $ bind-entry env _ (heap-entries _ h) meta holes literal name site written mult ty rule objid)
  (values (env-with-heap env2 _ $ heap-with-entries _ h en2) x))

(def-fns _ $ (many bind-raw : (many (Env) env) (many (Maybe $ Name) name) (many (Maybe $ Loc) site) (many (Bool) written) (many (Multiplicity) mult) (many (Term) ty) (many (Maybe $ Term) rule) (many (Nat) objid) ->
    (many (Env) r) (many (Nat) x))
  (bind-as-raw env (BFalse) (BFalse) (BFalse) name site written mult ty rule objid))

; A binder that is Settled at once: over a closed block, over the token, or over the token only in run
; position (section 29).
(def-fns _ $ (many bind-closed : (many (Env) env) (many (Maybe $ Name) name) (many (Maybe $ Loc) site) (many (Bool) written) (many (Multiplicity) mult) (many (Block (Ref Block (HEmpty Block))) b) (many (Term) ty) (many (Maybe $ Term) rule) (many (Nat) objid) ->
    (many (Env) r) (many (Nat) x))
  (let ((many env2) (many x)) $ bind-raw env name site written mult ty rule objid)
  (values (set-state-closed env2 x b) x))

(def-fns _ $ (many bind-token : (many (Env) env) (many (Maybe $ Name) name) (many (Maybe $ Loc) site) (many (Bool) written) (many (Multiplicity) mult) (many (Term) ty) (many (Maybe $ Term) rule) (many (Nat) objid) ->
    (many (Env) r) (many (Nat) x))
  (bind-closed env name site written mult (BToken _) ty rule objid))

(def-fns _ $ (many bind-lit : (many (Env) env) (erased (Hist Block) hs) (many (Heap hs) h) (many (Multiplicity) mult) (many (Block (Ref Block (HEmpty Block))) b) (many (Term) ty) (many (Maybe $ Term) rule) ->
    (many (Env) r) (erased (Hist Block) hs2) (many (Heap hs2) h2) (erased (Suffix Block hs2 hs) sf) (many (Nat) x))
  (let ((many env2) (many en2) (many x)) $ bind-entry env _ (heap-entries _ h) (BFalse) (BFalse) (BTrue) (None _) (None _) (BFalse) mult ty rule delegate-id)
  (let ((erased hs2) (many h2) (erased sf)) $ heap-set-closed _ (heap-with-entries _ h en2) x b)
  (values env2 hs2 h2 sf x))

(def-fns _ $ (many bind-erased-raw : (many (Env) env) (many (Maybe $ Name) name) (many (Maybe $ Loc) site) (many (Bool) written) (many (Multiplicity) mult) (many (Term) ty) (many (Maybe $ Term) rule) (many (Nat) objid) ->
    (many (Env) r) (many (Nat) x))
  (match many (env-run-pos env) _
    ((BTrue) (bind-token env name site written mult ty rule objid))
    ((BFalse) (bind-raw env name site written mult ty rule objid))))


; ---- Instantiation and abstraction over de Bruijn binders (lib/term.ml)

(def-adts $ (VOp : -> Type)
  enum
  (many OpInst : (many (List $ Term) args) -> (VOp))
  (many OpAbs : (many (List $ Nat) ids) -> (VOp))
  (many OpMeta : (many (Env) env) -> (VOp))
  (many OpWild : (many (Nat) fresh) -> (VOp))
  (many OpSlots : (many (List $ Nat) ids) (many (List $ Nat) slots) -> (VOp)))

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
      (let-match many rule (Some _ _)
        ((None _) t))
      (match many (is-meta env x) _ ((BTrue) (canon-env env t)) ((BFalse) t)))
    ((OpWild f)
      (let-match many t (TVar x) (else t))
      (match many (nat-lt x f) _ ((BTrue) t) ((BFalse) (TVar (Zero)))))
    ((OpSlots ids slots)
      (let-match many t (TVar s) (else t))
      (match many (index-of-bin slots s 0) _
        ((Some _ i) (TSlotOf $ TVar $ list-nth-or _ ids i s))
        ((None _) t)))))

(def-fns _ $ (many meta-slot : (many (VOp) op) (many (Term) c) -> (many (Maybe $ Env) r))
  (let-match many op (OpMeta env) (else (None _)))
  (let-match many c (TVar x) (else (None _)))
  (match many (is-meta env x) _ ((BTrue) (Some _ env)) ((BFalse) (None _))))

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
      ((TSlotOf c) (match many (meta-slot op c) _ ((Some _ env) (canon-env env t)) ((None _) (TSlotOf $ notail $ mapv c op d))))
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

(def-fns _ $ (many minted-type : (many (Env) env) (many (Nat) m) -> (many (Term) t))
  (match many (is-literal env m) _ ((BTrue) (type-of (trusted-snapshot env) m)) ((BFalse) (trusted-type env m))))
(def-fns _ $ (many minted-is : (many (Nat) m) -> (many (Term) t))
  (TVar m))

; ---- The built-in entries (lib/prelude.ml): Univ, Type, Level, the proof types, Special and its forms

(def-fns _ $ (many ty-entry : (many (String) name) (many (Term) t) -> (many (Entry) e))
  (MkEntry (Some _ $ NSrc name) (BFalse) (Erased) (SgTy t) (None _) (None _)))

(let ((many empty-env)) (MkEnv _ (store-empty Block) scope-empty (MEmpty _) _ _ (Zero) empty-table (TrustHere) (Nil _) (nm-empty _) (Nil _) (None _) (MkEnclosing (None _) (Nil _) (None _) (BFalse)) (Nil _) (Nil _) tracking-empty (Nil _) (MkLoc "" (MkSpot 0 0)) scope-empty unique-empty (nm-empty _) (MkMacros 0 0 (Nil _) (Nil _) 1000000000)))

(def-fns _ $ (many bind-builtin : (many (Env) env) (many (String) name) (many (Term) ty) (many (Maybe $ Term) rule) -> (many (Env) r))
  (let ((many env2) (many x)) $ bind-token env (Some _ $ NSrc name) (None _) (BFalse) (Erased) ty rule delegate-id)
  env2)

(let ((many special-adt-stub)) (MkAdt "Special" (BTrue) (Nil _) (None _) (BFalse)))

; Binds each form's %-constructor (ASSUMPTIONS 5) and the form's own entry holding that constructor's value;
; returns the constructors for the Special Matchable.
(def-fns _ $ (many bind-specials : (subterm many (List $ SpEntry) sps) (many (Env) env) (many (Nat) index) (many (List $ Nat) shape) -> (many (Env) r) (many (List $ Ctor) ctors) (many (List $ MCtor) mctors))
  (let-match many sps (Cons _ sp rest) ((Nil _) (values env (Nil _) $ Nil _)))
  (let-match many sp (MkSpEntry name _))
  (let ((many cname)) $ str-cat "%" name)
  (let ((many env2) (many c)) $ bind-raw env (Some _ $ NSrc cname) (None _) (BFalse) (Many) (TValCtor (Nil _) special-term) (None _) delegate-id)
  (let ((many ctor)) (MkCtor cname c index 0 (BTrue) (None _) shape (BFalse)))
  (let ((many env3)) $ set-state-closed env2 c $ BCtorFn _ ctor)
  (let ((many env4) (many ctors) (many mctors)) $ notail $ bind-specials rest env3 (Succ index) shape)
  (values env4 (Cons _ ctor ctors) $ Cons _ (MkMCtor (Many) $ TVar c) mctors))

(def-fns _ $ (many bind-special-names : (subterm many (List $ SpEntry) sps) (many (List $ Ctor) ctors) (many (Env) env) -> (many (Env) r))
  (let-match many sps (Cons _ sp rest) ((Nil _) env))
  (let-match many ctors (Cons _ ctor crest) ((Nil _) env))
  (let-match many sp (MkSpEntry name _))
  (let-match many ctor (MkCtor _ c _ _ _ _ _ _))
  (let ((many env2) (many x)) $ bind-closed env (Some _ $ NSrc name) (None _) (BFalse) (Many) (BTag _ ctor $ Nil _) special-term (Some _ $ TApp (TVar c) $ Nil _) delegate-id)
  (tail $ bind-special-names rest crest env2))

(def-fns _ $ (many make-builtins : -> (many (Env) env))
  (let ((many hetero)) (Cons _ (ty-entry "A" type-term) $ Cons _ (ty-entry "a" $ TBound 0) $
                      Cons _ (ty-entry "B" type-term) $ Cons _ (ty-entry "b" $ TBound 0) (Nil _)))
  (let ((many e1)) $ bind-builtin empty-env "Univ" (TTyCtor $ Nil _) $ None _)
  (let ((many e2)) $ bind-builtin e1 "Type" type-term $ Some _ type-term)
  (let ((many e3)) $ bind-builtin e2 "Level" (TTyCtor $ Nil _) $ None _)
  (let ((many eslot)) (bind-builtin e3 "Slot" (TTyCtor $ Nil _) $ None _))
  (let ((many enull) (many null)) (bind-token eslot (Some _ $ NSrc "vacant-slot") (None _) (BFalse) (Many) slot-term (None _) delegate-id))
  (let ((many eworld)) (bind-builtin (mark-word enull null (BFalse)) "World" (TTyCtor $ Nil _) $ None _))
  (let ((many e4)) (bind-builtin eworld "Predates"
                   (TTyCtor (Cons _ (ty-entry "A" type-term) $ Cons _ (ty-entry "a" $ TBound 0) $
                             Cons _ (ty-entry "l" level-term) (Nil _))) $ None _))
  (let ((many e5)) $ bind-builtin e4 "Subterm" (TTyCtor hetero) $ None _)
  (let ((many esharing)) (bind-builtin e5 "Sharing" (TTyCtor $ Nil _) $ None _))
  (let ((many ushape)) (Cons _ 0 $ Cons _ 0 $ Nil _))
  (let ((many uc)) (MkCtor "Unique" unique-id 0 0 (BTrue) (None _) ushape (BFalse)))
  (let ((many sc)) (MkCtor "Shared" shared-id 1 0 (BTrue) (None _) ushape (BFalse)))
  (let ((many eu) (many ui)) (bind-closed esharing (Some _ $ NSrc "Unique") (None _) (BFalse) (Many) (BCtorFn _ uc) (TValCtor (Nil _) sharing-term) (None _) delegate-id))
  (let ((many es) (many si)) (bind-closed eu (Some _ $ NSrc "Shared") (None _) (BFalse) (Many) (BCtorFn _ sc) (TValCtor (Nil _) sharing-term) (None _) delegate-id))
  (let ((many ucs)) (Cons _ uc $ Cons _ sc $ Nil _))
  (let ((many umcs)) (Cons _ (MkMCtor (Many) $ TVar ui) $ Cons _ (MkMCtor (Many) $ TVar si) $ Nil _))
  (let ((many em) (many mid)) (bind-closed es (None _) (None _) (BFalse) (Many) (BMat _ $ MkAdt "Sharing" (BTrue) ucs (None _) (BFalse)) (TMatchable (DEnum) (BFalse) (BFalse) (TVar sharing-id) umcs) (None _) delegate-id))
  (let ((many coercible-tele)) (Cons _ (ty-entry "sa" sharing-term) $ Cons _ (ty-entry "A" type-term) $ Cons _ (ty-entry "a" $ TBound 0) $ Cons _ (ty-entry "sb" sharing-term) $ Cons _ (ty-entry "B" type-term) $ Cons _ (ty-entry "b" $ TBound 0) $ Nil _))
  (let ((many e6)) (bind-builtin (env-settled $ env-open em mid) "Coercible" (TTyCtor coercible-tele) $ None _))
  (let ((many delegate-tele)) (Cons _ (ty-entry "sg" sharing-term) $ Cons _ (ty-entry "G" type-term) $ Cons _ (ty-entry "g" $ TBound 0) $ Cons _ (ty-entry "sf" sharing-term) $ Cons _ (ty-entry "F" type-term) $ Cons _ (ty-entry "f" $ TBound 0) $ Nil _))
  (let ((many edel)) (bind-builtin e6 "Delegate" (TTyCtor delegate-tele) $ None _))
  (let ((many eatfn)) (bind-builtin edel "AtFn" (TTyCtor $ Cons _ (ty-entry "F" type-term) $ Cons _ (ty-entry "f" $ TBound 0) $ Nil _) $ None _))
  (let ((many e7)) $ bind-builtin eatfn "Special" (TTyCtor $ Nil _) $ None _)
  (let ((many e8) (many ctors) (many mctors)) $ bind-specials sp-table e7 0 $ list-replicate _ (list-length _ sp-table) 0)
  (let ((many adt)) (MkAdt "Special" (BTrue) ctors (None _) (BFalse)))
  (let ((many e9) (many m)) $ bind-closed e8 (None _) (None _) (BFalse) (Many) (BMat _ adt) (TMatchable (DEnum) (BFalse) (BFalse) (TVar special-id) mctors) (None _) delegate-id)
  (bind-special-names sp-table ctors $ env-settled $ env-open e9 m))


; ---- Inference over the grammar (lib/elab.ml's infer)

; The head type constructor of a canonical type, if any.
(def-fns _ $ (many type-head : (many (Env) env) (many (Term) ty) -> (many (Maybe $ Nat) r))
  (let-match many (canon-env env ty) (TApp h _)
    ((TCell _ _) (None _)) (else (None $ Nat)))
  (match many h _ ((TVar x) (Some _ x)) (else (None $ Nat))))

(def-fns _ $ (many bool-eq : (many (Bool) a) (many (Bool) b) -> (many (Bool) r))
  (match many a _ ((BTrue) b) ((BFalse) (not b))))

; ---- Structural identity of canonical terms (section 9's canonicalize-then-compare)

(def-fns _ $ (many mult-eq : (many (Multiplicity) a) (many (Multiplicity) b) -> (many (Bool) r))
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
      ((TSlotOf c) (match many b _ ((TSlotOf c2) (tail $ term-eq c c2)) (else (BFalse))))
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
    (let ((many (Bool) same)) $ match many sg _
      ((SgTy t) (match many sg2 _ ((SgTy t2) (notail $ term-eq t t2)) ((SgIs _ _) (BFalse))))
      ((SgIs t _) (match many sg2 _ ((SgTy _) (BFalse)) ((SgIs t2 _) (notail $ term-eq t t2)))))
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

; ---- Forced unification (section 7): records the facts a branch forces, or reports the contradiction
; that refutes it (lib/env.ml's unify). The measure is the table's count of rule-free entries: a step is
; structural on canonical terms while no binding happens, and after a binding, which rules an entry out,
; the rest is re-canonicalized at the smaller count.

(def-adts
  ((Clash : -> Type)
    enum
    (many CText : (many (String) s) -> (Clash))
    (many CTerm : (many (Term) t) -> (Clash))
    (many CName : (many (Nat) x) -> (Clash))
    (many CIllTyped : (many (Nat) x) (many (Term) t) -> (Clash))
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

(def-fns _ $ (many lift : (erased (Nat) n) (many (Nat) bnd) (erased (Nat) k) (erased (Facts k) f2) (many (Table k f2 bnd) tb) (many (Env) env) (erased (Subterm (Nat) k (Nat) n) p) (many (Outcome k bnd) o) -> (many (Outcome n bnd) r))
  (match many o _
    ((Same _ _ env3) (Less _ _ _ _ tb env3 p))
    ((Less _ _ _ _ tb2 env2 q) (Less _ _ _ _ tb2 env2 $ subterm-trans q p))
    ((Contra _ _ m) (Contra _ _ m))))

(def-fns _ $ (many typed-solution : (erased (Nat) n) (many (Nat) bnd) (erased (Nat) k) (erased (Facts k) f2) (many (Table k f2 bnd) tb) (many (Env) env) (erased (Subterm (Nat) k (Nat) n) p) (many (Nat) x) (many (Term) t) (many (Outcome k bnd) o) -> (many (Outcome n bnd) r))
  (match many o _
    ((Contra _ _ m) (Contra _ _ $ match many m (((Clash) _)) ((CIllTyped _ _) m) (else (CIllTyped x t))))
    (else (lift _ bnd _ _ tb env p o))))

(def-fns _ $ (many mctors-list : (subterm many (List $ MCtor) cs) (many (Nat) x) -> (many (Bool) r))
  (let-match many cs (Cons _ c rest) ((Nil _) (BFalse)))
  (let-match many c (MkMCtor _ t))
  (match many t _
    ((TVar y) (or (nat-eq x y) $ notail $ mctors-list rest x)) (else (tail $ mctors-list rest x))))

; Constructors one opened Matchable lists are distinct (section 8), first-class ones included: the objects
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

; Whether an `AtFn` proof about [f] is open (section 39), keyed by f's canonical atom as section 8's
; opens are.
(def-fns _ $ (many atfn-open-in : (subterm many (List $ Opened) os) (many (Nat) f) -> (many (Bool) r))
  (let-match many os (Cons _ o rest) ((Nil _) (BFalse)))
  (let-match many o (MkOpened _ k names))
  (match many (and (nat-eq (open-kind-code k) 1) $ list-mem-bin names f) _
    ((BTrue) (BTrue))
    ((BFalse) (tail $ atfn-open-in rest f))))

(def-fns _ $ (many atfn-open : (many (Env) env) (many (Term) t) -> (many (Bool) r))
  (let-match many (canon-env env t) (TVar f) (else (BFalse)))
  (let-match many (index-of f $ env-index env) (Cons _ _ _) ((Nil _) (BFalse)))
  (atfn-open-in (env-opens env) f))

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
      ((TSlotOf c) (tail $ dangling c d)) (else (BFalse))))
  ((many dangling-list : (subterm many (List $ Term) ts) (many (Nat) d) -> (many (Bool) r))
    (match many ts _
      ((Nil _) (BFalse))
      ((Cons _ t rest) (or (notail $ dangling t d) $ notail $ dangling-list rest d))))
  ((many dangling-mctors : (subterm many (List $ MCtor) cs) (many (Nat) d) -> (many (Bool) r))
    (let-match many cs (Cons _ c rest)
      ((Nil _) (BFalse)))
    (match many c _ ((MkMCtor _ t) (or (notail $ dangling t d) $ notail $ dangling-mctors rest d))))
  ((many dangling-tele : (subterm many (List $ Entry) es) (many (Nat) d) -> (many (Bool) r))
    (let-match many es (Cons _ e rest) ((Nil _) (BFalse)))
    (let-match many e (MkEntry _ _ _ sg place _))
    (or (match many sg (((Bool) _)) ((SgTy t) (notail $ dangling t d)) ((SgIs t _) (notail $ dangling t d)))
      $ or (match many place (((Bool) _)) ((None _) (BFalse)) ((Some _ p) (notail $ dangling p d))) $ notail $ dangling-tele rest $ Succ d)))

(def-fns _ $ (many term-type : (many (Env) env) (many (Term) t) -> (many (Maybe $ Term) r))
  (let-match many t (TApp h args)
    ((TVar x) (Some _ $ type-of env x))
    ((TSlotOf _) (Some _ slot-term))
    ((TBound _) (None _))
    ((TErr _) (None _))
    (else (Some _ type-term)))
  (let-match many h (TVar x) (else (None _)))
  (match many (canon-env env $ type-of env x) _
    ((TTyCtor _) (Some _ type-term))
    ((TValCtor _ ret) (Some _ $ instantiate (list-rev _ args) ret))
    (else (None _))))

(def-adts $ (SolTypes : ((Nat) n) ((Facts n) f) -> Type)
  enum
  (many MkSolTypes : (erased (Nat) n) (erased (Facts n) f) (many (Term) a) (erased (Fr n f a) pa) (many (Term) b) (erased (Fr n f b) pb) -> (SolTypes n f))
  (many NoSolTypes : (erased (Nat) n) (erased (Facts n) f) -> (SolTypes n f)))

(def-fns _ $ (many solution-types : (erased (Nat) n) (erased (Facts n) f) (many (Nat) bnd) (many (Table n f bnd) tb) (many (Env) env) (many (Nat) x) (many (Term) t) (many (Bool) force) -> (many (SolTypes n f) r))
  (let-match many force (BFalse) ((BTrue) (NoSolTypes _ _)))
  (let-match many (term-type env t) (Some _ tt) ((None _) (NoSolTypes _ _)))
  (let ((many a) (erased pa)) $ canon-in _ _ bnd tb $ type-of env x)
  (let ((many b) (erased pb)) $ canon-in _ _ bnd tb tt)
  (MkSolTypes _ _ a pa b pb))

(def-fns _ $ (many contradiction : (erased (Nat) n) (many (Nat) bnd) (many (Term) a) (many (Term) b) -> (many (Outcome n bnd) r))
  (Contra _ _ $ CCat (CTerm a) $ CCat (CText " vs ") $ CTerm b))

; A variable against a term: a dangling binder refutes, and so does the variable occurring in the term,
; which is the term not being fresh once the variable is ruled out (section 7).
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
        (let-match many b (TVar y)
          ((TBound _) (contradiction _ bnd a b))
          ((TErr m) (Contra _ _ $ CText m))
          (else
            (let ((many o)) $ bind-var n f bnd tb env x (fr-var n f x pa) b a b force)
            (let-match many o (Less _ _ k f2 tb2 env2 p) (else o))
            (let-match many (solution-types _ _ bnd tb2 env2 x b force) (MkSolTypes _ _ s1 ps1 s2 ps2) ((NoSolTypes _ _) o))
            (typed-solution _ bnd _ _ tb2 env2 p x b $ notail $ unify (subterm p) k f2 bnd tb2 s1 ps1 s2 ps2 env2 force)))
        (let ((erased px)) $ fr-var _ _ _ pa)
        (let ((erased py)) $ fr-var _ _ _ pb)
        (let-match many (nat-eq-dec x y) (BNo _ _ ne) ((BYes _ _ _) (Same _ _ env)))
        (let ((erased hx) (many ex)) $ entry env x)
        (let ((erased hy) (many ey)) $ entry env y)
        (let-match many ex (MkEInfo _ _ _ _ _ iox mx _))
        (let-match many ey (MkEInfo _ _ _ _ _ ioy my _))
        (let ((many (Nat) newer) (many (Nat) older) (erased (In newer n f) pn) (erased (In older n f) po) (erased (Neq older newer) neq))
          (match many (older-of iox ioy x y) _
            ((BTrue) (values y x py px ne))
            ((BFalse) (values x y px py $ neq-sym _ _ ne))))
        (match many (or mx my) _
          ((BTrue)
            (let ((many (Nat) m) (many (Nat) o) (erased (In m n f) pm) (erased (In o n f) po2) (erased (Neq o m) neq2))
              (match many (and mx $ or (not my) $ nat-eq x newer) _
                ((BTrue) (values x y px py $ neq-sym _ _ ne))
                ((BFalse) (values y x py px ne))))
            (let-match many (rule-out-var _ _ bnd tb m o pm po2 neq2) (MkAdded k _ f2 _ tb2))
            (let ((many env2)) $ env-set-table env _ _ bnd tb2)
            (let ((erased p)) $ prove-subterm k n)
            (let-match many (solution-types _ _ bnd tb2 env2 m (TVar o) force) (MkSolTypes _ _ s1 ps1 s2 ps2) ((NoSolTypes _ _) (Less _ _ _ _ tb2 env2 p)))
            (typed-solution _ bnd _ _ tb2 env2 p m (TVar o) $ notail $ unify _ _ bnd tb2 s1 ps1 s2 ps2 env2 force))
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
      ((TErr m) (Contra _ _ $ CText m))
      (else
        (match many b _
          ((TVar y)
            (let ((many o)) $ bind-var _ _ bnd tb env y (fr-var n f y pb) a a b force)
            (let-match many o (Less _ _ k f2 tb2 env2 p) (else o))
            (let-match many (solution-types _ _ bnd tb2 env2 y a force) (MkSolTypes _ _ s1 ps1 s2 ps2) ((NoSolTypes _ _) o))
            (typed-solution _ bnd _ _ tb2 env2 p y a $ notail $ unify (subterm p) k f2 bnd tb2 s1 ps1 s2 ps2 env2 force))
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
                (let-match many (bool-eq uq uq2) (BTrue) ((BFalse) (contradiction _ bnd a b)))
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
                        (lift _ bnd _ _ tb3 env3 (subterm-trans q p) $ notail $ unify-tele (subterm (subterm-trans q p)) j f3 bnd tb3 rs3 prs3 rs4 prs4 env3 a b force))))))
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
              ((TSlotOf cn)
                (let-match many b (TSlotOf cn2) (else (contradiction _ bnd a b)))
                (let ((many c3) (erased _)) $ chase-in _ _ bnd tb cn)
                (let ((many c4) (erased _)) $ chase-in _ _ bnd tb cn2)
                (match many (term-eq c3 c4) _ ((BTrue) (Same _ _ env)) ((BFalse) (contradiction _ bnd a b))))
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
    (let ((erased psg) (erased ppl) (erased prest)) (frt-cons _ _ _ _ _ _ _ _ _ pas))
    (let ((erased psg2) (erased ppl2) (erased prest2)) (frt-cons _ _ _ _ _ _ _ _ _ pbs))
    (let-match many (notail $ unify-place _ _ bnd tb place ppl place2 ppl2 env wa wb force) (Less _ _ k0 f0 tb0 env0 p0)
      ((Contra _ _ msg) (Contra _ _ msg))
      ((Same _ _ env5)
        (let-match many (notail $ unify-sg _ _ bnd tb sg psg sg2 psg2 env5 wa wb force) (Less _ _ k f2 tb2 env2 p)
          ((Contra _ _ msg) (Contra _ _ msg))
          ((Same _ _ env4) (tail $ unify-tele _ _ bnd tb rest prest rest2 prest2 env4 wa wb force)))
        (let ((many rest3) (erased prest3)) $ canon-tele-in _ _ bnd tb2 rest)
        (let ((many rest4) (erased prest4)) $ canon-tele-in _ _ bnd tb2 rest2)
        (lift _ bnd _ _ tb2 env2 p $ notail $ unify-tele (subterm p) k f2 bnd tb2 rest3 prest3 rest4 prest4 env2 wa wb force)))
    (let ((many sg3) (erased psg3)) $ canon-sg-in _ _ bnd tb0 sg)
    (let ((many sg4) (erased psg4)) $ canon-sg-in _ _ bnd tb0 sg2)
    (let-match many (notail $ unify-sg (subterm p0) k0 f0 bnd tb0 sg3 psg3 sg4 psg4 env0 wa wb force) (Less _ _ k f2 tb2 env2 p)
      ((Contra _ _ msg) (Contra _ _ msg))
      ((Same _ _ env4)
        (let ((many rest3) (erased prest3)) $ canon-tele-in _ _ bnd tb0 rest)
        (let ((many rest4) (erased prest4)) $ canon-tele-in _ _ bnd tb0 rest2)
        (lift _ bnd _ _ tb0 env4 p0 $ notail $ unify-tele (subterm p0) k0 f0 bnd tb0 rest3 prest3 rest4 prest4 env4 wa wb force)))
    (let ((many rest3) (erased prest3)) $ canon-tele-in _ _ bnd tb2 rest)
    (let ((many rest4) (erased prest4)) $ canon-tele-in _ _ bnd tb2 rest2)
    (lift _ bnd _ _ tb2 env2 (subterm-trans p p0) $ notail $ unify-tele (subterm (subterm-trans p p0)) k f2 bnd tb2 rest3 prest3 rest4 prest4 env2 wa wb force))

  ; An entry's place against another's: both absent, or two slot terms unified as any terms are.
  ((many unify-place : (subterm erased (Nat) n) (erased (Facts n) f) (many (Nat) bnd) (many (Table n f bnd) tb) (subterm many (Maybe $ Term) place) (erased (FrP n f place) pp) (many (Maybe $ Term) place2) (erased (FrP n f place2) pp2) (many (Env) env) (many (Term) wa) (many (Term) wb) (many (Bool) force) -> (many (Outcome n bnd) r))
    (match many place _
      ((None _) (match many place2 _ ((None _) (Same _ _ env)) ((Some _ _) (contradiction _ bnd wa wb))))
      ((Some _ q)
        (let-match many place2 (Some _ q2) ((None _) (contradiction _ bnd wa wb)))
        (tail $ unify _ _ bnd tb q (frp-some n f q pp) q2 (frp-some n f q2 pp2) env force))))

  ((many unify-sg : (subterm erased (Nat) n) (erased (Facts n) f) (many (Nat) bnd) (many (Table n f bnd) tb) (subterm many (Sg) sg) (erased (FrS n f sg) psg) (many (Sg) sg2) (erased (FrS n f sg2) psg2) (many (Env) env) (many (Term) wa) (many (Term) wb) (many (Bool) force) -> (many (Outcome n bnd) r))
    (match many sg _
      ((SgTy t)
        (let-match many sg2 (SgTy t2) ((SgIs _ _) (contradiction _ bnd wa wb)))
        (tail $ unify _ _ bnd tb t (frs-ty n f t psg) t2 (frs-ty n f t2 psg2) env force))
      ((SgIs t ty)
        (let-match many sg2 (SgIs t2 ty2) ((SgTy _) (contradiction _ bnd wa wb)))
        (tail $ unify _ _ bnd tb t (frs-is n f t ty psg) t2 (frs-is n f t2 ty2 psg2) env force))))

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

; A forcing (section 7) leaves the opened objects it touched to be merged (section 8), so its environment
; is handed back as Forced, which only the restorers, merge-all and merge-opens, read an environment out of;
; a contradiction is carried along, and the next forcing is on the Forced.
(def-adts $ (Forced : -> Type)
  enum
  (many Forcing : (many (Env) e) -> (Forced))
  (many Refuted : (many (Clash) m) -> (Forced)))

(def-fns _ $ (many unify-force : (many (Forced) fe) (many (Term) a) (many (Term) b) -> (many (Forced) r))
  (let-match many fe (Forcing env)
    ((Refuted _) fe))
  (match many (unify-in env a b $ BTrue) _ ((UOk env2) (Forcing env2)) ((UContra m) (Refuted m))))

(let ((many nat-adt)) (MkAdt "Nat" (BTrue) (Nil _) (Some _ (ExtNat)) (BFalse)))
(let ((many str-adt)) (MkAdt "String" (BTrue) (Nil _) (Some _ (ExtString)) (BFalse)))

(def-fns _ $ (many shadow-covered : (many (Env) env) (many (Nat) prior) (many (Nat) x) -> (many (Bool) r))
  (let ((many ids)) $ scope-ids $ env-scope env)
  (let-match many (and (list-mem-bin ids x) $ list-mem-bin ids prior) (BTrue) ((BFalse) (BFalse)))
  (let-match many (term-eq (canon-env env $ TVar x) $ canon-env env $ TVar prior) (BTrue) ((BFalse) (BFalse)))
  (let-match many (entry-mult-of env x) (Many) ((Erased) (BTrue)) (else (BFalse)))
  (match many (entry-mult-of env prior) _ ((Many) (equal-env env (slot-atom x) $ slot-atom prior)) (else (BFalse))))

(def-fns _ $ (many shadow-said : (many (Env) env) (many (Bool) hinted) (subterm many (List $ Said) ss) -> (many (List $ Said) r))
  (let-match many ss (Cons _ s rest) ((Nil _) (Nil _)))
  (let-match many s (SaidShadow x prior pl n l) (else (Cons _ s $ notail $ shadow-said env hinted rest)))
  (let ((many covered)) $ match many (and hinted $ shadow-covered env prior x) (((List $ Pair (Loc) $ String) _))
    ((BTrue) (Cons _ (MkPair _ _ l "using `_` here instead would be equivalent") $ Nil _))
    ((BFalse) (Nil _)))
  (let ((many text)) $ diagnostic (env-at-loc env l) ": warning: " (Cons _ (MkPair _ _ pl "shadowed binder is here") covered) $ str-cat3 "declaration of " (tick-name n) " shadows a previous binder")
  (Cons _ (SaidWarning l text) $ notail $ shadow-said env hinted rest))

(def-fns _ $ (many report-shadows : (many (Env) env) (many (Bool) hinted) -> (many (Env) r))
  (env-set-said env $ shadow-said env hinted $ env-said env))
