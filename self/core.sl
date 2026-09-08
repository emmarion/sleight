; self/core.sl -- the compiler's data: the restricted type grammar (DESIGN.md section 5) as terms with de
; Bruijn telescopes, the special-form registry (section 27), runtime values and post-erasure code, the
; scope environment with its fact table (sections 3, 18), canonicalization, instantiation and the part of
; forced unification a trusting compiler needs. Mirrors lib/term.ml, lib/value.ml and lib/env.ml.

(def-adts $ Mult : -> Type
  enum
  (many Erased : -> (Mult))
  (many Many : -> (Mult)))

(def-adts $ Disc : -> Type
  enum
  (many DEnum : -> (Disc))
  (many DUnion : -> (Disc)))

(def-adts
  (Term : -> Type
    enum
    (many TVar : (many (Bin) id) -> (Term))
    (many TBound : (many (Nat) k) -> (Term))
    (many TApp : (many (Term) head) (many (List (Term)) args) -> (Term))
    (many TFn : (many (Term) level) (many (List (Entry)) params) (many (List (Entry)) rets) -> (Term))
    (many TTyCtor : (many (List (Entry)) params) -> (Term))
    (many TValCtor : (many (List (Entry)) params) (many (Term) ret) -> (Term))
    (many TMatchable : (many (Disc) disc) (many (Term) ty) (many (List (MCtor)) ctors) -> (Term))
    (many TNewtype : (many (Term) c) -> (Term))
    (many TErr : (many (String) msg) -> (Term)))
  (Entry : -> Type
    enum
    (many MkEntry : (many (Maybe (String)) name) (many (Bool) sub) (many (Mult) mult) (many (Sg) sg) -> (Entry)))
  (Sg : -> Type
    enum
    (many SgTy : (many (Term) t) -> (Sg))
    (many SgIs : (many (Term) t) -> (Sg)))
  (MCtor : -> Type
    enum
    (many MkMCtor : (many (Mult) m) (many (Term) c) -> (MCtor))))

(def-fns _ $ many sg-term : (many (Sg) sg) -> (many (Term) t)
  (match many sg _ ((SgTy t) t) ((SgIs t) t)))

(def-fns _ $ many entry-mult : (many (Entry) e) -> (many (Mult) m)
  (match many e _ ((MkEntry n s m sg) m)))

(def-fns _ $ many entry-sg : (many (Entry) e) -> (many (Sg) sg)
  (match many e _ ((MkEntry n s m sg) sg)))

(def-fns _ $ many entry-name : (many (Entry) e) -> (many (Maybe (String)) n)
  (match many e _ ((MkEntry n s m sg) n)))

(def-fns _ $ many entry-sub : (many (Entry) e) -> (many (Bool) s)
  (match many e _ ((MkEntry n s m sg) s)))

(def-fns _ $ many mult-is-many : (many (Mult) m) -> (many (Bool) r)
  (match many m _ ((Erased) (BFalse)) ((Many) (BTrue))))

(def-fns _ $ many under : (many (Mult) pos) (many (Mult) m) -> (many (Mult) r)
  (match many pos _ ((Erased) (Erased)) ((Many) m)))

; The position of a list of expected multiplicities: erased when every entry is.
(def-fns _ $ many pos-of : (subterm many (List (Mult)) ms) -> (many (Mult) r)
  (match many ms _
    ((Nil a) (Erased))
    ((Cons a m rest) (match many m _ ((Many) (Many)) ((Erased) (pos-of rest))))))

(def-fns _ $ many many-count : (subterm many (List (Entry)) es) -> (many (Nat) n)
  (match many es _
    ((Nil a) (Zero))
    ((Cons a e rest)
      (match many (entry-mult e) _
        ((Many) (Succ (many-count rest)))
        ((Erased) (many-count rest))))))

(def-fns _ $ many tele-mults : (subterm many (List (Entry)) es) -> (many (List (Mult)) ms)
  (match many es _
    ((Nil a) (Nil (Mult)))
    ((Cons a e rest) (Cons (Mult) (entry-mult e) (tele-mults rest)))))

; ---- The special-form registry (section 27), grouped by where each is dispatched.

(def-adts
  (Sp : -> Type
    enum
    (many SpStmt : (many (StmtK) k) -> (Sp))
    (many SpFormer : (many (FormerK) k) -> (Sp))
    (many SpExpr : (many (ExprK) k) -> (Sp))
    (many SpMark : (many (MarkK) k) -> (Sp)))
  (StmtK : -> Type
    enum
    (many StLet : -> (StmtK)) (many StDefLvl : -> (StmtK)) (many StDefFns : -> (StmtK))
    (many StDefAdts : -> (StmtK)) (many StComptimeMatch : -> (StmtK)) (many StLetMatch : -> (StmtK)) (many StUnary : -> (StmtK))
    (many StOpenAdt : -> (StmtK)))
  (FormerK : -> Type
    enum
    (many FoFn : -> (FormerK)) (many FoTyCtor : -> (FormerK)) (many FoValCtor : -> (FormerK))
    (many FoMatchable : -> (FormerK)) (many FoNewtype : -> (FormerK)))
  (ExprK : -> Type
    enum
    (many ExMatch : -> (ExprK)) (many ExMatchableOf : -> (ExprK)) (many ExNewtypeOf : -> (ExprK))
    (many ExNumeralOf : -> (ExprK)) (many ExLevelOf : -> (ExprK)) (many ExProveSubterm : -> (ExprK))
    (many ExProvePredates : -> (ExprK)) (many ExValues : -> (ExprK)) (many ExPredatesTrans : -> (ExprK))
    (many ExSubtermTrans : -> (ExprK)) (many ExPredatesSubterm : -> (ExprK)) (many ExCoerce : -> (ExprK))
    (many ExCoercibleRefl : -> (ExprK)) (many ExCoercibleSym : -> (ExprK)) (many ExCoercibleTrans : -> (ExprK))
    (many ExCoercibleWrap : -> (ExprK)) (many ExCoercibleCtor : -> (ExprK)) (many ExCoercibleOf : -> (ExprK))
    (many ExDistinct : -> (ExprK)) (many ExOpenAbsurd : -> (ExprK)))
  (MarkK : -> Type
    enum
    (many MkErased : -> (MarkK)) (many MkMany : -> (MarkK)) (many MkColon : -> (MarkK)) (many MkIs : -> (MarkK))
    (many MkArrow : -> (MarkK)) (many MkSubterm : -> (MarkK)) (many MkEnum : -> (MarkK)) (many MkUnion : -> (MarkK))
    (many MkTail : -> (MarkK)) (many MkDelegate : -> (MarkK)) (many MkPredates : -> (MarkK)) (many MkAbsurd : -> (MarkK))
    (many MkNewtypeMark : -> (MarkK)) (many MkExtern : -> (MarkK)) (many MkElse : -> (MarkK))))

(def-fns _ $ many stmt-code : (many (StmtK) k) -> (many (Nat) n)
  (match many k _ ((StLet) 0) ((StDefLvl) 1) ((StDefFns) 2) ((StDefAdts) 3) ((StComptimeMatch) 4) ((StLetMatch) 5) ((StUnary) 6) ((StOpenAdt) 7)))

(def-fns _ $ many former-code : (many (FormerK) k) -> (many (Nat) n)
  (match many k _ ((FoFn) 0) ((FoTyCtor) 1) ((FoValCtor) 2) ((FoMatchable) 3) ((FoNewtype) 4)))

(def-fns _ $ many expr-code : (many (ExprK) k) -> (many (Nat) n)
  (match many k _
    ((ExMatch) 0) ((ExMatchableOf) 1) ((ExNewtypeOf) 2) ((ExNumeralOf) 3) ((ExLevelOf) 4) ((ExProveSubterm) 5)
    ((ExProvePredates) 6) ((ExValues) 7) ((ExPredatesTrans) 8) ((ExSubtermTrans) 9) ((ExPredatesSubterm) 10)
    ((ExCoerce) 11) ((ExCoercibleRefl) 12) ((ExCoercibleSym) 13) ((ExCoercibleTrans) 14) ((ExCoercibleWrap) 15)
    ((ExCoercibleCtor) 16) ((ExCoercibleOf) 17) ((ExDistinct) 18) ((ExOpenAbsurd) 19)))

(def-fns _ $ many mark-code : (many (MarkK) k) -> (many (Nat) n)
  (match many k _
    ((MkErased) 0) ((MkMany) 1) ((MkColon) 2) ((MkIs) 3) ((MkArrow) 4) ((MkSubterm) 5) ((MkEnum) 6) ((MkUnion) 7)
    ((MkTail) 8) ((MkDelegate) 9) ((MkPredates) 10) ((MkAbsurd) 11) ((MkNewtypeMark) 12) ((MkExtern) 13) ((MkElse) 14)))

(def-fns _ $ many sp-code : (many (Sp) sp) -> (many (Nat) n)
  (match many sp _
    ((SpStmt k) (stmt-code k))
    ((SpFormer k) (nat-add 10 (former-code k)))
    ((SpExpr k) (nat-add 20 (expr-code k)))
    ((SpMark k) (nat-add 40 (mark-code k)))))

(def-fns _ $ many sp-eq : (many (Sp) a) (many (Sp) b) -> (many (Bool) r)
  (nat-eq (sp-code a) (sp-code b)))

(def-adts $ SpEntry : -> Type
  enum
  (many MkSpEntry : (many (String) name) (many (Sp) sp) -> (SpEntry)))

(def-fns _ $ many sp-cons : (many (String) name) (many (Sp) sp) (many (List (SpEntry)) rest) -> (many (List (SpEntry)) r)
  (Cons (SpEntry) (MkSpEntry name sp) rest))

; Every special form by name, in the order of lib/special.ml; a form's constructor index in the Special
; ADT is its position here.
(let (many sp-table)
  (sp-cons "let" (SpStmt (StLet)) $ sp-cons "def-lvl" (SpStmt (StDefLvl)) $ sp-cons "def-fns" (SpStmt (StDefFns)) $
  sp-cons "def-adts" (SpStmt (StDefAdts)) $ sp-cons "comptime-match" (SpStmt (StComptimeMatch)) $
  sp-cons "let-match" (SpStmt (StLetMatch)) $ sp-cons "unary" (SpStmt (StUnary)) $ sp-cons "distinct" (SpExpr (ExDistinct)) $
  sp-cons "open-adt" (SpStmt (StOpenAdt)) $ sp-cons "open-absurd" (SpExpr (ExOpenAbsurd)) $
  sp-cons "Fn" (SpFormer (FoFn)) $ sp-cons "TyCtor" (SpFormer (FoTyCtor)) $ sp-cons "ValCtor" (SpFormer (FoValCtor)) $
  sp-cons "Matchable" (SpFormer (FoMatchable)) $ sp-cons "Newtype" (SpFormer (FoNewtype)) $
  sp-cons "match" (SpExpr (ExMatch)) $ sp-cons "matchable-of" (SpExpr (ExMatchableOf)) $ sp-cons "newtype-of" (SpExpr (ExNewtypeOf)) $
  sp-cons "numeral-of" (SpExpr (ExNumeralOf)) $ sp-cons "level-of" (SpExpr (ExLevelOf)) $ sp-cons "prove-subterm" (SpExpr (ExProveSubterm)) $
  sp-cons "prove-predates" (SpExpr (ExProvePredates)) $ sp-cons "values" (SpExpr (ExValues)) $
  sp-cons "predates-trans" (SpExpr (ExPredatesTrans)) $ sp-cons "subterm-trans" (SpExpr (ExSubtermTrans)) $
  sp-cons "predates-subterm" (SpExpr (ExPredatesSubterm)) $
  sp-cons "coerce" (SpExpr (ExCoerce)) $ sp-cons "coercible-refl" (SpExpr (ExCoercibleRefl)) $ sp-cons "coercible-sym" (SpExpr (ExCoercibleSym)) $
  sp-cons "coercible-trans" (SpExpr (ExCoercibleTrans)) $ sp-cons "coercible-wrap" (SpExpr (ExCoercibleWrap)) $
  sp-cons "coercible-ctor" (SpExpr (ExCoercibleCtor)) $ sp-cons "coercible-of" (SpExpr (ExCoercibleOf)) $
  sp-cons "erased" (SpMark (MkErased)) $ sp-cons "many" (SpMark (MkMany)) $ sp-cons ":" (SpMark (MkColon)) $
  sp-cons "is" (SpMark (MkIs)) $ sp-cons "->" (SpMark (MkArrow)) $ sp-cons "subterm" (SpMark (MkSubterm)) $
  sp-cons "enum" (SpMark (MkEnum)) $ sp-cons "union" (SpMark (MkUnion)) $ sp-cons "tail" (SpMark (MkTail)) $
  sp-cons "delegate" (SpMark (MkDelegate)) $ sp-cons "predates" (SpMark (MkPredates)) $ sp-cons "absurd" (SpMark (MkAbsurd)) $
  sp-cons "newtype" (SpMark (MkNewtypeMark)) $ sp-cons "extern" (SpMark (MkExtern)) $ sp-cons "else" (SpMark (MkElse)) (Nil (SpEntry))))

(def-fns _ $ many sp-of-index : (many (Nat) i) -> (many (Maybe (Sp)) r)
  (match many (list-nth (SpEntry) sp-table i) _
    ((None a) (None (Sp)))
    ((Some a e) (match many e _ ((MkSpEntry n sp) (Some (Sp) sp))))))

; ---- Runtime values and post-erasure code (lib/value.ml)

(def-adts
  (Value : -> Type
    enum
    (many VCtor : (many (Ctor) c) (many (List (Value)) fields) -> (Value))
    (many VTuple : (many (List (Value)) fields) -> (Value))
    (many VExt : (many (Adt) adt) (many (Payload) p) -> (Value))
    (many VCtorFn : (many (Ctor) c) -> (Value))
    (many VMatchable : (many (Adt) adt) -> (Value))
    (many VFn : (many (Closure) cl) -> (Value))
    (many VToken : -> (Value))
    (many VError : (many (String) msg) -> (Value)))
  (Payload : -> Type
    enum
    (many PNat : (many (Nat) n) -> (Payload))
    (many PBin : (many (Bin) b) -> (Payload))
    (many PStr : (many (String) s) -> (Payload))
    (many PDec : (many (Nat) i) -> (Payload)))
  ; [tagged]: an enum with more than one non-phantom constructor (section 38); [ctors]: the non-phantom
  ; ones at their discriminants; [ext]: the extern type's name where the FFI holds it (section 41).
  (Adt : -> Type
    enum
    (many MkAdt : (many (String) name) (many (Bool) tagged) (many (List (Ctor)) ctors) (many (Maybe (String)) ext) -> (Adt)))
  (Ctor : -> Type
    enum
    (many MkCtor : (many (String) name) (many (Bin) id) (many (Nat) index) (many (Nat) arity) (many (Bool) tagged) (many (Maybe (String)) ext) -> (Ctor)))
  ; A closure re-closes its group over [env] when applied, which is how the group recurses.
  (Closure : -> Type
    enum
    (many MkClosure : (many (Func) fn) (many (List (Pair (Bin) (Func))) group) (many (IdMap (Value)) env) -> (Closure)))
  ; [top]: defined by a run-position def-fns, so the extracted program names it at top level.
  (Func : -> Type
    enum
    (many MkFunc : (many (String) name) (many (Bin) id) (many (List (Bin)) params) (many (Code) body) (many (Maybe (String)) impl) (many (Bool) top) -> (Func)))
  (Code : -> Type
    enum
    (many CVar : (many (Bin) id) -> (Code))
    (many CConst : (many (Value) v) -> (Code))
    (many CErased : -> (Code))
    (many CValues : (many (List (Code)) cs) -> (Code))
    (many CApp : (many (Code) f) (many (List (Code)) args) (many (CC) cc) -> (Code))
    (many CLet : (many (List (Bin)) ids) (many (Code) rhs) (many (Code) rest) -> (Code))
    (many CLetRec : (many (List (Pair (Bin) (Func))) fns) (many (Code) rest) -> (Code))
    (many CMatch : (many (Code) scrut) (many (Shape) shape) (many (List (Branch)) branches) (many (Maybe (Code)) dflt) -> (Code))
    (many CAbsurd : -> (Code))
    (many CError : (many (String) msg) -> (Code)))
  (CC : -> Type
    enum
    (many CCPlain : -> (CC)) (many CCTail : -> (CC)) (many CCDelegate : -> (CC)) (many CCCtor : -> (CC)))
  (Shape : -> Type
    enum
    (many ShKnown : (many (Adt) adt) -> (Shape))
    (many ShHeld : (many (Code) c) (many (Bool) tagged) -> (Shape)))
  (Branch : -> Type
    enum
    (many MkBranch : (many (Nat) disc) (many (List (Bin)) ids) (many (Code) body) -> (Branch))))

(def-fns _ $ many ctor-index : (many (Ctor) c) -> (many (Nat) i)
  (match many c _ ((MkCtor n id ix ar tg ext) ix)))

(def-fns _ $ many ctor-arity : (many (Ctor) c) -> (many (Nat) i)
  (match many c _ ((MkCtor n id ix ar tg ext) ar)))

(def-fns _ $ many ctor-name : (many (Ctor) c) -> (many (String) s)
  (match many c _ ((MkCtor n id ix ar tg ext) n)))

(def-fns _ $ many ctor-id : (many (Ctor) c) -> (many (Bin) s)
  (match many c _ ((MkCtor n id ix ar tg ext) id)))

(def-fns _ $ many adt-tagged : (many (Adt) a) -> (many (Bool) t)
  (match many a _ ((MkAdt n tg cs ext) tg)))

(def-fns _ $ many adt-ext : (many (Adt) a) -> (many (Maybe (String)) e)
  (match many a _ ((MkAdt n tg cs ext) ext)))

(def-fns _ $ many adt-ctors : (many (Adt) a) -> (many (List (Ctor)) cs)
  (match many a _ ((MkAdt n tg cs ext) cs)))

(def-fns _ $ many adt-name : (many (Adt) a) -> (many (String) s)
  (match many a _ ((MkAdt n tg cs ext) n)))

(def-fns _ $ many func-params : (many (Func) f) -> (many (List (Bin)) ps)
  (match many f _ ((MkFunc n id ps body impl top) ps)))

(def-fns _ $ many func-body : (many (Func) f) -> (many (Code) b)
  (match many f _ ((MkFunc n id ps body impl top) body)))

(def-fns _ $ many func-name : (many (Func) f) -> (many (String) b)
  (match many f _ ((MkFunc n id ps body impl top) n)))

(def-fns _ $ many func-id : (many (Func) f) -> (many (Bin) b)
  (match many f _ ((MkFunc n id ps body impl top) id)))

(def-fns _ $ many func-impl : (many (Func) f) -> (many (Maybe (String)) b)
  (match many f _ ((MkFunc n id ps body impl top) impl)))

(def-fns _ $ many func-top : (many (Func) f) -> (many (Bool) b)
  (match many f _ ((MkFunc n id ps body impl top) top)))

; An untagged value is its many fields: one of them bare, none the token (section 38).
(def-fns _ $ many tuple : (many (List (Value)) vs) -> (many (Value) v)
  (match many vs _
    ((Nil a) (VToken))
    ((Cons a v rest)
      (match many rest _
        ((Nil b) v)
        ((Cons b w rest2) (VTuple vs))))))

(def-fns _ $ many untuple : (many (Nat) n) (many (Value) v) -> (many (List (Value)) vs)
  (match many n _
    ((Zero) (Nil (Value)))
    ((Succ k)
      (match many k _
        ((Zero) (Cons (Value) v (Nil (Value))))
        ((Succ k2)
          (match many v _
            ((VTuple vs) vs) (else (Nil (Value)))))))))

; ---- Decidable equality on Bin, with inequality as an inductive so a refuted branch stays refutable.

(def-adts
  (Eq : ((Bin) a) ((Bin) b) -> Type
    enum
    (many Refl : (erased (Bin) x) -> (Eq x x)))
  (Neq : ((Bin) a) ((Bin) b) -> Type
    enum
    (many NeqZ1 : (erased (Bin) b) -> (Neq (BZ) (B1 b)))
    (many NeqZ2 : (erased (Bin) b) -> (Neq (BZ) (B2 b)))
    (many Neq1Z : (erased (Bin) a) -> (Neq (B1 a) (BZ)))
    (many Neq2Z : (erased (Bin) a) -> (Neq (B2 a) (BZ)))
    (many Neq12 : (erased (Bin) a) (erased (Bin) b) -> (Neq (B1 a) (B2 b)))
    (many Neq21 : (erased (Bin) a) (erased (Bin) b) -> (Neq (B2 a) (B1 b)))
    (many Neq11 : (erased (Bin) a) (erased (Bin) b) (erased (Neq a b) p) -> (Neq (B1 a) (B1 b)))
    (many Neq22 : (erased (Bin) a) (erased (Bin) b) (erased (Neq a b) p) -> (Neq (B2 a) (B2 b))))
  (BinDec : ((Bin) a) ((Bin) b) -> Type
    enum
    (many BYes : (erased (Bin) a) (erased (Bin) b) (erased (Eq a b) p) -> (BinDec a b))
    (many BNo : (erased (Bin) a) (erased (Bin) b) (erased (Neq a b) p) -> (BinDec a b))))

; The order on ids, digit by digit (B1 a is 2a+1, B2 a is 2a+2), and its decision with proofs.
(def-adts
  (BinLt : ((Bin) a) ((Bin) b) -> Type
    enum
    (many LtZ1 : (erased (Bin) b) -> (BinLt (BZ) (B1 b)))
    (many LtZ2 : (erased (Bin) b) -> (BinLt (BZ) (B2 b)))
    (many Lt11 : (erased (Bin) a) (erased (Bin) b) (erased (BinLt a b) p) -> (BinLt (B1 a) (B1 b)))
    (many Lt12 : (erased (Bin) a) (erased (Bin) b) (erased (BinLe a b) p) -> (BinLt (B1 a) (B2 b)))
    (many Lt21 : (erased (Bin) a) (erased (Bin) b) (erased (BinLt a b) p) -> (BinLt (B2 a) (B1 b)))
    (many Lt22 : (erased (Bin) a) (erased (Bin) b) (erased (BinLt a b) p) -> (BinLt (B2 a) (B2 b))))
  (BinLe : ((Bin) a) ((Bin) b) -> Type
    enum
    (many LeZ : (erased (Bin) b) -> (BinLe (BZ) b))
    (many Le11 : (erased (Bin) a) (erased (Bin) b) (erased (BinLe a b) p) -> (BinLe (B1 a) (B1 b)))
    (many Le12 : (erased (Bin) a) (erased (Bin) b) (erased (BinLe a b) p) -> (BinLe (B1 a) (B2 b)))
    (many Le21 : (erased (Bin) a) (erased (Bin) b) (erased (BinLt a b) p) -> (BinLe (B2 a) (B1 b)))
    (many Le22 : (erased (Bin) a) (erased (Bin) b) (erased (BinLe a b) p) -> (BinLe (B2 a) (B2 b))))
  (Cmp : ((Bin) a) ((Bin) b) -> Type
    enum
    (many CLt : (erased (Bin) a) (erased (Bin) b) (erased (BinLt a b) p) -> (Cmp a b))
    (many CEq : (erased (Bin) a) (erased (Bin) b) (erased (Eq a b) p) -> (Cmp a b))
    (many CGt : (erased (Bin) a) (erased (Bin) b) (erased (BinLt b a) p) -> (Cmp a b))))

(def-fns _ $ erased le-refl : (subterm erased (Bin) a) -> (erased (BinLe a a) r)
  (match erased a _
    ((BZ) (LeZ (BZ)))
    ((B1 a1) (Le11 a1 a1 (le-refl a1)))
    ((B2 a1) (Le22 a1 a1 (le-refl a1)))))

(def-fns _ $ erased lt-le : (erased (Bin) a) (erased (Bin) b) (subterm erased (BinLt a b) p) -> (erased (BinLe a b) r)
  (match erased p _
    ((LtZ1 b1) (LeZ (B1 b1))) ((LtZ2 b1) (LeZ (B2 b1)))
    ((Lt11 a1 b1 q) (Le11 a1 b1 (lt-le a1 b1 q)))
    ((Lt12 a1 b1 q) (Le12 a1 b1 q))
    ((Lt21 a1 b1 q) (Le21 a1 b1 q))
    ((Lt22 a1 b1 q) (Le22 a1 b1 (lt-le a1 b1 q)))))

(def-fns _
  (erased le-le : (erased (Bin) a) (erased (Bin) b) (erased (Bin) c) (subterm erased (BinLe a b) p) (erased (BinLe b c) q) -> (erased (BinLe a c) r)
    (match erased p _
      ((LeZ b1) (LeZ c))
      ((Le11 a1 b1 p1) (match erased q _ ((Le11 b2 c1 q1) (Le11 a1 c1 (le-le a1 b1 c1 p1 q1))) ((Le12 b2 c1 q1) (Le12 a1 c1 (le-le a1 b1 c1 p1 q1)))))
      ((Le12 a1 b1 p1) (match erased q _ ((Le21 b2 c1 q1) (Le11 a1 c1 (lt-le a1 c1 (le-lt a1 b1 c1 p1 q1)))) ((Le22 b2 c1 q1) (Le12 a1 c1 (le-le a1 b1 c1 p1 q1)))))
      ((Le21 a1 b1 p1) (match erased q _ ((Le11 b2 c1 q1) (Le21 a1 c1 (lt-le-lt a1 b1 c1 p1 q1))) ((Le12 b2 c1 q1) (Le22 a1 c1 (lt-le a1 c1 (lt-le-lt a1 b1 c1 p1 q1))))))
      ((Le22 a1 b1 p1) (match erased q _ ((Le21 b2 c1 q1) (Le21 a1 c1 (le-lt a1 b1 c1 p1 q1))) ((Le22 b2 c1 q1) (Le22 a1 c1 (le-le a1 b1 c1 p1 q1)))))))
  (erased le-lt : (erased (Bin) a) (erased (Bin) b) (erased (Bin) c) (subterm erased (BinLe a b) p) (erased (BinLt b c) q) -> (erased (BinLt a c) r)
    (match erased p _
      ((LeZ b1) (match erased q _ ((LtZ1 c1) (LtZ1 c1)) ((LtZ2 c1) (LtZ2 c1)) ((Lt11 b2 c1 q1) (LtZ1 c1)) ((Lt12 b2 c1 q1) (LtZ2 c1)) ((Lt21 b2 c1 q1) (LtZ1 c1)) ((Lt22 b2 c1 q1) (LtZ2 c1))))
      ((Le11 a1 b1 p1) (match erased q _ ((Lt11 b2 c1 q1) (Lt11 a1 c1 (le-lt a1 b1 c1 p1 q1))) ((Lt12 b2 c1 q1) (Lt12 a1 c1 (le-le a1 b1 c1 p1 q1)))))
      ((Le12 a1 b1 p1) (match erased q _ ((Lt21 b2 c1 q1) (Lt11 a1 c1 (le-lt a1 b1 c1 p1 q1))) ((Lt22 b2 c1 q1) (Lt12 a1 c1 (lt-le a1 c1 (le-lt a1 b1 c1 p1 q1))))))
      ((Le21 a1 b1 p1) (match erased q _ ((Lt11 b2 c1 q1) (Lt21 a1 c1 (lt-lt a1 b1 c1 p1 q1))) ((Lt12 b2 c1 q1) (Lt22 a1 c1 (lt-le-lt a1 b1 c1 p1 q1)))))
      ((Le22 a1 b1 p1) (match erased q _ ((Lt21 b2 c1 q1) (Lt21 a1 c1 (le-lt a1 b1 c1 p1 q1))) ((Lt22 b2 c1 q1) (Lt22 a1 c1 (le-lt a1 b1 c1 p1 q1)))))))
  (erased lt-le-lt : (erased (Bin) a) (erased (Bin) b) (erased (Bin) c) (subterm erased (BinLt a b) p) (erased (BinLe b c) q) -> (erased (BinLt a c) r)
    (match erased p _
      ((LtZ1 b1) (match erased q _ ((Le11 b2 c1 q1) (LtZ1 c1)) ((Le12 b2 c1 q1) (LtZ2 c1))))
      ((LtZ2 b1) (match erased q _ ((Le21 b2 c1 q1) (LtZ1 c1)) ((Le22 b2 c1 q1) (LtZ2 c1))))
      ((Lt11 a1 b1 p1) (match erased q _ ((Le11 b2 c1 q1) (Lt11 a1 c1 (lt-le-lt a1 b1 c1 p1 q1))) ((Le12 b2 c1 q1) (Lt12 a1 c1 (lt-le a1 c1 (lt-le-lt a1 b1 c1 p1 q1))))))
      ((Lt12 a1 b1 p1) (match erased q _ ((Le21 b2 c1 q1) (Lt11 a1 c1 (le-lt a1 b1 c1 p1 q1))) ((Le22 b2 c1 q1) (Lt12 a1 c1 (le-le a1 b1 c1 p1 q1)))))
      ((Lt21 a1 b1 p1) (match erased q _ ((Le11 b2 c1 q1) (Lt21 a1 c1 (lt-le-lt a1 b1 c1 p1 q1))) ((Le12 b2 c1 q1) (Lt22 a1 c1 (lt-le-lt a1 b1 c1 p1 q1)))))
      ((Lt22 a1 b1 p1) (match erased q _ ((Le21 b2 c1 q1) (Lt21 a1 c1 (lt-lt a1 b1 c1 p1 q1))) ((Le22 b2 c1 q1) (Lt22 a1 c1 (lt-le-lt a1 b1 c1 p1 q1)))))))
  (erased lt-lt : (erased (Bin) a) (erased (Bin) b) (erased (Bin) c) (subterm erased (BinLt a b) p) (erased (BinLt b c) q) -> (erased (BinLt a c) r)
    (match erased p _
      ((LtZ1 b1) (match erased q _ ((Lt11 b2 c1 q1) (LtZ1 c1)) ((Lt12 b2 c1 q1) (LtZ2 c1))))
      ((LtZ2 b1) (match erased q _ ((Lt21 b2 c1 q1) (LtZ1 c1)) ((Lt22 b2 c1 q1) (LtZ2 c1))))
      ((Lt11 a1 b1 p1) (match erased q _ ((Lt11 b2 c1 q1) (Lt11 a1 c1 (lt-lt a1 b1 c1 p1 q1))) ((Lt12 b2 c1 q1) (Lt12 a1 c1 (lt-le a1 c1 (lt-le-lt a1 b1 c1 p1 q1))))))
      ((Lt12 a1 b1 p1) (match erased q _ ((Lt21 b2 c1 q1) (Lt11 a1 c1 (le-lt a1 b1 c1 p1 q1))) ((Lt22 b2 c1 q1) (Lt12 a1 c1 (lt-le a1 c1 (le-lt a1 b1 c1 p1 q1))))))
      ((Lt21 a1 b1 p1) (match erased q _ ((Lt11 b2 c1 q1) (Lt21 a1 c1 (lt-lt a1 b1 c1 p1 q1))) ((Lt12 b2 c1 q1) (Lt22 a1 c1 (lt-le-lt a1 b1 c1 p1 q1)))))
      ((Lt22 a1 b1 p1) (match erased q _ ((Lt21 b2 c1 q1) (Lt21 a1 c1 (lt-lt a1 b1 c1 p1 q1))) ((Lt22 b2 c1 q1) (Lt22 a1 c1 (lt-lt a1 b1 c1 p1 q1))))))))

(def-fns _ $ erased lt-irrefl : (erased (Bin) a) (subterm erased (BinLt a a) p) -> (erased (False) f)
  (match erased p _
    ((Lt11 a1 b1 q) (lt-irrefl a1 q))
    ((Lt22 a1 b1 q) (lt-irrefl a1 q))))

(def-fns _ $ erased le-lt-absurd : (erased (Bin) a) (erased (Bin) b) (erased (BinLe a b) p) (erased (BinLt b a) q) -> (erased (False) f)
  (lt-irrefl a (le-lt a b a p q)))

(def-fns _ $ many bin-succ-lt : (subterm many (Bin) b) -> (many (Bin) c) (erased (BinLt b c) p)
  (match many b _
    ((BZ) (values (B1 (BZ)) (LtZ1 (BZ))))
    ((B1 b1) (values (B2 b1) (Lt12 b1 b1 (le-refl b1))))
    ((B2 b1)
      (let (many c1) (erased q) (bin-succ-lt b1))
      (values (B1 c1) (Lt21 b1 c1 q)))))

(def-fns _ $ many bin-cmp-dec : (subterm many (Bin) a) (many (Bin) b) -> (many (Cmp a b) r)
  (match many a _
    ((BZ) (match many b _ ((BZ) (CEq a b (Refl a))) ((B1 b1) (CLt a b (LtZ1 b1))) ((B2 b1) (CLt a b (LtZ2 b1)))))
    ((B1 a1)
      (match many b _
        ((BZ) (CGt a b (LtZ1 a1)))
        ((B1 b1) (match many (bin-cmp-dec a1 b1) _ ((CLt x y p) (CLt a b (Lt11 a1 b1 p))) ((CEq x y e) (match erased e _ ((Refl z) (CEq a b (Refl a))))) ((CGt x y p) (CGt a b (Lt11 b1 a1 p)))))
        ((B2 b1) (match many (bin-cmp-dec a1 b1) _ ((CLt x y p) (CLt a b (Lt12 a1 b1 (lt-le a1 b1 p)))) ((CEq x y e) (match erased e _ ((Refl z) (CLt a b (Lt12 a1 a1 (le-refl a1)))))) ((CGt x y p) (CGt a b (Lt21 b1 a1 p)))))))
    ((B2 a1)
      (match many b _
        ((BZ) (CGt a b (LtZ2 a1)))
        ((B1 b1) (match many (bin-cmp-dec a1 b1) _ ((CLt x y p) (CLt a b (Lt21 a1 b1 p))) ((CEq x y e) (match erased e _ ((Refl z) (CGt a b (Lt12 a1 a1 (le-refl a1)))))) ((CGt x y p) (CGt a b (Lt12 b1 a1 (lt-le b1 a1 p))))))
        ((B2 b1) (match many (bin-cmp-dec a1 b1) _ ((CLt x y p) (CLt a b (Lt22 a1 b1 p))) ((CEq x y e) (match erased e _ ((Refl z) (CEq a b (Refl a))))) ((CGt x y p) (CGt a b (Lt22 b1 a1 p)))))))))

(def-fns _ $ erased neq-irrefl : (subterm erased (Bin) a) (erased (Neq a a) p) -> (erased (False) f)
  (match erased p _
    ((Neq11 a1 b1 q) (neq-irrefl a1 q))
    ((Neq22 a1 b1 q) (neq-irrefl a1 q))))

(def-fns _ $ many bin-eq-dec : (subterm many (Bin) a) (many (Bin) b) -> (many (BinDec a b) r)
  (match many a _
    ((BZ) (match many b _ ((BZ) (BYes a b (Refl a))) ((B1 b1) (BNo a b (NeqZ1 b1))) ((B2 b1) (BNo a b (NeqZ2 b1)))))
    ((B1 a1)
      (match many b _
        ((BZ) (BNo a b (Neq1Z a1)))
        ((B1 b1) (match many (bin-eq-dec a1 b1) _ ((BYes x y e) (match erased e _ ((Refl z) (BYes a b (Refl a))))) ((BNo x y ne) (BNo a b (Neq11 a1 b1 ne)))))
        ((B2 b1) (BNo a b (Neq12 a1 b1)))))
    ((B2 a1)
      (match many b _
        ((BZ) (BNo a b (Neq2Z a1)))
        ((B1 b1) (BNo a b (Neq21 a1 b1)))
        ((B2 b1) (match many (bin-eq-dec a1 b1) _ ((BYes x y e) (match erased e _ ((Refl z) (BYes a b (Refl a))))) ((BNo x y ne) (BNo a b (Neq22 a1 b1 ne)))))))))

; ---- The rules list: membership, appending at the end as a relation, and membership through a path context.

(def-adts
  (Rule : -> Type
    enum
    (many MkRule : (many (Bin) x) (many (Term) t) -> (Rule)))
  (MemRule : ((Bin) x) ((Term) t) ((List (Rule)) rules) -> Type
    enum
    (many MRHere : (erased (Bin) x) (erased (Term) t) (erased (List (Rule)) rest) -> (MemRule x t (Cons (Rule) (MkRule x t) rest)))
    (many MRThere : (erased (Bin) x) (erased (Term) t) (erased (Rule) r) (erased (List (Rule)) rest) (erased (MemRule x t rest) m) -> (MemRule x t (Cons (Rule) r rest))))
  (AppendR : ((List (Rule)) rules) ((Rule) r) ((List (Rule)) res) -> Type
    enum
    (many ApNil : (erased (Rule) r) -> (AppendR (Nil (Rule)) r (Cons (Rule) r (Nil (Rule)))))
    (many ApCons : (erased (Rule) a) (erased (List (Rule)) rest) (erased (Rule) r) (erased (List (Rule)) res) (erased (AppendR rest r res) p) -> (AppendR (Cons (Rule) a rest) r (Cons (Rule) a res))))
  (Digit : -> Type
    enum
    (many D1 : -> (Digit))
    (many D2 : -> (Digit)))
  (Wrap : ((List (Digit)) ctx) ((Bin) inner) ((Bin) outer) -> Type
    enum
    (many WNil : (erased (Bin) x) -> (Wrap (Nil (Digit)) x x))
    (many W1 : (erased (List (Digit)) ctx) (erased (Bin) x) (erased (Bin) y) (erased (Wrap ctx (B1 x) y) p) -> (Wrap (Cons (Digit) (D1) ctx) x y))
    (many W2 : (erased (List (Digit)) ctx) (erased (Bin) x) (erased (Bin) y) (erased (Wrap ctx (B2 x) y) p) -> (Wrap (Cons (Digit) (D2) ctx) x y)))
  (MemRuleW : ((List (Digit)) ctx) ((Bin) inner) ((Term) t) ((List (Rule)) rules) -> Type
    enum
    (many MWNil : (erased (Bin) x) (erased (Term) t) (erased (List (Rule)) rules) (erased (MemRule x t rules) m) -> (MemRuleW (Nil (Digit)) x t rules))
    (many MW1 : (erased (List (Digit)) ctx) (erased (Bin) x) (erased (Term) t) (erased (List (Rule)) rules) (erased (MemRuleW ctx (B1 x) t rules) m) -> (MemRuleW (Cons (Digit) (D1) ctx) x t rules))
    (many MW2 : (erased (List (Digit)) ctx) (erased (Bin) x) (erased (Term) t) (erased (List (Rule)) rules) (erased (MemRuleW ctx (B2 x) t rules) m) -> (MemRuleW (Cons (Digit) (D2) ctx) x t rules))))

(def-fns _ $ many append-rule : (subterm many (List (Rule)) rules) (many (Rule) r) -> (many (List (Rule)) res) (erased (AppendR rules r res) p)
  (match many rules _
    ((Nil a) (values (Cons (Rule) r (Nil (Rule))) (ApNil r)))
    ((Cons a x rest)
      (let (many res) (erased p) (append-rule rest r))
      (values (Cons (Rule) x res) (ApCons x rest r res p)))))

(def-fns _ $ erased mem-append : (erased (Bin) x) (erased (Term) t) (erased (List (Rule)) rules) (erased (Rule) r) (erased (List (Rule)) res) (subterm erased (MemRule x t rules) m) (erased (AppendR rules r res) ap) -> (erased (MemRule x t res) m2)
  (match erased m _
    ((MRHere x1 t1 rest)
      (match erased ap _
        ((ApCons a rest2 r2 res2 ap2) (MRHere x t res2))))
    ((MRThere x1 t1 r1 rest m1)
      (match erased ap _
        ((ApCons a rest2 r2 res2 ap2) (MRThere x t a res2 (mem-append x t rest2 r res2 m1 ap2)))))))

(def-fns _ $ erased mem-last : (erased (Bin) x) (erased (Term) t) (erased (List (Rule)) rules) (erased (List (Rule)) res) (subterm erased (AppendR rules (MkRule x t) res) ap) -> (erased (MemRule x t res) m)
  (match erased ap _
    ((ApNil r) (MRHere x t (Nil (Rule))))
    ((ApCons a rest r res2 ap2) (MRThere x t a res2 (mem-last x t rest res2 ap2)))))

(def-fns _ $ erased wrap-mw : (erased (List (Digit)) ctx) (erased (Bin) a) (erased (Bin) x) (subterm erased (Wrap ctx a x) w) (erased (Term) t) (erased (List (Rule)) rules) (erased (MemRule x t rules) m) -> (erased (MemRuleW ctx a t rules) r)
  (match erased w _
    ((WNil z) (MWNil a t rules m))
    ((W1 ctx1 a1 y q) (MW1 ctx1 a t rules (wrap-mw ctx1 (B1 a) x q t rules m)))
    ((W2 ctx1 a1 y q) (MW2 ctx1 a t rules (wrap-mw ctx1 (B2 a) x q t rules m)))))

(def-fns _ $ erased mw-unwrap : (erased (List (Digit)) ctx) (erased (Bin) a) (erased (Bin) x) (subterm erased (Wrap ctx a x) w) (erased (Term) t) (erased (List (Rule)) rules) (erased (MemRuleW ctx a t rules) m) -> (erased (MemRule x t rules) r)
  (match erased w _
    ((WNil z) (match erased m _ ((MWNil a1 t1 r1 m1) m1)))
    ((W1 ctx1 a1 y q) (match erased m _ ((MW1 c2 a2 t2 r2 m1) (mw-unwrap ctx1 (B1 a) x q t rules m1))))
    ((W2 ctx1 a1 y q) (match erased m _ ((MW2 c2 a2 t2 r2 m1) (mw-unwrap ctx1 (B2 a) x q t rules m1))))))

(def-fns _ $ erased mw-append : (erased (List (Digit)) ctx) (erased (Bin) a) (erased (Term) t) (erased (List (Rule)) rules) (subterm erased (MemRuleW ctx a t rules) m) (erased (Rule) r) (erased (List (Rule)) res) (erased (AppendR rules r res) ap) -> (erased (MemRuleW ctx a t res) m2)
  (match erased m _
    ((MWNil a1 t1 r1 m1) (MWNil a t res (mem-append a t rules r res m1 ap)))
    ((MW1 c1 a1 t1 r1 m1) (MW1 c1 a t res (mw-append c1 (B1 a) t rules m1 r res ap)))
    ((MW2 c1 a1 t1 r1 m1) (MW2 c1 a t res (mw-append c1 (B2 a) t rules m1 r res ap)))))
; ---- The fact table, indexed by its number of rule-free entries (ASSUMPTIONS 94). Sums are relations,
; since a type may not call a function; [In] is the path to a rule-free entry, and ruling one out returns
; the table at the predecessor count, which is what unification's measure steps down on.

(def-adts
  (Plus : ((Nat) a) ((Nat) b) ((Nat) c) -> Type
    enum
    (many PZ : (erased (Nat) b) -> (Plus (Zero) b b))
    (many PS : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Plus a b c) p) -> (Plus (Succ a) b (Succ c))))
  (Plus3 : ((Nat) h) ((Nat) a) ((Nat) b) ((Nat) c) -> Type
    enum
    (many P3Z : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Plus a b c) p) -> (Plus3 (Zero) a b c))
    (many P3S : (erased (Nat) h) (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Plus3 h a b c) p) -> (Plus3 (Succ h) a b (Succ c))))
  (Pred : ((Nat) a) ((Nat) b) ((Nat) c) -> Type
    enum
    (many MkPred : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Plus a b c) q) -> (Pred a b (Succ c))))
  (Pred3 : ((Nat) h) ((Nat) a) ((Nat) b) ((Nat) c) -> Type
    enum
    (many MkPred3 : (erased (Nat) h) (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Plus3 h a b c) q) -> (Pred3 h a b (Succ c)))))

(def-fns _ $ erased plus-zero-right : (subterm erased (Nat) a) -> (erased (Plus a (Zero) a) r)
  (match erased a _
    ((Zero) (PZ (Zero)))
    ((Succ a1) (PS a1 (Zero) a1 (plus-zero-right a1)))))

(def-fns _ $ erased plus-succ-right : (subterm erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Plus a b c) p) -> (erased (Plus a (Succ b) (Succ c)) r)
  (match erased p _
    ((PZ b1) (PZ (Succ b)))
    ((PS a1 b1 c1 q) (PS a1 (Succ b) (Succ c1) (plus-succ-right a1 b c1 q)))))

(def-fns _ $ erased plus-right : (subterm erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Plus a (Succ b) c) p) -> (erased (Pred a b c) r)
  (match erased p _
    ((PZ b1) (MkPred a b b (PZ b)))
    ((PS a1 b1 c1 q)
      (match erased (plus-right a1 b c1 q) _
        ((MkPred a2 b2 c2 q2) (MkPred a b (Succ c2) (PS a1 b c2 q2)))))))

(def-fns _ $ erased plus3-mid-succ : (subterm erased (Nat) h) (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Plus3 h a b c) p) -> (erased (Plus3 h (Succ a) b (Succ c)) r)
  (match erased p _
    ((P3Z a1 b1 c1 q) (P3Z (Succ a) b (Succ c) (PS a b c q)))
    ((P3S h1 a1 b1 c1 q) (P3S h1 (Succ a) b (Succ c1) (plus3-mid-succ h1 a b c1 q)))))

(def-fns _ $ erased plus3-right-succ : (subterm erased (Nat) h) (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Plus3 h a b c) p) -> (erased (Plus3 h a (Succ b) (Succ c)) r)
  (match erased p _
    ((P3Z a1 b1 c1 q) (P3Z a (Succ b) (Succ c) (plus-succ-right a b c q)))
    ((P3S h1 a1 b1 c1 q) (P3S h1 a (Succ b) (Succ c1) (plus3-right-succ h1 a b c1 q)))))

(def-fns _ $ erased plus3-mid : (subterm erased (Nat) h) (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Plus3 h (Succ a) b c) p) -> (erased (Pred3 h a b c) r)
  (match erased p _
    ((P3Z a1 b1 c1 q)
      (match erased q _
        ((PS a2 b2 c2 q2) (MkPred3 h a b c2 (P3Z a b c2 q2)))))
    ((P3S h1 a1 b1 c1 q)
      (match erased (plus3-mid h1 a b c1 q) _
        ((MkPred3 h2 a2 b2 c2 q2) (MkPred3 h a b (Succ c2) (P3S h1 a b c2 q2)))))))

(def-fns _ $ erased plus3-right : (subterm erased (Nat) h) (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Plus3 h a (Succ b) c) p) -> (erased (Pred3 h a b c) r)
  (match erased p _
    ((P3Z a1 b1 c1 q)
      (match erased (plus-right a b c q) _
        ((MkPred a2 b2 c2 q2) (MkPred3 h a b c2 (P3Z a b c2 q2)))))
    ((P3S h1 a1 b1 c1 q)
      (match erased (plus3-right h1 a b c1 q) _
        ((MkPred3 h2 a2 b2 c2 q2) (MkPred3 h a b (Succ c2) (P3S h1 a b c2 q2)))))))

(def-adts
  (Here : ((Nat) h) -> Type
    enum
    (many HNone : -> (Here (Zero)))
    (many HRuled : (many (Term) ty) (many (Term) t) -> (Here (Zero)))
    (many HFree : (many (Term) ty) -> (Here (Succ (Zero)))))
  (Facts : ((Nat) n) -> Type
    enum
    (many FEmpty : -> (Facts (Zero)))
    (many FNode : (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (many (Here h) here) (many (Facts n1) one) (many (Facts n2) two) (erased (Plus3 h n1 n2 m) p) -> (Facts m)))
  (In : ((Bin) x) ((Nat) n) ((Facts n) f) -> Type
    enum
    (many InHere : (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Term) ty) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 (Succ (Zero)) n1 n2 m) p) ->
       (In (BZ) m (FNode (Succ (Zero)) n1 n2 m (HFree ty) one two p)))
    (many In1 : (erased (Bin) x) (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Here h) here) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 h n1 n2 m) p) (erased (In x n1 one) q) ->
       (In (B1 x) m (FNode h n1 n2 m here one two p)))
    (many In2 : (erased (Bin) x) (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Here h) here) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 h n1 n2 m) p) (erased (In x n2 two) q) ->
       (In (B2 x) m (FNode h n1 n2 m here one two p))))
  (RuledIn : ((Bin) x) ((Nat) n) ((Facts n) f) -> Type
    enum
    (many RHere : (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Term) ty) (erased (Term) t) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 (Zero) n1 n2 m) p) ->
       (RuledIn (BZ) m (FNode (Zero) n1 n2 m (HRuled ty t) one two p)))
    (many R1 : (erased (Bin) x) (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Here h) here) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 h n1 n2 m) p) (erased (RuledIn x n1 one) q) ->
       (RuledIn (B1 x) m (FNode h n1 n2 m here one two p)))
    (many R2 : (erased (Bin) x) (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Here h) here) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 h n1 n2 m) p) (erased (RuledIn x n2 two) q) ->
       (RuledIn (B2 x) m (FNode h n1 n2 m here one two p))))
  (Ins : ((Bin) x) ((Nat) n) ((Facts n) f) ((Nat) n2) ((Facts n2) f2) -> Type
    enum
    (many InsLeaf : (erased (Term) ty) (erased (Plus3 (Succ (Zero)) (Zero) (Zero) (Succ (Zero))) p) ->
       (Ins (BZ) (Zero) (FEmpty) (Succ (Zero)) (FNode (Succ (Zero)) (Zero) (Zero) (Succ (Zero)) (HFree ty) (FEmpty) (FEmpty) p)))
    (many InsGrow1 : (erased (Bin) x) (erased (Facts (Succ (Zero))) one) (erased (Ins x (Zero) (FEmpty) (Succ (Zero)) one) q) (erased (Plus (Succ (Zero)) (Zero) (Succ (Zero))) p) ->
       (Ins (B1 x) (Zero) (FEmpty) (Succ (Zero)) (FNode (Zero) (Succ (Zero)) (Zero) (Succ (Zero)) (HNone) one (FEmpty) (P3Z (Succ (Zero)) (Zero) (Succ (Zero)) p))))
    (many InsGrow2 : (erased (Bin) x) (erased (Facts (Succ (Zero))) two) (erased (Ins x (Zero) (FEmpty) (Succ (Zero)) two) q) (erased (Plus (Zero) (Succ (Zero)) (Succ (Zero))) p) ->
       (Ins (B2 x) (Zero) (FEmpty) (Succ (Zero)) (FNode (Zero) (Zero) (Succ (Zero)) (Succ (Zero)) (HNone) (FEmpty) two (P3Z (Zero) (Succ (Zero)) (Succ (Zero)) p))))
    (many InsHere : (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Term) ty) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 (Zero) n1 n2 m) p) ->
       (Ins (BZ) m (FNode (Zero) n1 n2 m (HNone) one two p) (Succ m) (FNode (Succ (Zero)) n1 n2 (Succ m) (HFree ty) one two (P3S (Zero) n1 n2 m p))))
    (many Ins1 : (erased (Bin) x) (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Here h) here) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 h n1 n2 m) p)
       (erased (Nat) k1) (erased (Nat) m2) (erased (Facts k1) one2) (erased (Plus3 h k1 n2 m2) p2) (erased (Ins x n1 one k1 one2) q) ->
       (Ins (B1 x) m (FNode h n1 n2 m here one two p) m2 (FNode h k1 n2 m2 here one2 two p2)))
    (many Ins2 : (erased (Bin) x) (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Here h) here) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 h n1 n2 m) p)
       (erased (Nat) k2) (erased (Nat) m2) (erased (Facts k2) two2) (erased (Plus3 h n1 k2 m2) p2) (erased (Ins x n2 two k2 two2) q) ->
       (Ins (B2 x) m (FNode h n1 n2 m here one two p) m2 (FNode h n1 k2 m2 here one two2 p2))))
  (Out : ((Bin) x) ((Term) t) ((Nat) n) ((Facts n) f) ((Nat) k) ((Facts k) f2) -> Type
    enum
    (many OutHere : (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Term) ty) (erased (Term) t) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 (Zero) n1 n2 m) p) ->
       (Out (BZ) t (Succ m) (FNode (Succ (Zero)) n1 n2 (Succ m) (HFree ty) one two (P3S (Zero) n1 n2 m p)) m (FNode (Zero) n1 n2 m (HRuled ty t) one two p)))
    (many Out1 : (erased (Bin) x) (erased (Term) t) (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Here h) here) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 h n1 n2 m) p)
       (erased (Nat) k1) (erased (Nat) m2) (erased (Facts k1) one2) (erased (Plus3 h k1 n2 m2) p2) (erased (Out x t n1 one k1 one2) q) ->
       (Out (B1 x) t m (FNode h n1 n2 m here one two p) m2 (FNode h k1 n2 m2 here one2 two p2)))
    (many Out2 : (erased (Bin) x) (erased (Term) t) (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Here h) here) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 h n1 n2 m) p)
       (erased (Nat) k2) (erased (Nat) m2) (erased (Facts k2) two2) (erased (Plus3 h n1 k2 m2) p2) (erased (Out x t n2 two k2 two2) q) ->
       (Out (B2 x) t m (FNode h n1 n2 m here one two p) m2 (FNode h n1 k2 m2 here one two2 p2))))
  (Taken : ((Bin) x) ((Nat) n) ((Facts n) f) -> Type
    enum
    (many TFree : (erased (Bin) x) (erased (Nat) n) (erased (Facts n) f) (erased (In x n f) p) -> (Taken x n f))
    (many TRuled : (erased (Bin) x) (erased (Nat) n) (erased (Facts n) f) (erased (RuledIn x n f) p) -> (Taken x n f)))
  (Inserted : ((Bin) x) ((Nat) n) ((Facts n) f) -> Type
    enum
    (many IKept : (erased (Bin) x) (erased (Nat) n) (erased (Facts n) f) (erased (Taken x n f) q) -> (Inserted x n f))
    (many IGrew : (erased (Bin) x) (erased (Nat) n) (erased (Facts n) f) (many (Facts (Succ n)) f2) (erased (Ins x n f (Succ n) f2) r) (erased (In x (Succ n) f2) q) -> (Inserted x n f)))
  (Removed : ((Bin) x) ((Term) t) ((Nat) n) ((Facts n) f) -> Type
    enum
    (many MkRemoved : (erased (Bin) x) (erased (Term) t) (erased (Nat) k) (erased (Facts (Succ k)) f) (many (Facts k) f2) (erased (Out x t (Succ k) f k f2) r) -> (Removed x t (Succ k) f))))

; Agreement between the table and the rules list, one direction each: every ruled entry's rule is in the
; list, at the key its path spells; every key of the list is a ruled entry.
(def-adts
  (C1Here : ((List (Digit)) ctx) ((Nat) h) ((Here h) here) ((List (Rule)) rules) -> Type
    enum
    (many C1None : (erased (List (Digit)) ctx) (erased (List (Rule)) rules) -> (C1Here ctx (Zero) (HNone) rules))
    (many C1Free : (erased (List (Digit)) ctx) (erased (Term) ty) (erased (List (Rule)) rules) -> (C1Here ctx (Succ (Zero)) (HFree ty) rules))
    (many C1Ruled : (erased (List (Digit)) ctx) (erased (Term) ty) (erased (Term) t) (erased (List (Rule)) rules) (erased (MemRuleW ctx (BZ) t rules) m) -> (C1Here ctx (Zero) (HRuled ty t) rules)))
  (C1 : ((List (Digit)) ctx) ((Nat) n) ((Facts n) f) ((List (Rule)) rules) -> Type
    enum
    (many C1Empty : (erased (List (Digit)) ctx) (erased (List (Rule)) rules) -> (C1 ctx (Zero) (FEmpty) rules))
    (many C1Node : (erased (List (Digit)) ctx) (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Here h) here) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 h n1 n2 m) p) (erased (List (Rule)) rules)
       (erased (C1Here ctx h here rules) ch) (erased (C1 (Cons (Digit) (D1) ctx) n1 one rules) c1) (erased (C1 (Cons (Digit) (D2) ctx) n2 two rules) c2) ->
       (C1 ctx m (FNode h n1 n2 m here one two p) rules)))
  (AllRuled : ((List (Bin)) ks) ((Nat) n) ((Facts n) f) -> Type
    enum
    (many ARNil : (erased (Nat) n) (erased (Facts n) f) -> (AllRuled (Nil (Bin)) n f))
    (many ARCons : (erased (Bin) z) (erased (List (Bin)) ks) (erased (Nat) n) (erased (Facts n) f) (erased (RuledIn z n f) r) (erased (AllRuled ks n f) rest) -> (AllRuled (Cons (Bin) z ks) n f)))
  (Keys : ((List (Bin)) seen) ((List (Rule)) rules) ((List (Bin)) ks) -> Type
    enum
    (many KNil : (erased (List (Bin)) seen) -> (Keys seen (Nil (Rule)) seen))
    (many KCons : (erased (List (Bin)) seen) (erased (Bin) x) (erased (Term) t) (erased (List (Rule)) rest) (erased (List (Bin)) ks) (erased (Keys (Cons (Bin) x seen) rest ks) k) -> (Keys seen (Cons (Rule) (MkRule x t) rest) ks)))
  (Looked : ((Bin) x) ((Nat) n) ((Facts n) f) ((Bin) xg) ((List (Rule)) rules) -> Type
    enum
    (many LNone : (erased (Bin) x) (erased (Nat) n) (erased (Facts n) f) (erased (Bin) xg) (erased (List (Rule)) rules) -> (Looked x n f xg rules))
    (many LRuled : (erased (Bin) x) (erased (Nat) n) (erased (Facts n) f) (erased (Bin) xg) (erased (List (Rule)) rules) (many (Term) ty) (many (Term) t) (erased (MemRule xg t rules) m) -> (Looked x n f xg rules))
    (many LFree : (erased (Bin) x) (erased (Nat) n) (erased (Facts n) f) (erased (Bin) xg) (erased (List (Rule)) rules) (many (Term) ty) (erased (In x n f) p) -> (Looked x n f xg rules))))

(def-fns _ $ erased in-empty : (erased (Bin) x) (erased (In x (Zero) (FEmpty)) p) -> (erased (False) f)
  (match erased p _))


(def-fns _ $ erased in-empty : (erased (Bin) x) (erased (In x (Zero) (FEmpty)) p) -> (erased (False) f)
  (match erased p _))

(def-fns _ $ erased in-ruled-clash : (erased (Bin) x) (erased (Nat) n) (erased (Facts n) f) (subterm erased (In x n f) p) (erased (RuledIn x n f) q) -> (erased (False) r)
  (match erased p _
    ((InHere n1 n2 m ty one two p3) (match erased q _))
    ((In1 x1 h n1 n2 m here one two p3 q1) (match erased q _ ((R1 x2 h2 a2 b2 c2 here2 one2 two2 p4 q2) (in-ruled-clash x1 n1 one q1 q2))))
    ((In2 x1 h n1 n2 m here one two p3 q1) (match erased q _ ((R2 x2 h2 a2 b2 c2 here2 one2 two2 p4 q2) (in-ruled-clash x1 n2 two q1 q2))))))

; Every key of a table is at most c: at each node, the key its path spells is, when the node holds an
; entry, and so on in both subtrees.
(def-adts
  (AboveHere : ((List (Digit)) ctx) ((Bin) c) ((Nat) h) ((Here h) here) -> Type
    enum
    (many AHNone : (erased (List (Digit)) ctx) (erased (Bin) c) -> (AboveHere ctx c (Zero) (HNone)))
    (many AHKey : (erased (List (Digit)) ctx) (erased (Bin) c) (erased (Nat) h) (erased (Here h) here) (erased (Bin) y) (erased (Wrap ctx (BZ) y) w) (erased (BinLe y c) le) -> (AboveHere ctx c h here)))
  (Above : ((List (Digit)) ctx) ((Bin) c) ((Nat) n) ((Facts n) f) -> Type
    enum
    (many AbEmpty : (erased (List (Digit)) ctx) (erased (Bin) c) -> (Above ctx c (Zero) (FEmpty)))
    (many AbNode : (erased (List (Digit)) ctx) (erased (Bin) c) (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Here h) here) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 h n1 n2 m) p)
       (erased (AboveHere ctx c h here) ah) (erased (Above (Cons (Digit) (D1) ctx) c n1 one) a1) (erased (Above (Cons (Digit) (D2) ctx) c n2 two) a2) -> (Above ctx c m (FNode h n1 n2 m here one two p)))))

(def-fns _ $ erased wrap-fun : (erased (List (Digit)) ctx) (erased (Bin) a) (erased (Bin) x) (erased (Bin) y) (subterm erased (Wrap ctx a x) w) (erased (Wrap ctx a y) v) -> (erased (Eq x y) e)
  (match erased w _
    ((WNil z) (match erased v _ ((WNil z2) (Refl x))))
    ((W1 ctx1 a1 y1 p) (match erased v _ ((W1 ctx2 a2 y2 q) (wrap-fun ctx1 (B1 a1) x y p q))))
    ((W2 ctx1 a1 y1 p) (match erased v _ ((W2 ctx2 a2 y2 q) (wrap-fun ctx1 (B2 a1) x y p q))))))

(def-fns _ $ erased above-in : (erased (List (Digit)) ctx) (erased (Bin) c) (erased (Nat) n) (erased (Facts n) f) (erased (Bin) x) (erased (Bin) y) (erased (Above ctx c n f) ab) (subterm erased (In x n f) p) (erased (Wrap ctx x y) w) -> (erased (BinLe y c) le)
  (match erased p _
    ((InHere n1 n2 m ty one two p3)
      (match erased ab _
        ((AbNode c2 c3 h4 n5 n6 m7 here8 one9 two10 p11 ah a1 a2)
          (match erased ah _
            ((AHKey c4 c5 h6 here7 y2 w2 le2) (match erased (wrap-fun ctx (BZ) y2 y w2 w) _ ((Refl z) le2)))))))
    ((In1 x1 h n1 n2 m here one two p3 q)
      (match erased ab _
        ((AbNode c2 c3 h4 n5 n6 m7 here8 one9 two10 p11 ah a1 a2) (above-in (Cons (Digit) (D1) ctx) c n1 one x1 y a1 q (W1 ctx x1 y w)))))
    ((In2 x1 h n1 n2 m here one two p3 q)
      (match erased ab _
        ((AbNode c2 c3 h4 n5 n6 m7 here8 one9 two10 p11 ah a1 a2) (above-in (Cons (Digit) (D2) ctx) c n2 two x1 y a2 q (W2 ctx x1 y w)))))))

(def-fns _ $ erased above-ruledin : (erased (List (Digit)) ctx) (erased (Bin) c) (erased (Nat) n) (erased (Facts n) f) (erased (Bin) x) (erased (Bin) y) (erased (Above ctx c n f) ab) (subterm erased (RuledIn x n f) p) (erased (Wrap ctx x y) w) -> (erased (BinLe y c) le)
  (match erased p _
    ((RHere n1 n2 m ty t one two p3)
      (match erased ab _
        ((AbNode c2 c3 h4 n5 n6 m7 here8 one9 two10 p11 ah a1 a2)
          (match erased ah _
            ((AHKey c4 c5 h6 here7 y2 w2 le2) (match erased (wrap-fun ctx (BZ) y2 y w2 w) _ ((Refl z) le2)))))))
    ((R1 x1 h n1 n2 m here one two p3 q)
      (match erased ab _
        ((AbNode c2 c3 h4 n5 n6 m7 here8 one9 two10 p11 ah a1 a2) (above-ruledin (Cons (Digit) (D1) ctx) c n1 one x1 y a1 q (W1 ctx x1 y w)))))
    ((R2 x1 h n1 n2 m here one two p3 q)
      (match erased ab _
        ((AbNode c2 c3 h4 n5 n6 m7 here8 one9 two10 p11 ah a1 a2) (above-ruledin (Cons (Digit) (D2) ctx) c n2 two x1 y a2 q (W2 ctx x1 y w)))))))

(def-fns _ $ erased above-taken : (erased (Bin) c) (erased (Nat) n) (erased (Facts n) f) (erased (Bin) x) (erased (Above (Nil (Digit)) c n f) ab) (erased (Taken x n f) t) -> (erased (BinLe x c) le)
  (match erased t _
    ((TFree z1 z2 z3 p) (above-in (Nil (Digit)) c n f x x ab p (WNil x)))
    ((TRuled z1 z2 z3 p) (above-ruledin (Nil (Digit)) c n f x x ab p (WNil x)))))

(def-fns _ $ erased above-ins : (erased (List (Digit)) ctx) (erased (Bin) c) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) n2) (erased (Facts n2) f2) (erased (Bin) x) (erased (Bin) y) (erased (Above ctx c n f) ab) (subterm erased (Ins x n f n2 f2) i) (erased (Wrap ctx x y) w) (erased (BinLe y c) le) -> (erased (Above ctx c n2 f2) ab2)
  (match erased i _
    ((InsLeaf ty p) (AbNode ctx c (Succ (Zero)) (Zero) (Zero) (Succ (Zero)) (HFree ty) (FEmpty) (FEmpty) p (AHKey ctx c (Succ (Zero)) (HFree ty) y w le) (AbEmpty (Cons (Digit) (D1) ctx) c) (AbEmpty (Cons (Digit) (D2) ctx) c)))
    ((InsGrow1 x1 one q p)
      (AbNode ctx c (Zero) (Succ (Zero)) (Zero) (Succ (Zero)) (HNone) one (FEmpty) (P3Z (Succ (Zero)) (Zero) (Succ (Zero)) p) (AHNone ctx c)
        (above-ins (Cons (Digit) (D1) ctx) c (Zero) (FEmpty) (Succ (Zero)) one x1 y (AbEmpty (Cons (Digit) (D1) ctx) c) q (W1 ctx x1 y w) le)
        (AbEmpty (Cons (Digit) (D2) ctx) c)))
    ((InsGrow2 x1 two q p)
      (AbNode ctx c (Zero) (Zero) (Succ (Zero)) (Succ (Zero)) (HNone) (FEmpty) two (P3Z (Zero) (Succ (Zero)) (Succ (Zero)) p) (AHNone ctx c)
        (AbEmpty (Cons (Digit) (D1) ctx) c)
        (above-ins (Cons (Digit) (D2) ctx) c (Zero) (FEmpty) (Succ (Zero)) two x1 y (AbEmpty (Cons (Digit) (D2) ctx) c) q (W2 ctx x1 y w) le)))
    ((InsHere n1 n2 m ty one two p)
      (match erased ab _
        ((AbNode c2 c3 h4 n5 n6 m7 here8 one9 two10 p11 ah a1 a2) (AbNode ctx c (Succ (Zero)) n1 n2 (Succ m) (HFree ty) one two (P3S (Zero) n1 n2 m p) (AHKey ctx c (Succ (Zero)) (HFree ty) y w le) a1 a2))))
    ((Ins1 x1 h n1 n2 m here one two p k1 m2 one2 p2 q)
      (match erased ab _
        ((AbNode c2 c3 h4 n5 n6 m7 here8 one9 two10 p11 ah a1 a2) (AbNode ctx c h k1 n2 m2 here one2 two p2 ah (above-ins (Cons (Digit) (D1) ctx) c n1 one k1 one2 x1 y a1 q (W1 ctx x1 y w) le) a2))))
    ((Ins2 x1 h n1 n2 m here one two p k2 m2 two2 p2 q)
      (match erased ab _
        ((AbNode c2 c3 h4 n5 n6 m7 here8 one9 two10 p11 ah a1 a2) (AbNode ctx c h n1 k2 m2 here one two2 p2 ah a1 (above-ins (Cons (Digit) (D2) ctx) c n2 two k2 two2 x1 y a2 q (W2 ctx x1 y w) le)))))))

(def-fns _ $ erased above-out : (erased (List (Digit)) ctx) (erased (Bin) c) (erased (Bin) x) (erased (Term) t) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) k) (erased (Facts k) f2) (erased (Above ctx c n f) ab) (subterm erased (Out x t n f k f2) o) -> (erased (Above ctx c k f2) ab2)
  (match erased o _
    ((OutHere n1 n2 m ty t1 one two p)
      (match erased ab _
        ((AbNode c2 c3 h4 n5 n6 m7 here8 one9 two10 p11 ah a1 a2)
          (match erased ah _
            ((AHKey c4 c5 h6 here7 y w le) (AbNode ctx c (Zero) n1 n2 m (HRuled ty t1) one two p (AHKey ctx c (Zero) (HRuled ty t1) y w le) a1 a2))))))
    ((Out1 x1 t1 h n1 n2 m here one two p k1 m2 one2 p2 q)
      (match erased ab _
        ((AbNode c2 c3 h4 n5 n6 m7 here8 one9 two10 p11 ah a1 a2) (AbNode ctx c h k1 n2 m2 here one2 two p2 ah (above-out (Cons (Digit) (D1) ctx) c x1 t1 n1 one k1 one2 a1 q) a2))))
    ((Out2 x1 t1 h n1 n2 m here one two p k2 m2 two2 p2 q)
      (match erased ab _
        ((AbNode c2 c3 h4 n5 n6 m7 here8 one9 two10 p11 ah a1 a2) (AbNode ctx c h n1 k2 m2 here one two2 p2 ah a1 (above-out (Cons (Digit) (D2) ctx) c x1 t1 n2 two k2 two2 a2 q)))))))

(def-fns _ $ erased above-weaken : (erased (List (Digit)) ctx) (erased (Bin) c) (erased (Bin) c2) (erased (Nat) n) (erased (Facts n) f) (subterm erased (Above ctx c n f) ab) (erased (BinLe c c2) le) -> (erased (Above ctx c2 n f) ab2)
  (match erased ab _
    ((AbEmpty z1 z2) (AbEmpty ctx c2))
    ((AbNode z1 z2 h n1 n2 m here one two p ah a1 a2)
      (AbNode ctx c2 h n1 n2 m here one two p
        (match erased ah (((AboveHere ctx c2 h here) r)) ((AHNone y1 y2) (AHNone ctx c2)) ((AHKey y1 y2 y3 y4 y w le0) (AHKey ctx c2 h here y w (le-le y c c2 le0 le))))
        (above-weaken (Cons (Digit) (D1) ctx) c c2 n1 one a1 le)
        (above-weaken (Cons (Digit) (D2) ctx) c c2 n2 two a2 le)))))

(def-fns _ $ erased taken-empty : (erased (Bin) x) (erased (Taken x (Zero) (FEmpty)) t) -> (erased (False) f)
  (match erased t _
    ((TFree z1 z2 z3 p) (in-empty x p))
    ((TRuled z1 z2 z3 p) (match erased p _))))

(def-fns _ $ erased taken-1 : (erased (Bin) x) (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Here h) here) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 h n1 n2 m) p) (erased (Taken x n1 one) t) -> (erased (Taken (B1 x) m (FNode h n1 n2 m here one two p)) r)
  (match erased t _
    ((TFree z1 z2 z3 q) (TFree (B1 x) m (FNode h n1 n2 m here one two p) (In1 x h n1 n2 m here one two p q)))
    ((TRuled z1 z2 z3 q) (TRuled (B1 x) m (FNode h n1 n2 m here one two p) (R1 x h n1 n2 m here one two p q)))))

(def-fns _ $ erased taken-2 : (erased (Bin) x) (erased (Nat) h) (erased (Nat) n1) (erased (Nat) n2) (erased (Nat) m) (erased (Here h) here) (erased (Facts n1) one) (erased (Facts n2) two) (erased (Plus3 h n1 n2 m) p) (erased (Taken x n2 two) t) -> (erased (Taken (B2 x) m (FNode h n1 n2 m here one two p)) r)
  (match erased t _
    ((TFree z1 z2 z3 q) (TFree (B2 x) m (FNode h n1 n2 m here one two p) (In2 x h n1 n2 m here one two p q)))
    ((TRuled z1 z2 z3 q) (TRuled (B2 x) m (FNode h n1 n2 m here one two p) (R2 x h n1 n2 m here one two p q)))))

(def-fns _ $ many facts-lookup : (subterm many (Bin) x) (erased (Nat) n) (many (Facts n) f) (erased (List (Digit)) ctx) (erased (Bin) xg) (erased (Wrap ctx x xg) w) (erased (List (Rule)) rules) (erased (C1 ctx n f rules) c) -> (many (Looked x n f xg rules) r)
  (match many f _
    ((FEmpty) (LNone x n f xg rules))
    ((FNode h n1 n2 m here one two p3)
      (match many x _
        ((BZ)
          (match many here _
            ((HNone) (LNone x n f xg rules))
            ((HRuled ty t)
              (let (erased ch) (match erased c (((C1Here ctx h here rules) ch)) ((C1Node c0 h0 a0 b0 m0 here0 one0 two0 p0 r0 ch c1 c2) ch)))
              (let (erased mw) (match erased ch (((MemRuleW ctx (BZ) t rules) mw)) ((C1Ruled c0 ty0 t0 r0 mw) mw)))
              (LRuled x n f xg rules ty t (mw-unwrap ctx (BZ) xg w t rules mw)))
            ((HFree ty) (LFree x n f xg rules ty (InHere n1 n2 m ty one two p3)))))
        ((B1 x1)
          (let (erased c1) (match erased c (((C1 (Cons (Digit) (D1) ctx) n1 one rules) c1)) ((C1Node c0 h0 a0 b0 m0 here0 one0 two0 p0 r0 ch c1 c2) c1)))
          (match many (facts-lookup x1 n1 one (Cons (Digit) (D1) ctx) xg (W1 ctx x1 xg w) rules c1) _
            ((LNone a b d e g) (LNone x n f xg rules))
            ((LRuled a b d e g ty t mr) (LRuled x n f xg rules ty t mr))
            ((LFree a b d e g ty q) (LFree x n f xg rules ty (In1 x1 h n1 n2 m here one two p3 q)))))
        ((B2 x1)
          (let (erased c2) (match erased c (((C1 (Cons (Digit) (D2) ctx) n2 two rules) c2)) ((C1Node c0 h0 a0 b0 m0 here0 one0 two0 p0 r0 ch c1 c2) c2)))
          (match many (facts-lookup x1 n2 two (Cons (Digit) (D2) ctx) xg (W2 ctx x1 xg w) rules c2) _
            ((LNone a b d e g) (LNone x n f xg rules))
            ((LRuled a b d e g ty t mr) (LRuled x n f xg rules ty t mr))
            ((LFree a b d e g ty q) (LFree x n f xg rules ty (In2 x1 h n1 n2 m here one two p3 q)))))))))

; A new rule-free entry; an occupied position is left as it is.
(def-fns _ $ many facts-insert : (subterm many (Bin) x) (erased (Nat) n) (many (Facts n) f) (many (Term) ty) -> (many (Inserted x n f) r)
  (match many f _
    ((FEmpty)
      (match many x _
        ((BZ)
          (let (erased p0) (P3S (Zero) (Zero) (Zero) (Zero) (P3Z (Zero) (Zero) (Zero) (PZ (Zero)))))
          (IGrew x n f (FNode (Succ (Zero)) (Zero) (Zero) (Succ (Zero)) (HFree ty) (FEmpty) (FEmpty) p0) (InsLeaf ty p0) (InHere (Zero) (Zero) (Succ (Zero)) ty (FEmpty) (FEmpty) p0)))
        ((B1 x1)
          (match many (facts-insert x1 (Zero) (FEmpty) ty) _
            (absurd (IKept a b d q) (taken-empty x1 q))
            ((IGrew a b d one r q1)
              (let (erased p0) (plus-zero-right (Succ (Zero))))
              (IGrew x n f (FNode (Zero) (Succ (Zero)) (Zero) (Succ (Zero)) (HNone) one (FEmpty) (P3Z (Succ (Zero)) (Zero) (Succ (Zero)) p0)) (InsGrow1 x1 one r p0)
                (In1 x1 (Zero) (Succ (Zero)) (Zero) (Succ (Zero)) (HNone) one (FEmpty) (P3Z (Succ (Zero)) (Zero) (Succ (Zero)) p0) q1)))))
        ((B2 x1)
          (match many (facts-insert x1 (Zero) (FEmpty) ty) _
            (absurd (IKept a b d q) (taken-empty x1 q))
            ((IGrew a b d two r q1)
              (let (erased p0) (PZ (Succ (Zero))))
              (IGrew x n f (FNode (Zero) (Zero) (Succ (Zero)) (Succ (Zero)) (HNone) (FEmpty) two (P3Z (Zero) (Succ (Zero)) (Succ (Zero)) p0)) (InsGrow2 x1 two r p0)
                (In2 x1 (Zero) (Zero) (Succ (Zero)) (Succ (Zero)) (HNone) (FEmpty) two (P3Z (Zero) (Succ (Zero)) (Succ (Zero)) p0) q1)))))))
    ((FNode h n1 n2 m here one two p3)
      (match many x _
        ((BZ)
          (match many here _
            ((HNone) (IGrew x n f (FNode (Succ (Zero)) n1 n2 (Succ m) (HFree ty) one two (P3S (Zero) n1 n2 m p3)) (InsHere n1 n2 m ty one two p3) (InHere n1 n2 (Succ m) ty one two (P3S (Zero) n1 n2 m p3))))
            ((HRuled ty0 t0) (IKept x n f (TRuled x n f (RHere n1 n2 m ty0 t0 one two p3))))
            ((HFree ty0) (IKept x n f (TFree x n f (InHere n1 n2 m ty0 one two p3))))))
        ((B1 x1)
          (match many (facts-insert x1 n1 one ty) _
            ((IKept a b d q) (IKept x n f (taken-1 x1 h n1 n2 m here one two p3 q)))
            ((IGrew a b d one2 r q1)
              (let (erased p4) (plus3-mid-succ h n1 n2 m p3))
              (IGrew x n f (FNode h (Succ n1) n2 (Succ m) here one2 two p4) (Ins1 x1 h n1 n2 m here one two p3 (Succ n1) (Succ m) one2 p4 r) (In1 x1 h (Succ n1) n2 (Succ m) here one2 two p4 q1)))))
        ((B2 x1)
          (match many (facts-insert x1 n2 two ty) _
            ((IKept a b d q) (IKept x n f (taken-2 x1 h n1 n2 m here one two p3 q)))
            ((IGrew a b d two2 r q1)
              (let (erased p4) (plus3-right-succ h n1 n2 m p3))
              (IGrew x n f (FNode h n1 (Succ n2) (Succ m) here one two2 p4) (Ins2 x1 h n1 n2 m here one two p3 (Succ n2) (Succ m) two2 p4 r) (In2 x1 h n1 (Succ n2) (Succ m) here one two2 p4 q1)))))))))

; Rules a rule-free entry out, at the path its proof gives.
(def-fns _ $ many facts-rule-out : (erased (Nat) n) (subterm many (Facts n) f) (many (Bin) x) (erased (In x n f) p) (many (Term) t) -> (many (Removed x t n f) r)
  (match many f _
    (absurd FEmpty (in-empty x p))
    ((FNode h n1 n2 m here one two p3)
      (match many x _
        ((BZ)
          (match many here _
            ((HFree ty)
              (match erased p3 _
                ((P3S h1 a1 b1 c1 q) (MkRemoved x t c1 f (FNode (Zero) n1 n2 c1 (HRuled ty t) one two q) (OutHere n1 n2 c1 ty t one two q)))))
            (absurd HNone (match erased p (((False) f))))
            (absurd (HRuled ty0 t0) (match erased p (((False) f))))))
        ((B1 x1)
          (let (erased q) (match erased p (((In x1 n1 one) q)) ((In1 x2 h2 a2 b2 c2 here2 one2 two2 p2 q) q)))
          (match many (facts-rule-out n1 one x1 q t) _
            ((MkRemoved a a0 k1 b one2 r)
              (match erased (plus3-mid h k1 n2 m p3) _
                ((MkPred3 h2 a2 b2 c2 q2) (MkRemoved x t c2 f (FNode h k1 n2 c2 here one2 two q2) (Out1 x1 t h n1 n2 m here one two p3 k1 c2 one2 q2 r)))))))
        ((B2 x1)
          (let (erased q) (match erased p (((In x1 n2 two) q)) ((In2 x2 h2 a2 b2 c2 here2 one2 two2 p2 q) q)))
          (match many (facts-rule-out n2 two x1 q t) _
            ((MkRemoved a a0 k2 b two2 r)
              (match erased (plus3-right h n1 k2 m p3) _
                ((MkPred3 h2 a2 b2 c2 q2) (MkRemoved x t c2 f (FNode h n1 k2 c2 here one two2 q2) (Out2 x1 t h n1 n2 m here one two p3 k2 c2 two2 q2 r)))))))))))

; ---- Transport of the agreement proofs through an insert, a rule-out and an append.

(def-fns _ $ erased ruledin-ins : (erased (Bin) z) (erased (Bin) x) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) n2) (erased (Facts n2) f2) (subterm erased (Ins x n f n2 f2) i) (erased (RuledIn z n f) r) -> (erased (RuledIn z n2 f2) r2)
  (match erased i _
    ((InsLeaf ty p) (match erased r _))
    ((InsGrow1 x1 one q p) (match erased r _))
    ((InsGrow2 x1 two q p) (match erased r _))
    ((InsHere n1 n2 m ty one two p)
      (match erased r _
        ((R1 z1 h a b c here one1 two1 p1 q1) (R1 z1 (Succ (Zero)) n1 n2 (Succ m) (HFree ty) one two (P3S (Zero) n1 n2 m p) q1))
        ((R2 z1 h a b c here one1 two1 p1 q1) (R2 z1 (Succ (Zero)) n1 n2 (Succ m) (HFree ty) one two (P3S (Zero) n1 n2 m p) q1))))
    ((Ins1 x1 h n1 a2 m here one two p k1 m2 one2 p2 q)
      (match erased r _
        ((RHere b1 b2 b3 ty t one1 two1 p1) (RHere k1 a2 m2 ty t one2 two p2))
        ((R1 z1 h1 a1 b1 c1 here1 one1 two1 p1 q1) (R1 z1 h k1 a2 m2 here one2 two p2 (ruledin-ins z1 x1 n1 one k1 one2 q q1)))
        ((R2 z1 h1 a1 b1 c1 here1 one1 two1 p1 q1) (R2 z1 h k1 a2 m2 here one2 two p2 q1))))
    ((Ins2 x1 h n1 a2 m here one two p k2 m2 two2 p2 q)
      (match erased r _
        ((RHere b1 b2 b3 ty t one1 two1 p1) (RHere n1 k2 m2 ty t one two2 p2))
        ((R1 z1 h1 a1 b1 c1 here1 one1 two1 p1 q1) (R1 z1 h n1 k2 m2 here one two2 p2 q1))
        ((R2 z1 h1 a1 b1 c1 here1 one1 two1 p1 q1) (R2 z1 h n1 k2 m2 here one two2 p2 (ruledin-ins z1 x1 a2 two k2 two2 q q1)))))))

(def-fns _ $ erased ruledin-out : (erased (Bin) z) (erased (Bin) x) (erased (Term) t) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) k) (erased (Facts k) f2) (subterm erased (Out x t n f k f2) o) (erased (RuledIn z n f) r) -> (erased (RuledIn z k f2) r2)
  (match erased o _
    ((OutHere n1 n2 m ty t0 one two p)
      (match erased r _
        ((R1 z1 h a b c here one1 two1 p1 q1) (R1 z1 (Zero) n1 n2 m (HRuled ty t0) one two p q1))
        ((R2 z1 h a b c here one1 two1 p1 q1) (R2 z1 (Zero) n1 n2 m (HRuled ty t0) one two p q1))))
    ((Out1 x1 t0 h n1 a2 m here one two p k1 m2 one2 p2 q)
      (match erased r _
        ((RHere b1 b2 b3 ty t1 one1 two1 p1) (RHere k1 a2 m2 ty t1 one2 two p2))
        ((R1 z1 h1 a1 b1 c1 here1 one1 two1 p1 q1) (R1 z1 h k1 a2 m2 here one2 two p2 (ruledin-out z1 x1 t0 n1 one k1 one2 q q1)))
        ((R2 z1 h1 a1 b1 c1 here1 one1 two1 p1 q1) (R2 z1 h k1 a2 m2 here one2 two p2 q1))))
    ((Out2 x1 t0 h n1 a2 m here one two p k2 m2 two2 p2 q)
      (match erased r _
        ((RHere b1 b2 b3 ty t1 one1 two1 p1) (RHere n1 k2 m2 ty t1 one two2 p2))
        ((R1 z1 h1 a1 b1 c1 here1 one1 two1 p1 q1) (R1 z1 h n1 k2 m2 here one two2 p2 q1))
        ((R2 z1 h1 a1 b1 c1 here1 one1 two1 p1 q1) (R2 z1 h n1 k2 m2 here one two2 p2 (ruledin-out z1 x1 t0 a2 two k2 two2 q q1)))))))

(def-fns _ $ erased ruledin-out-new : (erased (Bin) x) (erased (Term) t) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) k) (erased (Facts k) f2) (subterm erased (Out x t n f k f2) o) -> (erased (RuledIn x k f2) r)
  (match erased o _
    ((OutHere n1 n2 m ty t0 one two p) (RHere n1 n2 m ty t0 one two p))
    ((Out1 x1 t0 h n1 a2 m here one two p k1 m2 one2 p2 q) (R1 x1 h k1 a2 m2 here one2 two p2 (ruledin-out-new x1 t0 n1 one k1 one2 q)))
    ((Out2 x1 t0 h n1 a2 m here one two p k2 m2 two2 p2 q) (R2 x1 h n1 k2 m2 here one two2 p2 (ruledin-out-new x1 t0 a2 two k2 two2 q)))))

(def-fns _ $ erased allruled-ins : (erased (List (Bin)) ks) (erased (Bin) x) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) n2) (erased (Facts n2) f2) (erased (Ins x n f n2 f2) i) (subterm erased (AllRuled ks n f) a) -> (erased (AllRuled ks n2 f2) a2)
  (match erased a _
    ((ARNil b c) (ARNil n2 f2))
    ((ARCons z rest b c r q) (ARCons z rest n2 f2 (ruledin-ins z x n f n2 f2 i r) (allruled-ins rest x n f n2 f2 i q)))))

(def-fns _ $ erased allruled-out : (erased (List (Bin)) ks) (erased (Bin) x) (erased (Term) t) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) k) (erased (Facts k) f2) (erased (Out x t n f k f2) o) (subterm erased (AllRuled ks n f) a) -> (erased (AllRuled ks k f2) a2)
  (match erased a _
    ((ARNil b c) (ARNil k f2))
    ((ARCons z rest b c r q) (ARCons z rest k f2 (ruledin-out z x t n f k f2 o r) (allruled-out rest x t n f k f2 o q)))))

(def-fns _ $ erased c1here-append : (erased (List (Digit)) ctx) (erased (Nat) h) (erased (Here h) here) (erased (List (Rule)) rules) (erased (C1Here ctx h here rules) ch) (erased (Rule) r) (erased (List (Rule)) res) (erased (AppendR rules r res) ap) -> (erased (C1Here ctx h here res) ch2)
  (match erased ch _
    ((C1None c0 r0) (C1None ctx res))
    ((C1Free c0 ty r0) (C1Free ctx ty res))
    ((C1Ruled c0 ty t r0 mw) (C1Ruled ctx ty t res (mw-append ctx (BZ) t rules mw r res ap)))))

(def-fns _ $ erased c1-append : (erased (List (Digit)) ctx) (erased (Nat) n) (erased (Facts n) f) (erased (List (Rule)) rules) (subterm erased (C1 ctx n f rules) c) (erased (Rule) r) (erased (List (Rule)) res) (erased (AppendR rules r res) ap) -> (erased (C1 ctx n f res) c2)
  (match erased c _
    ((C1Empty c0 r0) (C1Empty ctx res))
    ((C1Node c0 h n1 n2 m here one two p r0 ch c1 c2)
      (C1Node ctx h n1 n2 m here one two p res (c1here-append ctx h here rules ch r res ap)
        (c1-append (Cons (Digit) (D1) ctx) n1 one rules c1 r res ap)
        (c1-append (Cons (Digit) (D2) ctx) n2 two rules c2 r res ap)))))

(def-fns _ $ erased c1-ins : (erased (List (Digit)) ctx) (erased (Bin) x) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) n2) (erased (Facts n2) f2) (subterm erased (Ins x n f n2 f2) i) (erased (List (Rule)) rules) (erased (C1 ctx n f rules) c) -> (erased (C1 ctx n2 f2 rules) c2)
  (match erased i _
    ((InsLeaf ty p) (C1Node ctx (Succ (Zero)) (Zero) (Zero) (Succ (Zero)) (HFree ty) (FEmpty) (FEmpty) p rules (C1Free ctx ty rules) (C1Empty (Cons (Digit) (D1) ctx) rules) (C1Empty (Cons (Digit) (D2) ctx) rules)))
    ((InsGrow1 x1 one q p)
      (C1Node ctx (Zero) (Succ (Zero)) (Zero) (Succ (Zero)) (HNone) one (FEmpty) (P3Z (Succ (Zero)) (Zero) (Succ (Zero)) p) rules (C1None ctx rules)
        (c1-ins (Cons (Digit) (D1) ctx) x1 (Zero) (FEmpty) (Succ (Zero)) one q rules (C1Empty (Cons (Digit) (D1) ctx) rules))
        (C1Empty (Cons (Digit) (D2) ctx) rules)))
    ((InsGrow2 x1 two q p)
      (C1Node ctx (Zero) (Zero) (Succ (Zero)) (Succ (Zero)) (HNone) (FEmpty) two (P3Z (Zero) (Succ (Zero)) (Succ (Zero)) p) rules (C1None ctx rules)
        (C1Empty (Cons (Digit) (D1) ctx) rules)
        (c1-ins (Cons (Digit) (D2) ctx) x1 (Zero) (FEmpty) (Succ (Zero)) two q rules (C1Empty (Cons (Digit) (D2) ctx) rules))))
    ((InsHere n1 n2 m ty one two p)
      (match erased c _
        ((C1Node c0 h0 a0 b0 m0 here0 one0 two0 p0 r0 ch c1 c2) (C1Node ctx (Succ (Zero)) n1 n2 (Succ m) (HFree ty) one two (P3S (Zero) n1 n2 m p) rules (C1Free ctx ty rules) c1 c2))))
    ((Ins1 x1 h n1 a2 m here one two p k1 m2 one2 p2 q)
      (match erased c _
        ((C1Node c0 h0 a0 b0 m0 here0 one0 two0 p0 r0 ch c1 c2) (C1Node ctx h k1 a2 m2 here one2 two p2 rules ch (c1-ins (Cons (Digit) (D1) ctx) x1 n1 one k1 one2 q rules c1) c2))))
    ((Ins2 x1 h n1 a2 m here one two p k2 m2 two2 p2 q)
      (match erased c _
        ((C1Node c0 h0 a0 b0 m0 here0 one0 two0 p0 r0 ch c1 c2) (C1Node ctx h n1 k2 m2 here one two2 p2 rules ch c1 (c1-ins (Cons (Digit) (D2) ctx) x1 a2 two k2 two2 q rules c2)))))))

(def-fns _ $ erased c1-out : (erased (List (Digit)) ctx) (erased (Bin) x) (erased (Bin) xg) (erased (Wrap ctx x xg) w) (erased (Term) t) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) k) (erased (Facts k) f2) (subterm erased (Out x t n f k f2) o)
    (erased (List (Rule)) rules) (erased (C1 ctx n f rules) c) (erased (List (Rule)) res) (erased (AppendR rules (MkRule xg t) res) ap) -> (erased (C1 ctx k f2 res) c2)
  (match erased o _
    ((OutHere n1 n2 m ty t0 one two p)
      (match erased c _
        ((C1Node c0 h0 a0 b0 m0 here0 one0 two0 p0 r0 ch c1 c2)
          (C1Node ctx (Zero) n1 n2 m (HRuled ty t0) one two p res
            (C1Ruled ctx ty t0 res (wrap-mw ctx (BZ) xg w t0 res (mem-last xg t0 rules res ap)))
            (c1-append (Cons (Digit) (D1) ctx) n1 one rules c1 (MkRule xg t) res ap)
            (c1-append (Cons (Digit) (D2) ctx) n2 two rules c2 (MkRule xg t) res ap)))))
    ((Out1 x1 t0 h n1 a2 m here one two p k1 m2 one2 p2 q)
      (match erased c _
        ((C1Node c0 h0 a0 b0 m0 here0 one0 two0 p0 r0 ch c1 c2)
          (C1Node ctx h k1 a2 m2 here one2 two p2 res (c1here-append ctx h here rules ch (MkRule xg t) res ap)
            (c1-out (Cons (Digit) (D1) ctx) x1 xg (W1 ctx x1 xg w) t n1 one k1 one2 q rules c1 res ap)
            (c1-append (Cons (Digit) (D2) ctx) a2 two rules c2 (MkRule xg t) res ap)))))
    ((Out2 x1 t0 h n1 a2 m here one two p k2 m2 two2 p2 q)
      (match erased c _
        ((C1Node c0 h0 a0 b0 m0 here0 one0 two0 p0 r0 ch c1 c2)
          (C1Node ctx h n1 k2 m2 here one two2 p2 res (c1here-append ctx h here rules ch (MkRule xg t) res ap)
            (c1-append (Cons (Digit) (D1) ctx) n1 one rules c1 (MkRule xg t) res ap)
            (c1-out (Cons (Digit) (D2) ctx) x1 xg (W2 ctx x1 xg w) t a2 two k2 two2 q rules c2 res ap)))))))

(def-fns _ $ erased keys-snoc : (erased (List (Bin)) seen) (erased (List (Rule)) rules) (erased (List (Bin)) ks) (subterm erased (Keys seen rules ks) k) (erased (Bin) x) (erased (Term) t) (erased (List (Rule)) res) (erased (AppendR rules (MkRule x t) res) ap) -> (erased (Keys seen res (Cons (Bin) x ks)) k2)
  (match erased k _
    ((KNil s) (match erased ap _ ((ApNil r) (KCons seen x t (Nil (Rule)) (Cons (Bin) x seen) (KNil (Cons (Bin) x seen))))))
    ((KCons s y u rest ks1 k1)
      (match erased ap _
        ((ApCons a rest2 r res2 ap2) (KCons seen y u res2 (Cons (Bin) x ks) (keys-snoc (Cons (Bin) y seen) rest ks k1 x t res2 ap2)))))))
; ---- Freshness: every variable of a term is a rule-free entry of a table. Canonicalization returns it.

(def-adts
  (Fr : ((Nat) n) ((Facts n) f) ((Term) t) -> Type
    enum
    (many FrVar : (erased (Nat) n) (erased (Facts n) f) (erased (Bin) x) (erased (In x n f) p) -> (Fr n f (TVar x)))
    (many FrBound : (erased (Nat) n) (erased (Facts n) f) (erased (Nat) k) -> (Fr n f (TBound k)))
    (many FrApp : (erased (Nat) n) (erased (Facts n) f) (erased (Term) h) (erased (List (Term)) args) (erased (Fr n f h) p) (erased (FrL n f args) q) -> (Fr n f (TApp h args)))
    (many FrFn : (erased (Nat) n) (erased (Facts n) f) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs) (erased (Fr n f l) p) (erased (FrT n f ps) q) (erased (FrT n f rs) r) -> (Fr n f (TFn l ps rs)))
    (many FrTyCtor : (erased (Nat) n) (erased (Facts n) f) (erased (List (Entry)) ps) (erased (FrT n f ps) q) -> (Fr n f (TTyCtor ps)))
    (many FrValCtor : (erased (Nat) n) (erased (Facts n) f) (erased (List (Entry)) ps) (erased (Term) ret) (erased (FrT n f ps) q) (erased (Fr n f ret) p) -> (Fr n f (TValCtor ps ret)))
    (many FrMatchable : (erased (Nat) n) (erased (Facts n) f) (erased (Disc) d) (erased (Term) ty) (erased (List (MCtor)) cs) (erased (Fr n f ty) p) (erased (FrM n f cs) q) -> (Fr n f (TMatchable d ty cs)))
    (many FrNewtype : (erased (Nat) n) (erased (Facts n) f) (erased (Term) c) (erased (Fr n f c) p) -> (Fr n f (TNewtype c)))
    (many FrErr : (erased (Nat) n) (erased (Facts n) f) (erased (String) m) -> (Fr n f (TErr m))))
  (FrL : ((Nat) n) ((Facts n) f) ((List (Term)) ts) -> Type
    enum
    (many FrLNil : (erased (Nat) n) (erased (Facts n) f) -> (FrL n f (Nil (Term))))
    (many FrLCons : (erased (Nat) n) (erased (Facts n) f) (erased (Term) t) (erased (List (Term)) rest) (erased (Fr n f t) p) (erased (FrL n f rest) q) -> (FrL n f (Cons (Term) t rest))))
  (FrT : ((Nat) n) ((Facts n) f) ((List (Entry)) es) -> Type
    enum
    (many FrTNil : (erased (Nat) n) (erased (Facts n) f) -> (FrT n f (Nil (Entry))))
    (many FrTCons : (erased (Nat) n) (erased (Facts n) f) (erased (Maybe (String)) nm) (erased (Bool) s) (erased (Mult) mu) (erased (Sg) sg) (erased (List (Entry)) rest) (erased (FrS n f sg) p) (erased (FrT n f rest) q) -> (FrT n f (Cons (Entry) (MkEntry nm s mu sg) rest))))
  (FrS : ((Nat) n) ((Facts n) f) ((Sg) sg) -> Type
    enum
    (many FrSTy : (erased (Nat) n) (erased (Facts n) f) (erased (Term) t) (erased (Fr n f t) p) -> (FrS n f (SgTy t)))
    (many FrSIs : (erased (Nat) n) (erased (Facts n) f) (erased (Term) t) (erased (Fr n f t) p) -> (FrS n f (SgIs t))))
  (FrM : ((Nat) n) ((Facts n) f) ((List (MCtor)) cs) -> Type
    enum
    (many FrMNil : (erased (Nat) n) (erased (Facts n) f) -> (FrM n f (Nil (MCtor))))
    (many FrMCons : (erased (Nat) n) (erased (Facts n) f) (erased (Mult) mu) (erased (Term) c) (erased (List (MCtor)) rest) (erased (Fr n f c) p) (erased (FrM n f rest) q) -> (FrM n f (Cons (MCtor) (MkMCtor mu c) rest)))))

; A guard for a term being canonicalized: nothing at the top, or a table in which the term is fresh and
; every key seen so far is ruled, which is how the term's variables are known not to be those keys.
(def-adts
  (Guard : ((Term) t) ((List (Bin)) seen) -> Type
    enum
    (many GTop : (erased (Term) t) -> (Guard t (Nil (Bin))))
    (many GAv : (erased (Term) t) (erased (List (Bin)) seen) (erased (Nat) n) (erased (Facts n) f) (erased (Fr n f t) p) (erased (AllRuled seen n f) a) -> (Guard t seen)))
  (GuardL : ((List (Term)) ts) ((List (Bin)) seen) -> Type
    enum
    (many GLTop : (erased (List (Term)) ts) -> (GuardL ts (Nil (Bin))))
    (many GLAv : (erased (List (Term)) ts) (erased (List (Bin)) seen) (erased (Nat) n) (erased (Facts n) f) (erased (FrL n f ts) p) (erased (AllRuled seen n f) a) -> (GuardL ts seen)))
  (GuardT : ((List (Entry)) es) ((List (Bin)) seen) -> Type
    enum
    (many GTTop : (erased (List (Entry)) es) -> (GuardT es (Nil (Bin))))
    (many GTAv : (erased (List (Entry)) es) (erased (List (Bin)) seen) (erased (Nat) n) (erased (Facts n) f) (erased (FrT n f es) p) (erased (AllRuled seen n f) a) -> (GuardT es seen)))
  (GuardS : ((Sg) sg) ((List (Bin)) seen) -> Type
    enum
    (many GSTop : (erased (Sg) sg) -> (GuardS sg (Nil (Bin))))
    (many GSAv : (erased (Sg) sg) (erased (List (Bin)) seen) (erased (Nat) n) (erased (Facts n) f) (erased (FrS n f sg) p) (erased (AllRuled seen n f) a) -> (GuardS sg seen)))
  (GuardM : ((List (MCtor)) cs) ((List (Bin)) seen) -> Type
    enum
    (many GMTop : (erased (List (MCtor)) cs) -> (GuardM cs (Nil (Bin))))
    (many GMAv : (erased (List (MCtor)) cs) (erased (List (Bin)) seen) (erased (Nat) n) (erased (Facts n) f) (erased (FrM n f cs) p) (erased (AllRuled seen n f) a) -> (GuardM cs seen))))

(def-fns _ $ erased fr-var : (erased (Nat) n) (erased (Facts n) f) (erased (Bin) x) (erased (Fr n f (TVar x)) p) -> (erased (In x n f) q)
  (match erased p _
    ((FrVar a b c q) q)))

(def-fns _ $ erased fr-app : (erased (Nat) n) (erased (Facts n) f) (erased (Term) h) (erased (List (Term)) args) (erased (Fr n f (TApp h args)) p) -> (erased (Fr n f h) ph) (erased (FrL n f args) pa)
  (match erased p _
    ((FrApp a b c d ph pa) (values ph pa))))

(def-fns _ $ erased fr-fn : (erased (Nat) n) (erased (Facts n) f) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs) (erased (Fr n f (TFn l ps rs)) p) -> (erased (Fr n f l) pl) (erased (FrT n f ps) pp) (erased (FrT n f rs) pr)
  (match erased p _
    ((FrFn a b c d e pl pp pr) (values pl pp pr))))

(def-fns _ $ erased fr-tyctor : (erased (Nat) n) (erased (Facts n) f) (erased (List (Entry)) ps) (erased (Fr n f (TTyCtor ps)) p) -> (erased (FrT n f ps) pp)
  (match erased p _
    ((FrTyCtor a b c pp) pp)))

(def-fns _ $ erased fr-valctor : (erased (Nat) n) (erased (Facts n) f) (erased (List (Entry)) ps) (erased (Term) ret) (erased (Fr n f (TValCtor ps ret)) p) -> (erased (FrT n f ps) pp) (erased (Fr n f ret) pr)
  (match erased p _
    ((FrValCtor a b c d pp pr) (values pp pr))))

(def-fns _ $ erased fr-matchable : (erased (Nat) n) (erased (Facts n) f) (erased (Disc) d) (erased (Term) ty) (erased (List (MCtor)) cs) (erased (Fr n f (TMatchable d ty cs)) p) -> (erased (Fr n f ty) pt) (erased (FrM n f cs) pc)
  (match erased p _
    ((FrMatchable a b c e g pt pc) (values pt pc))))

(def-fns _ $ erased fr-newtype : (erased (Nat) n) (erased (Facts n) f) (erased (Term) c) (erased (Fr n f (TNewtype c)) p) -> (erased (Fr n f c) pc)
  (match erased p _
    ((FrNewtype a b d pc) pc)))

(def-fns _ $ erased frl-cons : (erased (Nat) n) (erased (Facts n) f) (erased (Term) t) (erased (List (Term)) rest) (erased (FrL n f (Cons (Term) t rest)) p) -> (erased (Fr n f t) pt) (erased (FrL n f rest) pr)
  (match erased p _
    ((FrLCons a b c d pt pr) (values pt pr))))

(def-fns _ $ erased frt-cons : (erased (Nat) n) (erased (Facts n) f) (erased (Maybe (String)) nm) (erased (Bool) s) (erased (Mult) mu) (erased (Sg) sg) (erased (List (Entry)) rest) (erased (FrT n f (Cons (Entry) (MkEntry nm s mu sg) rest)) p) -> (erased (FrS n f sg) ps) (erased (FrT n f rest) pr)
  (match erased p _
    ((FrTCons a b c d e g h ps pr) (values ps pr))))

(def-fns _ $ erased frs-ty : (erased (Nat) n) (erased (Facts n) f) (erased (Term) t) (erased (FrS n f (SgTy t)) p) -> (erased (Fr n f t) pt)
  (match erased p _ ((FrSTy a b c pt) pt)))

(def-fns _ $ erased frs-is : (erased (Nat) n) (erased (Facts n) f) (erased (Term) t) (erased (FrS n f (SgIs t)) p) -> (erased (Fr n f t) pt)
  (match erased p _ ((FrSIs a b c pt) pt)))

(def-fns _ $ erased frm-cons : (erased (Nat) n) (erased (Facts n) f) (erased (Mult) mu) (erased (Term) c) (erased (List (MCtor)) rest) (erased (FrM n f (Cons (MCtor) (MkMCtor mu c) rest)) p) -> (erased (Fr n f c) pc) (erased (FrM n f rest) pr)
  (match erased p _
    ((FrMCons a b d e g pc pr) (values pc pr))))

(def-fns _ $ erased guard-app : (erased (Term) h) (erased (List (Term)) args) (erased (List (Bin)) seen) (erased (Guard (TApp h args) seen) g) -> (erased (Guard h seen) gh) (erased (GuardL args seen) ga)
  (match erased g _
    ((GTop t) (values (GTop h) (GLTop args)))
    ((GAv t s n f p a)
      (let (erased ph) (erased pa) (fr-app n f h args p))
      (values (GAv h seen n f ph a) (GLAv args seen n f pa a)))))

(def-fns _ $ erased guard-fn : (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs) (erased (List (Bin)) seen) (erased (Guard (TFn l ps rs) seen) g) -> (erased (Guard l seen) gl) (erased (GuardT ps seen) gp) (erased (GuardT rs seen) gr)
  (match erased g _
    ((GTop t) (values (GTop l) (GTTop ps) (GTTop rs)))
    ((GAv t s n f p a)
      (let (erased pl) (erased pp) (erased pr) (fr-fn n f l ps rs p))
      (values (GAv l seen n f pl a) (GTAv ps seen n f pp a) (GTAv rs seen n f pr a)))))

(def-fns _ $ erased guard-tyctor : (erased (List (Entry)) ps) (erased (List (Bin)) seen) (erased (Guard (TTyCtor ps) seen) g) -> (erased (GuardT ps seen) gp)
  (match erased g _
    ((GTop t) (GTTop ps))
    ((GAv t s n f p a) (GTAv ps seen n f (fr-tyctor n f ps p) a))))

(def-fns _ $ erased guard-valctor : (erased (List (Entry)) ps) (erased (Term) ret) (erased (List (Bin)) seen) (erased (Guard (TValCtor ps ret) seen) g) -> (erased (GuardT ps seen) gp) (erased (Guard ret seen) gr)
  (match erased g _
    ((GTop t) (values (GTTop ps) (GTop ret)))
    ((GAv t s n f p a)
      (let (erased pp) (erased pr) (fr-valctor n f ps ret p))
      (values (GTAv ps seen n f pp a) (GAv ret seen n f pr a)))))

(def-fns _ $ erased guard-matchable : (erased (Disc) d) (erased (Term) ty) (erased (List (MCtor)) cs) (erased (List (Bin)) seen) (erased (Guard (TMatchable d ty cs) seen) g) -> (erased (Guard ty seen) gt) (erased (GuardM cs seen) gc)
  (match erased g _
    ((GTop t) (values (GTop ty) (GMTop cs)))
    ((GAv t s n f p a)
      (let (erased pt) (erased pc) (fr-matchable n f d ty cs p))
      (values (GAv ty seen n f pt a) (GMAv cs seen n f pc a)))))

(def-fns _ $ erased guard-newtype : (erased (Term) c) (erased (List (Bin)) seen) (erased (Guard (TNewtype c) seen) g) -> (erased (Guard c seen) gc)
  (match erased g _
    ((GTop t) (GTop c))
    ((GAv t s n f p a) (GAv c seen n f (fr-newtype n f c p) a))))

(def-fns _ $ erased guardl-cons : (erased (Term) t) (erased (List (Term)) rest) (erased (List (Bin)) seen) (erased (GuardL (Cons (Term) t rest) seen) g) -> (erased (Guard t seen) gt) (erased (GuardL rest seen) gr)
  (match erased g _
    ((GLTop ts) (values (GTop t) (GLTop rest)))
    ((GLAv ts s n f p a)
      (let (erased pt) (erased pr) (frl-cons n f t rest p))
      (values (GAv t seen n f pt a) (GLAv rest seen n f pr a)))))

(def-fns _ $ erased guardt-cons : (erased (Maybe (String)) nm) (erased (Bool) s) (erased (Mult) mu) (erased (Sg) sg) (erased (List (Entry)) rest) (erased (List (Bin)) seen) (erased (GuardT (Cons (Entry) (MkEntry nm s mu sg) rest) seen) g) -> (erased (GuardS sg seen) gs) (erased (GuardT rest seen) gr)
  (match erased g _
    ((GTTop es) (values (GSTop sg) (GTTop rest)))
    ((GTAv es s0 n f p a)
      (let (erased ps) (erased pr) (frt-cons n f nm s mu sg rest p))
      (values (GSAv sg seen n f ps a) (GTAv rest seen n f pr a)))))

(def-fns _ $ erased guards-ty : (erased (Term) t) (erased (List (Bin)) seen) (erased (GuardS (SgTy t) seen) g) -> (erased (Guard t seen) gt)
  (match erased g _
    ((GSTop sg) (GTop t))
    ((GSAv sg s n f p a) (GAv t seen n f (frs-ty n f t p) a))))

(def-fns _ $ erased guards-is : (erased (Term) t) (erased (List (Bin)) seen) (erased (GuardS (SgIs t) seen) g) -> (erased (Guard t seen) gt)
  (match erased g _
    ((GSTop sg) (GTop t))
    ((GSAv sg s n f p a) (GAv t seen n f (frs-is n f t p) a))))

(def-fns _ $ erased guardm-cons : (erased (Mult) mu) (erased (Term) c) (erased (List (MCtor)) rest) (erased (List (Bin)) seen) (erased (GuardM (Cons (MCtor) (MkMCtor mu c) rest) seen) g) -> (erased (Guard c seen) gc) (erased (GuardM rest seen) gr)
  (match erased g _
    ((GMTop cs) (values (GTop c) (GMTop rest)))
    ((GMAv cs s n f p a)
      (let (erased pc) (erased pr) (frm-cons n f mu c rest p))
      (values (GAv c seen n f pc a) (GMAv rest seen n f pr a)))))

; ---- The order of the rules list and the position of a chase in it.

(def-adts
  (Ord : ((List (Bin)) seen) ((List (Rule)) rules) -> Type
    enum
    (many OrdNil : (erased (List (Bin)) seen) -> (Ord seen (Nil (Rule))))
    (many OrdCons : (erased (List (Bin)) seen) (erased (Bin) x) (erased (Term) t) (erased (List (Rule)) rest) (erased (Guard t (Cons (Bin) x seen)) g) (erased (Ord (Cons (Bin) x seen) rest) o) -> (Ord seen (Cons (Rule) (MkRule x t) rest))))
  (Prefix : ((List (Bin)) seen) ((List (Rule)) whole) ((List (Rule)) after) -> Type
    enum
    (many PNil : (erased (List (Rule)) whole) -> (Prefix (Nil (Bin)) whole whole))
    (many PCons : (erased (List (Bin)) seen) (erased (List (Rule)) whole) (erased (Bin) x) (erased (Term) t) (erased (List (Rule)) after) (erased (Prefix seen whole (Cons (Rule) (MkRule x t) after)) p) -> (Prefix (Cons (Bin) x seen) whole after)))
  (Found : ((List (Bin)) seen) ((List (Rule)) whole) ((List (Rule)) after) -> Type
    enum
    (many MkFound : (erased (List (Bin)) seen) (erased (List (Rule)) whole) (erased (List (Rule)) after) (many (Term) t) (many (List (Rule)) after2) (erased (List (Bin)) seen2)
       (erased (Prefix seen2 whole after2) pre) (erased (Ord seen2 after2) ord) (erased (Guard t seen2) g) (erased (Subterm (List (Rule)) after2 (List (Rule)) after) sub) -> (Found seen whole after))))

(def-fns _ $ erased ord-snoc : (erased (List (Bin)) seen) (erased (List (Rule)) rules) (subterm erased (Ord seen rules) o) (erased (List (Bin)) ks) (erased (Keys seen rules ks) k) (erased (Bin) x) (erased (Term) t) (erased (List (Rule)) res) (erased (AppendR rules (MkRule x t) res) ap) (erased (Guard t (Cons (Bin) x ks)) g) -> (erased (Ord seen res) o2)
  (match erased o _
    ((OrdNil s)
      (match erased k _
        ((KNil s1) (match erased ap _ ((ApNil r) (OrdCons seen x t (Nil (Rule)) g (OrdNil (Cons (Bin) x seen))))))))
    ((OrdCons s y u rest g1 o1)
      (match erased k _
        ((KCons s1 y1 u1 rest1 ks1 k1)
          (match erased ap _
            ((ApCons a rest2 r res2 ap2) (OrdCons seen y u res2 g1 (ord-snoc (Cons (Bin) y seen) rest o1 ks k1 x t res2 ap2 g)))))))))

(def-fns _ $ erased guard-weaken : (erased (Term) t) (erased (Bin) x) (erased (List (Bin)) seen) (erased (Guard t (Cons (Bin) x seen)) g) -> (erased (Guard t seen) g2)
  (match erased g _
    ((GAv t0 s n f p a) (match erased a _ ((ARCons z ks n1 f1 r rest) (GAv t seen n f p rest))))))

(def-fns _ $ erased guard-clash : (erased (Bin) v) (erased (List (Bin)) seen) (erased (Guard (TVar v) (Cons (Bin) v seen)) g) -> (erased (False) r)
  (match erased g _
    ((GAv t0 s n f p a)
      (match erased a _
        ((ARCons z ks n1 f1 r rest) (in-ruled-clash v n f (fr-var n f v p) r))))))

; A ruled variable met inside a rule's term has its rule after that rule: the guard rules it out of the
; keys before, and agreement puts it somewhere.
(def-fns _ $ erased mem-after : (erased (List (Bin)) seen) (erased (List (Rule)) whole) (erased (List (Rule)) after) (subterm erased (Prefix seen whole after) pre) (erased (Bin) v) (erased (Term) t) (erased (MemRule v t whole) m) (erased (Guard (TVar v) seen) g) -> (erased (MemRule v t after) m2)
  (match erased pre _
    ((PNil w) m)
    ((PCons s w x u after0 pre1)
      (match erased (mem-after s whole (Cons (Rule) (MkRule x u) after) pre1 v t m (guard-weaken (TVar v) x s g)) _
        (absurd (MRHere v1 t1 rest1) (guard-clash v s g))
        ((MRThere v1 t1 r1 rest1 m1) m1)))))

(def-fns _ $ many find-rule : (subterm many (List (Rule)) after) (many (Bin) x) (erased (List (Bin)) seen) (erased (List (Rule)) whole) (erased (Prefix seen whole after) pre) (erased (Ord seen after) ord) (erased (Term) t0) (erased (MemRule x t0 after) m) -> (many (Found seen whole after) r)
  (match many after _
    (absurd (Nil a) (match erased m (((False) f))))
    ((Cons a rule rest)
      (match many rule _
        ((MkRule y t)
          (let (erased g) (match erased ord (((Guard t (Cons (Bin) y seen)) g)) ((OrdCons s1 y1 t1 r1 g o) g)))
          (let (erased o) (match erased ord (((Ord (Cons (Bin) y seen) rest) o)) ((OrdCons s1 y1 t1 r1 g o) o)))
          (let (erased pre2) (PCons seen whole y t rest pre))
          (match many (bin-eq-dec x y) _
            ((BYes a1 b1 e) (MkFound seen whole after t rest (Cons (Bin) y seen) pre2 o g (prove-subterm rest after)))
            ((BNo a1 b1 ne)
              (let (erased m2) (match erased m (((MemRule x t0 rest) m2)) ((MRThere x1 t1 r1 rest1 m2) m2) (absurd (MRHere x1 t1 rest1) (neq-irrefl x ne))))
              (match many (find-rule rest x (Cons (Bin) y seen) whole pre2 o t0 m2) _
                ((MkFound s2 w2 a2 t2 after3 seen3 pre3 ord3 g3 sub) (MkFound seen whole after t2 after3 seen3 pre3 ord3 g3 (subterm-trans sub (prove-subterm rest after))))))))))))
; ---- Canonicalization (sections 5, 18): a chase continues along the rules after the one followed, the
; guard and the agreement proofs saying the rule is there; the result comes with its freshness.

(def-fns _
  (many canon : (subterm many (List (Rule)) after) (subterm many (Term) t) (erased (Nat) n) (many (Facts n) f) (erased (List (Rule)) whole) (erased (List (Bin)) seen) (erased (Prefix seen whole after) pre) (erased (Ord seen after) ord) (erased (Guard t seen) g) (erased (C1 (Nil (Digit)) n f whole) c) ->
      (many (Term) r) (erased (Fr n f r) fr)
    (match many t _
      ((TVar x)
        (match many (facts-lookup x n f (Nil (Digit)) x (WNil x) whole c) _
          ((LNone a b d e h)
            (let (many msg) (str-cat "no fact for " (bin-str x)))
            (values (TErr msg) (FrErr n f msg)))
          ((LFree a b d e h ty p) (values t (FrVar n f x p)))
          ((LRuled a b d e h ty r0 m)
            (match many (find-rule after x seen whole pre ord r0 (mem-after seen whole after pre x r0 m g)) _
              ((MkFound s w a2 r after2 seen2 pre2 ord2 g2 sub) (canon (subterm sub) after2 r n f whole seen2 pre2 ord2 g2 c))))))
      ((TBound k) (values t (FrBound n f k)))
      ((TApp h args)
        (let (erased gh) (erased ga) (guard-app h args seen g))
        (let (many h2) (erased fh) (canon after h n f whole seen pre ord gh c))
        (let (many args2) (erased fa) (canon-list after args n f whole seen pre ord ga c))
        (values (TApp h2 args2) (FrApp n f h2 args2 fh fa)))
      ((TFn l ps rs)
        (let (erased gl) (erased gp) (erased gr) (guard-fn l ps rs seen g))
        (let (many l2) (erased fl) (canon after l n f whole seen pre ord gl c))
        (let (many ps2) (erased fp) (canon-tele after ps n f whole seen pre ord gp c))
        (let (many rs2) (erased frs) (canon-tele after rs n f whole seen pre ord gr c))
        (values (TFn l2 ps2 rs2) (FrFn n f l2 ps2 rs2 fl fp frs)))
      ((TTyCtor ps)
        (let (erased gp) (guard-tyctor ps seen g))
        (let (many ps2) (erased fp) (canon-tele after ps n f whole seen pre ord gp c))
        (values (TTyCtor ps2) (FrTyCtor n f ps2 fp)))
      ((TValCtor ps ret)
        (let (erased gp) (erased gr) (guard-valctor ps ret seen g))
        (let (many ps2) (erased fp) (canon-tele after ps n f whole seen pre ord gp c))
        (let (many ret2) (erased fret) (canon after ret n f whole seen pre ord gr c))
        (values (TValCtor ps2 ret2) (FrValCtor n f ps2 ret2 fp fret)))
      ((TMatchable d ty cs)
        (let (erased gt) (erased gc) (guard-matchable d ty cs seen g))
        (let (many ty2) (erased ft) (canon after ty n f whole seen pre ord gt c))
        (let (many cs2) (erased fc) (canon-mctors after cs n f whole seen pre ord gc c))
        (values (TMatchable d ty2 cs2) (FrMatchable n f d ty2 cs2 ft fc)))
      ((TNewtype cn)
        (let (erased gc) (guard-newtype cn seen g))
        (let (many cn2) (erased fc) (canon after cn n f whole seen pre ord gc c))
        (values (TNewtype cn2) (FrNewtype n f cn2 fc)))
      ((TErr m) (values t (FrErr n f m)))))
  (many canon-list : (subterm many (List (Rule)) after) (subterm many (List (Term)) ts) (erased (Nat) n) (many (Facts n) f) (erased (List (Rule)) whole) (erased (List (Bin)) seen) (erased (Prefix seen whole after) pre) (erased (Ord seen after) ord) (erased (GuardL ts seen) g) (erased (C1 (Nil (Digit)) n f whole) c) ->
      (many (List (Term)) r) (erased (FrL n f r) fr)
    (match many ts _
      ((Nil a) (values ts (FrLNil n f)))
      ((Cons a t rest)
        (let (erased gt) (erased gr) (guardl-cons t rest seen g))
        (let (many t2) (erased ft) (canon after t n f whole seen pre ord gt c))
        (let (many rest2) (erased frest) (canon-list after rest n f whole seen pre ord gr c))
        (values (Cons (Term) t2 rest2) (FrLCons n f t2 rest2 ft frest)))))
  (many canon-tele : (subterm many (List (Rule)) after) (subterm many (List (Entry)) es) (erased (Nat) n) (many (Facts n) f) (erased (List (Rule)) whole) (erased (List (Bin)) seen) (erased (Prefix seen whole after) pre) (erased (Ord seen after) ord) (erased (GuardT es seen) g) (erased (C1 (Nil (Digit)) n f whole) c) ->
      (many (List (Entry)) r) (erased (FrT n f r) fr)
    (match many es _
      ((Nil a) (values es (FrTNil n f)))
      ((Cons a e rest)
        (match many e _
          ((MkEntry nm s mu sg)
            (let (erased gs) (erased gr) (guardt-cons nm s mu sg rest seen g))
            (let (many sg2) (erased fs) (canon-sg after sg n f whole seen pre ord gs c))
            (let (many rest2) (erased frest) (canon-tele after rest n f whole seen pre ord gr c))
            (values (Cons (Entry) (MkEntry nm s mu sg2) rest2) (FrTCons n f nm s mu sg2 rest2 fs frest)))))))
  (many canon-sg : (subterm many (List (Rule)) after) (subterm many (Sg) sg) (erased (Nat) n) (many (Facts n) f) (erased (List (Rule)) whole) (erased (List (Bin)) seen) (erased (Prefix seen whole after) pre) (erased (Ord seen after) ord) (erased (GuardS sg seen) g) (erased (C1 (Nil (Digit)) n f whole) c) ->
      (many (Sg) r) (erased (FrS n f r) fr)
    (match many sg _
      ((SgTy t)
        (let (erased gt) (guards-ty t seen g))
        (let (many t2) (erased ft) (canon after t n f whole seen pre ord gt c))
        (values (SgTy t2) (FrSTy n f t2 ft)))
      ((SgIs t)
        (let (erased gt) (guards-is t seen g))
        (let (many t2) (erased ft) (canon after t n f whole seen pre ord gt c))
        (values (SgIs t2) (FrSIs n f t2 ft)))))
  (many canon-mctors : (subterm many (List (Rule)) after) (subterm many (List (MCtor)) cs) (erased (Nat) n) (many (Facts n) f) (erased (List (Rule)) whole) (erased (List (Bin)) seen) (erased (Prefix seen whole after) pre) (erased (Ord seen after) ord) (erased (GuardM cs seen) g) (erased (C1 (Nil (Digit)) n f whole) c) ->
      (many (List (MCtor)) r) (erased (FrM n f r) fr)
    (match many cs _
      ((Nil a) (values cs (FrMNil n f)))
      ((Cons a mc rest)
        (match many mc _
          ((MkMCtor mu t)
            (let (erased gt) (erased gr) (guardm-cons mu t rest seen g))
            (let (many t2) (erased ft) (canon after t n f whole seen pre ord gt c))
            (let (many rest2) (erased frest) (canon-mctors after rest n f whole seen pre ord gr c))
            (values (Cons (MCtor) (MkMCtor mu t2) rest2) (FrMCons n f mu t2 rest2 ft frest))))))))

; ---- The occurs check, as a freshness proof against the table with the variable ruled out.

(def-adts
  (FrBox : ((Nat) n) ((Facts n) f) ((Term) t) -> Type
    enum
    (many MkFrBox : (erased (Nat) n) (erased (Facts n) f) (erased (Term) t) (erased (Fr n f t) p) -> (FrBox n f t)))
  (FrLBox : ((Nat) n) ((Facts n) f) ((List (Term)) ts) -> Type
    enum
    (many MkFrLBox : (erased (Nat) n) (erased (Facts n) f) (erased (List (Term)) ts) (erased (FrL n f ts) p) -> (FrLBox n f ts)))
  (FrTBox : ((Nat) n) ((Facts n) f) ((List (Entry)) es) -> Type
    enum
    (many MkFrTBox : (erased (Nat) n) (erased (Facts n) f) (erased (List (Entry)) es) (erased (FrT n f es) p) -> (FrTBox n f es)))
  (FrSBox : ((Nat) n) ((Facts n) f) ((Sg) sg) -> Type
    enum
    (many MkFrSBox : (erased (Nat) n) (erased (Facts n) f) (erased (Sg) sg) (erased (FrS n f sg) p) -> (FrSBox n f sg)))
  (FrMBox : ((Nat) n) ((Facts n) f) ((List (MCtor)) cs) -> Type
    enum
    (many MkFrMBox : (erased (Nat) n) (erased (Facts n) f) (erased (List (MCtor)) cs) (erased (FrM n f cs) p) -> (FrMBox n f cs))))

(def-fns _
  (many refresh : (subterm many (Term) t) (erased (Nat) n) (many (Facts n) f) (erased (List (Rule)) rules) (erased (C1 (Nil (Digit)) n f rules) c) -> (many (Maybe (FrBox n f t)) r)
    (match many t _
      ((TVar x)
        (match many (facts-lookup x n f (Nil (Digit)) x (WNil x) rules c) _
          ((LFree a b d e h ty p) (Some (FrBox n f t) (MkFrBox n f t (FrVar n f x p)))) (else (None (FrBox n f t)))))
      ((TBound k) (Some (FrBox n f t) (MkFrBox n f t (FrBound n f k))))
      ((TApp h args)
        (match many (refresh h n f rules c) _
          ((None a) (None (FrBox n f t)))
          ((Some a bh)
            (match many (refresh-list args n f rules c) _
              ((None b) (None (FrBox n f t)))
              ((Some b ba)
                (match many bh _ ((MkFrBox a1 b1 c1 ph) (match many ba _ ((MkFrLBox a2 b2 c2 pa) (Some (FrBox n f t) (MkFrBox n f t (FrApp n f h args ph pa))))))))))))
      ((TFn l ps rs)
        (match many (refresh l n f rules c) _
          ((None a) (None (FrBox n f t)))
          ((Some a bl)
            (match many (refresh-tele ps n f rules c) _
              ((None b) (None (FrBox n f t)))
              ((Some b bp)
                (match many (refresh-tele rs n f rules c) _
                  ((None d) (None (FrBox n f t)))
                  ((Some d br)
                    (match many bl _ ((MkFrBox a1 b1 c1 pl) (match many bp _ ((MkFrTBox a2 b2 c2 pp) (match many br _ ((MkFrTBox a3 b3 c3 pr) (Some (FrBox n f t) (MkFrBox n f t (FrFn n f l ps rs pl pp pr))))))))))))))))
      ((TTyCtor ps)
        (match many (refresh-tele ps n f rules c) _
          ((None a) (None (FrBox n f t)))
          ((Some a bp) (match many bp _ ((MkFrTBox a2 b2 c2 pp) (Some (FrBox n f t) (MkFrBox n f t (FrTyCtor n f ps pp))))))))
      ((TValCtor ps ret)
        (match many (refresh-tele ps n f rules c) _
          ((None a) (None (FrBox n f t)))
          ((Some a bp)
            (match many (refresh ret n f rules c) _
              ((None b) (None (FrBox n f t)))
              ((Some b bret)
                (match many bp _ ((MkFrTBox a2 b2 c2 pp) (match many bret _ ((MkFrBox a3 b3 c3 pr) (Some (FrBox n f t) (MkFrBox n f t (FrValCtor n f ps ret pp pr))))))))))))
      ((TMatchable d ty cs)
        (match many (refresh ty n f rules c) _
          ((None a) (None (FrBox n f t)))
          ((Some a bt)
            (match many (refresh-mctors cs n f rules c) _
              ((None b) (None (FrBox n f t)))
              ((Some b bc)
                (match many bt _ ((MkFrBox a2 b2 c2 pt) (match many bc _ ((MkFrMBox a3 b3 c3 pc) (Some (FrBox n f t) (MkFrBox n f t (FrMatchable n f d ty cs pt pc))))))))))))
      ((TNewtype cn)
        (match many (refresh cn n f rules c) _
          ((None a) (None (FrBox n f t)))
          ((Some a bc) (match many bc _ ((MkFrBox a2 b2 c2 pc) (Some (FrBox n f t) (MkFrBox n f t (FrNewtype n f cn pc))))))))
      ((TErr m) (Some (FrBox n f t) (MkFrBox n f t (FrErr n f m))))))
  (many refresh-list : (subterm many (List (Term)) ts) (erased (Nat) n) (many (Facts n) f) (erased (List (Rule)) rules) (erased (C1 (Nil (Digit)) n f rules) c) -> (many (Maybe (FrLBox n f ts)) r)
    (match many ts _
      ((Nil a) (Some (FrLBox n f ts) (MkFrLBox n f ts (FrLNil n f))))
      ((Cons a t rest)
        (match many (refresh t n f rules c) _
          ((None b) (None (FrLBox n f ts)))
          ((Some b bt)
            (match many (refresh-list rest n f rules c) _
              ((None d) (None (FrLBox n f ts)))
              ((Some d br)
                (match many bt _ ((MkFrBox a2 b2 c2 pt) (match many br _ ((MkFrLBox a3 b3 c3 pr) (Some (FrLBox n f ts) (MkFrLBox n f ts (FrLCons n f t rest pt pr))))))))))))))
  (many refresh-tele : (subterm many (List (Entry)) es) (erased (Nat) n) (many (Facts n) f) (erased (List (Rule)) rules) (erased (C1 (Nil (Digit)) n f rules) c) -> (many (Maybe (FrTBox n f es)) r)
    (match many es _
      ((Nil a) (Some (FrTBox n f es) (MkFrTBox n f es (FrTNil n f))))
      ((Cons a e rest)
        (match many e _
          ((MkEntry nm s mu sg)
            (match many (refresh-sg sg n f rules c) _
              ((None b) (None (FrTBox n f es)))
              ((Some b bs)
                (match many (refresh-tele rest n f rules c) _
                  ((None d) (None (FrTBox n f es)))
                  ((Some d br)
                    (match many bs _ ((MkFrSBox a2 b2 c2 ps) (match many br _ ((MkFrTBox a3 b3 c3 pr) (Some (FrTBox n f es) (MkFrTBox n f es (FrTCons n f nm s mu sg rest ps pr))))))))))))))))
  (many refresh-sg : (subterm many (Sg) sg) (erased (Nat) n) (many (Facts n) f) (erased (List (Rule)) rules) (erased (C1 (Nil (Digit)) n f rules) c) -> (many (Maybe (FrSBox n f sg)) r)
    (match many sg _
      ((SgTy t)
        (match many (refresh t n f rules c) _
          ((None a) (None (FrSBox n f sg)))
          ((Some a bt) (match many bt _ ((MkFrBox a2 b2 c2 pt) (Some (FrSBox n f sg) (MkFrSBox n f sg (FrSTy n f t pt))))))))
      ((SgIs t)
        (match many (refresh t n f rules c) _
          ((None a) (None (FrSBox n f sg)))
          ((Some a bt) (match many bt _ ((MkFrBox a2 b2 c2 pt) (Some (FrSBox n f sg) (MkFrSBox n f sg (FrSIs n f t pt))))))))))
  (many refresh-mctors : (subterm many (List (MCtor)) cs) (erased (Nat) n) (many (Facts n) f) (erased (List (Rule)) rules) (erased (C1 (Nil (Digit)) n f rules) c) -> (many (Maybe (FrMBox n f cs)) r)
    (match many cs _
      ((Nil a) (Some (FrMBox n f cs) (MkFrMBox n f cs (FrMNil n f))))
      ((Cons a mc rest)
        (match many mc _
          ((MkMCtor mu t)
            (match many (refresh t n f rules c) _
              ((None b) (None (FrMBox n f cs)))
              ((Some b bt)
                (match many (refresh-mctors rest n f rules c) _
                  ((None d) (None (FrMBox n f cs)))
                  ((Some d br)
                    (match many bt _ ((MkFrBox a2 b2 c2 pt) (match many br _ ((MkFrMBox a3 b3 c3 pr) (Some (FrMBox n f cs) (MkFrMBox n f cs (FrMCons n f mu t rest pt pr)))))))))))))))))

; ---- A fresh variable's own rule: freshness before the variable was inserted survives its insertion and
; its ruling out, since no path of the term's variables is the new one's.

(def-fns _ $ erased in-ins-out : (erased (Bin) z) (erased (Bin) x) (erased (Term) t) (erased (Nat) n0) (erased (Facts n0) f0) (erased (Nat) n1) (erased (Facts n1) f1) (erased (Nat) k) (erased (Facts k) f2)
    (subterm erased (Ins x n0 f0 n1 f1) i) (erased (Out x t n1 f1 k f2) o) (erased (In z n0 f0) p) -> (erased (In z k f2) q)
  (match erased i _
    ((InsLeaf ty pp) (match erased p _))
    ((InsGrow1 x1 one q1 pp) (match erased p _))
    ((InsGrow2 x1 two q1 pp) (match erased p _))
    ((InsHere n1 n2 m ty one two pp)
      (match erased o _
        ((OutHere a1 a2 a3 ty0 t0 one0 two0 p0)
          (match erased p _
            ((In1 z1 h b1 b2 b3 here1 one1 two1 p1 q1) (In1 z1 (Zero) n1 n2 m (HRuled ty t) one two pp q1))
            ((In2 z1 h b1 b2 b3 here1 one1 two1 p1 q1) (In2 z1 (Zero) n1 n2 m (HRuled ty t) one two pp q1))))))
    ((Ins1 x1 h n1 a2 m here one two pp k1 m2 one2 p2 q1)
      (match erased o _
        ((Out1 x2 t0 h0 b1 b2 b3 here0 one0 two0 p0 k3 m3 one3 p3 q2)
          (match erased p _
            ((InHere c1 c2 c3 ty one1 two1 p1) (InHere k3 a2 m3 ty one3 two p3))
            ((In1 z1 h1 c1 c2 c3 here1 one1 two1 p1 q3) (In1 z1 h k3 a2 m3 here one3 two p3 (in-ins-out z1 x1 t n1 one k1 one2 k3 one3 q1 q2 q3)))
            ((In2 z1 h1 c1 c2 c3 here1 one1 two1 p1 q3) (In2 z1 h k3 a2 m3 here one3 two p3 q3))))))
    ((Ins2 x1 h n1 a2 m here one two pp k2 m2 two2 p2 q1)
      (match erased o _
        ((Out2 x2 t0 h0 b1 b2 b3 here0 one0 two0 p0 k3 m3 two3 p3 q2)
          (match erased p _
            ((InHere c1 c2 c3 ty one1 two1 p1) (InHere n1 k3 m3 ty one two3 p3))
            ((In1 z1 h1 c1 c2 c3 here1 one1 two1 p1 q3) (In1 z1 h n1 k3 m3 here one two3 p3 q3))
            ((In2 z1 h1 c1 c2 c3 here1 one1 two1 p1 q3) (In2 z1 h n1 k3 m3 here one two3 p3 (in-ins-out z1 x1 t a2 two k2 two2 k3 two3 q1 q2 q3)))))))))

(def-fns _
  (erased fresh-ins-out : (erased (Bin) x) (erased (Term) t) (erased (Nat) n0) (erased (Facts n0) f0) (erased (Nat) n1) (erased (Facts n1) f1) (erased (Nat) k) (erased (Facts k) f2) (erased (Ins x n0 f0 n1 f1) i) (erased (Out x t n1 f1 k f2) o) (erased (Term) u) (subterm erased (Fr n0 f0 u) p) -> (erased (Fr k f2 u) q)
    (match erased p _
      ((FrVar a b z pz) (FrVar k f2 z (in-ins-out z x t n0 f0 n1 f1 k f2 i o pz)))
      ((FrBound a b kk) (FrBound k f2 kk))
      ((FrApp a b h args ph pa) (FrApp k f2 h args (fresh-ins-out x t n0 f0 n1 f1 k f2 i o h ph) (fresh-ins-out-list x t n0 f0 n1 f1 k f2 i o args pa)))
      ((FrFn a b l ps rs pl pp pr) (FrFn k f2 l ps rs (fresh-ins-out x t n0 f0 n1 f1 k f2 i o l pl) (fresh-ins-out-tele x t n0 f0 n1 f1 k f2 i o ps pp) (fresh-ins-out-tele x t n0 f0 n1 f1 k f2 i o rs pr)))
      ((FrTyCtor a b ps pp) (FrTyCtor k f2 ps (fresh-ins-out-tele x t n0 f0 n1 f1 k f2 i o ps pp)))
      ((FrValCtor a b ps ret pp pr) (FrValCtor k f2 ps ret (fresh-ins-out-tele x t n0 f0 n1 f1 k f2 i o ps pp) (fresh-ins-out x t n0 f0 n1 f1 k f2 i o ret pr)))
      ((FrMatchable a b d ty cs pt pc) (FrMatchable k f2 d ty cs (fresh-ins-out x t n0 f0 n1 f1 k f2 i o ty pt) (fresh-ins-out-mctors x t n0 f0 n1 f1 k f2 i o cs pc)))
      ((FrNewtype a b cn pc) (FrNewtype k f2 cn (fresh-ins-out x t n0 f0 n1 f1 k f2 i o cn pc)))
      ((FrErr a b m) (FrErr k f2 m))))
  (erased fresh-ins-out-list : (erased (Bin) x) (erased (Term) t) (erased (Nat) n0) (erased (Facts n0) f0) (erased (Nat) n1) (erased (Facts n1) f1) (erased (Nat) k) (erased (Facts k) f2) (erased (Ins x n0 f0 n1 f1) i) (erased (Out x t n1 f1 k f2) o) (erased (List (Term)) us) (subterm erased (FrL n0 f0 us) p) -> (erased (FrL k f2 us) q)
    (match erased p _
      ((FrLNil a b) (FrLNil k f2))
      ((FrLCons a b u rest pu pr) (FrLCons k f2 u rest (fresh-ins-out x t n0 f0 n1 f1 k f2 i o u pu) (fresh-ins-out-list x t n0 f0 n1 f1 k f2 i o rest pr)))))
  (erased fresh-ins-out-tele : (erased (Bin) x) (erased (Term) t) (erased (Nat) n0) (erased (Facts n0) f0) (erased (Nat) n1) (erased (Facts n1) f1) (erased (Nat) k) (erased (Facts k) f2) (erased (Ins x n0 f0 n1 f1) i) (erased (Out x t n1 f1 k f2) o) (erased (List (Entry)) es) (subterm erased (FrT n0 f0 es) p) -> (erased (FrT k f2 es) q)
    (match erased p _
      ((FrTNil a b) (FrTNil k f2))
      ((FrTCons a b nm s mu sg rest ps pr) (FrTCons k f2 nm s mu sg rest (fresh-ins-out-sg x t n0 f0 n1 f1 k f2 i o sg ps) (fresh-ins-out-tele x t n0 f0 n1 f1 k f2 i o rest pr)))))
  (erased fresh-ins-out-sg : (erased (Bin) x) (erased (Term) t) (erased (Nat) n0) (erased (Facts n0) f0) (erased (Nat) n1) (erased (Facts n1) f1) (erased (Nat) k) (erased (Facts k) f2) (erased (Ins x n0 f0 n1 f1) i) (erased (Out x t n1 f1 k f2) o) (erased (Sg) sg) (subterm erased (FrS n0 f0 sg) p) -> (erased (FrS k f2 sg) q)
    (match erased p _
      ((FrSTy a b u pu) (FrSTy k f2 u (fresh-ins-out x t n0 f0 n1 f1 k f2 i o u pu)))
      ((FrSIs a b u pu) (FrSIs k f2 u (fresh-ins-out x t n0 f0 n1 f1 k f2 i o u pu)))))
  (erased fresh-ins-out-mctors : (erased (Bin) x) (erased (Term) t) (erased (Nat) n0) (erased (Facts n0) f0) (erased (Nat) n1) (erased (Facts n1) f1) (erased (Nat) k) (erased (Facts k) f2) (erased (Ins x n0 f0 n1 f1) i) (erased (Out x t n1 f1 k f2) o) (erased (List (MCtor)) cs) (subterm erased (FrM n0 f0 cs) p) -> (erased (FrM k f2 cs) q)
    (match erased p _
      ((FrMNil a b) (FrMNil k f2))
      ((FrMCons a b mu cn rest pc pr) (FrMCons k f2 mu cn rest (fresh-ins-out x t n0 f0 n1 f1 k f2 i o cn pc) (fresh-ins-out-mctors x t n0 f0 n1 f1 k f2 i o rest pr))))))

; ---- The table: the facts, the rules, and the erased invariants that make canonicalization complete.

(def-adts
  (Table : ((Nat) n) ((Facts n) f) ((Bin) c) -> Type
    enum
    (many MkTable : (erased (Nat) n) (many (Facts n) f) (erased (Bin) c) (many (List (Rule)) ru) (erased (List (Bin)) ks) (erased (Ord (Nil (Bin)) ru) ord) (erased (Keys (Nil (Bin)) ru ks) keys) (erased (AllRuled ks n f) ar) (erased (C1 (Nil (Digit)) n f ru) c1) (erased (Above (Nil (Digit)) c n f) ab) -> (Table n f c)))
  (Added : ((Nat) n) ((Facts n) f) ((Bin) c) -> Type
    enum
    (many MkAdded : (erased (Nat) k) (erased (Facts (Succ k)) f) (erased (Facts k) f2) (erased (Bin) c) (many (Table k f2 c) tb) -> (Added (Succ k) f c))))

(let (many empty-table) (MkTable (Zero) (FEmpty) (BZ) (Nil (Rule)) (Nil (Bin)) (OrdNil (Nil (Bin))) (KNil (Nil (Bin))) (ARNil (Zero) (FEmpty)) (C1Empty (Nil (Digit)) (Nil (Rule))) (AbEmpty (Nil (Digit)) (BZ))))

; The table after a variable is ruled out with a term fresh in the result: the rule is appended, the
; keys and the order extended, and both agreements carried across.
(def-fns _ $ many rule-into : (erased (Nat) n) (erased (Facts n) f) (erased (Bin) c) (erased (Above (Nil (Digit)) c n f) ab) (many (List (Rule)) ru) (erased (List (Bin)) ks) (erased (Ord (Nil (Bin)) ru) ord) (erased (Keys (Nil (Bin)) ru ks) keys) (erased (AllRuled ks n f) ar) (erased (C1 (Nil (Digit)) n f ru) c1)
    (many (Bin) x) (many (Term) t) (erased (Nat) k) (many (Facts k) f2) (erased (Out x t n f k f2) o) (erased (Fr k f2 t) ft) -> (many (Table k f2 c) tb)
  (let (many ru2) (erased ap) (append-rule ru (MkRule x t)))
  (let (erased ar2) (ARCons x ks k f2 (ruledin-out-new x t n f k f2 o) (allruled-out ks x t n f k f2 o ar)))
  (MkTable k f2 c ru2 (Cons (Bin) x ks)
    (ord-snoc (Nil (Bin)) ru ord ks keys x t ru2 ap (GAv t (Cons (Bin) x ks) k f2 ft ar2))
    (keys-snoc (Nil (Bin)) ru ks keys x t ru2 ap)
    ar2
    (c1-out (Nil (Digit)) x x (WNil x) t n f k f2 o ru c1 ru2 ap)
    (above-out (Nil (Digit)) c x t n f k f2 ab o)))

; Unification's binding: rule the variable out, and the occurs check is the term still being fresh.
(def-fns _ $ many rule-out-refresh : (erased (Nat) n) (erased (Facts n) f) (many (Bin) bnd) (many (Table n f bnd) tb) (many (Bin) x) (erased (In x n f) p) (many (Term) t) -> (many (Maybe (Added n f bnd)) r)
  (match many tb _
    ((MkTable n0 f0 c0 ru ks ord keys ar c1 ab)
      (match many (facts-rule-out n f0 x p t) _
        ((MkRemoved a b k d f2 o)
          (let (many ru2) (erased ap) (append-rule ru (MkRule x t)))
          (let (erased c2) (c1-out (Nil (Digit)) x x (WNil x) t n f0 k f2 o ru c1 ru2 ap))
          (match many (refresh t k f2 ru2 c2) _
            ((None e) (None (Added n f bnd)))
            ((Some e box)
              (match many box _
                ((MkFrBox a2 b2 c3 ft) (Some (Added n f bnd) (MkAdded k f f2 bnd (rule-into n f0 c0 ab ru ks ord keys ar c1 x t k f2 o ft))))))))))))

; A new entry, rule-free, at the fresh id x above every key of the table: the count grows.
(def-fns _ $ many table-insert : (erased (Nat) n) (erased (Facts n) f) (erased (Bin) c) (many (Table n f c) tb) (many (Bin) x) (erased (BinLt c x) lt) (many (Term) ty) -> (erased (Nat) n2) (erased (Facts n2) f2) (many (Table n2 f2 x) tb2)
  (match many tb _
    ((MkTable n0 f0 c0 ru ks ord keys ar c1 ab)
      (match many (facts-insert x n f0 ty) (((Nat) n2) ((Facts n2) f2) ((Table n2 f2 x) tb2))
        (absurd (IKept a b d q) (le-lt-absurd x c (above-taken c n f0 x ab q) lt))
        ((IGrew a b d f1 i q)
          (values (Succ n) f1 (MkTable (Succ n) f1 x ru ks ord keys (allruled-ins ks x n f0 (Succ n) f1 i ar) (c1-ins (Nil (Digit)) x n f0 (Succ n) f1 i ru c1)
                                 (above-ins (Nil (Digit)) x n f0 (Succ n) f1 x x (above-weaken (Nil (Digit)) c x n f0 ab (lt-le c x lt)) i (WNil x) (le-refl x)))))))))

; A new entry with a rule, its term canonical: inserted rule-free and ruled out at once.
(def-fns _ $ many table-insert-ruled : (erased (Nat) n) (erased (Facts n) f) (erased (Bin) c) (many (Table n f c) tb) (many (Bin) x) (erased (BinLt c x) lt) (many (Term) ty) (many (Term) t) (erased (Fr n f t) ft) -> (erased (Nat) n2) (erased (Facts n2) f2) (many (Table n2 f2 x) tb2)
  (match many tb _
    ((MkTable n0 f0 c0 ru ks ord keys ar c1 ab)
      (match many (facts-insert x n f0 ty) (((Nat) n2) ((Facts n2) f2) ((Table n2 f2 x) tb2))
        (absurd (IKept a b d q) (le-lt-absurd x c (above-taken c n f0 x ab q) lt))
        ((IGrew a b d f1 i q)
          (match many (facts-rule-out (Succ n) f1 x q t) (((Nat) n2) ((Facts n2) f2) ((Table n2 f2 x) tb2))
            ((MkRemoved a2 b2 k d2 f2 o)
              (values k f2 (rule-into (Succ n) f1 x (above-ins (Nil (Digit)) x n f0 (Succ n) f1 x x (above-weaken (Nil (Digit)) c x n f0 ab (lt-le c x lt)) i (WNil x) (le-refl x))
                              ru ks ord keys (allruled-ins ks x n f0 (Succ n) f1 i ar) (c1-ins (Nil (Digit)) x n f0 (Succ n) f1 i ru c1)
                              x t k f2 o (fresh-ins-out x t n f0 (Succ n) f1 k f2 i o t ft))))))))))

(def-fns _ $ many table-weaken : (erased (Nat) n) (erased (Facts n) f) (erased (Bin) c) (erased (Bin) c2) (many (Table n f c) tb) (erased (BinLe c c2) le) -> (many (Table n f c2) tb2)
  (match many tb _
    ((MkTable n0 f0 c0 ru ks ord keys ar c1 ab) (MkTable n0 f0 c2 ru ks ord keys ar c1 (above-weaken (Nil (Digit)) c c2 n0 f0 ab le)))))

; Two distinct variables: ruling the newer out leaves the older rule-free, so the alias is fresh.
(def-fns _ $ erased neq-sym : (subterm erased (Bin) a) (erased (Bin) b) (erased (Neq a b) p) -> (erased (Neq b a) q)
  (match erased p _
    ((NeqZ1 b1) (Neq1Z b1)) ((NeqZ2 b1) (Neq2Z b1)) ((Neq1Z a1) (NeqZ1 a1)) ((Neq2Z a1) (NeqZ2 a1))
    ((Neq12 a1 b1) (Neq21 b1 a1)) ((Neq21 a1 b1) (Neq12 b1 a1))
    ((Neq11 a1 b1 q) (Neq11 b1 a1 (neq-sym a1 b1 q)))
    ((Neq22 a1 b1 q) (Neq22 b1 a1 (neq-sym a1 b1 q)))))

(def-fns _ $ erased in-out-neq : (erased (Bin) z) (erased (Bin) x) (erased (Term) t) (erased (Nat) n) (erased (Facts n) f) (erased (Nat) k) (erased (Facts k) f2) (subterm erased (Out x t n f k f2) o) (erased (Neq z x) ne) (erased (In z n f) p) -> (erased (In z k f2) q)
  (match erased o _
    ((OutHere n1 n2 m ty t0 one two pp)
      (match erased p _
        (absurd (InHere a1 a2 a3 ty1 one1 two1 p1) (neq-irrefl z ne))
        ((In1 z1 h b1 b2 b3 here1 one1 two1 p1 q1) (In1 z1 (Zero) n1 n2 m (HRuled ty t0) one two pp q1))
        ((In2 z1 h b1 b2 b3 here1 one1 two1 p1 q1) (In2 z1 (Zero) n1 n2 m (HRuled ty t0) one two pp q1))))
    ((Out1 x1 t0 h n1 a2 m here one two pp k1 m2 one2 p2 q)
      (match erased p _
        ((InHere c1 c2 c3 ty one1 two1 p1) (InHere k1 a2 m2 ty one2 two p2))
        ((In1 z1 h1 c1 c2 c3 here1 one1 two1 p1 q1)
          (In1 z1 h k1 a2 m2 here one2 two p2 (in-out-neq z1 x1 t0 n1 one k1 one2 q (match erased ne (((Neq z1 x1) r)) ((Neq11 a3 b3 q3) q3)) q1)))
        ((In2 z1 h1 c1 c2 c3 here1 one1 two1 p1 q1) (In2 z1 h k1 a2 m2 here one2 two p2 q1))))
    ((Out2 x1 t0 h n1 a2 m here one two pp k2 m2 two2 p2 q)
      (match erased p _
        ((InHere c1 c2 c3 ty one1 two1 p1) (InHere n1 k2 m2 ty one two2 p2))
        ((In1 z1 h1 c1 c2 c3 here1 one1 two1 p1 q1) (In1 z1 h n1 k2 m2 here one two2 p2 q1))
        ((In2 z1 h1 c1 c2 c3 here1 one1 two1 p1 q1)
          (In2 z1 h n1 k2 m2 here one two2 p2 (in-out-neq z1 x1 t0 a2 two k2 two2 q (match erased ne (((Neq z1 x1) r)) ((Neq22 a3 b3 q3) q3)) q1)))))))

(def-fns _ $ many rule-out-var : (erased (Nat) n) (erased (Facts n) f) (many (Bin) bnd) (many (Table n f bnd) tb) (many (Bin) newer) (many (Bin) older) (erased (In newer n f) pn) (erased (In older n f) po) (erased (Neq older newer) ne) -> (many (Added n f bnd) r)
  (match many tb _
    ((MkTable n0 f0 c0 ru ks ord keys ar c1 ab)
      (match many (facts-rule-out n f0 newer pn (TVar older)) _
        ((MkRemoved a b k d f2 o)
          (MkAdded k f f2 bnd (rule-into n f0 c0 ab ru ks ord keys ar c1 newer (TVar older) k f2 o (FrVar k f2 older (in-out-neq older newer (TVar older) n f0 k f2 o ne po)))))))))

(def-fns _ $ many canon-in : (erased (Nat) n) (erased (Facts n) f) (many (Bin) bnd) (many (Table n f bnd) tb) (many (Term) t) -> (many (Term) r) (erased (Fr n f r) fr)
  (match many tb _
    ((MkTable n0 f0 c0 ru ks ord keys ar c1 ab) (canon ru t n f0 ru (Nil (Bin)) (PNil ru) ord (GTop t) c1))))
(def-fns _ $ many canon-list-in : (erased (Nat) n) (erased (Facts n) f) (many (Bin) bnd) (many (Table n f bnd) tb) (many (List (Term)) ts) -> (many (List (Term)) r) (erased (FrL n f r) fr)
  (match many tb _
    ((MkTable n0 f0 c0 ru ks ord keys ar c1 ab) (canon-list ru ts n f0 ru (Nil (Bin)) (PNil ru) ord (GLTop ts) c1))))
(def-fns _ $ many canon-tele-in : (erased (Nat) n) (erased (Facts n) f) (many (Bin) bnd) (many (Table n f bnd) tb) (many (List (Entry)) es) -> (many (List (Entry)) r) (erased (FrT n f r) fr)
  (match many tb _
    ((MkTable n0 f0 c0 ru ks ord keys ar c1 ab) (canon-tele ru es n f0 ru (Nil (Bin)) (PNil ru) ord (GTTop es) c1))))
(def-fns _ $ many canon-mctors-in : (erased (Nat) n) (erased (Facts n) f) (many (Bin) bnd) (many (Table n f bnd) tb) (many (List (MCtor)) cs) -> (many (List (MCtor)) r) (erased (FrM n f r) fr)
  (match many tb _
    ((MkTable n0 f0 c0 ru ks ord keys ar c1 ab) (canon-mctors ru cs n f0 ru (Nil (Bin)) (PNil ru) ord (GMTop cs) c1))))


; ---- The scope environment (section 3) and fact table (section 18)

(def-adts
  (Env : -> Type
    enum
    (many MkEnv : (many (NameMap (Bin)) scope) (many (IdMap (EInfo)) entries) (erased (Nat) nfree) (erased (Facts nfree) ffacts) (many (Bin) fresh) (many (Table nfree ffacts fresh) table)
       (many (Bool) run-pos) (many (IdMap (Value)) values) (many (List (Bin)) objects)
       (many (NameMap (Bin)) literals) (many (List (Trace)) trace) (many (List (String)) errors)
       (many (Maybe (Bin)) level) (many (List (Bin)) subterms) (many (List (String)) claimed) (many (List (String)) warnings)
       (many (List (Pair (Bin) (Maybe (Bin)))) lits) (many (Loc) loc) (many (NameMap (Bin)) prelude) (many (List (Bin)) opens) -> (Env)))
  (Loc : -> Type
    enum
    (many MkLoc : (many (String) file) (many (Nat) line) -> (Loc)))
  (EInfo : -> Type
    enum
    (many MkEInfo : (many (Maybe (String)) name) (many (Mult) mult) (many (State) state) (many (Bool) minted) -> (EInfo)))
  (State : -> Type
    enum
    (many SConst : (many (Value) v) -> (State))
    (many SDyn : -> (State)))
  (Trace : -> Type
    enum
    (many TrFns : (many (List (Pair (Bin) (Func))) fns) -> (Trace))
    (many TrConst : (many (Bin) id) (many (Value) v) -> (Trace))
    (many TrFinal : (many (Value) v) (many (Term) ty) -> (Trace))))

(def-fns _ $ many env-scope : (many (Env) e) -> (many (NameMap (Bin)) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) sc)))
(def-fns _ $ many env-entries : (many (Env) e) -> (many (IdMap (EInfo)) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) en)))
(def-fns _ $ many env-table : (many (Env) e) -> (erased (Nat) n) (erased (Facts n) f) (many (Bin) bnd) (many (Table n f bnd) tb)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) (values nf ff fr tb))))
(def-fns _ $ many env-facts : (many (Env) e) -> (erased (Nat) n) (many (Facts n) f)
  (let (erased n) (erased f) (many bnd) (many tb) (env-table e))
  (match many tb _ ((MkTable n0 f0 c0 ru ks ord keys ar c1 ab) (values n0 f0))))
(def-fns _ $ many env-run-pos : (many (Env) e) -> (many (Bool) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) rp)))
(def-fns _ $ many env-values : (many (Env) e) -> (many (IdMap (Value)) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) va)))
(def-fns _ $ many env-objects : (many (Env) e) -> (many (List (Bin)) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) ob)))
(def-fns _ $ many env-literals : (many (Env) e) -> (many (NameMap (Bin)) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) li)))
(def-fns _ $ many env-trace : (many (Env) e) -> (many (List (Trace)) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) tr)))
(def-fns _ $ many env-errors : (many (Env) e) -> (many (List (String)) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) er)))

(def-fns _ $ many env-level : (many (Env) e) -> (many (Maybe (Bin)) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) lv)))
(def-fns _ $ many env-subterms : (many (Env) e) -> (many (List (Bin)) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) st)))
(def-fns _ $ many env-claimed : (many (Env) e) -> (many (List (String)) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) cl)))
(def-fns _ $ many env-warnings : (many (Env) e) -> (many (List (String)) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) wa)))
(def-fns _ $ many env-lits : (many (Env) e) -> (many (List (Pair (Bin) (Maybe (Bin)))) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) lt)))
(def-fns _ $ many env-enter-body : (many (Env) e) (many (Bin) level) (many (List (Bin)) subterms) -> (many (Env) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) (MkEnv sc en nf ff fr tb (BFalse) va ob li tr er (Some (Bin) level) subterms cl wa lt lo pr opn))))
(def-fns _ $ many env-claim : (many (Env) e) (many (String) x) -> (many (Env) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) (MkEnv sc en nf ff fr tb rp va ob li tr er lv st (Cons (String) x cl) wa lt lo pr opn))))
(def-fns _ $ many env-warn : (many (Env) e) (many (String) x) -> (many (Env) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) (MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl (Cons (String) x wa) lt lo pr opn))))
(def-fns _ $ many env-push-lit : (many (Env) e) (many (Bin) x) (many (Maybe (Bin)) proof) -> (many (Env) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) (MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa (Cons (Pair (Bin) (Maybe (Bin))) (MkPair (Bin) (Maybe (Bin)) x proof) lt) lo pr opn))))
(def-fns _ $ many env-set-scope : (many (Env) e) (many (NameMap (Bin)) x) -> (many (Env) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) (MkEnv x en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn))))
(def-fns _ $ many env-set-table : (many (Env) e) (erased (Nat) n) (erased (Facts n) f) (many (Bin) c) (many (Table n f c) x) -> (many (Env) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) (MkEnv sc en n f c x rp va ob li tr er lv st cl wa lt lo pr opn))))
(def-fns _ $ many env-set-run-pos : (many (Env) e) (many (Bool) x) -> (many (Env) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) (MkEnv sc en nf ff fr tb x va ob li tr er lv st cl wa lt lo pr opn))))
(def-fns _ $ many env-set-literals : (many (Env) e) (many (NameMap (Bin)) x) -> (many (Env) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) (MkEnv sc en nf ff fr tb rp va ob x tr er lv st cl wa lt lo pr opn))))
(def-fns _ $ many env-prelude : (many (Env) e) -> (many (NameMap (Bin)) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) pr)))
; The scope the prelude left, which generated forms elaborate in (lib/elab.ml's in_prelude).
(def-fns _ $ many env-set-prelude : (many (Env) e) (many (NameMap (Bin)) x) -> (many (Env) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) (MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo x opn))))
; The Matchables and Newtypes opened so far (proposals/matchable-newtype-opening.md, ASSUMPTIONS 114), one entry
; per merged group: what every read of one consults.
(def-fns _ $ many env-opens : (many (Env) e) -> (many (List (Bin)) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) opn)))
(def-fns _ $ many env-set-opens : (many (Env) e) (many (List (Bin)) x) -> (many (Env) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) (MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr x))))
; The next id, above every key of the table.
(def-fns _ $ many env-fresh-id : (many (Env) e) -> (many (Env) r) (many (Bin) x)
  (match many e _
    ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn)
      (let (many x) (erased ltp) (bin-succ-lt fr))
      (values (MkEnv sc en nf ff x (table-weaken nf ff fr x tb (lt-le fr x ltp)) rp va ob li tr er lv st cl wa lt lo pr opn) x))))
(def-fns _ $ many env-push-trace : (many (Env) e) (many (Trace) x) -> (many (Env) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) (MkEnv sc en nf ff fr tb rp va ob li (Cons (Trace) x tr) er lv st cl wa lt lo pr opn))))
(def-fns _ $ many env-loc : (many (Env) e) -> (many (Loc) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) lo)))
(def-fns _ $ many env-line : (many (Env) e) -> (many (Nat) r)
  (match many (env-loc e) _ ((MkLoc f l) l)))
(def-fns _ $ many env-at-loc : (many (Env) e) (many (Loc) x) -> (many (Env) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) (MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt x pr opn))))
(def-fns _ $ many env-at : (many (Env) e) (many (Nat) line) -> (many (Env) r)
  (match many (env-loc e) _ ((MkLoc f l) (env-at-loc e (MkLoc f line)))))
; Restores [outer]'s line in [inner], on leaving the form that set it.
(def-fns _ $ many env-back : (many (Env) outer) (many (Env) inner) -> (many (Env) r)
  (env-at-loc inner (env-loc outer)))
; A message with the file and line in force, in the reference's format.
(def-fns _ $ many located : (many (Env) e) (many (String) kind) (many (String) x) -> (many (String) r)
  (match many (env-loc e) _
    ((MkLoc f l) (str-cat3 f ":" (str-cat3 (nat-str l) kind x)))))
(def-fns _ $ many env-report : (many (Env) e) (many (String) msg) -> (many (Env) r)
  (match many e _ ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn) (MkEnv sc en nf ff fr tb rp va ob li tr (Cons (String) msg er) lv st cl wa lt lo pr opn))))
(def-fns _ $ many env-error : (many (Env) e) (many (String) x) -> (many (Env) r)
  (env-report e (located e ": error: " x)))

; Leaves a scope: keeps [inner]'s facts, opens, values, literals, fresh ids, trace and errors, restoring
; [outer]'s scope and objects; run position is [outer]'s.
(def-fns _ $ many env-restore : (many (Env) outer) (many (Env) inner) -> (many (Env) r)
  (match many outer _
    ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn)
      (match many inner _
        ((MkEnv sc2 en2 nf2 ff2 fr2 tb2 rp2 va2 ob2 li2 tr2 er2 lv2 st2 cl2 wa2 lt2 lo2 pr2 opn2) (MkEnv sc en2 nf2 ff2 fr2 tb2 rp va2 ob li2 tr2 er2 lv st cl2 wa2 lt2 lo pr opn2))))))

; Leaves a match branch or a body: the entries (whose names the extractor prints), the id supply, trace
; and errors survive; scope, facts, opens, values and objects are the outer ones again.
(def-fns _ $ many env-discard : (many (Env) outer) (many (Env) inner) -> (many (Env) r)
  (match many outer _
    ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn)
      (match many inner _
        ((MkEnv sc2 en2 nf2 ff2 fr2 tb2 rp2 va2 ob2 li2 tr2 er2 lv2 st2 cl2 wa2 lt2 lo2 pr2 opn2)
          (match many (bin-cmp-dec fr fr2) _
            ((CLt x y p) (MkEnv sc en2 nf ff fr2 (table-weaken nf ff fr fr2 tb (lt-le fr fr2 p)) rp va ob li tr2 er2 lv st cl2 wa2 lt2 lo pr opn)) (else (MkEnv sc en2 nf ff fr tb rp va ob li tr2 er2 lv st cl2 wa2 lt2 lo pr opn))))))))

(def-fns _ $ many entry : (many (Env) env) (many (Bin) x) -> (many (EInfo) r)
  (match many (idmap-get (EInfo) x (env-entries env)) _
    ((None a) (MkEInfo (None (String)) (Many) (SDyn) (BFalse)))
    ((Some a e) e)))

(def-fns _ $ many entry-mult-of : (many (Env) env) (many (Bin) x) -> (many (Mult) r)
  (match many (entry env x) _ ((MkEInfo n m s mi) m)))

(def-fns _ $ many entry-state : (many (Env) env) (many (Bin) x) -> (many (State) r)
  (match many (entry env x) _ ((MkEInfo n m s mi) s)))

(def-fns _ $ many entry-minted : (many (Env) env) (many (Bin) x) -> (many (Bool) r)
  (match many (entry env x) _ ((MkEInfo n m s mi) mi)))

(def-fns _ $ many mark-minted : (many (Env) env) (many (Bin) x) -> (many (Env) r)
  (match many env _
    ((MkEnv sc en nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn)
      (let (many info) (match many (idmap-get (EInfo) x en) (((EInfo) i))
                         ((None a) (MkEInfo (None (String)) (Erased) (SDyn) (BTrue)))
                         ((Some a e) (match many e (((EInfo) i)) ((MkEInfo n m s mi) (MkEInfo n m s (BTrue)))))))
      (MkEnv sc (idmap-set (EInfo) x info en) nf ff fr tb rp va ob li tr er lv st cl wa lt lo pr opn))))

(def-fns _ $ many name-of : (many (Env) env) (many (Bin) x) -> (many (String) r)
  (match many (entry env x) _
    ((MkEInfo n m s mi) (match many n _ ((None a) (str-cat "_" (bin-str x))) ((Some a s2) s2)))))

(def-fns _ $ many fact-ty : (many (Env) env) (many (Bin) x) -> (many (Term) r)
  (let (erased n) (erased f) (many bnd) (many tb) (env-table env))
  (match many tb _
    ((MkTable n0 f0 c0 ru ks ord keys ar c1 ab)
      (match many (facts-lookup x n0 f0 (Nil (Digit)) x (WNil x) ru c1) _
        ((LNone a b c d e) (TErr (str-cat "no fact for " (bin-str x))))
        ((LRuled a b c d e ty t m) ty)
        ((LFree a b c d e ty p) ty)))))

(def-fns _ $ many rule-of : (many (Env) env) (many (Bin) x) -> (many (Maybe (Term)) r)
  (let (erased n) (erased f) (many bnd) (many tb) (env-table env))
  (match many tb _
    ((MkTable n0 f0 c0 ru ks ord keys ar c1 ab)
      (match many (facts-lookup x n0 f0 (Nil (Digit)) x (WNil x) ru c1) _
        ((LRuled a b c d e ty t m) (Some (Term) t)) (else (None (Term)))))))

(def-fns _ $ many lookup : (many (Env) env) (many (String) name) -> (many (Maybe (Bin)) r)
  (nm-get (Bin) name (env-scope env)))

(def-fns _ $ many set-state : (many (Env) env) (many (Bin) x) (many (State) st) -> (many (Env) r)
  (match many env _
    ((MkEnv sc en nf ff fr tb rp va ob li tr er lv sts cl wa lt lo pr opn)
      (let (many info) (match many (idmap-get (EInfo) x en) (((EInfo) i))
                         ((None a) (MkEInfo (None (String)) (Many) st (BFalse)))
                         ((Some a e) (match many e (((EInfo) i)) ((MkEInfo n m s mi) (MkEInfo n m st mi))))))
      (let (many va2) (match many st (((IdMap (Value)) m))
                        ((SConst v) (idmap-set (Value) x v va))
                        ((SDyn) va)))
      (MkEnv sc (idmap-set (EInfo) x info en) nf ff fr tb rp va2 ob li tr er lv sts cl wa lt lo pr opn))))

; Whether a type is one the fetching forms look for in ambient scope (sections 19, 38).
(def-fns _ $ many is-object-type : (many (Term) ty) (many (Bin) coercible) -> (many (Bool) r)
  (match many ty _
    ((TMatchable d t cs) (BTrue))
    ((TNewtype c) (BTrue))
    ((TApp h args) (match many h _ ((TVar x) (bin-eq x coercible)) (else (BFalse)))) (else (BFalse))))

; Mints an entry: a fresh id, its name in scope, its state, its type and optional rule (section 3).
(def-fns _ $ many bind : (many (Env) env) (many (Maybe (String)) name) (many (Mult) mult) (many (State) st) (many (Term) ty) (many (Maybe (Term)) rule) (many (Bin) coercible) ->
    (many (Env) r) (many (Bin) x)
  (let (many bad) (match many name (((Maybe (String)) m)) ((None a) (None (String))) ((Some a n) (match many (is-literal-name n) (((Maybe (String)) m)) ((BTrue) (Some (String) (located env ": error: " (str-cat n " is a literal, not a name")))) ((BFalse) (None (String)))))))
  (match many env _
    ((MkEnv sc en nf ff fr tb rp va ob li tr er0 lv sts cl wa lt lo pr opn)
      (let (many er) (match many bad (((List (String)) e)) ((None a) er0) ((Some a m) (Cons (String) m er0))))
      (let (many x) (erased ltp) (bin-succ-lt fr))
      (let (many sc2) (match many name (((NameMap (Bin)) m)) ((None a) sc) ((Some a n) (nm-set (Bin) n x sc))))
      (let (many en2) (idmap-set (EInfo) x (MkEInfo name mult st (BFalse)) en))
      (let (erased nf2) (erased ff2) (many tb2)
        (match many rule (((Nat) n2) ((Facts n2) f2) ((Table n2 f2 x) t2))
          ((None a) (table-insert nf ff fr tb x ltp ty))
          ((Some a t)
            (match many tb (((Nat) n2) ((Facts n2) f2) ((Table n2 f2 x) t2))
              ((MkTable n0 f0 c0 ru ks ord keys ar c1 ab)
                (let (many t2) (erased ft) (canon ru t n0 f0 ru (Nil (Bin)) (PNil ru) ord (GTop t) c1))
                (table-insert-ruled nf ff fr tb x ltp ty t2 ft))))))
      (let (many va2) (match many st (((IdMap (Value)) m)) ((SConst v) (idmap-set (Value) x v va)) ((SDyn) va)))
      (let (many ob2) (match many (is-object-type ty coercible) (((List (Bin)) l)) ((BTrue) (Cons (Bin) x ob)) ((BFalse) ob)))
      (values (MkEnv sc2 en2 nf2 ff2 x tb2 rp va2 ob2 li tr er lv sts cl wa lt lo pr opn) x))))

; ---- Instantiation and abstraction over de Bruijn binders (lib/term.ml)

(def-adts $ VOp : -> Type
  enum
  (many OpInst : (many (List (Term)) args) -> (VOp))
  (many OpAbs : (many (List (Bin)) ids) -> (VOp)))

; [args] are closed terms, innermost binder first; [ids] likewise, the head becoming Bound 0.
(def-fns _ $ many op-leaf : (many (VOp) op) (many (Nat) d) (many (Term) t) -> (many (Term) r)
  (match many op _
    ((OpInst args)
      (match many t _
        ((TBound k)
          (match many (nat-lt k d) _
            ((BTrue) t)
            ((BFalse)
              (let (many n) (list-length (Term) args))
              (match many (list-nth (Term) args (nat-sub k d)) _
                ((Some a s) s)
                ((None a) (TBound (nat-sub k n))))))) (else t)))
    ((OpAbs ids)
      (match many t _
        ((TVar x)
          (match many (index-of-bin ids x 0) _
            ((Some a i) (TBound (nat-add i d)))
            ((None a) t))) (else t)))))

(def-fns _
  (many mapv : (subterm many (Term) t) (many (VOp) op) (many (Nat) d) -> (many (Term) r)
    (match many t _
      ((TApp h args) (TApp (mapv h op d) (mapv-list args op d)))
      ((TFn l ps rs)
        (let (many d2) (many ps2) (mapv-tele ps op d))
        (let (many d3) (many rs2) (mapv-tele rs op d2))
        (TFn (mapv l op d) ps2 rs2))
      ((TTyCtor ps)
        (let (many d2) (many ps2) (mapv-tele ps op d))
        (TTyCtor ps2))
      ((TValCtor ps ret)
        (let (many d2) (many ps2) (mapv-tele ps op d))
        (TValCtor ps2 (mapv ret op d2)))
      ((TMatchable disc ty cs) (TMatchable disc (mapv ty op d) (mapv-mctors cs op d)))
      ((TNewtype c) (TNewtype (mapv c op d)))
      ((TErr m) t) (else (op-leaf op d t))))
  (many mapv-list : (subterm many (List (Term)) ts) (many (VOp) op) (many (Nat) d) -> (many (List (Term)) r)
    (match many ts _
      ((Nil a) (Nil (Term)))
      ((Cons a t rest) (Cons (Term) (mapv t op d) (mapv-list rest op d)))))
  (many mapv-mctors : (subterm many (List (MCtor)) cs) (many (VOp) op) (many (Nat) d) -> (many (List (MCtor)) r)
    (match many cs _
      ((Nil a) (Nil (MCtor)))
      ((Cons a c rest)
        (match many c _
          ((MkMCtor m t) (Cons (MCtor) (MkMCtor m (mapv t op d)) (mapv-mctors rest op d)))))))
  ; Each entry is mapped at the depth of the entries before it; returns the depth after the telescope.
  (many mapv-tele : (subterm many (List (Entry)) es) (many (VOp) op) (many (Nat) d) -> (many (Nat) d2) (many (List (Entry)) r)
    (match many es _
      ((Nil a) (values d (Nil (Entry))))
      ((Cons a e rest)
        (let (many e2) (match many e (((Entry) x))
                         ((MkEntry n s m sg)
                           (MkEntry n s m (match many sg (((Sg) y)) ((SgTy t) (SgTy (mapv t op d))) ((SgIs t) (SgIs (mapv t op d))))))))
        (let (many d3) (many rest2) (mapv-tele rest op (Succ d)))
        (values d3 (Cons (Entry) e2 rest2))))))

(def-fns _ $ many instantiate : (many (List (Term)) args) (many (Term) t) -> (many (Term) r)
  (mapv t (OpInst args) 0))

(def-fns _ $ many instantiate-tele : (many (List (Term)) args) (many (List (Entry)) tele) -> (many (List (Entry)) r)
  (let (many d) (many r) (mapv-tele tele (OpInst args) 0))
  r)

(def-fns _ $ many abstract : (many (List (Bin)) ids) (many (Term) t) -> (many (Term) r)
  (mapv t (OpAbs ids) 0))

(def-fns _ $ many abstract-sg : (many (List (Bin)) ids) (many (Sg) sg) -> (many (Sg) r)
  (match many sg _
    ((SgTy t) (SgTy (abstract ids t)))
    ((SgIs t) (SgIs (abstract ids t)))))

(def-fns _ $ many canon-env : (many (Env) env) (many (Term) t) -> (many (Term) r)
  (let (erased n) (erased f) (many bnd) (many tb) (env-table env))
  (let (many r) (erased fr) (canon-in n f bnd tb t))
  r)

(def-fns _ $ many type-of : (many (Env) env) (many (Bin) x) -> (many (Term) r)
  (canon-env env (fact-ty env x)))

; An entry read through its alias rule (section 9).
(def-fns _ $ many resolve : (many (Env) env) (many (Bin) x) -> (many (Bin) r)
  (match many (canon-env env (TVar x)) _
    ((TVar y) y) (else x)))

; ---- The built-in entries (lib/prelude.ml): Univ, Type, Level, the proof types, Special and its forms

(def-fns _ $ many ty-entry : (many (String) name) (many (Term) t) -> (many (Entry) e)
  (MkEntry (Some (String) name) (BFalse) (Erased) (SgTy t)))

(let (many empty-env)
  (MkEnv (nm-empty (Bin)) (MEmpty (EInfo)) (Zero) (FEmpty) (BZ) empty-table (BTrue) (MEmpty (Value)) (Nil (Bin)) (nm-empty (Bin)) (Nil (Trace)) (Nil (String)) (None (Bin)) (Nil (Bin)) (Nil (String)) (Nil (String)) (Nil (Pair (Bin) (Maybe (Bin)))) (MkLoc "" 0) (nm-empty (Bin)) (Nil (Bin))))

; The ids below are fixed by the order of the binds that follow; [bind-builtin] mints in that order.
(let (many univ-id) (bin-succ (BZ)))
(let (many type-id) (bin-succ univ-id))
(let (many level-id) (bin-succ type-id))
(let (many predates-id) (bin-succ level-id))
(let (many subterm-id) (bin-succ predates-id))
(let (many coercible-id) (bin-succ subterm-id))
(let (many special-id) (bin-succ coercible-id))
(let (many type-term) (TApp (TVar univ-id) (Nil (Term))))
(let (many level-term) (TApp (TVar level-id) (Nil (Term))))
(let (many special-term) (TApp (TVar special-id) (Nil (Term))))

(def-fns _ $ many bind-builtin : (many (Env) env) (many (String) name) (many (Term) ty) (many (Maybe (Term)) rule) -> (many (Env) r)
  (let (many env2) (many x) (bind env (Some (String) name) (Erased) (SConst (VToken)) ty rule coercible-id))
  env2)

(let (many special-adt-stub) (MkAdt "Special" (BTrue) (Nil (Ctor)) (None (String))))

; Binds each form's %-constructor (ASSUMPTIONS 5) and the form's own entry holding that constructor's value;
; returns the constructors for the Special Matchable.
(def-fns _ $ many bind-specials : (subterm many (List (SpEntry)) sps) (many (Env) env) (many (Nat) index) -> (many (Env) r) (many (List (Ctor)) ctors) (many (List (MCtor)) mctors)
  (match many sps _
    ((Nil a) (values env (Nil (Ctor)) (Nil (MCtor))))
    ((Cons a sp rest)
      (match many sp _
        ((MkSpEntry name k)
          (let (many cname) (str-cat "%" name))
          (let (many env2) (many c) (bind env (Some (String) cname) (Many) (SDyn) (TValCtor (Nil (Entry)) special-term) (None (Term)) coercible-id))
          (let (many ctor) (MkCtor cname c index 0 (BTrue) (None (String))))
          (let (many env3) (set-state env2 c (SConst (VCtorFn ctor))))
          (let (many env4) (many x) (bind env3 (Some (String) name) (Many) (SConst (VCtor ctor (Nil (Value)))) special-term (Some (Term) (TApp (TVar c) (Nil (Term)))) coercible-id))
          (let (many env4b) (env-push-trace (env-push-trace env4 (TrConst c (VCtorFn ctor))) (TrConst x (VCtor ctor (Nil (Value))))))
          (let (many env5) (many ctors) (many mctors) (bind-specials rest env4b (Succ index)))
          (values env5 (Cons (Ctor) ctor ctors) (Cons (MCtor) (MkMCtor (Many) (TVar c)) mctors)))))))

(def-fns _ $ many make-builtins : -> (many (Env) env)
  (let (many hetero) (Cons (Entry) (ty-entry "A" type-term) $ Cons (Entry) (ty-entry "a" (TBound 0)) $
                      Cons (Entry) (ty-entry "B" type-term) $ Cons (Entry) (ty-entry "b" (TBound 0)) (Nil (Entry))))
  (let (many e1) (bind-builtin empty-env "Univ" (TTyCtor (Nil (Entry))) (None (Term))))
  (let (many e2) (bind-builtin e1 "Type" type-term (Some (Term) type-term)))
  (let (many e3) (bind-builtin e2 "Level" (TTyCtor (Nil (Entry))) (None (Term))))
  (let (many e4) (bind-builtin e3 "Predates"
                   (TTyCtor (Cons (Entry) (ty-entry "A" type-term) $ Cons (Entry) (ty-entry "a" (TBound 0)) $
                             Cons (Entry) (ty-entry "l" level-term) (Nil (Entry)))) (None (Term))))
  (let (many e5) (bind-builtin e4 "Subterm" (TTyCtor hetero) (None (Term))))
  (let (many e6) (bind-builtin e5 "Coercible" (TTyCtor hetero) (None (Term))))
  (let (many e7) (bind-builtin e6 "Special" (TTyCtor (Nil (Entry))) (None (Term))))
  (let (many e8) (many ctors) (many mctors) (bind-specials sp-table e7 0))
  (let (many adt) (MkAdt "Special" (BTrue) ctors (None (String))))
  (let (many e9) (many m) (bind e8 (None (String)) (Many) (SConst (VMatchable adt)) (TMatchable (DEnum) (TVar special-id) mctors) (None (Term)) coercible-id))
  (env-push-trace (env-set-opens e9 (Cons (Bin) m (Nil (Bin)))) (TrConst m (VMatchable adt))))

; ---- Inference over the grammar (lib/elab.ml's infer)

(def-fns _ $ many infer : (subterm many (Term) t) (many (Env) env) -> (many (Term) r)
  (match many t _
    ((TVar x) (type-of env x))
    ((TApp h args)
      (match many (canon-env env (infer h env)) _
        ((TTyCtor ps) type-term)
        ((TValCtor ps ret) (instantiate (list-rev (Term) args) ret))
        ((TFn l p r) (TErr "cannot apply a function in a type")) ((TErr m) (TErr m)) (else (TErr "cannot apply"))))
    ((TBound k) (TErr "dangling binder")) ((TErr m) t) (else type-term)))

; The head type constructor of a canonical type, if any.
(def-fns _ $ many type-head : (many (Env) env) (many (Term) ty) -> (many (Maybe (Bin)) r)
  (match many (canon-env env ty) _
    ((TApp h args) (match many h _ ((TVar x) (Some (Bin) x)) (else (None (Bin))))) (else (None (Bin)))))

(def-fns _ $ many bool-eq : (many (Bool) a) (many (Bool) b) -> (many (Bool) r)
  (match many a _ ((BTrue) b) ((BFalse) (not b))))

; ---- Printing terms and values, for diagnostics and the final value (lib/term.ml's to_string, lib/value.ml's show)

(def-fns _
  (many show-term : (subterm many (Term) t) (many (Env) env) -> (many (Rope) r)
    (match many t _
      ((TVar x) (RStr (name-of env x)))
      ((TBound k) (RStr (str-cat "#" (nat-str k))))
      ((TApp h args) (rcat4 (RStr "(") (show-term h env) (show-terms args env) (RStr ")")))
      ((TFn l ps rs) (rcat5 (RStr "(Fn ") (show-term l env) (show-tele ps env) (rcat (RStr " ->") (show-tele rs env)) (RStr ")")))
      ((TTyCtor ps) (rcat3 (RStr "(TyCtor") (show-tele ps env) (RStr " -> Type)")))
      ((TValCtor ps ret) (rcat4 (RStr "(ValCtor") (show-tele ps env) (rcat (RStr " -> ") (show-term ret env)) (RStr ")")))
      ((TMatchable d ty cs) (rcat4 (RStr (match many d (((String) s)) ((DEnum) "(Matchable enum ") ((DUnion) "(Matchable union "))) (show-term ty env) (show-mctors cs env) (RStr ")")))
      ((TNewtype c) (rcat3 (RStr "(Newtype ") (show-term c env) (RStr ")")))
      ((TErr m) (rcat3 (RStr "<error: ") (RStr m) (RStr ">")))))
  (many show-terms : (subterm many (List (Term)) ts) (many (Env) env) -> (many (Rope) r)
    (match many ts _
      ((Nil a) (REmpty))
      ((Cons a t rest) (rcat3 (RStr " ") (show-term t env) (show-terms rest env)))))
  (many show-mctors : (subterm many (List (MCtor)) cs) (many (Env) env) -> (many (Rope) r)
    (match many cs _
      ((Nil a) (REmpty))
      ((Cons a c rest)
        (match many c _
          ((MkMCtor m t) (rcat4 (RStr (match many m (((String) s)) ((Erased) " (erased ") ((Many) " (many "))) (show-term t env) (RStr ")") (show-mctors rest env)))))))
  (many show-tele : (subterm many (List (Entry)) es) (many (Env) env) -> (many (Rope) r)
    (match many es _
      ((Nil a) (REmpty))
      ((Cons a e rest)
        (match many e _
          ((MkEntry n s m sg)
            (let (many nm) (match many n (((String) x)) ((None b) "_") ((Some b x) x)))
            (let (many marks) (str-cat (match many s (((String) x)) ((BTrue) "subterm ") ((BFalse) ""))
                                                    (match many m (((String) x)) ((Erased) "erased ") ((Many) "many "))))
            (let (many body) (match many sg (((Rope) x))
                               ((SgTy t) (rcat3 (show-term t env) (RStr " ") (RStr nm)))
                               ((SgIs t) (rcat3 (show-term t env) (RStr " is ") (RStr nm)))))
            (rcat5 (RStr " (") (RStr marks) body (RStr ")") (show-tele rest env))))))))

; ---- Structural identity of canonical terms (section 5's canonicalize-then-compare)

(def-fns _ $ many mult-eq : (many (Mult) a) (many (Mult) b) -> (many (Bool) r)
  (match many a _
    ((Erased) (match many b _ ((Erased) (BTrue)) ((Many) (BFalse))))
    ((Many) (match many b _ ((Erased) (BFalse)) ((Many) (BTrue))))))

(def-fns _ $ many disc-eq : (many (Disc) a) (many (Disc) b) -> (many (Bool) r)
  (match many a _
    ((DEnum) (match many b _ ((DEnum) (BTrue)) ((DUnion) (BFalse))))
    ((DUnion) (match many b _ ((DEnum) (BFalse)) ((DUnion) (BTrue))))))

(def-fns _
  (many term-eq : (subterm many (Term) a) (many (Term) b) -> (many (Bool) r)
    (match many a _
      ((TVar x) (match many b _ ((TVar y) (bin-eq x y)) (else (BFalse))))
      ((TBound k) (match many b _ ((TBound j) (nat-eq k j)) (else (BFalse))))
      ((TApp h as) (match many b _
                     ((TApp h2 as2) (and (term-eq h h2) (terms-eq as as2))) (else (BFalse))))
      ((TFn l p r) (match many b _
                     ((TFn l2 p2 r2) (and (term-eq l l2) (and (tele-eq p p2) (tele-eq r r2)))) (else (BFalse))))
      ((TTyCtor p) (match many b _
                     ((TTyCtor p2) (tele-eq p p2)) (else (BFalse))))
      ((TValCtor p r) (match many b _
                        ((TValCtor p2 r2) (and (tele-eq p p2) (term-eq r r2))) (else (BFalse))))
      ((TMatchable d t c) (match many b _
                            ((TMatchable d2 t2 c2) (and (disc-eq d d2) (and (term-eq t t2) (mctors-eq c c2)))) (else (BFalse))))
      ((TNewtype c) (match many b _ ((TNewtype c2) (term-eq c c2)) (else (BFalse))))
      ((TErr m) (BFalse))))
  (many terms-eq : (subterm many (List (Term)) as) (many (List (Term)) bs) -> (many (Bool) r)
    (match many as _
      ((Nil x) (list-is-empty (Term) bs))
      ((Cons x a rest)
        (match many bs _
          ((Nil y) (BFalse))
          ((Cons y b rest2) (and (term-eq a b) (terms-eq rest rest2)))))))
  (many tele-eq : (subterm many (List (Entry)) as) (many (List (Entry)) bs) -> (many (Bool) r)
    (match many as _
      ((Nil x) (list-is-empty (Entry) bs))
      ((Cons x a rest)
        (match many bs _
          ((Nil y) (BFalse))
          ((Cons y b rest2)
            (match many a _
              ((MkEntry n s m sg)
                (match many b _
                  ((MkEntry n2 s2 m2 sg2)
                    (let (many t2) (sg-term sg2))
                    (let (many same) (match many sg (((Bool) r)) ((SgTy t) (term-eq t t2)) ((SgIs t) (term-eq t t2))))
                    (and (mult-eq m m2)
                      (and same (tele-eq rest rest2))))))))))))
  (many mctors-eq : (subterm many (List (MCtor)) as) (many (List (MCtor)) bs) -> (many (Bool) r)
    (match many as _
      ((Nil x) (list-is-empty (MCtor) bs))
      ((Cons x a rest)
        (match many bs _
          ((Nil y) (BFalse))
          ((Cons y b rest2)
            (match many a _
              ((MkMCtor m t)
                (match many b _
                  ((MkMCtor m2 t2) (and (mult-eq m m2) (and (term-eq t t2) (mctors-eq rest rest2)))))))))))))

(def-fns _ $ many equal-env : (many (Env) env) (many (Term) a) (many (Term) b) -> (many (Bool) r)
  (term-eq (canon-env env a) (canon-env env b)))

; ---- Forced unification (section 18): records the facts a branch forces, or reports the contradiction
; that refutes it (lib/env.ml's unify). The measure is the table's count of rule-free entries: a step is
; structural on canonical terms while no binding happens, and after a binding, which rules an entry out,
; the rest is re-canonicalized at the smaller count.

(def-adts
  (UnifyRes : -> Type
    enum
    (many UOk : (many (Env) env) -> (UnifyRes))
    (many UContra : (many (String) msg) -> (UnifyRes)))
  (Outcome : ((Nat) n) ((Bin) c) -> Type
    enum
    (many Same : (erased (Nat) n) (erased (Bin) c) -> (Outcome n c))
    (many Less : (erased (Nat) n) (erased (Bin) c) (erased (Nat) k) (erased (Facts k) f2) (many (Table k f2 c) tb) (many (Env) env) (erased (Subterm (Nat) k (Nat) n) p) -> (Outcome n c))
    (many Contra : (erased (Nat) n) (erased (Bin) c) (many (String) msg) -> (Outcome n c))))

(def-fns _ $ many lift : (erased (Nat) n) (many (Bin) bnd) (erased (Nat) k) (erased (Facts k) f2) (many (Table k f2 bnd) tb) (many (Env) env) (erased (Subterm (Nat) k (Nat) n) p) (many (Outcome k bnd) o) -> (many (Outcome n bnd) r)
  (match many o _
    ((Same a ac) (Less n bnd k f2 tb env p))
    ((Less a ac j f3 tb2 env2 q) (Less n bnd j f3 tb2 env2 (subterm-trans q p)))
    ((Contra a ac m) (Contra n bnd m))))

(def-fns _ $ many mctors-list : (subterm many (List (MCtor)) cs) (many (Bin) x) -> (many (Bool) r)
  (match many cs _
    ((Nil a) (BFalse))
    ((Cons a c rest)
      (match many c _
        ((MkMCtor m t)
          (match many t _
            ((TVar y) (or (bin-eq x y) (mctors-list rest x))) (else (mctors-list rest x))))))))

; Constructors one opened Matchable lists are distinct (section 19), first-class ones included.
(def-fns _ $ many listed : (subterm many (List (Bin)) opens) (many (Env) env) (many (Bin) x) (many (Bin) y) -> (many (Bool) r)
  (match many opens _
    ((Nil a) (BFalse))
    ((Cons a o rest)
      (let (many here)
        (match many (type-of env o) (((Bool) b))
          ((TMatchable d t cs) (and (mctors-list cs x) (mctors-list cs y))) (else (BFalse))))
      (match many here _
        ((BTrue) (BTrue))
        ((BFalse) (listed rest env x y))))))

; The opened Matchable a type constructor heads, if any.
(def-fns _ $ many matchable-heading : (subterm many (List (Bin)) opens) (many (Env) env) (many (Bin) z) -> (many (Maybe (Term)) r)
  (match many opens _
    ((Nil a) (None (Term)))
    ((Cons a o rest)
      (let (many ty) (type-of env o))
      (let (many hit)
        (match many ty (((Bool) b))
          ((TMatchable d t cs) (match many t (((Bool) b)) ((TVar z2) (bin-eq z z2)) (else (BFalse)))) (else (BFalse))))
      (match many hit _
        ((BTrue) (Some (Term) ty))
        ((BFalse) (matchable-heading rest env z))))))

(def-fns _ $ many signature-of : (many (Env) env) (many (Bin) z) -> (many (Maybe (Term)) r)
  (match many (type-of env z) _
    ((TTyCtor p) (Some (Term) (TTyCtor p)))
    ((TValCtor p r) (Some (Term) (TValCtor p r))) (else (None (Term)))))

; Whether a term mentions a binder no telescope of its own binds (a dangling de Bruijn index) at depth d.
(def-fns _
  (many dangling : (subterm many (Term) t) (many (Nat) d) -> (many (Bool) r)
    (match many t _
      ((TBound k) (not (nat-lt k d)))
      ((TApp h args) (or (dangling h d) (dangling-list args d)))
      ((TFn l ps rs) (or (dangling l d) (or (dangling-tele ps d) (dangling-tele rs (nat-add d (list-length (Entry) ps))))))
      ((TTyCtor ps) (dangling-tele ps d))
      ((TValCtor ps ret) (or (dangling-tele ps d) (dangling ret (nat-add d (list-length (Entry) ps)))))
      ((TMatchable disc ty cs) (or (dangling ty d) (dangling-mctors cs d)))
      ((TNewtype c) (dangling c d)) (else (BFalse))))
  (many dangling-list : (subterm many (List (Term)) ts) (many (Nat) d) -> (many (Bool) r)
    (match many ts _
      ((Nil a) (BFalse))
      ((Cons a t rest) (or (dangling t d) (dangling-list rest d)))))
  (many dangling-mctors : (subterm many (List (MCtor)) cs) (many (Nat) d) -> (many (Bool) r)
    (match many cs _
      ((Nil a) (BFalse))
      ((Cons a c rest) (match many c _ ((MkMCtor m t) (or (dangling t d) (dangling-mctors rest d)))))))
  (many dangling-tele : (subterm many (List (Entry)) es) (many (Nat) d) -> (many (Bool) r)
    (match many es _
      ((Nil a) (BFalse))
      ((Cons a e rest)
        (match many e _
          ((MkEntry n s m sg)
            (or (match many sg (((Bool) b)) ((SgTy t) (dangling t d)) ((SgIs t) (dangling t d)))
              (dangling-tele rest (Succ d)))))))))

(def-fns _ $ many contradiction : (erased (Nat) n) (many (Bin) bnd) (many (Env) env) (many (Term) a) (many (Term) b) -> (many (Outcome n bnd) r)
  (Contra n bnd (rope-str (rcat3 (show-term a env) (RStr " vs ") (show-term b env)))))

; A variable against a term: a dangling binder refutes, and so does the variable occurring in the term,
; which is the term not being fresh once the variable is ruled out (section 18).
(def-fns _ $ many bind-var : (erased (Nat) n) (erased (Facts n) f) (many (Bin) bnd) (many (Table n f bnd) tb) (many (Env) env) (many (Bin) x) (erased (In x n f) p) (many (Term) t) (many (Term) a) (many (Term) b) -> (many (Outcome n bnd) r)
  (match many (dangling t 0) _
    ((BTrue) (contradiction n bnd env a b))
    ((BFalse)
      (match many (rule-out-refresh n f bnd tb x p t) _
        ((None c) (Contra n bnd (rope-str (rcat3 (RStr (name-of env x)) (RStr " occurs in ") (show-term t env)))))
        ((Some c added)
          (match many added _
            ((MkAdded k f0 f2 tb2c tb2) (Less n bnd k f2 tb2 (env-set-table env k f2 bnd tb2) (prove-subterm k n)))))))))

(def-fns _
  (many unify : (subterm erased (Nat) n) (erased (Facts n) f) (many (Bin) bnd) (many (Table n f bnd) tb) (subterm many (Term) a) (erased (Fr n f a) pa) (many (Term) b) (erased (Fr n f b) pb) (many (Env) env) -> (many (Outcome n bnd) r)
    (match many (term-eq a b) _
      ((BTrue) (Same n bnd))
      ((BFalse)
        (match many a _
          ((TVar x)
            (match many b _
              ((TVar y)
              (let (erased px) (fr-var n f x pa))
              (let (erased py) (fr-var n f y pb))
              (match many (bin-eq-dec x y) _
                ((BYes c1 c2 e) (Same n bnd))
                ((BNo c1 c2 ne)
                  (match many (listed (env-opens env) env x y) _
                    ((BTrue) (contradiction n bnd env a b))
                    ((BFalse)
                      (let (many newer) (many older) (erased pn) (erased po) (erased neq)
                        (match many (bin-lt x y) (((Bin) nw) ((Bin) ol) ((In nw n f) p1) ((In ol n f) p2) ((Neq ol nw) q))
                          ((BTrue) (values y x py px ne))
                          ((BFalse) (values x y px py (neq-sym x y ne)))))
                      (let (many sx) (signature-of env newer))
                      (let (many sy) (signature-of env older))
                      (let (many mx) (matchable-heading (env-opens env) env newer))
                      (let (many my) (matchable-heading (env-opens env) env older))
                      (match many (rule-out-var n f bnd tb newer older pn po neq) _
                        ((MkAdded k f0 f2 tb2c tb2)
                          (let (many env2) (env-set-table env k f2 bnd tb2))
                          (let (erased p) (prove-subterm k n))
                          (let (many after-sig)
                            (match many sx (((Outcome k bnd) r))
                              ((None c) (Same k bnd))
                              ((Some c s)
                                (match many sy (((Outcome k bnd) r))
                                  ((None d) (Same k bnd))
                                  ((Some d s2)
                                    (let (many s3) (erased ps3) (canon-in k f2 bnd tb2 s))
                                    (let (many s4) (erased ps4) (canon-in k f2 bnd tb2 s2))
                                    (unify k f2 bnd tb2 s3 ps3 s4 ps4 env2))))))
                          (match many after-sig _
                            ((Contra c cc m) (Contra n bnd m))
                            ((Same c cc)
                              (match many mx (((Outcome n bnd) r))
                                ((None d) (Less n bnd k f2 tb2 env2 p))
                                ((Some d m1)
                                  (match many my (((Outcome n bnd) r))
                                    ((None e) (Less n bnd k f2 tb2 env2 p))
                                    ((Some e m2)
                                      (let (many m3) (erased pm3) (canon-in k f2 bnd tb2 m1))
                                      (let (many m4) (erased pm4) (canon-in k f2 bnd tb2 m2))
                                      (lift n bnd k f2 tb2 env2 p (unify k f2 bnd tb2 m3 pm3 m4 pm4 env2)))))))
                            ((Less c cc j f3 tb3 env3 q)
                              (match many mx (((Outcome n bnd) r))
                                ((None d) (Less n bnd j f3 tb3 env3 (subterm-trans q p)))
                                ((Some d m1)
                                  (match many my (((Outcome n bnd) r))
                                    ((None e) (Less n bnd j f3 tb3 env3 (subterm-trans q p)))
                                    ((Some e m2)
                                      (let (many m3) (erased pm3) (canon-in j f3 bnd tb3 m1))
                                      (let (many m4) (erased pm4) (canon-in j f3 bnd tb3 m2))
                                      (lift n bnd j f3 tb3 env3 (subterm-trans q p) (unify (subterm (subterm-trans q p)) j f3 bnd tb3 m3 pm3 m4 pm4 env3)))))))))))))))
              ((TBound j) (contradiction n bnd env a b))
              ((TErr m) (Contra n bnd m)) (else (bind-var n f bnd tb env x (fr-var n f x pa) b a b))))
          ((TBound j) (contradiction n bnd env a b))
          ((TApp h as)
            (match many b _
              ((TVar y) (bind-var n f bnd tb env y (fr-var n f y pb) a a b))
              ((TApp h2 as2)
                (match many (nat-eq (list-length (Term) as) (list-length (Term) as2)) _
                  ((BFalse) (contradiction n bnd env a b))
                  ((BTrue)
                    (let (erased ph) (erased pas) (fr-app n f h as pa))
                    (let (erased ph2) (erased pas2) (fr-app n f h2 as2 pb))
                    (match many (unify n f bnd tb h ph h2 ph2 env) _
                      ((Same c cc) (unify-list n f bnd tb as pas as2 pas2 env))
                      ((Less c cc k f2 tb2 env2 p)
                        (let (many as3) (erased pas3) (canon-list-in k f2 bnd tb2 as))
                        (let (many bs3) (erased pbs3) (canon-list-in k f2 bnd tb2 as2))
                        (lift n bnd k f2 tb2 env2 p (unify-list (subterm p) k f2 bnd tb2 as3 pas3 bs3 pbs3 env2)))
                      ((Contra c cc m) (Contra n bnd m))))))
              ((TErr m) (Contra n bnd m)) (else (contradiction n bnd env a b))))
          ((TFn l ps rs)
            (match many b _
              ((TVar y) (bind-var n f bnd tb env y (fr-var n f y pb) a a b))
              ((TFn l2 ps2 rs2)
                (let (erased pl) (erased pps) (erased prs) (fr-fn n f l ps rs pa))
                (let (erased pl2) (erased pps2) (erased prs2) (fr-fn n f l2 ps2 rs2 pb))
                (match many (unify n f bnd tb l pl l2 pl2 env) _
                  ((Contra c cc m) (Contra n bnd m))
                  ((Same c cc)
                    (match many (unify-tele n f bnd tb ps pps ps2 pps2 env a b) _
                      ((Contra d dc m) (Contra n bnd m))
                      ((Same d dc) (unify-tele n f bnd tb rs prs rs2 prs2 env a b))
                      ((Less d dc k f2 tb2 env2 p)
                        (let (many rs3) (erased prs3) (canon-tele-in k f2 bnd tb2 rs))
                        (let (many rs4) (erased prs4) (canon-tele-in k f2 bnd tb2 rs2))
                        (lift n bnd k f2 tb2 env2 p (unify-tele (subterm p) k f2 bnd tb2 rs3 prs3 rs4 prs4 env2 a b)))))
                  ((Less c cc k f2 tb2 env2 p)
                    (let (many ps3) (erased pps3) (canon-tele-in k f2 bnd tb2 ps))
                    (let (many ps4) (erased pps4) (canon-tele-in k f2 bnd tb2 ps2))
                    (match many (unify-tele (subterm p) k f2 bnd tb2 ps3 pps3 ps4 pps4 env2 a b) _
                      ((Contra d dc m) (Contra n bnd m))
                      ((Same d dc)
                        (let (many rs3) (erased prs3) (canon-tele-in k f2 bnd tb2 rs))
                        (let (many rs4) (erased prs4) (canon-tele-in k f2 bnd tb2 rs2))
                        (lift n bnd k f2 tb2 env2 p (unify-tele (subterm p) k f2 bnd tb2 rs3 prs3 rs4 prs4 env2 a b)))
                      ((Less d dc j f3 tb3 env3 q)
                        (let (many rs3) (erased prs3) (canon-tele-in j f3 bnd tb3 rs))
                        (let (many rs4) (erased prs4) (canon-tele-in j f3 bnd tb3 rs2))
                        (lift n bnd j f3 tb3 env3 (subterm-trans q p) (unify-tele (subterm (subterm-trans q p)) j f3 bnd tb3 rs3 prs3 rs4 prs4 env3 a b)))))))
              ((TErr m) (Contra n bnd m)) (else (contradiction n bnd env a b))))
          ((TTyCtor ps)
            (match many b _
              ((TVar y) (bind-var n f bnd tb env y (fr-var n f y pb) a a b))
              ((TTyCtor ps2) (unify-tele n f bnd tb ps (fr-tyctor n f ps pa) ps2 (fr-tyctor n f ps2 pb) env a b))
              ((TErr m) (Contra n bnd m)) (else (contradiction n bnd env a b))))
          ((TValCtor ps ret)
            (match many b _
              ((TVar y) (bind-var n f bnd tb env y (fr-var n f y pb) a a b))
              ((TValCtor ps2 ret2)
                (let (erased pps) (erased pret) (fr-valctor n f ps ret pa))
                (let (erased pps2) (erased pret2) (fr-valctor n f ps2 ret2 pb))
                (match many (unify-tele n f bnd tb ps pps ps2 pps2 env a b) _
                  ((Contra c cc m) (Contra n bnd m))
                  ((Same c cc) (unify n f bnd tb ret pret ret2 pret2 env))
                  ((Less c cc k f2 tb2 env2 p)
                    (let (many ret3) (erased pret3) (canon-in k f2 bnd tb2 ret))
                    (let (many ret4) (erased pret4) (canon-in k f2 bnd tb2 ret2))
                    (lift n bnd k f2 tb2 env2 p (unify (subterm p) k f2 bnd tb2 ret3 pret3 ret4 pret4 env2)))))
              ((TErr m) (Contra n bnd m)) (else (contradiction n bnd env a b))))
          ((TMatchable d t cs)
            (match many b _
              ((TVar y) (bind-var n f bnd tb env y (fr-var n f y pb) a a b))
              ((TMatchable d2 t2 cs2)
                (match many (and (disc-eq d d2) (nat-eq (list-length (MCtor) cs) (list-length (MCtor) cs2))) _
                  ((BFalse) (contradiction n bnd env a b))
                  ((BTrue)
                    (let (erased pt) (erased pcs) (fr-matchable n f d t cs pa))
                    (let (erased pt2) (erased pcs2) (fr-matchable n f d2 t2 cs2 pb))
                    (match many (unify n f bnd tb t pt t2 pt2 env) _
                      ((Contra c cc m) (Contra n bnd m))
                      ((Same c cc) (unify-mctors n f bnd tb cs pcs cs2 pcs2 env a b))
                      ((Less c cc k f2 tb2 env2 p)
                        (let (many cs3) (erased pcs3) (canon-mctors-in k f2 bnd tb2 cs))
                        (let (many cs4) (erased pcs4) (canon-mctors-in k f2 bnd tb2 cs2))
                        (lift n bnd k f2 tb2 env2 p (unify-mctors (subterm p) k f2 bnd tb2 cs3 pcs3 cs4 pcs4 env2 a b)))))))
              ((TErr m) (Contra n bnd m)) (else (contradiction n bnd env a b))))
          ((TNewtype cn)
            (match many b _
              ((TVar y) (bind-var n f bnd tb env y (fr-var n f y pb) a a b))
              ((TNewtype cn2) (unify n f bnd tb cn (fr-newtype n f cn pa) cn2 (fr-newtype n f cn2 pb) env))
              ((TErr m) (Contra n bnd m)) (else (contradiction n bnd env a b))))
          ((TErr m) (Contra n bnd m))))))

  (many unify-list : (subterm erased (Nat) n) (erased (Facts n) f) (many (Bin) bnd) (many (Table n f bnd) tb) (subterm many (List (Term)) as) (erased (FrL n f as) pas) (many (List (Term)) bs) (erased (FrL n f bs) pbs) (many (Env) env) -> (many (Outcome n bnd) r)
    (match many as _
      ((Nil x) (Same n bnd))
      ((Cons x a rest)
        (match many bs _
          ((Nil y) (Same n bnd))
          ((Cons y b rest2)
            (let (erased pa) (erased prest) (frl-cons n f a rest pas))
            (let (erased pb) (erased prest2) (frl-cons n f b rest2 pbs))
            (match many (unify n f bnd tb a pa b pb env) _
              ((Contra c cc m) (Contra n bnd m))
              ((Same c cc) (unify-list n f bnd tb rest prest rest2 prest2 env))
              ((Less c cc k f2 tb2 env2 p)
                (let (many rest3) (erased prest3) (canon-list-in k f2 bnd tb2 rest))
                (let (many rest4) (erased prest4) (canon-list-in k f2 bnd tb2 rest2))
                (lift n bnd k f2 tb2 env2 p (unify-list (subterm p) k f2 bnd tb2 rest3 prest3 rest4 prest4 env2)))))))))

  ; Telescopes unify entry by entry; a different length, multiplicity or subterm mark is a mismatch of shape.
  (many unify-tele : (subterm erased (Nat) n) (erased (Facts n) f) (many (Bin) bnd) (many (Table n f bnd) tb) (subterm many (List (Entry)) as) (erased (FrT n f as) pas) (many (List (Entry)) bs) (erased (FrT n f bs) pbs) (many (Env) env) (many (Term) wa) (many (Term) wb) -> (many (Outcome n bnd) r)
    (match many as _
      ((Nil x) (match many bs _ ((Nil y) (Same n bnd)) ((Cons y b rest2) (contradiction n bnd env wa wb))))
      ((Cons x a rest)
        (match many bs _
          ((Nil y) (contradiction n bnd env wa wb))
          ((Cons y b rest2)
            (match many a _
              ((MkEntry nm s m sg)
                (match many b _
                  ((MkEntry nm2 s2 m2 sg2)
                    (match many (and (mult-eq m m2) (bool-eq s s2)) _
                      ((BFalse) (contradiction n bnd env wa wb))
                      ((BTrue)
                        (let (erased psg) (erased prest) (frt-cons n f nm s m sg rest pas))
                        (let (erased psg2) (erased prest2) (frt-cons n f nm2 s2 m2 sg2 rest2 pbs))
                        (match many (unify-sg n f bnd tb sg psg sg2 psg2 env) _
                          ((Contra c cc msg) (Contra n bnd msg))
                          ((Same c cc) (unify-tele n f bnd tb rest prest rest2 prest2 env wa wb))
                          ((Less c cc k f2 tb2 env2 p)
                            (let (many rest3) (erased prest3) (canon-tele-in k f2 bnd tb2 rest))
                            (let (many rest4) (erased prest4) (canon-tele-in k f2 bnd tb2 rest2))
                            (lift n bnd k f2 tb2 env2 p (unify-tele (subterm p) k f2 bnd tb2 rest3 prest3 rest4 prest4 env2 wa wb)))))))))))))))

  (many unify-sg : (subterm erased (Nat) n) (erased (Facts n) f) (many (Bin) bnd) (many (Table n f bnd) tb) (subterm many (Sg) sg) (erased (FrS n f sg) psg) (many (Sg) sg2) (erased (FrS n f sg2) psg2) (many (Env) env) -> (many (Outcome n bnd) r)
    (match many sg _
      ((SgTy t)
        (match many sg2 _
          ((SgTy t2) (unify n f bnd tb t (frs-ty n f t psg) t2 (frs-ty n f t2 psg2) env))
          ((SgIs t2) (unify n f bnd tb t (frs-ty n f t psg) t2 (frs-is n f t2 psg2) env))))
      ((SgIs t)
        (match many sg2 _
          ((SgTy t2) (unify n f bnd tb t (frs-is n f t psg) t2 (frs-ty n f t2 psg2) env))
          ((SgIs t2) (unify n f bnd tb t (frs-is n f t psg) t2 (frs-is n f t2 psg2) env))))))

  (many unify-mctors : (subterm erased (Nat) n) (erased (Facts n) f) (many (Bin) bnd) (many (Table n f bnd) tb) (subterm many (List (MCtor)) as) (erased (FrM n f as) pas) (many (List (MCtor)) bs) (erased (FrM n f bs) pbs) (many (Env) env) (many (Term) wa) (many (Term) wb) -> (many (Outcome n bnd) r)
    (match many as _
      ((Nil x) (Same n bnd))
      ((Cons x a rest)
        (match many bs _
          ((Nil y) (Same n bnd))
          ((Cons y b rest2)
            (match many a _
              ((MkMCtor m t)
                (match many b _
                  ((MkMCtor m2 t2)
                    (match many (mult-eq m m2) _
                      ((BFalse) (contradiction n bnd env wa wb))
                      ((BTrue)
                        (let (erased pt) (erased prest) (frm-cons n f m t rest pas))
                        (let (erased pt2) (erased prest2) (frm-cons n f m2 t2 rest2 pbs))
                        (match many (unify n f bnd tb t pt t2 pt2 env) _
                          ((Contra c cc msg) (Contra n bnd msg))
                          ((Same c cc) (unify-mctors n f bnd tb rest prest rest2 prest2 env wa wb))
                          ((Less c cc k f2 tb2 env2 p)
                            (let (many rest3) (erased prest3) (canon-mctors-in k f2 bnd tb2 rest))
                            (let (many rest4) (erased prest4) (canon-mctors-in k f2 bnd tb2 rest2))
                            (lift n bnd k f2 tb2 env2 p (unify-mctors (subterm p) k f2 bnd tb2 rest3 prest3 rest4 prest4 env2 wa wb))))))))))))))))

(def-fns _ $ many unify-env : (many (Env) env) (many (Term) a) (many (Term) b) -> (many (UnifyRes) r)
  (let (erased n) (erased f) (many bnd) (many tb) (env-table env))
  (let (many a1) (erased pa) (canon-in n f bnd tb a))
  (let (many b1) (erased pb) (canon-in n f bnd tb b))
  (match many (unify n f bnd tb a1 pa b1 pb env) _
    ((Same c cc) (UOk env))
    ((Less c cc k f2 tb2 env2 p) (UOk env2))
    ((Contra c cc m) (UContra m))))

; Extern construction and destruction over the host's own values (section 41; lib/ffi_core.ml).
(def-fns _ $ many ext-destruct : (many (Adt) adt) (many (Payload) p) -> (many (Nat) index) (many (List (Value)) fields)
  (let (many nat-adt) (MkAdt "Nat" (BTrue) (Nil (Ctor)) (Some (String) "Nat")))
  (match many p _
    ((PNat n) (match many n _ ((Zero) (values 0 (Nil (Value)))) ((Succ k) (values 1 (Cons (Value) (VExt adt (PNat k)) (Nil (Value)))))))
    ((PBin b) (match many b _ ((BZ) (values 0 (Nil (Value)))) ((B1 r) (values 1 (Cons (Value) (VExt adt (PBin r)) (Nil (Value)))))
                ((B2 r) (values 2 (Cons (Value) (VExt adt (PBin r)) (Nil (Value)))))))
    ((PStr s) (match many s _ ((SNil) (values 0 (Nil (Value))))
                ((SCons c rest) (values 1 (Cons (Value) (VExt nat-adt (PNat (char-code c))) (Cons (Value) (VExt adt (PStr rest)) (Nil (Value))))))))
    ((PDec i) (values i (Nil (Value))))))

(def-fns _ $ many value-nat : (many (Value) v) -> (many (Nat) n)
  (match many v _
    ((VExt a p) (match many p _ ((PNat n) n) ((PDec i) i) (else 0))) (else 0)))

(def-fns _ $ many value-bin : (many (Value) v) -> (many (Bin) n)
  (match many v _
    ((VExt a p) (match many p _ ((PBin b) b) (else (BZ)))) (else (BZ))))

(def-fns _ $ many value-str : (many (Value) v) -> (many (String) n)
  (match many v _
    ((VExt a p) (match many p _ ((PStr s) s) (else (SNil)))) (else (SNil))))

; Builds an extern value from a constructor index and its many fields.
(def-fns _ $ many ext-construct : (many (Adt) adt) (many (String) ext) (many (Nat) index) (many (List (Value)) fields) -> (many (Value) v)
  (let (many f0) (match many fields (((Value) x)) ((Nil a) (VToken)) ((Cons a f rest) f)))
  (let (many f1) (match many fields (((Value) x)) ((Nil a) (VToken)) ((Cons a f rest) (match many rest (((Value) y)) ((Nil b) (VToken)) ((Cons b g rest2) g)))))
  (match many (str-eq ext "Nat") _
    ((BTrue) (VExt adt (PNat (match many index (((Nat) n)) ((Zero) (Zero)) ((Succ k) (Succ (value-nat f0)))))))
    ((BFalse)
      (match many (str-eq ext "Bin") _
        ((BTrue) (VExt adt (PBin (match many index (((Bin) b)) ((Zero) (BZ)) ((Succ k) (match many k (((Bin) b)) ((Zero) (B1 (value-bin f0))) ((Succ k2) (B2 (value-bin f0)))))))))
        ((BFalse)
          (match many (str-eq ext "String") _
            ((BTrue) (VExt adt (PStr (match many index (((String) s)) ((Zero) (SNil)) ((Succ k) (SCons (char-of-code (value-nat f0)) (value-str f1)))))))
            ((BFalse) (VExt adt (PDec index)))))))))

(def-fns _ $ many construct : (many (Ctor) c) (many (List (Value)) args) -> (many (Value) v)
  (match many c _
    ((MkCtor name id index arity tagged ext)
      (match many ext _
        ((Some a e) (ext-construct (MkAdt (SNil) tagged (Nil (Ctor)) ext) e index args))
        ((None a) (match many tagged _ ((BTrue) (VCtor c args)) ((BFalse) (tuple args))))))))

; A value's discriminant and many fields where the FFI holds the type or a tag says (section 38); None
; otherwise, the value then being its fields as they stand.
(def-fns _ $ many dispatch : (many (Maybe (String)) ext) (many (Bool) tagged) (many (Value) v) -> (many (Maybe (Pair (Nat) (List (Value)))) r)
  (match many v _
    ((VExt adt p)
      (match many ext _
        ((None a) (None (Pair (Nat) (List (Value)))))
        ((Some a e)
          (let (many i) (many fs) (ext-destruct adt p))
          (Some (Pair (Nat) (List (Value))) (MkPair (Nat) (List (Value)) i fs)))))
    ((VCtor c fs)
      (match many tagged _
        ((BTrue) (Some (Pair (Nat) (List (Value))) (MkPair (Nat) (List (Value)) (ctor-index c) fs)))
        ((BFalse) (None (Pair (Nat) (List (Value))))))) (else (None (Pair (Nat) (List (Value)))))))

(def-fns _ $ many destruct : (many (Ctor) c) (many (Value) v) -> (many (Nat) i) (many (List (Value)) fields)
  (match many c _
    ((MkCtor name id index arity tagged ext)
      (match many (dispatch ext tagged v) _
        ((Some a p) (match many p _ ((MkPair x y i fs) (values i fs))))
        ((None a) (values index (untuple arity v)))))))

(def-fns _ $ many ctor-at : (many (Adt) adt) (many (Nat) i) -> (many (Maybe (Ctor)) c)
  (list-nth (Ctor) (adt-ctors adt) i))

(def-fns _ $ many show-nat : (subterm many (Nat) n) -> (many (Rope) r)
    (match many n _
      ((Zero) (RStr "(Zero)"))
      ((Succ k) (rcat3 (RStr "(Succ ") (show-nat k) (RStr ")")))))

(def-fns _ $ many show-bin : (subterm many (Bin) b) -> (many (Rope) r)
    (match many b _
      ((BZ) (RStr "(BZ)"))
      ((B1 r) (rcat3 (RStr "(B1 ") (show-bin r) (RStr ")")))
      ((B2 r) (rcat3 (RStr "(B2 ") (show-bin r) (RStr ")")))))

(def-fns _ $ many show-str : (subterm many (String) s) -> (many (Rope) r)
    (match many s _
      ((SNil) (RStr "(SNil)"))
      ((SCons c rest) (rcat5 (RStr "(SCons ") (show-nat (char-code c)) (RStr " ") (show-str rest) (RStr ")")))))

(def-fns _
  (many show-value : (subterm many (Value) v) -> (many (Rope) r)
    (match many v _
      ((VCtor c fields) (rcat4 (RStr "(") (RStr (ctor-name c)) (show-values fields) (RStr ")")))
      ((VTuple fields) (rcat3 (RStr "(") (show-values-bare fields) (RStr ")")))
      ((VExt adt p) (show-payload p adt))
      ((VCtorFn c) (rcat3 (RStr "<constructor ") (RStr (ctor-name c)) (RStr ">")))
      ((VMatchable adt) (rcat3 (RStr "<matchable ") (RStr (adt-name adt)) (RStr ">")))
      ((VFn cl) (match many cl _ ((MkClosure fn g e) (rcat3 (RStr "<function ") (RStr (func-name fn)) (RStr ">")))))
      ((VToken) (RStr "_"))
      ((VError m) (rcat3 (RStr "<error: ") (RStr m) (RStr ">")))))
  (many show-values : (subterm many (List (Value)) vs) -> (many (Rope) r)
    (match many vs _
      ((Nil a) (REmpty))
      ((Cons a v rest) (rcat3 (RStr " ") (show-value v) (show-values rest)))))
  (many show-values-bare : (subterm many (List (Value)) vs) -> (many (Rope) r)
    (match many vs _
      ((Nil a) (REmpty))
      ((Cons a v rest)
        (match many rest _
          ((Nil b) (show-value v))
          ((Cons b w rest2) (rcat3 (show-value v) (RStr " ") (show-values-bare rest)))))))
  ; An extern value prints through its model's constructors, as the interpreter does.
  (many show-payload : (subterm many (Payload) p) (many (Adt) adt) -> (many (Rope) r)
    (match many p _
      ((PNat n) (show-nat n))
      ((PBin b) (show-bin b))
      ((PStr s) (show-str s))
      ((PDec i) (match many i _ ((Zero) (RStr "(Yes)")) ((Succ k) (RStr "(No)")))))))
