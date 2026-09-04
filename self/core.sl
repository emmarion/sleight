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
    ((Cons a m rest) (match many m _ ((Many) (Many)) ((Erased) (pos-of (subterm _) rest))))))

(def-fns _ $ many many-count : (subterm many (List (Entry)) es) -> (many (Nat) n)
  (match many es _
    ((Nil a) (Zero))
    ((Cons a e rest)
      (match many (entry-mult (predates _) e) _
        ((Many) (Succ (many-count (subterm _) rest)))
        ((Erased) (many-count (subterm _) rest))))))

(def-fns _ $ many tele-mults : (subterm many (List (Entry)) es) -> (many (List (Mult)) ms)
  (match many es _
    ((Nil a) (Nil (Mult)))
    ((Cons a e rest) (Cons (Mult) (entry-mult (predates _) e) (tele-mults (subterm _) rest)))))

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
    (many StDefAdts : -> (StmtK)) (many StComptimeMatch : -> (StmtK)))
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
    (many ExCoercibleWrap : -> (ExprK)) (many ExCoercibleCtor : -> (ExprK)) (many ExCoercibleOf : -> (ExprK)))
  (MarkK : -> Type
    enum
    (many MkErased : -> (MarkK)) (many MkMany : -> (MarkK)) (many MkColon : -> (MarkK)) (many MkIs : -> (MarkK))
    (many MkArrow : -> (MarkK)) (many MkSubterm : -> (MarkK)) (many MkEnum : -> (MarkK)) (many MkUnion : -> (MarkK))
    (many MkTail : -> (MarkK)) (many MkDelegate : -> (MarkK)) (many MkPredates : -> (MarkK)) (many MkAbsurd : -> (MarkK))
    (many MkNewtypeMark : -> (MarkK)) (many MkExtern : -> (MarkK))))

(def-fns _ $ many stmt-code : (many (StmtK) k) -> (many (Nat) n)
  (match many k _ ((StLet) 0) ((StDefLvl) 1) ((StDefFns) 2) ((StDefAdts) 3) ((StComptimeMatch) 4)))

(def-fns _ $ many former-code : (many (FormerK) k) -> (many (Nat) n)
  (match many k _ ((FoFn) 0) ((FoTyCtor) 1) ((FoValCtor) 2) ((FoMatchable) 3) ((FoNewtype) 4)))

(def-fns _ $ many expr-code : (many (ExprK) k) -> (many (Nat) n)
  (match many k _
    ((ExMatch) 0) ((ExMatchableOf) 1) ((ExNewtypeOf) 2) ((ExNumeralOf) 3) ((ExLevelOf) 4) ((ExProveSubterm) 5)
    ((ExProvePredates) 6) ((ExValues) 7) ((ExPredatesTrans) 8) ((ExSubtermTrans) 9) ((ExPredatesSubterm) 10)
    ((ExCoerce) 11) ((ExCoercibleRefl) 12) ((ExCoercibleSym) 13) ((ExCoercibleTrans) 14) ((ExCoercibleWrap) 15)
    ((ExCoercibleCtor) 16) ((ExCoercibleOf) 17)))

(def-fns _ $ many mark-code : (many (MarkK) k) -> (many (Nat) n)
  (match many k _
    ((MkErased) 0) ((MkMany) 1) ((MkColon) 2) ((MkIs) 3) ((MkArrow) 4) ((MkSubterm) 5) ((MkEnum) 6) ((MkUnion) 7)
    ((MkTail) 8) ((MkDelegate) 9) ((MkPredates) 10) ((MkAbsurd) 11) ((MkNewtypeMark) 12) ((MkExtern) 13)))

(def-fns _ $ many sp-code : (many (Sp) sp) -> (many (Nat) n)
  (match many sp _
    ((SpStmt k) (stmt-code (predates _) k))
    ((SpFormer k) (nat-add (predates _) 10 (former-code (predates _) k)))
    ((SpExpr k) (nat-add (predates _) 20 (expr-code (predates _) k)))
    ((SpMark k) (nat-add (predates _) 40 (mark-code (predates _) k)))))

(def-fns _ $ many sp-eq : (many (Sp) a) (many (Sp) b) -> (many (Bool) r)
  (nat-eq (predates _) (sp-code (predates _) a) (sp-code (predates _) b)))

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
  sp-cons "newtype" (SpMark (MkNewtypeMark)) $ sp-cons "extern" (SpMark (MkExtern)) (Nil (SpEntry))))

(def-fns _ $ many sp-of-index : (many (Nat) i) -> (many (Maybe (Sp)) r)
  (match many (list-nth (predates _) (SpEntry) sp-table i) _
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
    (many PU8 : (many (U8) u) -> (Payload))
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
    (many CMatch : (many (Code) scrut) (many (Shape) shape) (many (List (Branch)) branches) -> (Code))
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
            ((VTuple vs) vs)
            ((VCtor c fs) (Nil (Value)))
            ((VExt a p) (Nil (Value)))
            ((VCtorFn c) (Nil (Value)))
            ((VMatchable a) (Nil (Value)))
            ((VFn cl) (Nil (Value)))
            ((VToken) (Nil (Value)))
            ((VError m) (Nil (Value)))))))))

; ---- The scope environment (section 3) and fact table (section 18)

(def-adts
  (Env : -> Type
    enum
    (many MkEnv : (many (NameMap (Bin)) scope) (many (IdMap (EInfo)) entries) (many (IdMap (Fact)) facts)
       (many (Bool) run-pos) (many (IdMap (Value)) values) (many (List (Bin)) objects)
       (many (NameMap (Bin)) literals) (many (Bin) fresh) (many (List (Trace)) trace) (many (List (String)) errors) -> (Env)))
  (EInfo : -> Type
    enum
    (many MkEInfo : (many (Maybe (String)) name) (many (Mult) mult) (many (State) state) -> (EInfo)))
  (State : -> Type
    enum
    (many SConst : (many (Value) v) -> (State))
    (many SDyn : -> (State)))
  (Fact : -> Type
    enum
    (many MkFact : (many (Term) ty) (many (Maybe (Term)) rule) -> (Fact)))
  (Trace : -> Type
    enum
    (many TrFns : (many (List (Pair (Bin) (Func))) fns) -> (Trace))
    (many TrConst : (many (Bin) id) (many (Value) v) -> (Trace))
    (many TrFinal : (many (Value) v) (many (Term) ty) -> (Trace))))

(def-fns _ $ many env-scope : (many (Env) e) -> (many (NameMap (Bin)) r)
  (match many e _ ((MkEnv sc en fa rp va ob li fr tr er) sc)))
(def-fns _ $ many env-entries : (many (Env) e) -> (many (IdMap (EInfo)) r)
  (match many e _ ((MkEnv sc en fa rp va ob li fr tr er) en)))
(def-fns _ $ many env-facts : (many (Env) e) -> (many (IdMap (Fact)) r)
  (match many e _ ((MkEnv sc en fa rp va ob li fr tr er) fa)))
(def-fns _ $ many env-run-pos : (many (Env) e) -> (many (Bool) r)
  (match many e _ ((MkEnv sc en fa rp va ob li fr tr er) rp)))
(def-fns _ $ many env-values : (many (Env) e) -> (many (IdMap (Value)) r)
  (match many e _ ((MkEnv sc en fa rp va ob li fr tr er) va)))
(def-fns _ $ many env-objects : (many (Env) e) -> (many (List (Bin)) r)
  (match many e _ ((MkEnv sc en fa rp va ob li fr tr er) ob)))
(def-fns _ $ many env-literals : (many (Env) e) -> (many (NameMap (Bin)) r)
  (match many e _ ((MkEnv sc en fa rp va ob li fr tr er) li)))
(def-fns _ $ many env-fresh : (many (Env) e) -> (many (Bin) r)
  (match many e _ ((MkEnv sc en fa rp va ob li fr tr er) fr)))
(def-fns _ $ many env-trace : (many (Env) e) -> (many (List (Trace)) r)
  (match many e _ ((MkEnv sc en fa rp va ob li fr tr er) tr)))
(def-fns _ $ many env-errors : (many (Env) e) -> (many (List (String)) r)
  (match many e _ ((MkEnv sc en fa rp va ob li fr tr er) er)))

(def-fns _ $ many env-set-scope : (many (Env) e) (many (NameMap (Bin)) x) -> (many (Env) r)
  (match many e _ ((MkEnv sc en fa rp va ob li fr tr er) (MkEnv x en fa rp va ob li fr tr er))))
(def-fns _ $ many env-set-facts : (many (Env) e) (many (IdMap (Fact)) x) -> (many (Env) r)
  (match many e _ ((MkEnv sc en fa rp va ob li fr tr er) (MkEnv sc en x rp va ob li fr tr er))))
(def-fns _ $ many env-set-run-pos : (many (Env) e) (many (Bool) x) -> (many (Env) r)
  (match many e _ ((MkEnv sc en fa rp va ob li fr tr er) (MkEnv sc en fa x va ob li fr tr er))))
(def-fns _ $ many env-set-literals : (many (Env) e) (many (NameMap (Bin)) x) -> (many (Env) r)
  (match many e _ ((MkEnv sc en fa rp va ob li fr tr er) (MkEnv sc en fa rp va ob x fr tr er))))
(def-fns _ $ many env-set-fresh : (many (Env) e) (many (Bin) x) -> (many (Env) r)
  (match many e _ ((MkEnv sc en fa rp va ob li fr tr er) (MkEnv sc en fa rp va ob li x tr er))))
(def-fns _ $ many env-push-trace : (many (Env) e) (many (Trace) x) -> (many (Env) r)
  (match many e _ ((MkEnv sc en fa rp va ob li fr tr er) (MkEnv sc en fa rp va ob li fr (Cons (Trace) x tr) er))))
(def-fns _ $ many env-error : (many (Env) e) (many (String) x) -> (many (Env) r)
  (match many e _ ((MkEnv sc en fa rp va ob li fr tr er) (MkEnv sc en fa rp va ob li fr tr (Cons (String) x er)))))

; Leaves a scope: keeps [inner]'s facts, values, literals, fresh ids, trace and errors, restoring [outer]'s
; scope and objects; run position is [outer]'s.
(def-fns _ $ many env-restore : (many (Env) outer) (many (Env) inner) -> (many (Env) r)
  (match many outer _
    ((MkEnv sc en fa rp va ob li fr tr er)
      (match many inner _
        ((MkEnv sc2 en2 fa2 rp2 va2 ob2 li2 fr2 tr2 er2) (MkEnv sc en2 fa2 rp va2 ob li2 fr2 tr2 er2))))))

; Leaves a match branch or a body: the entries (whose names the extractor prints), the id supply, trace
; and errors survive; scope, facts, values and objects are the outer ones again.
(def-fns _ $ many env-discard : (many (Env) outer) (many (Env) inner) -> (many (Env) r)
  (match many outer _
    ((MkEnv sc en fa rp va ob li fr tr er)
      (match many inner _
        ((MkEnv sc2 en2 fa2 rp2 va2 ob2 li2 fr2 tr2 er2) (MkEnv sc en2 fa rp va ob li fr2 tr2 er2))))))

(def-fns _ $ many entry : (many (Env) env) (many (Bin) x) -> (many (EInfo) r)
  (match many (idmap-get (predates _) (EInfo) x (env-entries (predates _) env)) _
    ((None a) (MkEInfo (None (String)) (Many) (SDyn)))
    ((Some a e) e)))

(def-fns _ $ many entry-mult-of : (many (Env) env) (many (Bin) x) -> (many (Mult) r)
  (match many (entry (predates _) env x) _ ((MkEInfo n m s) m)))

(def-fns _ $ many entry-state : (many (Env) env) (many (Bin) x) -> (many (State) r)
  (match many (entry (predates _) env x) _ ((MkEInfo n m s) s)))

(def-fns _ $ many name-of : (many (Env) env) (many (Bin) x) -> (many (String) r)
  (match many (entry (predates _) env x) _
    ((MkEInfo n m s) (match many n _ ((None a) (str-cat (predates _) "_" (bin-str (predates _) x))) ((Some a s2) s2)))))

(def-fns _ $ many fact : (many (Env) env) (many (Bin) x) -> (many (Fact) r)
  (match many (idmap-get (predates _) (Fact) x (env-facts (predates _) env)) _
    ((None a) (MkFact (TErr (str-cat (predates _) "no fact for " (bin-str (predates _) x))) (None (Term))))
    ((Some a f) f)))

(def-fns _ $ many fact-ty : (many (Env) env) (many (Bin) x) -> (many (Term) r)
  (match many (fact (predates _) env x) _ ((MkFact ty rule) ty)))

(def-fns _ $ many rule-of : (many (Env) env) (many (Bin) x) -> (many (Maybe (Term)) r)
  (match many (fact (predates _) env x) _ ((MkFact ty rule) rule)))

(def-fns _ $ many lookup : (many (Env) env) (many (String) name) -> (many (Maybe (Bin)) r)
  (nm-get (predates _) (Bin) name (env-scope (predates _) env)))

(def-fns _ $ many add-rule : (many (Env) env) (many (Bin) x) (many (Term) t) -> (many (Env) r)
  (let (many ty) (fact-ty (predates _) env x))
  (env-set-facts (predates _) env (idmap-set (predates _) (Fact) x (MkFact ty (Some (Term) t)) (env-facts (predates _) env))))

(def-fns _ $ many set-state : (many (Env) env) (many (Bin) x) (many (State) st) -> (many (Env) r)
  (match many env _
    ((MkEnv sc en fa rp va ob li fr tr er)
      (let (many info) (match many (idmap-get (predates _) (EInfo) x en) (((EInfo) i))
                         ((None a) (MkEInfo (None (String)) (Many) st))
                         ((Some a e) (match many e (((EInfo) i)) ((MkEInfo n m s) (MkEInfo n m st))))))
      (let (many va2) (match many st (((IdMap (Value)) m))
                        ((SConst v) (idmap-set (predates _) (Value) x v va))
                        ((SDyn) va)))
      (MkEnv sc (idmap-set (predates _) (EInfo) x info en) fa rp va2 ob li fr tr er))))

; Whether a type is one the fetching forms look for in ambient scope (sections 19, 38).
(def-fns _ $ many is-object-type : (many (Term) ty) (many (Bin) coercible) -> (many (Bool) r)
  (match many ty _
    ((TMatchable d t cs) (BTrue))
    ((TNewtype c) (BTrue))
    ((TApp h args) (match many h _ ((TVar x) (bin-eq (predates _) x coercible)) ((TBound k) (BFalse)) ((TApp h2 a2) (BFalse))
                     ((TFn l p r) (BFalse)) ((TTyCtor p) (BFalse)) ((TValCtor p r) (BFalse)) ((TMatchable d t c) (BFalse))
                     ((TNewtype c) (BFalse)) ((TErr m) (BFalse))))
    ((TVar x) (BFalse)) ((TBound k) (BFalse)) ((TFn l p r) (BFalse)) ((TTyCtor p) (BFalse)) ((TValCtor p r) (BFalse)) ((TErr m) (BFalse))))

; Mints an entry: a fresh id, its name in scope, its state, its type and optional rule (section 3).
(def-fns _ $ many bind : (many (Env) env) (many (Maybe (String)) name) (many (Mult) mult) (many (State) st) (many (Term) ty) (many (Maybe (Term)) rule) (many (Bin) coercible) ->
    (many (Env) r) (many (Bin) x)
  (match many env _
    ((MkEnv sc en fa rp va ob li fr tr er)
      (let (many x) (bin-succ (predates _) fr))
      (let (many sc2) (match many name (((NameMap (Bin)) m)) ((None a) sc) ((Some a n) (nm-set (predates _) (Bin) n x sc))))
      (let (many en2) (idmap-set (predates _) (EInfo) x (MkEInfo name mult st) en))
      (let (many fa2) (idmap-set (predates _) (Fact) x (MkFact ty rule) fa))
      (let (many va2) (match many st (((IdMap (Value)) m)) ((SConst v) (idmap-set (predates _) (Value) x v va)) ((SDyn) va)))
      (let (many ob2) (match many (is-object-type (predates _) ty coercible) (((List (Bin)) l)) ((BTrue) (Cons (Bin) x ob)) ((BFalse) ob)))
      (values (MkEnv sc2 en2 fa2 rp va2 ob2 li x tr er) x))))

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
          (match many (nat-lt (predates _) k d) _
            ((BTrue) t)
            ((BFalse)
              (let (many n) (list-length (predates _) (Term) args))
              (match many (list-nth (predates _) (Term) args (nat-sub (predates _) k d)) _
                ((Some a s) s)
                ((None a) (TBound (nat-sub (predates _) k n)))))))
        ((TVar x) t) ((TApp h a) t) ((TFn l p r) t) ((TTyCtor p) t) ((TValCtor p r) t) ((TMatchable dd ty c) t) ((TNewtype c) t) ((TErr m) t)))
    ((OpAbs ids)
      (match many t _
        ((TVar x)
          (match many (index-of-bin (predates _) ids x 0) _
            ((Some a i) (TBound (nat-add (predates _) i d)))
            ((None a) t)))
        ((TBound k) t) ((TApp h a) t) ((TFn l p r) t) ((TTyCtor p) t) ((TValCtor p r) t) ((TMatchable dd ty c) t) ((TNewtype c) t) ((TErr m) t)))))

(def-fns _
  (many mapv : (subterm many (Term) t) (many (VOp) op) (many (Nat) d) -> (many (Term) r)
    (match many t _
      ((TVar x) (op-leaf (predates _) op d t))
      ((TBound k) (op-leaf (predates _) op d t))
      ((TApp h args) (TApp (mapv (subterm _) h op d) (mapv-list (subterm _) args op d)))
      ((TFn l ps rs)
        (let (many d2) (many ps2) (mapv-tele (subterm _) ps op d))
        (let (many d3) (many rs2) (mapv-tele (subterm _) rs op d2))
        (TFn (mapv (subterm _) l op d) ps2 rs2))
      ((TTyCtor ps)
        (let (many d2) (many ps2) (mapv-tele (subterm _) ps op d))
        (TTyCtor ps2))
      ((TValCtor ps ret)
        (let (many d2) (many ps2) (mapv-tele (subterm _) ps op d))
        (TValCtor ps2 (mapv (subterm _) ret op d2)))
      ((TMatchable disc ty cs) (TMatchable disc (mapv (subterm _) ty op d) (mapv-mctors (subterm _) cs op d)))
      ((TNewtype c) (TNewtype (mapv (subterm _) c op d)))
      ((TErr m) t)))
  (many mapv-list : (subterm many (List (Term)) ts) (many (VOp) op) (many (Nat) d) -> (many (List (Term)) r)
    (match many ts _
      ((Nil a) (Nil (Term)))
      ((Cons a t rest) (Cons (Term) (mapv (subterm _) t op d) (mapv-list (subterm _) rest op d)))))
  (many mapv-mctors : (subterm many (List (MCtor)) cs) (many (VOp) op) (many (Nat) d) -> (many (List (MCtor)) r)
    (match many cs _
      ((Nil a) (Nil (MCtor)))
      ((Cons a c rest)
        (match many c _
          ((MkMCtor m t) (Cons (MCtor) (MkMCtor m (mapv (subterm _) t op d)) (mapv-mctors (subterm _) rest op d)))))))
  ; Each entry is mapped at the depth of the entries before it; returns the depth after the telescope.
  (many mapv-tele : (subterm many (List (Entry)) es) (many (VOp) op) (many (Nat) d) -> (many (Nat) d2) (many (List (Entry)) r)
    (match many es _
      ((Nil a) (values d (Nil (Entry))))
      ((Cons a e rest)
        (let (many e2) (match many e (((Entry) x))
                         ((MkEntry n s m sg)
                           (MkEntry n s m (match many sg (((Sg) y)) ((SgTy t) (SgTy (mapv (subterm _) t op d))) ((SgIs t) (SgIs (mapv (subterm _) t op d))))))))
        (let (many d3) (many rest2) (mapv-tele (subterm _) rest op (Succ d)))
        (values d3 (Cons (Entry) e2 rest2))))))

(def-fns _ $ many instantiate : (many (List (Term)) args) (many (Term) t) -> (many (Term) r)
  (mapv (predates _) t (OpInst args) 0))

(def-fns _ $ many instantiate-tele : (many (List (Term)) args) (many (List (Entry)) tele) -> (many (List (Entry)) r)
  (let (many d) (many r) (mapv-tele (predates _) tele (OpInst args) 0))
  r)

(def-fns _ $ many abstract : (many (List (Bin)) ids) (many (Term) t) -> (many (Term) r)
  (mapv (predates _) t (OpAbs ids) 0))

(def-fns _ $ many abstract-sg : (many (List (Bin)) ids) (many (Sg) sg) -> (many (Sg) r)
  (match many sg _
    ((SgTy t) (SgTy (abstract (predates _) ids t)))
    ((SgIs t) (SgIs (abstract (predates _) ids t)))))

; ---- Canonicalization through the fact table's rules (sections 5, 18)

(let (many big-fuel) 100000)

(def-fns _
  (many canon : (subterm many (Nat) fuel) (subterm many (Term) t) (many (IdMap (Fact)) facts) -> (many (Term) r)
    (match many t _
      ((TVar x)
        (match many (idmap-get (predates _) (Fact) x facts) _
          ((None a) t)
          ((Some a f)
            (match many f _
              ((MkFact ty rule)
                (match many rule _
                  ((None b) t)
                  ((Some b r)
                    (match many fuel _
                      ((Zero) t)
                      ((Succ k) (canon (subterm _) k r facts))))))))))
      ((TBound k) t)
      ((TApp h args) (TApp (canon fuel (subterm _) h facts) (canon-list fuel (subterm _) args facts)))
      ((TFn l ps rs) (TFn (canon fuel (subterm _) l facts) (canon-tele fuel (subterm _) ps facts) (canon-tele fuel (subterm _) rs facts)))
      ((TTyCtor ps) (TTyCtor (canon-tele fuel (subterm _) ps facts)))
      ((TValCtor ps ret) (TValCtor (canon-tele fuel (subterm _) ps facts) (canon fuel (subterm _) ret facts)))
      ((TMatchable disc ty cs) (TMatchable disc (canon fuel (subterm _) ty facts) (canon-mctors fuel (subterm _) cs facts)))
      ((TNewtype c) (TNewtype (canon fuel (subterm _) c facts)))
      ((TErr m) t)))
  (many canon-list : (subterm many (Nat) fuel) (subterm many (List (Term)) ts) (many (IdMap (Fact)) facts) -> (many (List (Term)) r)
    (match many ts _
      ((Nil a) (Nil (Term)))
      ((Cons a t rest) (Cons (Term) (canon fuel (subterm _) t facts) (canon-list fuel (subterm _) rest facts)))))
  (many canon-mctors : (subterm many (Nat) fuel) (subterm many (List (MCtor)) cs) (many (IdMap (Fact)) facts) -> (many (List (MCtor)) r)
    (match many cs _
      ((Nil a) (Nil (MCtor)))
      ((Cons a c rest)
        (match many c _
          ((MkMCtor m t) (Cons (MCtor) (MkMCtor m (canon fuel (subterm _) t facts)) (canon-mctors fuel (subterm _) rest facts)))))))
  (many canon-tele : (subterm many (Nat) fuel) (subterm many (List (Entry)) es) (many (IdMap (Fact)) facts) -> (many (List (Entry)) r)
    (match many es _
      ((Nil a) (Nil (Entry)))
      ((Cons a e rest)
        (let (many e2) (match many e (((Entry) x))
                         ((MkEntry n s m sg)
                           (MkEntry n s m (match many sg (((Sg) y)) ((SgTy t) (SgTy (canon fuel (subterm _) t facts))) ((SgIs t) (SgIs (canon fuel (subterm _) t facts))))))))
        (Cons (Entry) e2 (canon-tele fuel (subterm _) rest facts))))))

(def-fns _ $ many canon-env : (many (Env) env) (many (Term) t) -> (many (Term) r)
  (canon (predates _) big-fuel t (env-facts (predates _) env)))

(def-fns _ $ many type-of : (many (Env) env) (many (Bin) x) -> (many (Term) r)
  (canon-env (predates _) env (fact-ty (predates _) env x)))

; An entry read through its alias rule (section 9).
(def-fns _ $ many resolve : (many (Env) env) (many (Bin) x) -> (many (Bin) r)
  (match many (canon-env (predates _) env (TVar x)) _
    ((TVar y) y)
    ((TBound k) x) ((TApp h a) x) ((TFn l p r) x) ((TTyCtor p) x) ((TValCtor p r) x) ((TMatchable d t c) x) ((TNewtype c) x) ((TErr m) x)))

; ---- The built-in entries (lib/prelude.ml): Univ, Type, Level, the proof types, Special and its forms

(def-fns _ $ many ty-entry : (many (String) name) (many (Term) t) -> (many (Entry) e)
  (MkEntry (Some (String) name) (BFalse) (Erased) (SgTy t)))

(let (many empty-env)
  (MkEnv (nm-empty (Bin)) (MEmpty (EInfo)) (MEmpty (Fact)) (BTrue) (MEmpty (Value)) (Nil (Bin)) (nm-empty (Bin)) (BZ) (Nil (Trace)) (Nil (String))))

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
  (let (many env2) (many x) (bind (predates _) env (Some (String) name) (Erased) (SConst (VToken)) ty rule coercible-id))
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
          (let (many cname) (str-cat (predates _) "%" name))
          (let (many env2) (many c) (bind (predates _) env (Some (String) cname) (Many) (SDyn) (TValCtor (Nil (Entry)) special-term) (None (Term)) coercible-id))
          (let (many ctor) (MkCtor cname c index 0 (BTrue) (None (String))))
          (let (many env3) (set-state (predates _) env2 c (SConst (VCtorFn ctor))))
          (let (many env4) (many x) (bind (predates _) env3 (Some (String) name) (Many) (SConst (VCtor ctor (Nil (Value)))) special-term (Some (Term) (TApp (TVar c) (Nil (Term)))) coercible-id))
          (let (many env4b) (env-push-trace (predates _) (env-push-trace (predates _) env4 (TrConst c (VCtorFn ctor))) (TrConst x (VCtor ctor (Nil (Value))))))
          (let (many env5) (many ctors) (many mctors) (bind-specials (subterm _) rest env4b (Succ index)))
          (values env5 (Cons (Ctor) ctor ctors) (Cons (MCtor) (MkMCtor (Many) (TVar c)) mctors)))))))

(def-fns _ $ many make-builtins : -> (many (Env) env)
  (let (many hetero) (Cons (Entry) (ty-entry (predates _) "A" type-term) $ Cons (Entry) (ty-entry (predates _) "a" (TBound 0)) $
                      Cons (Entry) (ty-entry (predates _) "B" type-term) $ Cons (Entry) (ty-entry (predates _) "b" (TBound 0)) (Nil (Entry))))
  (let (many e1) (bind-builtin (predates _) empty-env "Univ" (TTyCtor (Nil (Entry))) (None (Term))))
  (let (many e2) (bind-builtin (predates _) e1 "Type" type-term (Some (Term) type-term)))
  (let (many e3) (bind-builtin (predates _) e2 "Level" (TTyCtor (Nil (Entry))) (None (Term))))
  (let (many e4) (bind-builtin (predates _) e3 "Predates"
                   (TTyCtor (Cons (Entry) (ty-entry (predates _) "A" type-term) $ Cons (Entry) (ty-entry (predates _) "a" (TBound 0)) $
                             Cons (Entry) (ty-entry (predates _) "l" level-term) (Nil (Entry)))) (None (Term))))
  (let (many e5) (bind-builtin (predates _) e4 "Subterm" (TTyCtor hetero) (None (Term))))
  (let (many e6) (bind-builtin (predates _) e5 "Coercible" (TTyCtor hetero) (None (Term))))
  (let (many e7) (bind-builtin (predates _) e6 "Special" (TTyCtor (Nil (Entry))) (None (Term))))
  (let (many e8) (many ctors) (many mctors) (bind-specials (predates _) sp-table e7 0))
  (let (many adt) (MkAdt "Special" (BTrue) ctors (None (String))))
  (let (many e9) (many m) (bind (predates _) e8 (None (String)) (Many) (SConst (VMatchable adt)) (TMatchable (DEnum) (TVar special-id) mctors) (None (Term)) coercible-id))
  (env-push-trace (predates _) e9 (TrConst m (VMatchable adt))))

; ---- Inference over the grammar (lib/elab.ml's infer)

(def-fns _ $ many infer : (subterm many (Term) t) (many (Env) env) -> (many (Term) r)
  (match many t _
    ((TVar x) (type-of (predates _) env x))
    ((TApp h args)
      (match many (canon-env (predates _) env (infer (subterm _) h env)) _
        ((TTyCtor ps) type-term)
        ((TValCtor ps ret) (instantiate (predates _) (list-rev (predates _) (Term) args) ret))
        ((TVar x) (TErr "cannot apply")) ((TBound k) (TErr "cannot apply")) ((TApp h2 a2) (TErr "cannot apply"))
        ((TFn l p r) (TErr "cannot apply a function in a type")) ((TMatchable d ty c) (TErr "cannot apply"))
        ((TNewtype c) (TErr "cannot apply")) ((TErr m) (TErr m))))
    ((TBound k) (TErr "dangling binder"))
    ((TFn l p r) type-term) ((TTyCtor p) type-term) ((TValCtor p r) type-term)
    ((TMatchable d ty c) type-term) ((TNewtype c) type-term) ((TErr m) t)))

; The head type constructor of a canonical type, if any.
(def-fns _ $ many type-head : (many (Env) env) (many (Term) ty) -> (many (Maybe (Bin)) r)
  (match many (canon-env (predates _) env ty) _
    ((TApp h args) (match many h _ ((TVar x) (Some (Bin) x)) ((TBound k) (None (Bin))) ((TApp h2 a2) (None (Bin)))
                     ((TFn l p r) (None (Bin))) ((TTyCtor p) (None (Bin))) ((TValCtor p r) (None (Bin)))
                     ((TMatchable d t c) (None (Bin))) ((TNewtype c) (None (Bin))) ((TErr m) (None (Bin)))))
    ((TVar x) (None (Bin))) ((TBound k) (None (Bin))) ((TFn l p r) (None (Bin))) ((TTyCtor p) (None (Bin)))
    ((TValCtor p r) (None (Bin))) ((TMatchable d t c) (None (Bin))) ((TNewtype c) (None (Bin))) ((TErr m) (None (Bin)))))

; ---- Forced unification, the part that records facts (section 18); contradictions are the checker's job.

(def-fns _
  (many unify : (subterm many (Nat) fuel) (many (Term) a) (many (Term) b) (many (Env) env) -> (many (Env) r)
    (match many fuel _
      ((Zero) env)
      ((Succ k)
        (let (many a1) (canon-env (predates _) env a))
        (let (many b1) (canon-env (predates _) env b))
        (match many a1 _
          ((TVar x)
            (match many b1 _
              ((TVar y)
                (match many (bin-cmp (predates _) x y) _
                  ((OEq) env)
                  ((OLt) (add-rule (predates _) env y a1))
                  ((OGt) (add-rule (predates _) env x b1))))
              ((TBound j) env)
              ((TApp h as) (add-rule (predates _) env x b1))
              ((TFn l p r) (add-rule (predates _) env x b1))
              ((TTyCtor p) (add-rule (predates _) env x b1))
              ((TValCtor p r) (add-rule (predates _) env x b1))
              ((TMatchable d t c) (add-rule (predates _) env x b1))
              ((TNewtype c) (add-rule (predates _) env x b1))
              ((TErr m) env)))
          ((TBound j) env)
          ((TApp h as)
            (match many b1 _
              ((TVar y) (add-rule (predates _) env y a1))
              ((TApp h2 as2) (unify-list (subterm _) k as as2 (unify (subterm _) k h h2 env)))
              ((TBound j) env) ((TFn l p r) env) ((TTyCtor p) env) ((TValCtor p r) env) ((TMatchable d t c) env) ((TNewtype c) env) ((TErr m) env)))
          ((TFn l p r)
            (match many b1 _
              ((TVar y) (add-rule (predates _) env y a1))
              ((TFn l2 p2 r2) (unify-tele (subterm _) k r r2 (unify-tele (subterm _) k p p2 (unify (subterm _) k l l2 env))))
              ((TBound j) env) ((TApp h2 as2) env) ((TTyCtor p2) env) ((TValCtor p2 r2) env) ((TMatchable d t c) env) ((TNewtype c) env) ((TErr m) env)))
          ((TTyCtor p)
            (match many b1 _
              ((TVar y) (add-rule (predates _) env y a1))
              ((TTyCtor p2) (unify-tele (subterm _) k p p2 env))
              ((TBound j) env) ((TApp h2 as2) env) ((TFn l2 p2 r2) env) ((TValCtor p2 r2) env) ((TMatchable d t c) env) ((TNewtype c) env) ((TErr m) env)))
          ((TValCtor p r)
            (match many b1 _
              ((TVar y) (add-rule (predates _) env y a1))
              ((TValCtor p2 r2) (unify (subterm _) k r r2 (unify-tele (subterm _) k p p2 env)))
              ((TBound j) env) ((TApp h2 as2) env) ((TFn l2 p2 r2) env) ((TTyCtor p2) env) ((TMatchable d t c) env) ((TNewtype c) env) ((TErr m) env)))
          ((TMatchable d t c)
            (match many b1 _
              ((TVar y) (add-rule (predates _) env y a1))
              ((TMatchable d2 t2 c2) (unify-mctors (subterm _) k c c2 (unify (subterm _) k t t2 env)))
              ((TBound j) env) ((TApp h2 as2) env) ((TFn l2 p2 r2) env) ((TTyCtor p2) env) ((TValCtor p2 r2) env) ((TNewtype c2) env) ((TErr m) env)))
          ((TNewtype c)
            (match many b1 _
              ((TVar y) (add-rule (predates _) env y a1))
              ((TNewtype c2) (unify (subterm _) k c c2 env))
              ((TBound j) env) ((TApp h2 as2) env) ((TFn l2 p2 r2) env) ((TTyCtor p2) env) ((TValCtor p2 r2) env) ((TMatchable d t c2) env) ((TErr m) env)))
          ((TErr m) env)))))
  (many unify-list : (subterm many (Nat) fuel) (many (List (Term)) as) (many (List (Term)) bs) (many (Env) env) -> (many (Env) r)
    (match many fuel _
      ((Zero) env)
      ((Succ k)
        (match many as _
          ((Nil x) env)
          ((Cons x a rest)
            (match many bs _
              ((Nil y) env)
              ((Cons y b rest2) (unify-list (subterm _) k rest rest2 (unify (subterm _) k a b env)))))))))
  (many unify-tele : (subterm many (Nat) fuel) (many (List (Entry)) as) (many (List (Entry)) bs) (many (Env) env) -> (many (Env) r)
    (match many fuel _
      ((Zero) env)
      ((Succ k)
        (match many as _
          ((Nil x) env)
          ((Cons x a rest)
            (match many bs _
              ((Nil y) env)
              ((Cons y b rest2)
                (unify-tele (subterm _) k rest rest2
                  (unify (subterm _) k (sg-term (predates _) (entry-sg (predates _) a)) (sg-term (predates _) (entry-sg (predates _) b)) env)))))))))
  (many unify-mctors : (subterm many (Nat) fuel) (many (List (MCtor)) as) (many (List (MCtor)) bs) (many (Env) env) -> (many (Env) r)
    (match many fuel _
      ((Zero) env)
      ((Succ k)
        (match many as _
          ((Nil x) env)
          ((Cons x a rest)
            (match many bs _
              ((Nil y) env)
              ((Cons y b rest2)
                (match many a _
                  ((MkMCtor m t)
                    (match many b _
                      ((MkMCtor m2 t2) (unify-mctors (subterm _) k rest rest2 (unify (subterm _) k t t2 env))))))))))))))

(def-fns _ $ many unify-env : (many (Env) env) (many (Term) a) (many (Term) b) -> (many (Env) r)
  (unify (predates _) big-fuel a b env))

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
      ((TVar x) (match many b _ ((TVar y) (bin-eq (predates _) x y)) ((TBound j) (BFalse)) ((TApp h2 a2) (BFalse)) ((TFn l2 p2 r2) (BFalse))
                  ((TTyCtor p2) (BFalse)) ((TValCtor p2 r2) (BFalse)) ((TMatchable d2 t2 c2) (BFalse)) ((TNewtype c2) (BFalse)) ((TErr m) (BFalse))))
      ((TBound k) (match many b _ ((TVar y) (BFalse)) ((TBound j) (nat-eq (predates _) k j)) ((TApp h2 a2) (BFalse)) ((TFn l2 p2 r2) (BFalse))
                    ((TTyCtor p2) (BFalse)) ((TValCtor p2 r2) (BFalse)) ((TMatchable d2 t2 c2) (BFalse)) ((TNewtype c2) (BFalse)) ((TErr m) (BFalse))))
      ((TApp h as) (match many b _ ((TVar y) (BFalse)) ((TBound j) (BFalse))
                     ((TApp h2 as2) (and (predates _) (term-eq (subterm _) h h2) (terms-eq (subterm _) as as2)))
                     ((TFn l2 p2 r2) (BFalse)) ((TTyCtor p2) (BFalse)) ((TValCtor p2 r2) (BFalse)) ((TMatchable d2 t2 c2) (BFalse)) ((TNewtype c2) (BFalse)) ((TErr m) (BFalse))))
      ((TFn l p r) (match many b _ ((TVar y) (BFalse)) ((TBound j) (BFalse)) ((TApp h2 a2) (BFalse))
                     ((TFn l2 p2 r2) (and (predates _) (term-eq (subterm _) l l2) (and (predates _) (tele-eq (subterm _) p p2) (tele-eq (subterm _) r r2))))
                     ((TTyCtor p2) (BFalse)) ((TValCtor p2 r2) (BFalse)) ((TMatchable d2 t2 c2) (BFalse)) ((TNewtype c2) (BFalse)) ((TErr m) (BFalse))))
      ((TTyCtor p) (match many b _ ((TVar y) (BFalse)) ((TBound j) (BFalse)) ((TApp h2 a2) (BFalse)) ((TFn l2 p2 r2) (BFalse))
                     ((TTyCtor p2) (tele-eq (subterm _) p p2))
                     ((TValCtor p2 r2) (BFalse)) ((TMatchable d2 t2 c2) (BFalse)) ((TNewtype c2) (BFalse)) ((TErr m) (BFalse))))
      ((TValCtor p r) (match many b _ ((TVar y) (BFalse)) ((TBound j) (BFalse)) ((TApp h2 a2) (BFalse)) ((TFn l2 p2 r2) (BFalse)) ((TTyCtor p2) (BFalse))
                        ((TValCtor p2 r2) (and (predates _) (tele-eq (subterm _) p p2) (term-eq (subterm _) r r2)))
                        ((TMatchable d2 t2 c2) (BFalse)) ((TNewtype c2) (BFalse)) ((TErr m) (BFalse))))
      ((TMatchable d t c) (match many b _ ((TVar y) (BFalse)) ((TBound j) (BFalse)) ((TApp h2 a2) (BFalse)) ((TFn l2 p2 r2) (BFalse)) ((TTyCtor p2) (BFalse)) ((TValCtor p2 r2) (BFalse))
                            ((TMatchable d2 t2 c2) (and (predates _) (disc-eq (predates _) d d2) (and (predates _) (term-eq (subterm _) t t2) (mctors-eq (subterm _) c c2))))
                            ((TNewtype c2) (BFalse)) ((TErr m) (BFalse))))
      ((TNewtype c) (match many b _ ((TVar y) (BFalse)) ((TBound j) (BFalse)) ((TApp h2 a2) (BFalse)) ((TFn l2 p2 r2) (BFalse)) ((TTyCtor p2) (BFalse)) ((TValCtor p2 r2) (BFalse))
                      ((TMatchable d2 t2 c2) (BFalse)) ((TNewtype c2) (term-eq (subterm _) c c2)) ((TErr m) (BFalse))))
      ((TErr m) (BFalse))))
  (many terms-eq : (subterm many (List (Term)) as) (many (List (Term)) bs) -> (many (Bool) r)
    (match many as _
      ((Nil x) (list-is-empty (predates _) (Term) bs))
      ((Cons x a rest)
        (match many bs _
          ((Nil y) (BFalse))
          ((Cons y b rest2) (and (predates _) (term-eq (subterm _) a b) (terms-eq (subterm _) rest rest2)))))))
  (many tele-eq : (subterm many (List (Entry)) as) (many (List (Entry)) bs) -> (many (Bool) r)
    (match many as _
      ((Nil x) (list-is-empty (predates _) (Entry) bs))
      ((Cons x a rest)
        (match many bs _
          ((Nil y) (BFalse))
          ((Cons y b rest2)
            (match many a _
              ((MkEntry n s m sg)
                (match many b _
                  ((MkEntry n2 s2 m2 sg2)
                    (let (many t2) (sg-term (predates _) sg2))
                    (let (many same) (match many sg (((Bool) r)) ((SgTy t) (term-eq (subterm _) t t2)) ((SgIs t) (term-eq (subterm _) t t2))))
                    (and (predates _) (mult-eq (predates _) m m2)
                      (and (predates _) same (tele-eq (subterm _) rest rest2))))))))))))
  (many mctors-eq : (subterm many (List (MCtor)) as) (many (List (MCtor)) bs) -> (many (Bool) r)
    (match many as _
      ((Nil x) (list-is-empty (predates _) (MCtor) bs))
      ((Cons x a rest)
        (match many bs _
          ((Nil y) (BFalse))
          ((Cons y b rest2)
            (match many a _
              ((MkMCtor m t)
                (match many b _
                  ((MkMCtor m2 t2) (and (predates _) (mult-eq (predates _) m m2) (and (predates _) (term-eq (subterm _) t t2) (mctors-eq (subterm _) rest rest2)))))))))))))

(def-fns _ $ many equal-env : (many (Env) env) (many (Term) a) (many (Term) b) -> (many (Bool) r)
  (term-eq (predates _) (canon-env (predates _) env a) (canon-env (predates _) env b)))

; ---- Printing terms and values, for diagnostics and the final value (lib/term.ml's to_string, lib/value.ml's show)

(def-fns _
  (many show-term : (subterm many (Term) t) (many (Env) env) -> (many (Rope) r)
    (match many t _
      ((TVar x) (RStr (name-of (predates _) env x)))
      ((TBound k) (RStr (str-cat (predates _) "#" (nat-str (predates _) k))))
      ((TApp h args) (rcat4 (predates _) (RStr "(") (show-term (subterm _) h env) (show-terms (subterm _) args env) (RStr ")")))
      ((TFn l ps rs) (rcat5 (predates _) (RStr "(Fn ") (show-term (subterm _) l env) (show-tele (subterm _) ps env) (rcat (predates _) (RStr " ->") (show-tele (subterm _) rs env)) (RStr ")")))
      ((TTyCtor ps) (rcat3 (predates _) (RStr "(TyCtor") (show-tele (subterm _) ps env) (RStr " -> Type)")))
      ((TValCtor ps ret) (rcat4 (predates _) (RStr "(ValCtor") (show-tele (subterm _) ps env) (rcat (predates _) (RStr " -> ") (show-term (subterm _) ret env)) (RStr ")")))
      ((TMatchable d ty cs) (rcat4 (predates _) (RStr (match many d (((String) s)) ((DEnum) "(Matchable enum ") ((DUnion) "(Matchable union "))) (show-term (subterm _) ty env) (show-mctors (subterm _) cs env) (RStr ")")))
      ((TNewtype c) (rcat3 (predates _) (RStr "(Newtype ") (show-term (subterm _) c env) (RStr ")")))
      ((TErr m) (rcat3 (predates _) (RStr "<error: ") (RStr m) (RStr ">")))))
  (many show-terms : (subterm many (List (Term)) ts) (many (Env) env) -> (many (Rope) r)
    (match many ts _
      ((Nil a) (REmpty))
      ((Cons a t rest) (rcat3 (predates _) (RStr " ") (show-term (subterm _) t env) (show-terms (subterm _) rest env)))))
  (many show-mctors : (subterm many (List (MCtor)) cs) (many (Env) env) -> (many (Rope) r)
    (match many cs _
      ((Nil a) (REmpty))
      ((Cons a c rest)
        (match many c _
          ((MkMCtor m t) (rcat4 (predates _) (RStr (match many m (((String) s)) ((Erased) " (erased ") ((Many) " (many "))) (show-term (subterm _) t env) (RStr ")") (show-mctors (subterm _) rest env)))))))
  (many show-tele : (subterm many (List (Entry)) es) (many (Env) env) -> (many (Rope) r)
    (match many es _
      ((Nil a) (REmpty))
      ((Cons a e rest)
        (match many e _
          ((MkEntry n s m sg)
            (let (many nm) (match many n (((String) x)) ((None b) "_") ((Some b x) x)))
            (let (many marks) (str-cat (predates _) (match many s (((String) x)) ((BTrue) "subterm ") ((BFalse) ""))
                                                    (match many m (((String) x)) ((Erased) "erased ") ((Many) "many "))))
            (let (many body) (match many sg (((Rope) x))
                               ((SgTy t) (rcat3 (predates _) (show-term (subterm _) t env) (RStr " ") (RStr nm)))
                               ((SgIs t) (rcat3 (predates _) (show-term (subterm _) t env) (RStr " is ") (RStr nm)))))
            (rcat5 (predates _) (RStr " (") (RStr marks) body (RStr ")") (show-tele (subterm _) rest env))))))))

; Extern construction and destruction over the host's own values (section 41; lib/ffi_core.ml).
(def-fns _ $ many ext-destruct : (many (Adt) adt) (many (Payload) p) -> (many (Nat) index) (many (List (Value)) fields)
  (let (many nat-adt) (MkAdt "Nat" (BTrue) (Nil (Ctor)) (Some (String) "Nat")))
  (let (many u8-adt) (MkAdt "U8" (BFalse) (Nil (Ctor)) (Some (String) "U8")))
  (match many p _
    ((PNat n) (match many n _ ((Zero) (values 0 (Nil (Value)))) ((Succ k) (values 1 (Cons (Value) (VExt adt (PNat k)) (Nil (Value)))))))
    ((PU8 u) (values 0 (Cons (Value) (VExt nat-adt (PNat (u8-to-nat (predates _) u))) (Nil (Value)))))
    ((PBin b) (match many b _ ((BZ) (values 0 (Nil (Value)))) ((B1 r) (values 1 (Cons (Value) (VExt adt (PBin r)) (Nil (Value)))))
                ((B2 r) (values 2 (Cons (Value) (VExt adt (PBin r)) (Nil (Value)))))))
    ((PStr s) (match many s _ ((SNil) (values 0 (Nil (Value))))
                ((SCons c rest) (values 1 (Cons (Value) (VExt u8-adt (PU8 (match many c (((U8) u)) ((MkChar u) u)))) (Cons (Value) (VExt adt (PStr rest)) (Nil (Value))))))))
    ((PDec i) (values i (Nil (Value))))))

(def-fns _ $ many value-nat : (many (Value) v) -> (many (Nat) n)
  (match many v _
    ((VExt a p) (match many p _ ((PNat n) n) ((PU8 u) (u8-to-nat (predates _) u)) ((PBin b) 0) ((PStr s) 0) ((PDec i) i)))
    ((VCtor c fs) 0) ((VTuple fs) 0) ((VCtorFn c) 0) ((VMatchable a) 0) ((VFn cl) 0) ((VToken) 0) ((VError m) 0)))

(def-fns _ $ many value-u8 : (many (Value) v) -> (many (U8) n)
  (match many v _
    ((VExt a p) (match many p _ ((PNat n) (nat-to-u8 (predates _) n)) ((PU8 u) u) ((PBin b) (nat-to-u8 (predates _) 0)) ((PStr s) (nat-to-u8 (predates _) 0)) ((PDec i) (nat-to-u8 (predates _) 0))))
    ((VCtor c fs) (nat-to-u8 (predates _) 0)) ((VTuple fs) (nat-to-u8 (predates _) 0)) ((VCtorFn c) (nat-to-u8 (predates _) 0))
    ((VMatchable a) (nat-to-u8 (predates _) 0)) ((VFn cl) (nat-to-u8 (predates _) 0)) ((VToken) (nat-to-u8 (predates _) 0)) ((VError m) (nat-to-u8 (predates _) 0))))

(def-fns _ $ many value-bin : (many (Value) v) -> (many (Bin) n)
  (match many v _
    ((VExt a p) (match many p _ ((PNat n) (BZ)) ((PU8 u) (BZ)) ((PBin b) b) ((PStr s) (BZ)) ((PDec i) (BZ))))
    ((VCtor c fs) (BZ)) ((VTuple fs) (BZ)) ((VCtorFn c) (BZ)) ((VMatchable a) (BZ)) ((VFn cl) (BZ)) ((VToken) (BZ)) ((VError m) (BZ))))

(def-fns _ $ many value-str : (many (Value) v) -> (many (String) n)
  (match many v _
    ((VExt a p) (match many p _ ((PNat n) (SNil)) ((PU8 u) (SNil)) ((PBin b) (SNil)) ((PStr s) s) ((PDec i) (SNil))))
    ((VCtor c fs) (SNil)) ((VTuple fs) (SNil)) ((VCtorFn c) (SNil)) ((VMatchable a) (SNil)) ((VFn cl) (SNil)) ((VToken) (SNil)) ((VError m) (SNil))))

; Builds an extern value from a constructor index and its many fields.
(def-fns _ $ many ext-construct : (many (Adt) adt) (many (String) ext) (many (Nat) index) (many (List (Value)) fields) -> (many (Value) v)
  (let (many f0) (match many fields (((Value) x)) ((Nil a) (VToken)) ((Cons a f rest) f)))
  (let (many f1) (match many fields (((Value) x)) ((Nil a) (VToken)) ((Cons a f rest) (match many rest (((Value) y)) ((Nil b) (VToken)) ((Cons b g rest2) g)))))
  (match many (str-eq (predates _) ext "Nat") _
    ((BTrue) (VExt adt (PNat (match many index (((Nat) n)) ((Zero) (Zero)) ((Succ k) (Succ (value-nat (predates _) f0)))))))
    ((BFalse)
      (match many (str-eq (predates _) ext "U8") _
        ((BTrue) (VExt adt (PU8 (nat-to-u8 (predates _) (value-nat (predates _) f0)))))
        ((BFalse)
          (match many (str-eq (predates _) ext "Bin") _
            ((BTrue) (VExt adt (PBin (match many index (((Bin) b)) ((Zero) (BZ)) ((Succ k) (match many k (((Bin) b)) ((Zero) (B1 (value-bin (predates _) f0))) ((Succ k2) (B2 (value-bin (predates _) f0)))))))))
            ((BFalse)
              (match many (str-eq (predates _) ext "String") _
                ((BTrue) (VExt adt (PStr (match many index (((String) s)) ((Zero) (SNil)) ((Succ k) (SCons (MkChar (value-u8 (predates _) f0)) (value-str (predates _) f1)))))))
                ((BFalse) (VExt adt (PDec index)))))))))))

(def-fns _ $ many construct : (many (Ctor) c) (many (List (Value)) args) -> (many (Value) v)
  (match many c _
    ((MkCtor name id index arity tagged ext)
      (match many ext _
        ((Some a e) (ext-construct (predates _) (MkAdt (SNil) tagged (Nil (Ctor)) ext) e index args))
        ((None a) (match many tagged _ ((BTrue) (VCtor c args)) ((BFalse) (tuple (predates _) args))))))))

; A value's discriminant and many fields where the FFI holds the type or a tag says (section 38); None
; otherwise, the value then being its fields as they stand.
(def-fns _ $ many dispatch : (many (Maybe (String)) ext) (many (Bool) tagged) (many (Value) v) -> (many (Maybe (Pair (Nat) (List (Value)))) r)
  (match many v _
    ((VExt adt p)
      (match many ext _
        ((None a) (None (Pair (Nat) (List (Value)))))
        ((Some a e)
          (let (many i) (many fs) (ext-destruct (predates _) adt p))
          (Some (Pair (Nat) (List (Value))) (MkPair (Nat) (List (Value)) i fs)))))
    ((VCtor c fs)
      (match many tagged _
        ((BTrue) (Some (Pair (Nat) (List (Value))) (MkPair (Nat) (List (Value)) (ctor-index (predates _) c) fs)))
        ((BFalse) (None (Pair (Nat) (List (Value)))))))
    ((VTuple fs) (None (Pair (Nat) (List (Value))))) ((VCtorFn c) (None (Pair (Nat) (List (Value)))))
    ((VMatchable a) (None (Pair (Nat) (List (Value))))) ((VFn cl) (None (Pair (Nat) (List (Value))))) ((VToken) (None (Pair (Nat) (List (Value)))))
    ((VError m) (None (Pair (Nat) (List (Value)))))))

(def-fns _ $ many destruct : (many (Ctor) c) (many (Value) v) -> (many (Nat) i) (many (List (Value)) fields)
  (match many c _
    ((MkCtor name id index arity tagged ext)
      (match many (dispatch (predates _) ext tagged v) _
        ((Some a p) (match many p _ ((MkPair x y i fs) (values i fs))))
        ((None a) (values index (untuple (predates _) arity v)))))))

(def-fns _ $ many ctor-at : (many (Adt) adt) (many (Nat) i) -> (many (Maybe (Ctor)) c)
  (list-nth (predates _) (Ctor) (adt-ctors (predates _) adt) i))

(def-fns _ $ many show-nat : (subterm many (Nat) n) -> (many (Rope) r)
    (match many n _
      ((Zero) (RStr "(Zero)"))
      ((Succ k) (rcat3 (predates _) (RStr "(Succ ") (show-nat (subterm _) k) (RStr ")")))))

(def-fns _ $ many show-bin : (subterm many (Bin) b) -> (many (Rope) r)
    (match many b _
      ((BZ) (RStr "(BZ)"))
      ((B1 r) (rcat3 (predates _) (RStr "(B1 ") (show-bin (subterm _) r) (RStr ")")))
      ((B2 r) (rcat3 (predates _) (RStr "(B2 ") (show-bin (subterm _) r) (RStr ")")))))

(def-fns _ $ many show-str : (subterm many (String) s) -> (many (Rope) r)
    (match many s _
      ((SNil) (RStr "(SNil)"))
      ((SCons c rest) (rcat5 (predates _) (RStr "(SCons ") (show-nat (predates _) (char-code (predates _) c)) (RStr " ") (show-str (subterm _) rest) (RStr ")")))))

(def-fns _
  (many show-value : (subterm many (Value) v) -> (many (Rope) r)
    (match many v _
      ((VCtor c fields) (rcat4 (predates _) (RStr "(") (RStr (ctor-name (predates _) c)) (show-values (subterm _) fields) (RStr ")")))
      ((VTuple fields) (rcat3 (predates _) (RStr "(") (show-values-bare (subterm _) fields) (RStr ")")))
      ((VExt adt p) (show-payload (subterm _) p adt))
      ((VCtorFn c) (rcat3 (predates _) (RStr "<constructor ") (RStr (ctor-name (predates _) c)) (RStr ">")))
      ((VMatchable adt) (rcat3 (predates _) (RStr "<matchable ") (RStr (adt-name (predates _) adt)) (RStr ">")))
      ((VFn cl) (match many cl _ ((MkClosure fn g e) (rcat3 (predates _) (RStr "<function ") (RStr (func-name (predates _) fn)) (RStr ">")))))
      ((VToken) (RStr "_"))
      ((VError m) (rcat3 (predates _) (RStr "<error: ") (RStr m) (RStr ">")))))
  (many show-values : (subterm many (List (Value)) vs) -> (many (Rope) r)
    (match many vs _
      ((Nil a) (REmpty))
      ((Cons a v rest) (rcat3 (predates _) (RStr " ") (show-value (subterm _) v) (show-values (subterm _) rest)))))
  (many show-values-bare : (subterm many (List (Value)) vs) -> (many (Rope) r)
    (match many vs _
      ((Nil a) (REmpty))
      ((Cons a v rest)
        (match many rest _
          ((Nil b) (show-value (subterm _) v))
          ((Cons b w rest2) (rcat3 (predates _) (show-value (subterm _) v) (RStr " ") (show-values-bare (subterm _) rest)))))))
  ; An extern value prints through its model's constructors, as the interpreter does.
  (many show-payload : (subterm many (Payload) p) (many (Adt) adt) -> (many (Rope) r)
    (match many p _
      ((PNat n) (show-nat (predates _) n))
      ((PU8 u) (show-nat (predates _) (u8-to-nat (predates _) u)))
      ((PBin b) (show-bin (predates _) b))
      ((PStr s) (show-str (predates _) s))
      ((PDec i) (match many i _ ((Zero) (RStr "(Yes)")) ((Succ k) (RStr "(No)")))))))
