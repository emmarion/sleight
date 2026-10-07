; mini/elab.sl -- elaboration of the minimal language (MINIMAL.md) as relations: raw syntax to core code
; (mini/core.sl) with the types and facts of DESIGN.md sections 5 to 7, 9, 18 to 21, 26 and 27. Each
; judgment is total, its outcome an [Ok] with what was derived or an [Err] with the first reason found, so
; that the relation that types a program and the [Fails] relation are one. Every rule follows the simplest
; algorithm the session could write down, however slow. One session's proposal; the surface syntax of the
; minimal language is this session's choice and open for the owner (mini/README.md).

; ---- Raw syntax. The reader turns keyword atoms into [RKey], so keywords are reserved and a name never is
; one. Telescopes are lists: (TFn L (params) (rets)), (TTyCtor (params)), (TValCtor (params) ret), an entry
; being (T x), (subterm T x) or (e is x); a let is (let (binders) items...), a binder x, (T x) or (e is x);
; a def-fns is (def-fns L (f (params) (rets) items...)...); a def-adts is (def-adts (T (params) (C (fields)
; ret)...)...); a match is (match s (rets) ((C fields...) items...)...); a call carries (predates p) after
; its head or (subterm p) before the decreasing argument (section 19).
(def-adts
  ((Key : -> Type)
    enum
    (many KFn : -> (Key))
    (many KTyCtor : -> (Key))
    (many KValCtor : -> (Key))
    (many KIs : -> (Key))
    (many KSubterm : -> (Key))
    (many KPredates : -> (Key))
    (many KLet : -> (Key))
    (many KDefLvl : -> (Key))
    (many KDefFns : -> (Key))
    (many KDefAdts : -> (Key))
    (many KMatch : -> (Key))
    (many KValues : -> (Key))
    (many KProveSubterm : -> (Key))
    (many KProvePredates : -> (Key))
    (many KPredatesTrans : -> (Key))
    (many KSubtermTrans : -> (Key))
    (many KPredatesSubterm : -> (Key)))
  ((Raw : -> Type)
    enum
    (many RAtom : (many (String) name) -> (Raw))
    (many RKey : (many (Key) key) -> (Raw))
    (many RList : (many (List (Raw)) items) -> (Raw))))

; Why a program is refused: the first reason met, carried out unchanged by every enclosing judgment. A
; malformed shape is not a reason: the relations have no derivation for one, and [Fails] speaks of
; well-formed programs that do not type.
(def-adts $ (Reason : -> Type)
  enum
  (many RUnbound : -> (Reason))
  (many RNotApplicable : -> (Reason))
  (many RArity : -> (Reason))
  (many RMismatch : -> (Reason))
  (many RNotMatchable : -> (Reason))
  (many RNotCtor : -> (Reason))
  (many RDuplicateBranch : -> (Reason))
  (many RRefutedBranch : -> (Reason))
  (many RMissingBranch : -> (Reason))
  (many RNoProof : -> (Reason))
  (many RBadProof : -> (Reason))
  (many RTopLevelOnly : -> (Reason))
  (many RNotLevel : -> (Reason))
  (many RBadReturn : -> (Reason))
  (many RSize : -> (Reason)))

; ---- The context record: projections, and the operations elaboration performs on it.
(def-adts
  ((Ents : ((Ctx) ctx) ((List (Ent)) ents) -> Type)
    enum
    (many EntsOf : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       -> (Ents (MkCtx n s e r a l sa) e)))
  ((Rules : ((Ctx) ctx) ((List (Rule)) rules) -> Type)
    enum
    (many RulesOf : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       -> (Rules (MkCtx n s e r a l sa) r)))
  ((Scope : ((Ctx) ctx) ((List (Name)) scope) -> Type)
    enum
    (many ScopeOf : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       -> (Scope (MkCtx n s e r a l sa) s)))
  ((Adts : ((Ctx) ctx) ((List (Adt)) adts) -> Type)
    enum
    (many AdtsOf : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       -> (Adts (MkCtx n s e r a l sa) a)))
  ((LevelOf : ((Ctx) ctx) ((Maybe (Term)) level) -> Type)
    enum
    (many MkLevelOf : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       -> (LevelOf (MkCtx n s e r a l sa) l)))
  ((SubArgs : ((Ctx) ctx) ((List (Term)) subargs) -> Type)
    enum
    (many SubArgsOf : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       -> (SubArgs (MkCtx n s e r a l sa) sa)))
  ; Leaving a scope restores everything but the id supply; leaving a let's right-hand side hides its names
  ; and keeps its entries and facts (section 27); entering a body sets the level and subterm arguments.
  ((Leave : ((Ctx) inner) ((Ctx) outer) ((Ctx) out) -> Type)
    enum
    (many LeaveTo : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (Nat) n0) (erased (List (Name)) s0) (erased (List (Ent)) e0) (erased (List (Rule)) r0) (erased (List (Adt)) a0) (erased (Maybe (Term)) l0) (erased (List (Term)) sa0)
       -> (Leave (MkCtx n s e r a l sa) (MkCtx n0 s0 e0 r0 a0 l0 sa0) (MkCtx n s0 e0 r0 a0 l0 sa0))))
  ((Hide : ((Ctx) inner) ((List (Name)) scope) ((Ctx) out) -> Type)
    enum
    (many HideTo : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (List (Name)) s0) -> (Hide (MkCtx n s e r a l sa) s0 (MkCtx n s0 e r a l sa))))
  ((Enter : ((Ctx) ctx) ((Term) level) ((List (Term)) subargs) ((Ctx) out) -> Type)
    enum
    (many EnterTo : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (Term) l2) (erased (List (Term)) sa2) -> (Enter (MkCtx n s e r a l sa) l2 sa2 (MkCtx n s e r a (Some (Term) l2) sa2))))
  ((WithRules : ((Ctx) ctx) ((List (Rule)) rules) ((Ctx) out) -> Type)
    enum
    (many WithRulesTo : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (List (Rule)) r2) -> (WithRules (MkCtx n s e r a l sa) r2 (MkCtx n s e r2 a l sa))))
  ((WithScope : ((Ctx) ctx) ((List (Name)) scope) ((Ctx) out) -> Type)
    enum
    (many WithScopeTo : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (List (Name)) s2) -> (WithScope (MkCtx n s e r a l sa) s2 (MkCtx n s2 e r a l sa))))
  ((AddAdt : ((Ctx) ctx) ((Adt) adt) ((Ctx) out) -> Type)
    enum
    (many AddAdtTo : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (Adt) adt) -> (AddAdt (MkCtx n s e r a l sa) adt (MkCtx n s e r (Cons (Adt) adt a) l sa))))
  ; Minting an entry: the next id, with a name in scope or not, a type, a kind, and a rule or not.
  ((Mint : ((Ctx) ctx) ((Maybe (String)) name) ((Term) ty) ((Kind) k) ((Maybe (Term)) rule) ((Nat) id) ((Ctx) out) -> Type)
    enum
    (many MintTo : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (Maybe (String)) name) (erased (Term) ty) (erased (Kind) k) (erased (Maybe (Term)) rule) (erased (List (Name)) s2) (erased (List (Rule)) r2)
       (erased (AddName s name n s2) an) (erased (AddRule r rule n r2) ar) -> (Mint (MkCtx n s e r a l sa) name ty k rule n (MkCtx (Succ n) s2 (Cons (Ent) (MkEnt n ty k) e) r2 a l sa))))
  ((AddName : ((List (Name)) s) ((Maybe (String)) name) ((Nat) id) ((List (Name)) out) -> Type)
    enum
    (many AddNameNone : (erased (List (Name)) s) (erased (Nat) id) -> (AddName s (None (String)) id s))
    (many AddNameSome : (erased (List (Name)) s) (erased (String) name) (erased (Nat) id) -> (AddName s (Some (String) name) id (Cons (Name) (MkName name id) s))))
  ((AddRule : ((List (Rule)) r) ((Maybe (Term)) rule) ((Nat) id) ((List (Rule)) out) -> Type)
    enum
    (many AddRuleNone : (erased (List (Rule)) r) (erased (Nat) id) -> (AddRule r (None (Term)) id r))
    (many AddRuleSome : (erased (List (Rule)) r) (erased (Term) t) (erased (Nat) id) -> (AddRule r (Some (Term) t) id (Cons (Rule) (MkRule id t) r)))))

; ---- Identity and refinement, through mini/unify.sl: two terms are the same when their canonical forms
; are identical (section 9); a branch refines the facts by forcing one equation (section 7), or contradicts
; them.
(def-adts
  ((Same : ((Ctx) ctx) ((Term) t) ((Term) u) -> Type)
    enum
    (many SameBy : (erased (Ctx) ctx) (erased (Term) t) (erased (Term) u) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Rule)) rules2)
       (erased (Ents ctx ents) e) (erased (Rules ctx rules) r) (erased (Unify (Check) ents rules (Cons (Eqn) (MkEqn t u) (Nil (Eqn))) (UOk rules2)) p) -> (Same ctx t u)))
  ((Differ : ((Ctx) ctx) ((Term) t) ((Term) u) -> Type)
    enum
    (many DifferBy : (erased (Ctx) ctx) (erased (Term) t) (erased (Term) u) (erased (List (Ent)) ents) (erased (List (Rule)) rules)
       (erased (Ents ctx ents) e) (erased (Rules ctx rules) r) (erased (Unify (Check) ents rules (Cons (Eqn) (MkEqn t u) (Nil (Eqn))) (UFail)) p) -> (Differ ctx t u)))
  ((Refine : ((Ctx) ctx) ((Term) t) ((Term) u) ((Ctx) out) -> Type)
    enum
    (many RefineBy : (erased (Ctx) ctx) (erased (Term) t) (erased (Term) u) (erased (Ctx) out) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Rule)) rules2)
       (erased (Ents ctx ents) e) (erased (Rules ctx rules) r) (erased (Unify (Force) ents rules (Cons (Eqn) (MkEqn t u) (Nil (Eqn))) (UOk rules2)) p) (erased (WithRules ctx rules2 out) w) -> (Refine ctx t u out)))
  ((Contradict : ((Ctx) ctx) ((Term) t) ((Term) u) -> Type)
    enum
    (many ContradictBy : (erased (Ctx) ctx) (erased (Term) t) (erased (Term) u) (erased (List (Ent)) ents) (erased (List (Rule)) rules)
       (erased (Ents ctx ents) e) (erased (Rules ctx rules) r) (erased (Unify (Force) ents rules (Cons (Eqn) (MkEqn t u) (Nil (Eqn))) (UFail)) p) -> (Contradict ctx t u))))

; The type of an entry, and of a closed term of the grammar (mini/unify.sl), through the context.
(def-adts
  ((TypeOf : ((Ctx) ctx) ((Nat) x) ((Term) ty) -> Type)
    enum
    (many TypeOfBy : (erased (Ctx) ctx) (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (List (Ent)) ents) (erased (Ents ctx ents) e) (erased (EntOf ents x ty k) p) -> (TypeOf ctx x ty)))
  ((KindOf : ((Ctx) ctx) ((Nat) x) ((Kind) k) -> Type)
    enum
    (many KindOfBy : (erased (Ctx) ctx) (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (List (Ent)) ents) (erased (Ents ctx ents) e) (erased (EntOf ents x ty k) p) -> (KindOf ctx x k)))
  ((CanonAt : ((Ctx) ctx) ((Term) t) ((Term) u) -> Type)
    enum
    (many CanonicalBy : (erased (Ctx) ctx) (erased (Term) t) (erased (Term) u) (erased (List (Rule)) rules) (erased (Rules ctx rules) r) (erased (Canon rules t u) p) -> (CanonAt ctx t u)))
  ((Typed : ((Ctx) ctx) ((Term) t) ((Term) ty) -> Type)
    enum
    (many TypedBy : (erased (Ctx) ctx) (erased (Term) t) (erased (Term) ty) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Ents ctx ents) e) (erased (Rules ctx rules) r)
       (erased (TypeOfTerm ents rules t ty) p) -> (Typed ctx t ty))))

; ---- Minting a telescope's entries: each entry's term instantiated with the entries before it, a type
; entry giving its entry that type, an is entry giving its entry the rule and the rule's type (section 12).
(def-adts
  ((MintTele : ((Ctx) ctx) ((List (Maybe (Term))) acc) ((List (Entry)) tele) ((List (Maybe (String))) names) ((Ctx) out) ((List (Nat)) ids) -> Type)
    enum
    (many MTNil : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) -> (MintTele ctx acc (Nil (Entry)) (Nil (Maybe (String))) ctx (Nil (Nat))))
    (many MTTy : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (Bool) s) (erased (Term) t) (erased (List (Entry)) es) (erased (Maybe (String)) name) (erased (List (Maybe (String))) names)
       (erased (Term) t2) (erased (Nat) x) (erased (Ctx) ctx1) (erased (Ctx) out) (erased (List (Nat)) ids)
       (erased (Subst acc t t2) sb) (erased (Mint ctx name t2 (KPlain) (None (Term)) x ctx1) m) (erased (MintTele ctx1 (Cons (Maybe (Term)) (Some (Term) (Ref x)) acc) es names out ids) p)
       -> (MintTele ctx acc (Cons (Entry) (MkEntry s (BFalse) t) es) (Cons (Maybe (String)) name names) out (Cons (Nat) x ids)))
    (many MTIs : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (Bool) s) (erased (Term) t) (erased (List (Entry)) es) (erased (Maybe (String)) name) (erased (List (Maybe (String))) names)
       (erased (Term) t2) (erased (Term) ty) (erased (Nat) x) (erased (Ctx) ctx1) (erased (Ctx) out) (erased (List (Nat)) ids)
       (erased (Subst acc t t2) sb) (erased (Typed ctx t2 ty) tt) (erased (Mint ctx name ty (KPlain) (Some (Term) t2) x ctx1) m)
       (erased (MintTele ctx1 (Cons (Maybe (Term)) (Some (Term) (Ref x)) acc) es names out ids) p)
       -> (MintTele ctx acc (Cons (Entry) (MkEntry s (BTrue) t) es) (Cons (Maybe (String)) name names) out (Cons (Nat) x ids))))
  ((Nones : ((List (Entry)) tele) ((List (Maybe (String))) names) -> Type)
    enum
    (many NonesNil : -> (Nones (Nil (Entry)) (Nil (Maybe (String)))))
    (many NonesCons : (erased (Entry) e) (erased (List (Entry)) es) (erased (List (Maybe (String))) names) (erased (Nones es names) p)
       -> (Nones (Cons (Entry) e es) (Cons (Maybe (String)) (None (String)) names))))
  ; The references to the entries a telescope's subterm-marked positions got, section 5's enclosing subterm
  ; arguments, and, at a call, the decreasing candidates.
  ((Marked : ((List (Entry)) tele) ((List (Nat)) ids) ((List (Term)) out) -> Type)
    enum
    (many MarkedNil : -> (Marked (Nil (Entry)) (Nil (Nat)) (Nil (Term))))
    (many MarkedYes : (erased (Bool) i) (erased (Term) t) (erased (List (Entry)) es) (erased (Nat) x) (erased (List (Nat)) ids) (erased (List (Term)) out) (erased (Marked es ids out) p)
       -> (Marked (Cons (Entry) (MkEntry (BTrue) i t) es) (Cons (Nat) x ids) (Cons (Term) (Ref x) out)))
    (many MarkedNo : (erased (Bool) i) (erased (Term) t) (erased (List (Entry)) es) (erased (Nat) x) (erased (List (Nat)) ids) (erased (List (Term)) out) (erased (Marked es ids out) p)
       -> (Marked (Cons (Entry) (MkEntry (BFalse) i t) es) (Cons (Nat) x ids) out))))

; ---- Elaborating a term of the grammar (section 9): a name is its entry; an application checks its
; arguments, themselves terms, against the head's telescope; a former binds its telescopes.
(def-adts
  ((TOut : -> Type)
    enum
    (many TOk : (many (Term) t) (many (Term) ty) -> (TOut))
    (many TErr : (many (Reason) r) -> (TOut)))
  ; A telescope elaborated in a scope of its own entries; [ctx] afterwards still holds them, for a body to
  ; use, and the caller leaves the scope when done.
  ((TeleOut : -> Type)
    enum
    (many TeleOk : (many (Ctx) ctx) (many (List (Entry)) tele) (many (List (Nat)) ids) (many (List (Maybe (String))) names) -> (TeleOut))
    (many TeleErr : (many (Reason) r) -> (TeleOut)))
  ((ArgsOut : -> Type)
    enum
    (many ArgsOk : (many (List (Term)) ts) -> (ArgsOut))
    (many ArgsErr : (many (Reason) r) -> (ArgsOut))))

(def-adts
  ((Mem : ((Nat) x) ((List (Nat)) xs) -> Type)
    enum
    (many MemHere : (erased (Nat) x) (erased (List (Nat)) xs) -> (Mem x (Cons (Nat) x xs)))
    (many MemThere : (erased (Nat) x) (erased (Nat) y) (erased (List (Nat)) xs) (erased (Mem x xs) p) -> (Mem x (Cons (Nat) y xs))))
  ((NotMem : ((Nat) x) ((List (Nat)) xs) -> Type)
    enum
    (many NotMemNil : (erased (Nat) x) -> (NotMem x (Nil (Nat))))
    (many NotMemCons : (erased (Nat) x) (erased (Nat) y) (erased (List (Nat)) xs) (erased (Neq x y) n) (erased (NotMem x xs) p) -> (NotMem x (Cons (Nat) y xs))))
  ((NotApp : ((Term) t) -> Type)
    enum
    (many NotAppRef : (erased (Nat) x) -> (NotApp (Ref x)))
    (many NotAppBound : (erased (Nat) k) -> (NotApp (Bound k)))
    (many NotAppUniv : -> (NotApp (TUniv)))
    (many NotAppFn : (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs) -> (NotApp (TFn l ps rs)))
    (many NotAppTyCtor : (erased (List (Entry)) ps) -> (NotApp (TTyCtor ps)))
    (many NotAppValCtor : (erased (List (Entry)) ps) (erased (Term) r) -> (NotApp (TValCtor ps r))))
  ((NotTyApp : ((Term) t) -> Type)
    enum
    (many NTAOther : (erased (Term) t) (erased (NotApp t) p) -> (NotTyApp t))
    (many NTAValApp : (erased (Term) h) (erased (List (Entry)) ps) (erased (Term) r) (erased (List (Term)) as) -> (NotTyApp (ValApp h ps r as)))))

(let ((many level-ty)) (TyApp (Ref (Zero)) (Nil _) (Nil _)))
(let ((many predates-ps)) (Cons _ (MkEntry (BFalse) (BFalse) (TUniv)) $ Cons _ (MkEntry (BFalse) (BFalse) (Bound (Zero))) $ Cons _ (MkEntry (BFalse) (BFalse) level-ty) $ Nil _))
(let ((many subterm-ps)) (Cons _ (MkEntry (BFalse) (BFalse) (TUniv)) $ Cons _ (MkEntry (BFalse) (BFalse) (Bound (Zero))) $ Cons _ (MkEntry (BFalse) (BFalse) (TUniv)) $ Cons _ (MkEntry (BFalse) (BFalse) (Bound (Zero))) $ Nil _))
(def-adts
  ((ElabTerm : ((Ctx) ctx) ((Raw) raw) ((TOut) out) -> Type)
    enum
    (many ETName : (erased (Ctx) ctx) (erased (String) s) (erased (Nat) x) (erased (Term) ty) (erased (List (Name)) scope)
       (erased (Scope ctx scope) sc) (erased (NameOf scope s x) n) (erased (TypeOf ctx x ty) t) -> (ElabTerm ctx (RAtom s) (TOk (Ref x) ty)))
    (many ETUnbound : (erased (Ctx) ctx) (erased (String) s) (erased (List (Name)) scope) (erased (Scope ctx scope) sc) (erased (NoName scope s) n) -> (ElabTerm ctx (RAtom s) (TErr (RUnbound))))
    ; an application of a type constructor or a value constructor
    (many ETTyApp : (erased (Ctx) ctx) (erased (Raw) h) (erased (List (Raw)) args) (erased (Term) ht) (erased (Term) hty) (erased (List (Entry)) ps) (erased (List (Term)) ts)
       (erased (ElabTerm ctx h (TOk ht hty)) p) (erased (CanonAt ctx hty (TTyCtor ps)) c) (erased (ElabTermArgs ctx (Nil (Maybe (Term))) ps args (ArgsOk ts)) a)
       -> (ElabTerm ctx (RList (Cons (Raw) h args)) (TOk (TyApp ht ps ts) (TUniv))))
    (many ETValApp : (erased (Ctx) ctx) (erased (Raw) h) (erased (List (Raw)) args) (erased (Term) ht) (erased (Term) hty) (erased (List (Entry)) ps) (erased (Term) ret) (erased (List (Term)) ts)
       (erased (List (Maybe (Term))) subs) (erased (Term) ty)
       (erased (ElabTerm ctx h (TOk ht hty)) p) (erased (CanonAt ctx hty (TValCtor ps ret)) c) (erased (ElabTermArgs ctx (Nil (Maybe (Term))) ps args (ArgsOk ts)) a)
       (erased (Somes ts subs) s) (erased (Subst subs ret ty) q) -> (ElabTerm ctx (RList (Cons (Raw) h args)) (TOk (ValApp ht ps ret ts) ty)))
    (many ETAppHeadErr : (erased (Ctx) ctx) (erased (Raw) h) (erased (List (Raw)) args) (erased (Reason) r) (erased (ElabTerm ctx h (TErr r)) p)
       -> (ElabTerm ctx (RList (Cons (Raw) h args)) (TErr r)))
    (many ETAppArgsErr : (erased (Ctx) ctx) (erased (Raw) h) (erased (List (Raw)) args) (erased (Term) ht) (erased (Term) hty) (erased (List (Entry)) ps) (erased (Reason) r)
       (erased (ElabTerm ctx h (TOk ht hty)) p) (erased (HeadTele ctx hty ps) c) (erased (ElabTermArgs ctx (Nil (Maybe (Term))) ps args (ArgsErr r)) a)
       -> (ElabTerm ctx (RList (Cons (Raw) h args)) (TErr r)))
    (many ETNotApplicable : (erased (Ctx) ctx) (erased (Raw) h) (erased (List (Raw)) args) (erased (Term) ht) (erased (Term) hty) (erased (Term) c)
       (erased (ElabTerm ctx h (TOk ht hty)) p) (erased (CanonAt ctx hty c) cn) (erased (NoTele c) nt) -> (ElabTerm ctx (RList (Cons (Raw) h args)) (TErr (RNotApplicable))))
    ; the formers
    (many ETFn : (erased (Ctx) ctx) (erased (Raw) lr) (erased (List (Raw)) ps) (erased (List (Raw)) rs) (erased (Term) l) (erased (Term) lty) (erased (Ctx) ctx1) (erased (List (Entry)) pt) (erased (List (Nat)) pids)
       (erased (List (Maybe (String))) pn) (erased (List (Maybe (Nat))) acc) (erased (Ctx) ctx2) (erased (List (Entry)) rt) (erased (List (Nat)) rids) (erased (List (Maybe (String))) rn)
       (erased (ElabTerm ctx lr (TOk l lty)) p) (erased (Same ctx lty level-ty) sl)
       (erased (ElabTele ctx (Nil (Maybe (Nat))) ps (TeleOk ctx1 pt pids pn)) ep) (erased (Binders pids acc) b) (erased (ElabTele ctx1 acc rs (TeleOk ctx2 rt rids rn)) er)
       -> (ElabTerm ctx (RList (Cons (Raw) (RKey (KFn)) (Cons (Raw) lr (Cons (Raw) (RList ps) (Cons (Raw) (RList rs) (Nil (Raw))))))) (TOk (TFn l pt rt) (TUniv))))
    (many ETFnLevelErr : (erased (Ctx) ctx) (erased (Raw) lr) (erased (List (Raw)) ps) (erased (List (Raw)) rs) (erased (Reason) r) (erased (ElabTerm ctx lr (TErr r)) p)
       -> (ElabTerm ctx (RList (Cons (Raw) (RKey (KFn)) (Cons (Raw) lr (Cons (Raw) (RList ps) (Cons (Raw) (RList rs) (Nil (Raw))))))) (TErr r)))
    (many ETFnNotLevel : (erased (Ctx) ctx) (erased (Raw) lr) (erased (List (Raw)) ps) (erased (List (Raw)) rs) (erased (Term) l) (erased (Term) lty)
       (erased (ElabTerm ctx lr (TOk l lty)) p) (erased (Differ ctx lty level-ty) d)
       -> (ElabTerm ctx (RList (Cons (Raw) (RKey (KFn)) (Cons (Raw) lr (Cons (Raw) (RList ps) (Cons (Raw) (RList rs) (Nil (Raw))))))) (TErr (RNotLevel))))
    (many ETFnParamsErr : (erased (Ctx) ctx) (erased (Raw) lr) (erased (List (Raw)) ps) (erased (List (Raw)) rs) (erased (Term) l) (erased (Term) lty) (erased (Reason) r)
       (erased (ElabTerm ctx lr (TOk l lty)) p) (erased (Same ctx lty level-ty) sl) (erased (ElabTele ctx (Nil (Maybe (Nat))) ps (TeleErr r)) ep)
       -> (ElabTerm ctx (RList (Cons (Raw) (RKey (KFn)) (Cons (Raw) lr (Cons (Raw) (RList ps) (Cons (Raw) (RList rs) (Nil (Raw))))))) (TErr r)))
    (many ETFnRetsErr : (erased (Ctx) ctx) (erased (Raw) lr) (erased (List (Raw)) ps) (erased (List (Raw)) rs) (erased (Term) l) (erased (Term) lty) (erased (Ctx) ctx1) (erased (List (Entry)) pt) (erased (List (Nat)) pids)
       (erased (List (Maybe (String))) pn) (erased (List (Maybe (Nat))) acc) (erased (Reason) r)
       (erased (ElabTerm ctx lr (TOk l lty)) p) (erased (Same ctx lty level-ty) sl)
       (erased (ElabTele ctx (Nil (Maybe (Nat))) ps (TeleOk ctx1 pt pids pn)) ep) (erased (Binders pids acc) b) (erased (ElabTele ctx1 acc rs (TeleErr r)) er)
       -> (ElabTerm ctx (RList (Cons (Raw) (RKey (KFn)) (Cons (Raw) lr (Cons (Raw) (RList ps) (Cons (Raw) (RList rs) (Nil (Raw))))))) (TErr r)))
    (many ETTyCtor : (erased (Ctx) ctx) (erased (List (Raw)) ps) (erased (Ctx) ctx1) (erased (List (Entry)) pt) (erased (List (Nat)) pids) (erased (List (Maybe (String))) pn)
       (erased (ElabTele ctx (Nil (Maybe (Nat))) ps (TeleOk ctx1 pt pids pn)) ep)
       -> (ElabTerm ctx (RList (Cons (Raw) (RKey (KTyCtor)) (Cons (Raw) (RList ps) (Nil (Raw))))) (TOk (TTyCtor pt) (TUniv))))
    (many ETTyCtorErr : (erased (Ctx) ctx) (erased (List (Raw)) ps) (erased (Reason) r) (erased (ElabTele ctx (Nil (Maybe (Nat))) ps (TeleErr r)) ep)
       -> (ElabTerm ctx (RList (Cons (Raw) (RKey (KTyCtor)) (Cons (Raw) (RList ps) (Nil (Raw))))) (TErr r)))
    (many ETValCtor : (erased (Ctx) ctx) (erased (List (Raw)) ps) (erased (Raw) rr) (erased (Ctx) ctx1) (erased (List (Entry)) pt) (erased (List (Nat)) pids) (erased (List (Maybe (String))) pn)
       (erased (List (Maybe (Nat))) acc) (erased (Term) ret) (erased (Term) rty) (erased (Nat) t) (erased (List (Entry)) aps) (erased (List (Term)) args) (erased (Term) tty) (erased (List (Entry)) tps) (erased (Term) ret2)
       (erased (ElabTele ctx (Nil (Maybe (Nat))) ps (TeleOk ctx1 pt pids pn)) ep) (erased (ElabTerm ctx1 rr (TOk ret rty)) er)
       (erased (CanonAt ctx1 ret (TyApp (Ref t) aps args)) cr) (erased (NotMem t pids) nm) (erased (TypeOf ctx1 t tty) tt) (erased (CanonAt ctx1 tty (TTyCtor tps)) ct)
       (erased (Binders pids acc) b) (erased (Abstract acc ret ret2) ab)
       -> (ElabTerm ctx (RList (Cons (Raw) (RKey (KValCtor)) (Cons (Raw) (RList ps) (Cons (Raw) rr (Nil (Raw)))))) (TOk (TValCtor pt ret2) (TUniv))))
    (many ETValCtorParamsErr : (erased (Ctx) ctx) (erased (List (Raw)) ps) (erased (Raw) rr) (erased (Reason) r) (erased (ElabTele ctx (Nil (Maybe (Nat))) ps (TeleErr r)) ep)
       -> (ElabTerm ctx (RList (Cons (Raw) (RKey (KValCtor)) (Cons (Raw) (RList ps) (Cons (Raw) rr (Nil (Raw)))))) (TErr r)))
    (many ETValCtorRetErr : (erased (Ctx) ctx) (erased (List (Raw)) ps) (erased (Raw) rr) (erased (Ctx) ctx1) (erased (List (Entry)) pt) (erased (List (Nat)) pids) (erased (List (Maybe (String))) pn) (erased (Reason) r)
       (erased (ElabTele ctx (Nil (Maybe (Nat))) ps (TeleOk ctx1 pt pids pn)) ep) (erased (ElabTerm ctx1 rr (TErr r)) er)
       -> (ElabTerm ctx (RList (Cons (Raw) (RKey (KValCtor)) (Cons (Raw) (RList ps) (Cons (Raw) rr (Nil (Raw)))))) (TErr r)))
    (many ETValCtorBadRet : (erased (Ctx) ctx) (erased (List (Raw)) ps) (erased (Raw) rr) (erased (Ctx) ctx1) (erased (List (Entry)) pt) (erased (List (Nat)) pids) (erased (List (Maybe (String))) pn)
       (erased (Term) ret) (erased (Term) rty) (erased (Term) c)
       (erased (ElabTele ctx (Nil (Maybe (Nat))) ps (TeleOk ctx1 pt pids pn)) ep) (erased (ElabTerm ctx1 rr (TOk ret rty)) er) (erased (CanonAt ctx1 ret c) cr) (erased (BadFormerRet ctx1 pids c) br)
       -> (ElabTerm ctx (RList (Cons (Raw) (RKey (KValCtor)) (Cons (Raw) (RList ps) (Cons (Raw) rr (Nil (Raw)))))) (TErr (RBadReturn)))))
  ; A TValCtor former's return is an application of a type constructor in scope, not of one of the former's own
  ; binders (ASSUMPTIONS 80); the four ways it is not.
  ((BadFormerRet : ((Ctx) ctx) ((List (Nat)) pids) ((Term) c) -> Type)
    enum
    (many BFNotApp : (erased (Ctx) ctx) (erased (List (Nat)) pids) (erased (Term) c) (erased (NotTyApp c) p) -> (BadFormerRet ctx pids c))
    (many BFHead : (erased (Ctx) ctx) (erased (List (Nat)) pids) (erased (Term) h) (erased (List (Entry)) hps) (erased (List (Term)) as) (erased (NonRef h) p) -> (BadFormerRet ctx pids (TyApp h hps as)))
    (many BFOwn : (erased (Ctx) ctx) (erased (List (Nat)) pids) (erased (Nat) t) (erased (List (Entry)) hps) (erased (List (Term)) as) (erased (Mem t pids) p) -> (BadFormerRet ctx pids (TyApp (Ref t) hps as)))
    (many BFNotTycon : (erased (Ctx) ctx) (erased (List (Nat)) pids) (erased (Nat) t) (erased (List (Entry)) hps) (erased (List (Term)) as) (erased (Term) tty) (erased (Term) c)
       (erased (TypeOf ctx t tty) p) (erased (CanonAt ctx tty c) q) (erased (NotTyCtor c) n) -> (BadFormerRet ctx pids (TyApp (Ref t) hps as))))
  ((NotTyCtor : ((Term) t) -> Type)
    enum
    (many NTCRef : (erased (Nat) x) -> (NotTyCtor (Ref x)))
    (many NTCBound : (erased (Nat) k) -> (NotTyCtor (Bound k)))
    (many NTCTyApp : (erased (Term) h) (erased (List (Entry)) ps) (erased (List (Term)) as) -> (NotTyCtor (TyApp h ps as)))
    (many NTCValApp : (erased (Term) h) (erased (List (Entry)) ps) (erased (Term) r) (erased (List (Term)) as) -> (NotTyCtor (ValApp h ps r as)))
    (many NTCUniv : -> (NotTyCtor (TUniv)))
    (many NTCFn : (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs) -> (NotTyCtor (TFn l ps rs)))
    (many NTCValCtor : (erased (List (Entry)) ps) (erased (Term) r) -> (NotTyCtor (TValCtor ps r))))
  ; The head's telescope, for the error rules that do not care which former it is; and a canonical type
  ; that is no former's, for the rule that refuses the application.
  ((HeadTele : ((Ctx) ctx) ((Term) hty) ((List (Entry)) ps) -> Type)
    enum
    (many HeadTy : (erased (Ctx) ctx) (erased (Term) hty) (erased (List (Entry)) ps) (erased (CanonAt ctx hty (TTyCtor ps)) c) -> (HeadTele ctx hty ps))
    (many HeadVal : (erased (Ctx) ctx) (erased (Term) hty) (erased (List (Entry)) ps) (erased (Term) ret) (erased (CanonAt ctx hty (TValCtor ps ret)) c) -> (HeadTele ctx hty ps)))
  ((NoTele : ((Term) c) -> Type)
    enum
    (many NoTeleRef : (erased (Nat) x) -> (NoTele (Ref x)))
    (many NoTeleBound : (erased (Nat) k) -> (NoTele (Bound k)))
    (many NoTeleTyApp : (erased (Term) h) (erased (List (Entry)) ps) (erased (List (Term)) as) -> (NoTele (TyApp h ps as)))
    (many NoTeleValApp : (erased (Term) h) (erased (List (Entry)) ps) (erased (Term) r) (erased (List (Term)) as) -> (NoTele (ValApp h ps r as)))
    (many NoTeleUniv : -> (NoTele (TUniv)))
    (many NoTeleFn : (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs) -> (NoTele (TFn l ps rs))))
  ; The binders a telescope's entries become, innermost first.
  ((Binders : ((List (Nat)) ids) ((List (Maybe (Nat))) acc) -> Type)
    enum
    (many BindersNil : -> (Binders (Nil (Nat)) (Nil (Maybe (Nat)))))
    (many BindersCons : (erased (Nat) x) (erased (List (Nat)) ids) (erased (List (Maybe (Nat))) acc) (erased (List (Maybe (Nat))) out)
       (erased (Binders ids acc) p) (erased (SnocId acc (Some (Nat) x) out) q) -> (Binders (Cons (Nat) x ids) out)))
  ((SnocId : ((List (Maybe (Nat))) xs) ((Maybe (Nat)) x) ((List (Maybe (Nat))) out) -> Type)
    enum
    (many SnocIdNil : (erased (Maybe (Nat)) x) -> (SnocId (Nil (Maybe (Nat))) x (Cons (Maybe (Nat)) x (Nil (Maybe (Nat))))))
    (many SnocIdCons : (erased (Maybe (Nat)) y) (erased (List (Maybe (Nat))) ys) (erased (Maybe (Nat)) x) (erased (List (Maybe (Nat))) out) (erased (SnocId ys x out) p)
       -> (SnocId (Cons (Maybe (Nat)) y ys) x (Cons (Maybe (Nat)) y out))))
  ; Arguments of the grammar against a telescope: a type entry wants the argument's type the same as the
  ; entry's, instantiated; an is entry wants the argument itself the same as the entry's expression
  ; (ASSUMPTIONS 20).
  ((ElabTermArgs : ((Ctx) ctx) ((List (Maybe (Term))) acc) ((List (Entry)) tele) ((List (Raw)) args) ((ArgsOut) out) -> Type)
    enum
    (many ETANil : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) -> (ElabTermArgs ctx acc (Nil (Entry)) (Nil (Raw)) (ArgsOk (Nil (Term)))))
    (many ETAArity : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (List (Entry)) tele) (erased (List (Raw)) args) (erased (LenMismatch (Entry) (Raw) tele args) m)
       -> (ElabTermArgs ctx acc tele args (ArgsErr (RArity))))
    (many ETATy : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (Bool) s) (erased (Term) t) (erased (List (Entry)) es) (erased (Raw) a) (erased (List (Raw)) args)
       (erased (Term) aterm) (erased (Term) aty) (erased (Term) t2) (erased (List (Term)) ts)
       (erased (ElabTerm ctx a (TOk aterm aty)) p) (erased (Subst acc t t2) sb) (erased (Same ctx aty t2) sm) (erased (ElabTermArgs ctx (Cons (Maybe (Term)) (Some (Term) aterm) acc) es args (ArgsOk ts)) q)
       -> (ElabTermArgs ctx acc (Cons (Entry) (MkEntry s (BFalse) t) es) (Cons (Raw) a args) (ArgsOk (Cons (Term) aterm ts))))
    (many ETAIs : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (Bool) s) (erased (Term) t) (erased (List (Entry)) es) (erased (Raw) a) (erased (List (Raw)) args)
       (erased (Term) aterm) (erased (Term) aty) (erased (Term) t2) (erased (List (Term)) ts)
       (erased (ElabTerm ctx a (TOk aterm aty)) p) (erased (Subst acc t t2) sb) (erased (Same ctx aterm t2) sm) (erased (ElabTermArgs ctx (Cons (Maybe (Term)) (Some (Term) aterm) acc) es args (ArgsOk ts)) q)
       -> (ElabTermArgs ctx acc (Cons (Entry) (MkEntry s (BTrue) t) es) (Cons (Raw) a args) (ArgsOk (Cons (Term) aterm ts))))
    (many ETAErr : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (Entry) e) (erased (List (Entry)) es) (erased (Raw) a) (erased (List (Raw)) args) (erased (Reason) r)
       (erased (ElabTerm ctx a (TErr r)) p) -> (ElabTermArgs ctx acc (Cons (Entry) e es) (Cons (Raw) a args) (ArgsErr r)))
    (many ETATyMismatch : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (Bool) s) (erased (Term) t) (erased (List (Entry)) es) (erased (Raw) a) (erased (List (Raw)) args)
       (erased (Term) aterm) (erased (Term) aty) (erased (Term) t2)
       (erased (ElabTerm ctx a (TOk aterm aty)) p) (erased (Subst acc t t2) sb) (erased (Differ ctx aty t2) d)
       -> (ElabTermArgs ctx acc (Cons (Entry) (MkEntry s (BFalse) t) es) (Cons (Raw) a args) (ArgsErr (RMismatch))))
    (many ETAIsMismatch : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (Bool) s) (erased (Term) t) (erased (List (Entry)) es) (erased (Raw) a) (erased (List (Raw)) args)
       (erased (Term) aterm) (erased (Term) aty) (erased (Term) t2)
       (erased (ElabTerm ctx a (TOk aterm aty)) p) (erased (Subst acc t t2) sb) (erased (Differ ctx aterm t2) d)
       -> (ElabTermArgs ctx acc (Cons (Entry) (MkEntry s (BTrue) t) es) (Cons (Raw) a args) (ArgsErr (RMismatch))))
    (many ETARestErr : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (Bool) s) (erased (Bool) i) (erased (Term) t) (erased (List (Entry)) es) (erased (Raw) a) (erased (List (Raw)) args)
       (erased (Term) aterm) (erased (Term) aty) (erased (Reason) r)
       (erased (ElabTerm ctx a (TOk aterm aty)) p) (erased (ElabTermArgs ctx (Cons (Maybe (Term)) (Some (Term) aterm) acc) es args (ArgsErr r)) q)
       -> (ElabTermArgs ctx acc (Cons (Entry) (MkEntry s i t) es) (Cons (Raw) a args) (ArgsErr r))))
  ; A telescope written as entries: each entry's term is elaborated with the earlier entries in scope, a
  ; type entry's must be a type, and the entry is minted and then abstracted into a binder.
  ((EntryRaw : ((Raw) raw) ((Bool) subs) ((Bool) has-is) ((Raw) term) ((String) name) -> Type)
    enum
    (many EntryTy : (erased (Raw) tr) (erased (String) x) -> (EntryRaw (RList (Cons (Raw) tr (Cons (Raw) (RAtom x) (Nil (Raw))))) (BFalse) (BFalse) tr x))
    (many EntrySub : (erased (Raw) tr) (erased (String) x) -> (EntryRaw (RList (Cons (Raw) (RKey (KSubterm)) (Cons (Raw) tr (Cons (Raw) (RAtom x) (Nil (Raw)))))) (BTrue) (BFalse) tr x))
    (many EntryIs : (erased (Raw) er) (erased (String) x) -> (EntryRaw (RList (Cons (Raw) er (Cons (Raw) (RKey (KIs)) (Cons (Raw) (RAtom x) (Nil (Raw)))))) (BFalse) (BTrue) er x)))
  ((ElabTele : ((Ctx) ctx) ((List (Maybe (Nat))) acc) ((List (Raw)) raws) ((TeleOut) out) -> Type)
    enum
    (many ELNil : (erased (Ctx) ctx) (erased (List (Maybe (Nat))) acc) -> (ElabTele ctx acc (Nil (Raw)) (TeleOk ctx (Nil (Entry)) (Nil (Nat)) (Nil (Maybe (String))))))
    (many ELTy : (erased (Ctx) ctx) (erased (List (Maybe (Nat))) acc) (erased (Raw) e) (erased (Bool) s) (erased (Raw) tr) (erased (String) x) (erased (List (Raw)) rest)
       (erased (Term) t) (erased (Term) tty) (erased (Nat) id) (erased (Ctx) ctx1) (erased (Term) t2) (erased (Ctx) out) (erased (List (Entry)) es) (erased (List (Nat)) ids) (erased (List (Maybe (String))) names)
       (erased (EntryRaw e s (BFalse) tr x) shape)
       (erased (ElabTerm ctx tr (TOk t tty)) p) (erased (Same ctx tty (TUniv)) su) (erased (Mint ctx (Some (String) x) t (KPlain) (None (Term)) id ctx1) m)
       (erased (Abstract acc t t2) ab) (erased (ElabTele ctx1 (Cons (Maybe (Nat)) (Some (Nat) id) acc) rest (TeleOk out es ids names)) q)
       -> (ElabTele ctx acc (Cons (Raw) e rest) (TeleOk out (Cons (Entry) (MkEntry s (BFalse) t2) es) (Cons (Nat) id ids) (Cons (Maybe (String)) (Some (String) x) names))))
    (many ELIs : (erased (Ctx) ctx) (erased (List (Maybe (Nat))) acc) (erased (Raw) e) (erased (Bool) s) (erased (Raw) er) (erased (String) x) (erased (List (Raw)) rest)
       (erased (Term) t) (erased (Term) tty) (erased (Nat) id) (erased (Ctx) ctx1) (erased (Term) t2) (erased (Ctx) out) (erased (List (Entry)) es) (erased (List (Nat)) ids) (erased (List (Maybe (String))) names)
       (erased (EntryRaw e s (BTrue) er x) shape)
       (erased (ElabTerm ctx er (TOk t tty)) p) (erased (Mint ctx (Some (String) x) tty (KPlain) (Some (Term) t) id ctx1) m)
       (erased (Abstract acc t t2) ab) (erased (ElabTele ctx1 (Cons (Maybe (Nat)) (Some (Nat) id) acc) rest (TeleOk out es ids names)) q)
       -> (ElabTele ctx acc (Cons (Raw) e rest) (TeleOk out (Cons (Entry) (MkEntry s (BTrue) t2) es) (Cons (Nat) id ids) (Cons (Maybe (String)) (Some (String) x) names))))
    (many ELTermErr : (erased (Ctx) ctx) (erased (List (Maybe (Nat))) acc) (erased (Raw) e) (erased (Bool) s) (erased (Bool) i) (erased (Raw) tr) (erased (String) x) (erased (List (Raw)) rest) (erased (Reason) r)
       (erased (EntryRaw e s i tr x) shape) (erased (ElabTerm ctx tr (TErr r)) p) -> (ElabTele ctx acc (Cons (Raw) e rest) (TeleErr r)))
    (many ELNotType : (erased (Ctx) ctx) (erased (List (Maybe (Nat))) acc) (erased (Raw) e) (erased (Bool) s) (erased (Raw) tr) (erased (String) x) (erased (List (Raw)) rest) (erased (Term) t) (erased (Term) tty)
       (erased (EntryRaw e s (BFalse) tr x) shape) (erased (ElabTerm ctx tr (TOk t tty)) p) (erased (Differ ctx tty (TUniv)) d) -> (ElabTele ctx acc (Cons (Raw) e rest) (TeleErr (RMismatch))))
    (many ELRestErr : (erased (Ctx) ctx) (erased (List (Maybe (Nat))) acc) (erased (Raw) e) (erased (Bool) s) (erased (Bool) i) (erased (Raw) tr) (erased (String) x) (erased (List (Raw)) rest)
       (erased (Term) t) (erased (Term) tty) (erased (Nat) id) (erased (Ctx) ctx1) (erased (Term) ety) (erased (Maybe (Term)) rule) (erased (Reason) r)
       (erased (EntryRaw e s i tr x) shape) (erased (ElabTerm ctx tr (TOk t tty)) p) (erased (EntryMint i t tty ety rule) em) (erased (Mint ctx (Some (String) x) ety (KPlain) rule id ctx1) m)
       (erased (ElabTele ctx1 (Cons (Maybe (Nat)) (Some (Nat) id) acc) rest (TeleErr r)) q) -> (ElabTele ctx acc (Cons (Raw) e rest) (TeleErr r))))
  ; What an entry's entry gets: a type entry its term as type, an is entry the term's type and the term as rule.
  ((EntryMint : ((Bool) has-is) ((Term) t) ((Term) tty) ((Term) ety) ((Maybe (Term)) rule) -> Type)
    enum
    (many EMTy : (erased (Term) t) (erased (Term) tty) -> (EntryMint (BFalse) t tty t (None (Term))))
    (many EMIs : (erased (Term) t) (erased (Term) tty) -> (EntryMint (BTrue) t tty tty (Some (Term) t)))))

; ---- Expressions (section 27): an expression elaborates to core code and the entries of its values, in a
; context extended with those entries and whatever facts the expression minted. A name is its entry; a
; constructor application, a former and a proof each get an entry of their own (section 5), a call one per
; return, a match one per result.
(def-adts
  ((EOut : -> Type)
    enum
    (many EOk : (many (Ctx) ctx) (many (Core) core) (many (List (Nat)) ids) -> (EOut))
    (many EErr : (many (Reason) r) -> (EOut)))
  ((AOut : -> Type)
    enum
    (many AllOk : (many (Ctx) ctx) (many (List (Core)) cores) (many (List (Nat)) ids) -> (AOut))
    (many AErr : (many (Reason) r) -> (AOut)))
  ((SOut : -> Type)
    enum
    (many SOk : (many (Ctx) ctx) (many (Stmt) s) -> (SOut))
    (many SErr : (many (Reason) r) -> (SOut)))
  ((DOut : -> Type)
    enum
    (many DOk : (many (Ctx) ctx) -> (DOut))
    (many DErr : (many (Reason) r) -> (DOut)))
  ((ROut : -> Type)
    enum
    (many ROk : -> (ROut))
    (many RErr : (many (Reason) r) -> (ROut)))
  ((BrOut : -> Type)
    enum
    (many BrOk : (many (Ctx) ctx) (many (List (Branch)) bs) (many (List (Nat)) seen) -> (BrOut))
    (many BrErr : (many (Reason) r) -> (BrOut)))
  ((Sig : -> Type)
    enum
    (many MkSig : (many (Nat) fid) (many (List (Entry)) ps) (many (List (Maybe (String))) pnames) (many (List (Entry)) rs) -> (Sig)))
  ((FOut : -> Type)
    enum
    (many FOk : (many (Ctx) ctx) (many (List (Sig)) sigs) -> (FOut))
    (many FErr : (many (Reason) r) -> (FOut)))
  ((BsOut : -> Type)
    enum
    (many BsOk : (many (Ctx) ctx) (many (List (FnDef)) fds) -> (BsOut))
    (many BsErr : (many (Reason) r) -> (BsOut)))
  ((FOutT : -> Type)
    enum
    (many FOkT : (many (Ctx) ctx) (many (List (Nat)) ids) -> (FOutT))
    (many FErrT : (many (Reason) r) -> (FOutT)))
  ; A call's decrease annotation (section 19): none, (predates p) after the head, or (subterm p) before the
  ; i-th argument.
  ((Ann : -> Type)
    enum
    (many ANone : -> (Ann))
    (many APredates : (many (Raw) p) -> (Ann))
    (many ASubterm : (many (Nat) i) (many (Raw) p) -> (Ann))))

(def-adts
  ((Refs : ((List (Nat)) ids) ((List (Term)) ts) -> Type)
    enum
    (many RefsNil : -> (Refs (Nil (Nat)) (Nil (Term))))
    (many RefsCons : (erased (Nat) x) (erased (List (Nat)) ids) (erased (List (Term)) ts) (erased (Refs ids ts) p) -> (Refs (Cons (Nat) x ids) (Cons (Term) (Ref x) ts))))
  ((NotOne : ((List (Nat)) ids) -> Type)
    enum
    (many NotOneNil : -> (NotOne (Nil (Nat))))
    (many NotOneMore : (erased (Nat) x) (erased (Nat) y) (erased (List (Nat)) ids) -> (NotOne (Cons (Nat) x (Cons (Nat) y ids)))))
  ((AtomNames : ((List (Raw)) raws) ((List (Maybe (String))) names) -> Type)
    enum
    (many ANNil : -> (AtomNames (Nil (Raw)) (Nil (Maybe (String)))))
    (many ANCons : (erased (String) x) (erased (List (Raw)) raws) (erased (List (Maybe (String))) names) (erased (AtomNames raws names) p)
       -> (AtomNames (Cons (Raw) (RAtom x) raws) (Cons (Maybe (String)) (Some (String) x) names))))
  ; A call's items after the head: the annotation found and the arguments without it.
  ((CallRaw : ((List (Raw)) items) ((Ann) ann) ((List (Raw)) args) -> Type)
    enum
    (many CRPredates : (erased (Raw) p) (erased (List (Raw)) args) (erased (Plain args) pl) -> (CallRaw (Cons (Raw) (RList (Cons (Raw) (RKey (KPredates)) (Cons (Raw) p (Nil (Raw))))) args) (APredates p) args))
    (many CRPlain : (erased (List (Raw)) args) (erased (Plain args) pl) -> (CallRaw args (ANone) args))
    (many CRSubterm : (erased (List (Raw)) items) (erased (Nat) i) (erased (Raw) p) (erased (List (Raw)) args) (erased (SubtermAt items i p args) sat) -> (CallRaw items (ASubterm i p) args)))
  ; Arguments with no annotation among them, and the position of a (subterm p) among them.
  ((Plain : ((List (Raw)) args) -> Type)
    enum
    (many PlainNil : -> (Plain (Nil (Raw))))
    (many PlainAtom : (erased (String) x) (erased (List (Raw)) args) (erased (Plain args) p) -> (Plain (Cons (Raw) (RAtom x) args)))
    (many PlainNilList : (erased (List (Raw)) args) (erased (Plain args) p) -> (Plain (Cons (Raw) (RList (Nil (Raw))) args)))
    (many PlainAtomList : (erased (String) x) (erased (List (Raw)) items) (erased (List (Raw)) args) (erased (Plain args) p) -> (Plain (Cons (Raw) (RList (Cons (Raw) (RAtom x) items)) args)))
    (many PlainListList : (erased (List (Raw)) inner) (erased (List (Raw)) items) (erased (List (Raw)) args) (erased (Plain args) p) -> (Plain (Cons (Raw) (RList (Cons (Raw) (RList inner) items)) args)))
    (many PlainKeyList : (erased (Key) k) (erased (List (Raw)) items) (erased (List (Raw)) args) (erased (NotAnnKey k) nk) (erased (Plain args) p) -> (Plain (Cons (Raw) (RList (Cons (Raw) (RKey k) items)) args))))
  ((NotAnnKey : ((Key) k) -> Type)
    enum
    (many NAKFn : -> (NotAnnKey (KFn)))
    (many NAKTyCtor : -> (NotAnnKey (KTyCtor)))
    (many NAKValCtor : -> (NotAnnKey (KValCtor)))
    (many NAKMatch : -> (NotAnnKey (KMatch)))
    (many NAKValues : -> (NotAnnKey (KValues)))
    (many NAKProveSubterm : -> (NotAnnKey (KProveSubterm)))
    (many NAKProvePredates : -> (NotAnnKey (KProvePredates)))
    (many NAKPredatesTrans : -> (NotAnnKey (KPredatesTrans)))
    (many NAKSubtermTrans : -> (NotAnnKey (KSubtermTrans)))
    (many NAKPredatesSubterm : -> (NotAnnKey (KPredatesSubterm))))
  ((SubtermAt : ((List (Raw)) items) ((Nat) i) ((Raw) p) ((List (Raw)) args) -> Type)
    enum
    (many SAHere : (erased (Raw) p) (erased (Raw) a) (erased (List (Raw)) args) (erased (Plain (Cons (Raw) a args)) pl)
       -> (SubtermAt (Cons (Raw) (RList (Cons (Raw) (RKey (KSubterm)) (Cons (Raw) p (Nil (Raw))))) (Cons (Raw) a args)) (Zero) p (Cons (Raw) a args)))
    (many SAThere : (erased (Raw) a) (erased (List (Raw)) items) (erased (Nat) i) (erased (Raw) p) (erased (List (Raw)) args) (erased (Plain (Cons (Raw) a (Nil (Raw)))) pl) (erased (SubtermAt items i p args) q)
       -> (SubtermAt (Cons (Raw) a items) (Succ i) p (Cons (Raw) a args))))
  ; Among a telescope's entries, the i-th is marked subterm and j earlier ones are.
  ((MarkedIndex : ((List (Entry)) tele) ((Nat) i) ((Nat) j) -> Type)
    enum
    (many MIHere : (erased (Bool) has-is) (erased (Term) t) (erased (List (Entry)) es) -> (MarkedIndex (Cons (Entry) (MkEntry (BTrue) has-is t) es) (Zero) (Zero)))
    (many MIYes : (erased (Bool) has-is) (erased (Term) t) (erased (List (Entry)) es) (erased (Nat) i) (erased (Nat) j) (erased (MarkedIndex es i j) p)
       -> (MarkedIndex (Cons (Entry) (MkEntry (BTrue) has-is t) es) (Succ i) (Succ j)))
    (many MINo : (erased (Bool) has-is) (erased (Term) t) (erased (List (Entry)) es) (erased (Nat) i) (erased (Nat) j) (erased (MarkedIndex es i j) p)
       -> (MarkedIndex (Cons (Entry) (MkEntry (BFalse) has-is t) es) (Succ i) j)))
  ; The first j of two lists the same, pairwise, and the j-th of the second.
  ((SamePrefix : ((Ctx) ctx) ((Nat) j) ((List (Term)) as) ((List (Term)) bs) ((Term) b) -> Type)
    enum
    (many SPZero : (erased (Ctx) ctx) (erased (List (Term)) as) (erased (Term) b) (erased (List (Term)) bs) -> (SamePrefix ctx (Zero) as (Cons (Term) b bs) b))
    (many SPSucc : (erased (Ctx) ctx) (erased (Nat) j) (erased (Term) a) (erased (List (Term)) as) (erased (Term) b0) (erased (List (Term)) bs) (erased (Term) b)
       (erased (Same ctx a b0) sm) (erased (SamePrefix ctx j as bs b) p) -> (SamePrefix ctx (Succ j) (Cons (Term) a as) (Cons (Term) b0 bs) b))))

; A strict subterm through constructor applications (section 18), on canonical terms, and its absence.
(def-adts
  ((StrictSub : ((Ctx) ctx) ((Term) a) ((Term) b) -> Type)
    enum
    (many SSHead : (erased (Ctx) ctx) (erased (Term) a) (erased (Term) b) (erased (Term) h) (erased (List (Term)) as) (erased (AppParts b h as) ap) (erased (Same ctx a h) s) -> (StrictSub ctx a b))
    (many SSArg : (erased (Ctx) ctx) (erased (Term) a) (erased (Term) b) (erased (Term) h) (erased (List (Term)) as) (erased (AppParts b h as) ap) (erased (SubOfList ctx a as) p) -> (StrictSub ctx a b)))
  ((AppParts : ((Term) t) ((Term) h) ((List (Term)) as) -> Type)
    enum
    (many APTy : (erased (Term) h) (erased (List (Entry)) ps) (erased (List (Term)) as) -> (AppParts (TyApp h ps as) h as))
    (many APVal : (erased (Term) h) (erased (List (Entry)) ps) (erased (Term) r) (erased (List (Term)) as) -> (AppParts (ValApp h ps r as) h as)))
  ((SubOfList : ((Ctx) ctx) ((Term) a) ((List (Term)) as) -> Type)
    enum
    (many SLSame : (erased (Ctx) ctx) (erased (Term) a) (erased (Term) b) (erased (List (Term)) as) (erased (Same ctx a b) s) -> (SubOfList ctx a (Cons (Term) b as)))
    (many SLDeep : (erased (Ctx) ctx) (erased (Term) a) (erased (Term) b) (erased (List (Term)) as) (erased (StrictSub ctx a b) s) -> (SubOfList ctx a (Cons (Term) b as)))
    (many SLThere : (erased (Ctx) ctx) (erased (Term) a) (erased (Term) b) (erased (List (Term)) as) (erased (SubOfList ctx a as) p) -> (SubOfList ctx a (Cons (Term) b as))))
  ((NotSub : ((Ctx) ctx) ((Term) a) ((Term) b) -> Type)
    enum
    (many NSNotApp : (erased (Ctx) ctx) (erased (Term) a) (erased (Term) b) (erased (NotApp b) n) -> (NotSub ctx a b))
    (many NSApp : (erased (Ctx) ctx) (erased (Term) a) (erased (Term) b) (erased (Term) h) (erased (List (Term)) as) (erased (AppParts b h as) ap) (erased (Differ ctx a h) d) (erased (NotSubList ctx a as) p) -> (NotSub ctx a b)))
  ((NotSubList : ((Ctx) ctx) ((Term) a) ((List (Term)) as) -> Type)
    enum
    (many NSLNil : (erased (Ctx) ctx) (erased (Term) a) -> (NotSubList ctx a (Nil (Term))))
    (many NSLCons : (erased (Ctx) ctx) (erased (Term) a) (erased (Term) b) (erased (List (Term)) as) (erased (Differ ctx a b) d) (erased (NotSub ctx a b) n) (erased (NotSubList ctx a as) p)
       -> (NotSubList ctx a (Cons (Term) b as)))))

; The shapes a proof's canonical type must have, and their absence: (Predates A a l) is entry 1 applied,
; (Subterm A a B b) entry 2.
(def-adts
  ((NotPredates : ((Ctx) ctx) ((Term) t) ((Term) l) ((Term) cur) -> Type)
    enum
    (many NPNotApp : (erased (Ctx) ctx) (erased (Term) t) (erased (Term) l) (erased (Term) cur) (erased (NotTyApp t) n) -> (NotPredates ctx t l cur))
    (many NPHead : (erased (Ctx) ctx) (erased (Term) h) (erased (List (Entry)) hps) (erased (List (Term)) as) (erased (Term) l) (erased (Term) cur) (erased (Differ ctx h (Ref (Succ (Zero)))) d) -> (NotPredates ctx (TyApp h hps as) l cur))
    (many NPArity : (erased (Ctx) ctx) (erased (Term) h) (erased (List (Entry)) hps) (erased (List (Term)) as) (erased (Term) l) (erased (Term) cur) (erased (NotLen (Succ (Succ (Succ (Zero)))) as) n) -> (NotPredates ctx (TyApp h hps as) l cur))
    (many NPType : (erased (Ctx) ctx) (erased (Term) h) (erased (List (Entry)) hps) (erased (Term) ty) (erased (Term) a) (erased (Term) lv) (erased (Term) l) (erased (Term) cur) (erased (Differ ctx ty level-ty) d)
       -> (NotPredates ctx (TyApp h hps (Cons (Term) ty (Cons (Term) a (Cons (Term) lv (Nil (Term)))))) l cur))
    (many NPLevel : (erased (Ctx) ctx) (erased (Term) h) (erased (List (Entry)) hps) (erased (Term) ty) (erased (Term) a) (erased (Term) lv) (erased (Term) l) (erased (Term) cur) (erased (Differ ctx a l) d)
       -> (NotPredates ctx (TyApp h hps (Cons (Term) ty (Cons (Term) a (Cons (Term) lv (Nil (Term)))))) l cur))
    (many NPCur : (erased (Ctx) ctx) (erased (Term) h) (erased (List (Entry)) hps) (erased (Term) ty) (erased (Term) a) (erased (Term) lv) (erased (Term) l) (erased (Term) cur) (erased (Differ ctx lv cur) d)
       -> (NotPredates ctx (TyApp h hps (Cons (Term) ty (Cons (Term) a (Cons (Term) lv (Nil (Term)))))) l cur)))
  ((NotSubtermOf : ((Ctx) ctx) ((Term) t) ((Term) a) ((Term) b) -> Type)
    enum
    (many NTNotApp : (erased (Ctx) ctx) (erased (Term) t) (erased (Term) a) (erased (Term) b) (erased (NotTyApp t) n) -> (NotSubtermOf ctx t a b))
    (many NTHead : (erased (Ctx) ctx) (erased (Term) h) (erased (List (Entry)) hps) (erased (List (Term)) as) (erased (Term) a) (erased (Term) b) (erased (Differ ctx h (Ref (Succ (Succ (Zero))))) d) -> (NotSubtermOf ctx (TyApp h hps as) a b))
    (many NTArity : (erased (Ctx) ctx) (erased (Term) h) (erased (List (Entry)) hps) (erased (List (Term)) as) (erased (Term) a) (erased (Term) b) (erased (NotLen (Succ (Succ (Succ (Succ (Zero))))) as) n) -> (NotSubtermOf ctx (TyApp h hps as) a b))
    (many NTSmall : (erased (Ctx) ctx) (erased (Term) h) (erased (List (Entry)) hps) (erased (Term) ta) (erased (Term) a0) (erased (Term) tb) (erased (Term) b0) (erased (Term) a) (erased (Term) b) (erased (Differ ctx a0 a) d)
       -> (NotSubtermOf ctx (TyApp h hps (Cons (Term) ta (Cons (Term) a0 (Cons (Term) tb (Cons (Term) b0 (Nil (Term))))))) a b))
    (many NTBig : (erased (Ctx) ctx) (erased (Term) h) (erased (List (Entry)) hps) (erased (Term) ta) (erased (Term) a0) (erased (Term) tb) (erased (Term) b0) (erased (Term) a) (erased (Term) b) (erased (Differ ctx b0 b) d)
       -> (NotSubtermOf ctx (TyApp h hps (Cons (Term) ta (Cons (Term) a0 (Cons (Term) tb (Cons (Term) b0 (Nil (Term))))))) a b)))
  ((NotLen : ((Nat) n) ((List (Term)) as) -> Type)
    enum
    (many NLNilSucc : (erased (Nat) n) -> (NotLen (Succ n) (Nil (Term))))
    (many NLConsZero : (erased (Term) a) (erased (List (Term)) as) -> (NotLen (Zero) (Cons (Term) a as)))
    (many NLCons : (erased (Nat) n) (erased (Term) a) (erased (List (Term)) as) (erased (NotLen n as) p) -> (NotLen (Succ n) (Cons (Term) a as))))
  ((NotLevelKind : ((Kind) k) -> Type)
    enum
    (many NLKPlain : -> (NotLevelKind (KPlain)))
    (many NLKDecl : -> (NotLevelKind (KDecl)))))

; A canonical type as a Predates or Subterm application, or evidence that it is neither, for the three
; transitivity axioms of section 18, special forms by the owner's decision.
(def-adts
  ((PredatesShape : ((Ctx) ctx) ((Term) c) ((Term) ty) ((Term) a) ((Term) lv) -> Type)
    enum
    (many PSBy : (erased (Ctx) ctx) (erased (Term) h) (erased (List (Entry)) hps) (erased (Term) ty) (erased (Term) a) (erased (Term) lv) (erased (Same ctx h (Ref (Succ (Zero)))) sh)
       -> (PredatesShape ctx (TyApp h hps (Cons (Term) ty (Cons (Term) a (Cons (Term) lv (Nil (Term)))))) ty a lv)))
  ((NotPredatesShape : ((Ctx) ctx) ((Term) c) -> Type)
    enum
    (many NPSNotApp : (erased (Ctx) ctx) (erased (Term) c) (erased (NotTyApp c) n) -> (NotPredatesShape ctx c))
    (many NPSHead : (erased (Ctx) ctx) (erased (Term) h) (erased (List (Entry)) hps) (erased (List (Term)) as) (erased (Differ ctx h (Ref (Succ (Zero)))) d) -> (NotPredatesShape ctx (TyApp h hps as)))
    (many NPSArity : (erased (Ctx) ctx) (erased (Term) h) (erased (List (Entry)) hps) (erased (List (Term)) as) (erased (NotLen (Succ (Succ (Succ (Zero)))) as) n) -> (NotPredatesShape ctx (TyApp h hps as))))
  ((SubtermShape : ((Ctx) ctx) ((Term) c) ((Term) ta) ((Term) a) ((Term) tb) ((Term) b) -> Type)
    enum
    (many SSBy : (erased (Ctx) ctx) (erased (Term) h) (erased (List (Entry)) hps) (erased (Term) ta) (erased (Term) a) (erased (Term) tb) (erased (Term) b) (erased (Same ctx h (Ref (Succ (Succ (Zero))))) sh)
       -> (SubtermShape ctx (TyApp h hps (Cons (Term) ta (Cons (Term) a (Cons (Term) tb (Cons (Term) b (Nil (Term))))))) ta a tb b)))
  ((NotSubtermShape : ((Ctx) ctx) ((Term) c) -> Type)
    enum
    (many NSSNotApp : (erased (Ctx) ctx) (erased (Term) c) (erased (NotTyApp c) n) -> (NotSubtermShape ctx c))
    (many NSSHead : (erased (Ctx) ctx) (erased (Term) h) (erased (List (Entry)) hps) (erased (List (Term)) as) (erased (Differ ctx h (Ref (Succ (Succ (Zero))))) d) -> (NotSubtermShape ctx (TyApp h hps as)))
    (many NSSArity : (erased (Ctx) ctx) (erased (Term) h) (erased (List (Entry)) hps) (erased (List (Term)) as) (erased (NotLen (Succ (Succ (Succ (Succ (Zero))))) as) n) -> (NotSubtermShape ctx (TyApp h hps as)))))

; The initial context: Level, Predates and Subterm as built-in type constructors, and Type, whose rule is
; the universe (section 10). (Predates A a l) takes a type, a value of it and a level; (Subterm A a B b)
; two typed values.
(let ((many init-ctx))
  (MkCtx (Succ (Succ (Succ (Succ (Zero)))))
    (Cons _ (MkName "Type" (Succ (Succ (Succ (Zero))))) $ Cons _ (MkName "Subterm" (Succ (Succ (Zero)))) $ Cons _ (MkName "Predates" (Succ (Zero))) $ Cons _ (MkName "Level" (Zero)) $ Nil _)
    (Cons _ (MkEnt (Succ (Succ (Succ (Zero)))) (TUniv) (KPlain))
      $ Cons _ (MkEnt (Succ (Succ (Zero))) (TTyCtor subterm-ps) (KDecl))
      $ Cons _ (MkEnt (Succ (Zero)) (TTyCtor predates-ps) (KDecl))
      $ Cons _ (MkEnt (Zero) (TTyCtor (Nil _)) (KDecl)) $ Nil _)
    (Cons _ (MkRule (Succ (Succ (Succ (Zero)))) (TUniv)) (Nil _))
    (Nil _) (None _) (Nil _)))

(def-adts
  ((ElabExpr : ((Ctx) ctx) ((Raw) raw) ((EOut) out) -> Type)
    enum
    ; a name
    (many EXName : (erased (Ctx) ctx) (erased (String) s) (erased (Nat) x) (erased (List (Name)) scope) (erased (Scope ctx scope) sc) (erased (NameOf scope s x) n)
       -> (ElabExpr ctx (RAtom s) (EOk ctx (CVar x) (Cons (Nat) x (Nil (Nat))))))
    (many EXUnbound : (erased (Ctx) ctx) (erased (String) s) (erased (List (Name)) scope) (erased (Scope ctx scope) sc) (erased (NoName scope s) n) -> (ElabExpr ctx (RAtom s) (EErr (RUnbound))))
    ; values
    (many EXValues : (erased (Ctx) ctx) (erased (List (Raw)) items) (erased (Ctx) out) (erased (List (Core)) cores) (erased (List (Nat)) ids) (erased (ElabItems ctx items (AllOk out cores ids)) p)
       -> (ElabExpr ctx (RList (Cons (Raw) (RKey (KValues)) items)) (EOk out (CValues cores) ids)))
    (many EXValuesErr : (erased (Ctx) ctx) (erased (List (Raw)) items) (erased (Reason) r) (erased (ElabItems ctx items (AErr r)) p) -> (ElabExpr ctx (RList (Cons (Raw) (RKey (KValues)) items)) (EErr r)))
    ; a former as a value
    (many EXFormer : (erased (Ctx) ctx) (erased (Key) k) (erased (List (Raw)) items) (erased (Term) t) (erased (Term) ty) (erased (Nat) x) (erased (Ctx) out)
       (erased (FormerKey k) fk) (erased (ElabTerm ctx (RList (Cons (Raw) (RKey k) items)) (TOk t ty)) p) (erased (Mint ctx (None (String)) ty (KPlain) (Some (Term) t) x out) m)
       -> (ElabExpr ctx (RList (Cons (Raw) (RKey k) items)) (EOk out (CFormer t) (Cons (Nat) x (Nil (Nat))))))
    (many EXFormerErr : (erased (Ctx) ctx) (erased (Key) k) (erased (List (Raw)) items) (erased (Reason) r) (erased (FormerKey k) fk) (erased (ElabTerm ctx (RList (Cons (Raw) (RKey k) items)) (TErr r)) p)
       -> (ElabExpr ctx (RList (Cons (Raw) (RKey k) items)) (EErr r)))
    ; an application: of a type constructor, of a value constructor, or a call
    (many EXHeadErr : (erased (Ctx) ctx) (erased (Raw) h) (erased (List (Raw)) items) (erased (Reason) r) (erased (HeadRaw h) hr) (erased (ElabExpr ctx h (EErr r)) p)
       -> (ElabExpr ctx (RList (Cons (Raw) h items)) (EErr r)))
    (many EXHeadSize : (erased (Ctx) ctx) (erased (Raw) h) (erased (List (Raw)) items) (erased (Ctx) ctx1) (erased (Core) hc) (erased (List (Nat)) ids) (erased (HeadRaw h) hr) (erased (ElabExpr ctx h (EOk ctx1 hc ids)) p) (erased (NotOne ids) n)
       -> (ElabExpr ctx (RList (Cons (Raw) h items)) (EErr (RSize))))
    (many EXTyApp : (erased (Ctx) ctx) (erased (Raw) h) (erased (List (Raw)) items) (erased (Ctx) ctx1) (erased (Core) hc) (erased (Nat) x) (erased (Term) hty) (erased (List (Entry)) ps)
       (erased (Ctx) ctx2) (erased (List (Core)) cores) (erased (List (Nat)) ids) (erased (List (Term)) ts) (erased (Nat) e) (erased (Ctx) out)
       (erased (HeadRaw h) hr) (erased (ElabExpr ctx h (EOk ctx1 hc (Cons (Nat) x (Nil (Nat))))) p) (erased (TypeOf ctx1 x hty) t) (erased (CanonAt ctx1 hty (TTyCtor ps)) c)
       (erased (ElabExprArgs ctx1 (Nil (Maybe (Term))) ps items (AllOk ctx2 cores ids)) a) (erased (Refs ids ts) rf) (erased (Mint ctx2 (None (String)) (TUniv) (KPlain) (Some (Term) (TyApp (Ref x) ps ts)) e out) m)
       -> (ElabExpr ctx (RList (Cons (Raw) h items)) (EOk out (CApp hc cores) (Cons (Nat) e (Nil (Nat))))))
    (many EXValApp : (erased (Ctx) ctx) (erased (Raw) h) (erased (List (Raw)) items) (erased (Ctx) ctx1) (erased (Core) hc) (erased (Nat) x) (erased (Term) hty) (erased (List (Entry)) ps) (erased (Term) ret)
       (erased (Ctx) ctx2) (erased (List (Core)) cores) (erased (List (Nat)) ids) (erased (List (Term)) ts) (erased (List (Maybe (Term))) subs) (erased (Term) ty) (erased (Nat) e) (erased (Ctx) out)
       (erased (HeadRaw h) hr) (erased (ElabExpr ctx h (EOk ctx1 hc (Cons (Nat) x (Nil (Nat))))) p) (erased (TypeOf ctx1 x hty) t) (erased (CanonAt ctx1 hty (TValCtor ps ret)) c)
       (erased (ElabExprArgs ctx1 (Nil (Maybe (Term))) ps items (AllOk ctx2 cores ids)) a) (erased (Refs ids ts) rf) (erased (Somes ts subs) s) (erased (Subst subs ret ty) sb)
       (erased (Mint ctx2 (None (String)) ty (KPlain) (Some (Term) (ValApp (Ref x) ps ret ts)) e out) m)
       -> (ElabExpr ctx (RList (Cons (Raw) h items)) (EOk out (CApp hc cores) (Cons (Nat) e (Nil (Nat))))))
    (many EXAppArgsErr : (erased (Ctx) ctx) (erased (Raw) h) (erased (List (Raw)) items) (erased (Ctx) ctx1) (erased (Core) hc) (erased (Nat) x) (erased (Term) hty) (erased (List (Entry)) ps) (erased (Reason) r)
       (erased (HeadRaw h) hr) (erased (ElabExpr ctx h (EOk ctx1 hc (Cons (Nat) x (Nil (Nat))))) p) (erased (TypeOf ctx1 x hty) t) (erased (HeadTele ctx1 hty ps) c)
       (erased (ElabExprArgs ctx1 (Nil (Maybe (Term))) ps items (AErr r)) a) -> (ElabExpr ctx (RList (Cons (Raw) h items)) (EErr r)))
    (many EXCall : (erased (Ctx) ctx) (erased (Raw) h) (erased (List (Raw)) items) (erased (Ctx) ctx1) (erased (Core) hc) (erased (Nat) x) (erased (Term) hty) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs)
       (erased (Ann) ann) (erased (List (Raw)) args) (erased (Ctx) ctx2) (erased (List (Core)) cores) (erased (List (Nat)) ids) (erased (Ctx) ctx3) (erased (List (Term)) ts) (erased (List (Maybe (Term))) subs)
       (erased (List (Maybe (String))) names) (erased (Ctx) out) (erased (List (Nat)) rids)
       (erased (HeadRaw h) hr) (erased (ElabExpr ctx h (EOk ctx1 hc (Cons (Nat) x (Nil (Nat))))) p) (erased (TypeOf ctx1 x hty) t) (erased (CanonAt ctx1 hty (TFn l ps rs)) c)
       (erased (CallRaw items ann args) cr) (erased (ElabExprArgs ctx1 (Nil (Maybe (Term))) ps args (AllOk ctx2 cores ids)) a) (erased (Decrease ctx2 l ps ids ann (DOk ctx3)) d)
       (erased (Refs ids ts) rf) (erased (Somes ts subs) s) (erased (Nones rs names) nn) (erased (MintTele ctx3 subs rs names out rids) m)
       -> (ElabExpr ctx (RList (Cons (Raw) h items)) (EOk out (CCall hc cores) rids)))
    (many EXCallArgsErr : (erased (Ctx) ctx) (erased (Raw) h) (erased (List (Raw)) items) (erased (Ctx) ctx1) (erased (Core) hc) (erased (Nat) x) (erased (Term) hty) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs)
       (erased (Ann) ann) (erased (List (Raw)) args) (erased (Reason) r)
       (erased (HeadRaw h) hr) (erased (ElabExpr ctx h (EOk ctx1 hc (Cons (Nat) x (Nil (Nat))))) p) (erased (TypeOf ctx1 x hty) t) (erased (CanonAt ctx1 hty (TFn l ps rs)) c)
       (erased (CallRaw items ann args) cr) (erased (ElabExprArgs ctx1 (Nil (Maybe (Term))) ps args (AErr r)) a) -> (ElabExpr ctx (RList (Cons (Raw) h items)) (EErr r)))
    (many EXCallDecreaseErr : (erased (Ctx) ctx) (erased (Raw) h) (erased (List (Raw)) items) (erased (Ctx) ctx1) (erased (Core) hc) (erased (Nat) x) (erased (Term) hty) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs)
       (erased (Ann) ann) (erased (List (Raw)) args) (erased (Ctx) ctx2) (erased (List (Core)) cores) (erased (List (Nat)) ids) (erased (Reason) r)
       (erased (HeadRaw h) hr) (erased (ElabExpr ctx h (EOk ctx1 hc (Cons (Nat) x (Nil (Nat))))) p) (erased (TypeOf ctx1 x hty) t) (erased (CanonAt ctx1 hty (TFn l ps rs)) c)
       (erased (CallRaw items ann args) cr) (erased (ElabExprArgs ctx1 (Nil (Maybe (Term))) ps args (AllOk ctx2 cores ids)) a) (erased (Decrease ctx2 l ps ids ann (DErr r)) d)
       -> (ElabExpr ctx (RList (Cons (Raw) h items)) (EErr r)))
    (many EXNotApplicable : (erased (Ctx) ctx) (erased (Raw) h) (erased (List (Raw)) items) (erased (Ctx) ctx1) (erased (Core) hc) (erased (Nat) x) (erased (Term) hty) (erased (Term) c)
       (erased (HeadRaw h) hr) (erased (ElabExpr ctx h (EOk ctx1 hc (Cons (Nat) x (Nil (Nat))))) p) (erased (TypeOf ctx1 x hty) t) (erased (CanonAt ctx1 hty c) cn) (erased (NoTeleNoFn c) nt)
       -> (ElabExpr ctx (RList (Cons (Raw) h items)) (EErr (RNotApplicable))))
    ; match (sections 7, 21, 26): the scrutinee's type must be a declared type constructor's application
    (many EXMatch : (erased (Ctx) ctx) (erased (Raw) sr) (erased (List (Raw)) ann) (erased (List (Raw)) brs) (erased (Ctx) ctx1) (erased (Core) sc) (erased (Nat) s) (erased (Term) sty) (erased (Nat) tc)
       (erased (List (Entry)) tps) (erased (List (Term)) targs) (erased (List (Adt)) adts) (erased (List (Nat)) ctors) (erased (Ctx) ctxA) (erased (List (Entry)) rt) (erased (List (Nat)) rids) (erased (List (Maybe (String))) rn)
       (erased (Ctx) ctx2) (erased (Ctx) ctx3) (erased (List (Branch)) cbs) (erased (List (Nat)) seen) (erased (List (Maybe (String))) names) (erased (Ctx) out) (erased (List (Nat)) ids)
       (erased (ElabExpr ctx sr (EOk ctx1 sc (Cons (Nat) s (Nil (Nat))))) p) (erased (TypeOf ctx1 s sty) t) (erased (CanonAt ctx1 sty (TyApp (Ref tc) tps targs)) c) (erased (Adts ctx1 adts) ad) (erased (AdtOf adts tc ctors) ao)
       (erased (ElabTele ctx1 (Nil (Maybe (Nat))) ann (TeleOk ctxA rt rids rn)) et) (erased (Leave ctxA ctx1 ctx2) lv)
       (erased (ElabBranches ctx2 s tc ctors (Nil (Nat)) rt brs (BrOk ctx3 cbs seen)) eb) (erased (Covered ctx3 s ctors seen) cv)
       (erased (Nones rt names) nn) (erased (MintTele ctx3 (Nil (Maybe (Term))) rt names out ids) m)
       -> (ElabExpr ctx (RList (Cons (Raw) (RKey (KMatch)) (Cons (Raw) sr (Cons (Raw) (RList ann) brs)))) (EOk out (CMatch sc cbs) ids)))
    (many EXMatchScrutErr : (erased (Ctx) ctx) (erased (Raw) sr) (erased (List (Raw)) ann) (erased (List (Raw)) brs) (erased (Reason) r) (erased (ElabExpr ctx sr (EErr r)) p)
       -> (ElabExpr ctx (RList (Cons (Raw) (RKey (KMatch)) (Cons (Raw) sr (Cons (Raw) (RList ann) brs)))) (EErr r)))
    (many EXMatchScrutSize : (erased (Ctx) ctx) (erased (Raw) sr) (erased (List (Raw)) ann) (erased (List (Raw)) brs) (erased (Ctx) ctx1) (erased (Core) sc) (erased (List (Nat)) ids)
       (erased (ElabExpr ctx sr (EOk ctx1 sc ids)) p) (erased (NotOne ids) n) -> (ElabExpr ctx (RList (Cons (Raw) (RKey (KMatch)) (Cons (Raw) sr (Cons (Raw) (RList ann) brs)))) (EErr (RSize))))
    (many EXNotMatchable : (erased (Ctx) ctx) (erased (Raw) sr) (erased (List (Raw)) ann) (erased (List (Raw)) brs) (erased (Ctx) ctx1) (erased (Core) sc) (erased (Nat) s) (erased (Term) sty) (erased (Term) c)
       (erased (ElabExpr ctx sr (EOk ctx1 sc (Cons (Nat) s (Nil (Nat))))) p) (erased (TypeOf ctx1 s sty) t) (erased (CanonAt ctx1 sty c) cn) (erased (Unmatchable ctx1 c) u)
       -> (ElabExpr ctx (RList (Cons (Raw) (RKey (KMatch)) (Cons (Raw) sr (Cons (Raw) (RList ann) brs)))) (EErr (RNotMatchable))))
    (many EXMatchAnnErr : (erased (Ctx) ctx) (erased (Raw) sr) (erased (List (Raw)) ann) (erased (List (Raw)) brs) (erased (Ctx) ctx1) (erased (Core) sc) (erased (Nat) s) (erased (Reason) r)
       (erased (ElabExpr ctx sr (EOk ctx1 sc (Cons (Nat) s (Nil (Nat))))) p) (erased (ElabTele ctx1 (Nil (Maybe (Nat))) ann (TeleErr r)) et)
       -> (ElabExpr ctx (RList (Cons (Raw) (RKey (KMatch)) (Cons (Raw) sr (Cons (Raw) (RList ann) brs)))) (EErr r)))
    (many EXMatchBranchesErr : (erased (Ctx) ctx) (erased (Raw) sr) (erased (List (Raw)) ann) (erased (List (Raw)) brs) (erased (Ctx) ctx1) (erased (Core) sc) (erased (Nat) s) (erased (Term) sty) (erased (Nat) tc)
       (erased (List (Entry)) tps) (erased (List (Term)) targs) (erased (List (Adt)) adts) (erased (List (Nat)) ctors) (erased (Ctx) ctxA) (erased (List (Entry)) rt) (erased (List (Nat)) rids) (erased (List (Maybe (String))) rn)
       (erased (Ctx) ctx2) (erased (Reason) r)
       (erased (ElabExpr ctx sr (EOk ctx1 sc (Cons (Nat) s (Nil (Nat))))) p) (erased (TypeOf ctx1 s sty) t) (erased (CanonAt ctx1 sty (TyApp (Ref tc) tps targs)) c) (erased (Adts ctx1 adts) ad) (erased (AdtOf adts tc ctors) ao)
       (erased (ElabTele ctx1 (Nil (Maybe (Nat))) ann (TeleOk ctxA rt rids rn)) et) (erased (Leave ctxA ctx1 ctx2) lv)
       (erased (ElabBranches ctx2 s tc ctors (Nil (Nat)) rt brs (BrErr r)) eb)
       -> (ElabExpr ctx (RList (Cons (Raw) (RKey (KMatch)) (Cons (Raw) sr (Cons (Raw) (RList ann) brs)))) (EErr r)))
    (many EXMatchUncovered : (erased (Ctx) ctx) (erased (Raw) sr) (erased (List (Raw)) ann) (erased (List (Raw)) brs) (erased (Ctx) ctx1) (erased (Core) sc) (erased (Nat) s) (erased (Term) sty) (erased (Nat) tc)
       (erased (List (Entry)) tps) (erased (List (Term)) targs) (erased (List (Adt)) adts) (erased (List (Nat)) ctors) (erased (Ctx) ctxA) (erased (List (Entry)) rt) (erased (List (Nat)) rids) (erased (List (Maybe (String))) rn)
       (erased (Ctx) ctx2) (erased (Ctx) ctx3) (erased (List (Branch)) cbs) (erased (List (Nat)) seen)
       (erased (ElabExpr ctx sr (EOk ctx1 sc (Cons (Nat) s (Nil (Nat))))) p) (erased (TypeOf ctx1 s sty) t) (erased (CanonAt ctx1 sty (TyApp (Ref tc) tps targs)) c) (erased (Adts ctx1 adts) ad) (erased (AdtOf adts tc ctors) ao)
       (erased (ElabTele ctx1 (Nil (Maybe (Nat))) ann (TeleOk ctxA rt rids rn)) et) (erased (Leave ctxA ctx1 ctx2) lv)
       (erased (ElabBranches ctx2 s tc ctors (Nil (Nat)) rt brs (BrOk ctx3 cbs seen)) eb) (erased (Uncovered ctx3 s ctors seen) uc)
       -> (ElabExpr ctx (RList (Cons (Raw) (RKey (KMatch)) (Cons (Raw) sr (Cons (Raw) (RList ann) brs)))) (EErr (RMissingBranch))))
    ; (prove-subterm a b): both terms of the grammar, the first a strict subterm of the second, canonically
    (many EXProveSubterm : (erased (Ctx) ctx) (erased (Raw) ar) (erased (Raw) br) (erased (Term) a) (erased (Term) aty) (erased (Term) b) (erased (Term) bty) (erased (Term) ca) (erased (Term) cb) (erased (Nat) e) (erased (Ctx) out)
       (erased (ElabTerm ctx ar (TOk a aty)) p) (erased (ElabTerm ctx br (TOk b bty)) q) (erased (CanonAt ctx a ca) c1) (erased (CanonAt ctx b cb) c2) (erased (StrictSub ctx ca cb) ss)
       (erased (Mint ctx (None (String)) (TyApp (Ref (Succ (Succ (Zero)))) subterm-ps (Cons (Term) aty (Cons (Term) a (Cons (Term) bty (Cons (Term) b (Nil (Term))))))) (KPlain) (None (Term)) e out) m)
       -> (ElabExpr ctx (RList (Cons (Raw) (RKey (KProveSubterm)) (Cons (Raw) ar (Cons (Raw) br (Nil (Raw)))))) (EOk out (CToken) (Cons (Nat) e (Nil (Nat))))))
    (many EXProveSubtermErrA : (erased (Ctx) ctx) (erased (Raw) ar) (erased (Raw) br) (erased (Reason) r) (erased (ElabTerm ctx ar (TErr r)) p)
       -> (ElabExpr ctx (RList (Cons (Raw) (RKey (KProveSubterm)) (Cons (Raw) ar (Cons (Raw) br (Nil (Raw)))))) (EErr r)))
    (many EXProveSubtermErrB : (erased (Ctx) ctx) (erased (Raw) ar) (erased (Raw) br) (erased (Term) a) (erased (Term) aty) (erased (Reason) r) (erased (ElabTerm ctx ar (TOk a aty)) p) (erased (ElabTerm ctx br (TErr r)) q)
       -> (ElabExpr ctx (RList (Cons (Raw) (RKey (KProveSubterm)) (Cons (Raw) ar (Cons (Raw) br (Nil (Raw)))))) (EErr r)))
    (many EXProveSubtermNot : (erased (Ctx) ctx) (erased (Raw) ar) (erased (Raw) br) (erased (Term) a) (erased (Term) aty) (erased (Term) b) (erased (Term) bty) (erased (Term) ca) (erased (Term) cb)
       (erased (ElabTerm ctx ar (TOk a aty)) p) (erased (ElabTerm ctx br (TOk b bty)) q) (erased (CanonAt ctx a ca) c1) (erased (CanonAt ctx b cb) c2) (erased (NotSub ctx ca cb) ns)
       -> (ElabExpr ctx (RList (Cons (Raw) (RKey (KProveSubterm)) (Cons (Raw) ar (Cons (Raw) br (Nil (Raw)))))) (EErr (RBadProof))))
    ; (prove-predates x L): x in scope before the def-lvl that minted L (section 18)
    (many EXProvePredates : (erased (Ctx) ctx) (erased (String) xs) (erased (String) ls) (erased (List (Name)) scope) (erased (Nat) x) (erased (Nat) l) (erased (Term) tx) (erased (Nat) e) (erased (Ctx) out)
       (erased (Scope ctx scope) sc) (erased (NameOf scope xs x) nx) (erased (NameOf scope ls l) nl) (erased (TypeOf ctx x tx) t) (erased (KindOf ctx l (KLevel)) k) (erased (Lt x l) lt)
       (erased (Mint ctx (None (String)) (TyApp (Ref (Succ (Zero))) predates-ps (Cons (Term) tx (Cons (Term) (Ref x) (Cons (Term) (Ref l) (Nil (Term)))))) (KPlain) (None (Term)) e out) m)
       -> (ElabExpr ctx (RList (Cons (Raw) (RKey (KProvePredates)) (Cons (Raw) (RAtom xs) (Cons (Raw) (RAtom ls) (Nil (Raw)))))) (EOk out (CToken) (Cons (Nat) e (Nil (Nat))))))
    (many EXProvePredatesUnboundX : (erased (Ctx) ctx) (erased (String) xs) (erased (String) ls) (erased (List (Name)) scope) (erased (Scope ctx scope) sc) (erased (NoName scope xs) n)
       -> (ElabExpr ctx (RList (Cons (Raw) (RKey (KProvePredates)) (Cons (Raw) (RAtom xs) (Cons (Raw) (RAtom ls) (Nil (Raw)))))) (EErr (RUnbound))))
    (many EXProvePredatesUnboundL : (erased (Ctx) ctx) (erased (String) xs) (erased (String) ls) (erased (List (Name)) scope) (erased (Nat) x) (erased (Scope ctx scope) sc) (erased (NameOf scope xs x) nx) (erased (NoName scope ls) n)
       -> (ElabExpr ctx (RList (Cons (Raw) (RKey (KProvePredates)) (Cons (Raw) (RAtom xs) (Cons (Raw) (RAtom ls) (Nil (Raw)))))) (EErr (RUnbound))))
    (many EXProvePredatesNotLevel : (erased (Ctx) ctx) (erased (String) xs) (erased (String) ls) (erased (List (Name)) scope) (erased (Nat) x) (erased (Nat) l) (erased (Kind) k)
       (erased (Scope ctx scope) sc) (erased (NameOf scope xs x) nx) (erased (NameOf scope ls l) nl) (erased (KindOf ctx l k) kd) (erased (NotLevelKind k) nk)
       -> (ElabExpr ctx (RList (Cons (Raw) (RKey (KProvePredates)) (Cons (Raw) (RAtom xs) (Cons (Raw) (RAtom ls) (Nil (Raw)))))) (EErr (RNotLevel))))
    (many EXProvePredatesAfter : (erased (Ctx) ctx) (erased (String) xs) (erased (String) ls) (erased (List (Name)) scope) (erased (Nat) x) (erased (Nat) l)
       (erased (Scope ctx scope) sc) (erased (NameOf scope xs x) nx) (erased (NameOf scope ls l) nl) (erased (KindOf ctx l (KLevel)) k) (erased (Lt l (Succ x)) le)
       -> (ElabExpr ctx (RList (Cons (Raw) (RKey (KProvePredates)) (Cons (Raw) (RAtom xs) (Cons (Raw) (RAtom ls) (Nil (Raw)))))) (EErr (RBadProof))))
    ; the three axioms (section 18): each takes two proofs, of size one, whose canonical types have the
    ; shapes below with the shared parts the same, and mints the conclusion; a proof of the wrong shape, or
    ; shared parts that differ, is RBadProof
    (many EXPredatesTrans : (erased (Ctx) ctx) (erased (Raw) pr) (erased (Raw) qr) (erased (Ctx) ctx1) (erased (Core) pc) (erased (Nat) p) (erased (Term) pty) (erased (Term) cp) (erased (Term) ty) (erased (Term) a) (erased (Term) l1)
       (erased (Ctx) ctx2) (erased (Core) qc) (erased (Nat) q) (erased (Term) qty) (erased (Term) cq) (erased (Term) ty2) (erased (Term) l1b) (erased (Term) l2) (erased (Nat) e) (erased (Ctx) out)
       (erased (ElabExpr ctx pr (EOk ctx1 pc (Cons (Nat) p (Nil (Nat))))) ep) (erased (TypeOf ctx1 p pty) tp) (erased (CanonAt ctx1 pty cp) c1) (erased (PredatesShape ctx1 cp ty a l1) s1)
       (erased (ElabExpr ctx1 qr (EOk ctx2 qc (Cons (Nat) q (Nil (Nat))))) eq) (erased (TypeOf ctx2 q qty) tq) (erased (CanonAt ctx2 qty cq) c2) (erased (PredatesShape ctx2 cq ty2 l1b l2) s2)
       (erased (Same ctx2 ty2 level-ty) st) (erased (Same ctx2 l1b l1) sl)
       (erased (Mint ctx2 (None (String)) (TyApp (Ref (Succ (Zero))) predates-ps (Cons (Term) ty (Cons (Term) a (Cons (Term) l2 (Nil (Term)))))) (KPlain) (None (Term)) e out) m)
       -> (ElabExpr ctx (RList (Cons (Raw) (RKey (KPredatesTrans)) (Cons (Raw) pr (Cons (Raw) qr (Nil (Raw)))))) (EOk out (CToken) (Cons (Nat) e (Nil (Nat))))))
    (many EXSubtermTrans : (erased (Ctx) ctx) (erased (Raw) pr) (erased (Raw) qr) (erased (Ctx) ctx1) (erased (Core) pc) (erased (Nat) p) (erased (Term) pty) (erased (Term) cp) (erased (Term) ta) (erased (Term) a) (erased (Term) tb) (erased (Term) b)
       (erased (Ctx) ctx2) (erased (Core) qc) (erased (Nat) q) (erased (Term) qty) (erased (Term) cq) (erased (Term) tb2) (erased (Term) b2) (erased (Term) tc) (erased (Term) c) (erased (Nat) e) (erased (Ctx) out)
       (erased (ElabExpr ctx pr (EOk ctx1 pc (Cons (Nat) p (Nil (Nat))))) ep) (erased (TypeOf ctx1 p pty) tp) (erased (CanonAt ctx1 pty cp) c1) (erased (SubtermShape ctx1 cp ta a tb b) s1)
       (erased (ElabExpr ctx1 qr (EOk ctx2 qc (Cons (Nat) q (Nil (Nat))))) eq) (erased (TypeOf ctx2 q qty) tq) (erased (CanonAt ctx2 qty cq) c2) (erased (SubtermShape ctx2 cq tb2 b2 tc c) s2)
       (erased (Same ctx2 tb2 tb) st) (erased (Same ctx2 b2 b) sb)
       (erased (Mint ctx2 (None (String)) (TyApp (Ref (Succ (Succ (Zero)))) subterm-ps (Cons (Term) ta (Cons (Term) a (Cons (Term) tc (Cons (Term) c (Nil (Term))))))) (KPlain) (None (Term)) e out) m)
       -> (ElabExpr ctx (RList (Cons (Raw) (RKey (KSubtermTrans)) (Cons (Raw) pr (Cons (Raw) qr (Nil (Raw)))))) (EOk out (CToken) (Cons (Nat) e (Nil (Nat))))))
    (many EXPredatesSubterm : (erased (Ctx) ctx) (erased (Raw) pr) (erased (Raw) qr) (erased (Ctx) ctx1) (erased (Core) pc) (erased (Nat) p) (erased (Term) pty) (erased (Term) cp) (erased (Term) ty) (erased (Term) a) (erased (Term) l)
       (erased (Ctx) ctx2) (erased (Core) qc) (erased (Nat) q) (erased (Term) qty) (erased (Term) cq) (erased (Term) tb) (erased (Term) b) (erased (Term) ty2) (erased (Term) a2) (erased (Nat) e) (erased (Ctx) out)
       (erased (ElabExpr ctx pr (EOk ctx1 pc (Cons (Nat) p (Nil (Nat))))) ep) (erased (TypeOf ctx1 p pty) tp) (erased (CanonAt ctx1 pty cp) c1) (erased (PredatesShape ctx1 cp ty a l) s1)
       (erased (ElabExpr ctx1 qr (EOk ctx2 qc (Cons (Nat) q (Nil (Nat))))) eq) (erased (TypeOf ctx2 q qty) tq) (erased (CanonAt ctx2 qty cq) c2) (erased (SubtermShape ctx2 cq tb b ty2 a2) s2)
       (erased (Same ctx2 ty2 ty) st) (erased (Same ctx2 a2 a) sa)
       (erased (Mint ctx2 (None (String)) (TyApp (Ref (Succ (Zero))) predates-ps (Cons (Term) tb (Cons (Term) b (Cons (Term) l (Nil (Term)))))) (KPlain) (None (Term)) e out) m)
       -> (ElabExpr ctx (RList (Cons (Raw) (RKey (KPredatesSubterm)) (Cons (Raw) pr (Cons (Raw) qr (Nil (Raw)))))) (EOk out (CToken) (Cons (Nat) e (Nil (Nat))))))
    ; and the ways an axiom fails, the same for all three
    (many EXAxiomErrP : (erased (Ctx) ctx) (erased (Key) k) (erased (Raw) pr) (erased (Raw) qr) (erased (Reason) r) (erased (AxiomKey k) ak) (erased (ElabExpr ctx pr (EErr r)) ep)
       -> (ElabExpr ctx (RList (Cons (Raw) (RKey k) (Cons (Raw) pr (Cons (Raw) qr (Nil (Raw)))))) (EErr r)))
    (many EXAxiomSizeP : (erased (Ctx) ctx) (erased (Key) k) (erased (Raw) pr) (erased (Raw) qr) (erased (Ctx) ctx1) (erased (Core) pc) (erased (List (Nat)) pids) (erased (AxiomKey k) ak)
       (erased (ElabExpr ctx pr (EOk ctx1 pc pids)) ep) (erased (NotOne pids) n) -> (ElabExpr ctx (RList (Cons (Raw) (RKey k) (Cons (Raw) pr (Cons (Raw) qr (Nil (Raw)))))) (EErr (RSize))))
    (many EXAxiomErrQ : (erased (Ctx) ctx) (erased (Key) k) (erased (Raw) pr) (erased (Raw) qr) (erased (Ctx) ctx1) (erased (Core) pc) (erased (Nat) p) (erased (Reason) r) (erased (AxiomKey k) ak)
       (erased (ElabExpr ctx pr (EOk ctx1 pc (Cons (Nat) p (Nil (Nat))))) ep) (erased (ElabExpr ctx1 qr (EErr r)) eq) -> (ElabExpr ctx (RList (Cons (Raw) (RKey k) (Cons (Raw) pr (Cons (Raw) qr (Nil (Raw)))))) (EErr r)))
    (many EXAxiomSizeQ : (erased (Ctx) ctx) (erased (Key) k) (erased (Raw) pr) (erased (Raw) qr) (erased (Ctx) ctx1) (erased (Core) pc) (erased (Nat) p) (erased (Ctx) ctx2) (erased (Core) qc) (erased (List (Nat)) qids) (erased (AxiomKey k) ak)
       (erased (ElabExpr ctx pr (EOk ctx1 pc (Cons (Nat) p (Nil (Nat))))) ep) (erased (ElabExpr ctx1 qr (EOk ctx2 qc qids)) eq) (erased (NotOne qids) n)
       -> (ElabExpr ctx (RList (Cons (Raw) (RKey k) (Cons (Raw) pr (Cons (Raw) qr (Nil (Raw)))))) (EErr (RSize))))
    ; a proof of the wrong shape, or shared parts that differ: the axiom's premises are named by [AxiomBad]
    (many EXAxiomBad : (erased (Ctx) ctx) (erased (Key) k) (erased (Raw) pr) (erased (Raw) qr) (erased (Ctx) ctx1) (erased (Core) pc) (erased (Nat) p) (erased (Term) pty) (erased (Term) cp)
       (erased (Ctx) ctx2) (erased (Core) qc) (erased (Nat) q) (erased (Term) qty) (erased (Term) cq)
       (erased (ElabExpr ctx pr (EOk ctx1 pc (Cons (Nat) p (Nil (Nat))))) ep) (erased (TypeOf ctx1 p pty) tp) (erased (CanonAt ctx1 pty cp) c1)
       (erased (ElabExpr ctx1 qr (EOk ctx2 qc (Cons (Nat) q (Nil (Nat))))) eq) (erased (TypeOf ctx2 q qty) tq) (erased (CanonAt ctx2 qty cq) c2) (erased (AxiomBad k ctx1 cp ctx2 cq) bad)
       -> (ElabExpr ctx (RList (Cons (Raw) (RKey k) (Cons (Raw) pr (Cons (Raw) qr (Nil (Raw)))))) (EErr (RBadProof)))))
  ((AxiomKey : ((Key) k) -> Type)
    enum
    (many AKPredatesTrans : -> (AxiomKey (KPredatesTrans)))
    (many AKSubtermTrans : -> (AxiomKey (KSubtermTrans)))
    (many AKPredatesSubterm : -> (AxiomKey (KPredatesSubterm))))
  ; Why an axiom's two canonical proof types do not fit it.
  ((AxiomBad : ((Key) k) ((Ctx) ctx1) ((Term) cp) ((Ctx) ctx2) ((Term) cq) -> Type)
    enum
    (many ABPredatesTransP : (erased (Ctx) ctx1) (erased (Term) cp) (erased (Ctx) ctx2) (erased (Term) cq) (erased (NotPredatesShape ctx1 cp) n) -> (AxiomBad (KPredatesTrans) ctx1 cp ctx2 cq))
    (many ABPredatesTransQ : (erased (Ctx) ctx1) (erased (Term) cp) (erased (Ctx) ctx2) (erased (Term) cq) (erased (NotPredatesShape ctx2 cq) n) -> (AxiomBad (KPredatesTrans) ctx1 cp ctx2 cq))
    (many ABPredatesTransType : (erased (Ctx) ctx1) (erased (Term) cp) (erased (Ctx) ctx2) (erased (Term) cq) (erased (Term) ty2) (erased (Term) l1b) (erased (Term) l2)
       (erased (PredatesShape ctx2 cq ty2 l1b l2) s2) (erased (Differ ctx2 ty2 level-ty) d) -> (AxiomBad (KPredatesTrans) ctx1 cp ctx2 cq))
    (many ABPredatesTransLink : (erased (Ctx) ctx1) (erased (Term) cp) (erased (Ctx) ctx2) (erased (Term) cq) (erased (Term) ty) (erased (Term) a) (erased (Term) l1) (erased (Term) ty2) (erased (Term) l1b) (erased (Term) l2)
       (erased (PredatesShape ctx1 cp ty a l1) s1) (erased (PredatesShape ctx2 cq ty2 l1b l2) s2) (erased (Differ ctx2 l1b l1) d) -> (AxiomBad (KPredatesTrans) ctx1 cp ctx2 cq))
    (many ABSubtermTransP : (erased (Ctx) ctx1) (erased (Term) cp) (erased (Ctx) ctx2) (erased (Term) cq) (erased (NotSubtermShape ctx1 cp) n) -> (AxiomBad (KSubtermTrans) ctx1 cp ctx2 cq))
    (many ABSubtermTransQ : (erased (Ctx) ctx1) (erased (Term) cp) (erased (Ctx) ctx2) (erased (Term) cq) (erased (NotSubtermShape ctx2 cq) n) -> (AxiomBad (KSubtermTrans) ctx1 cp ctx2 cq))
    (many ABSubtermTransType : (erased (Ctx) ctx1) (erased (Term) cp) (erased (Ctx) ctx2) (erased (Term) cq) (erased (Term) ta) (erased (Term) a) (erased (Term) tb) (erased (Term) b) (erased (Term) tb2) (erased (Term) b2) (erased (Term) tc) (erased (Term) c)
       (erased (SubtermShape ctx1 cp ta a tb b) s1) (erased (SubtermShape ctx2 cq tb2 b2 tc c) s2) (erased (Differ ctx2 tb2 tb) d) -> (AxiomBad (KSubtermTrans) ctx1 cp ctx2 cq))
    (many ABSubtermTransLink : (erased (Ctx) ctx1) (erased (Term) cp) (erased (Ctx) ctx2) (erased (Term) cq) (erased (Term) ta) (erased (Term) a) (erased (Term) tb) (erased (Term) b) (erased (Term) tb2) (erased (Term) b2) (erased (Term) tc) (erased (Term) c)
       (erased (SubtermShape ctx1 cp ta a tb b) s1) (erased (SubtermShape ctx2 cq tb2 b2 tc c) s2) (erased (Differ ctx2 b2 b) d) -> (AxiomBad (KSubtermTrans) ctx1 cp ctx2 cq))
    (many ABPredatesSubtermP : (erased (Ctx) ctx1) (erased (Term) cp) (erased (Ctx) ctx2) (erased (Term) cq) (erased (NotPredatesShape ctx1 cp) n) -> (AxiomBad (KPredatesSubterm) ctx1 cp ctx2 cq))
    (many ABPredatesSubtermQ : (erased (Ctx) ctx1) (erased (Term) cp) (erased (Ctx) ctx2) (erased (Term) cq) (erased (NotSubtermShape ctx2 cq) n) -> (AxiomBad (KPredatesSubterm) ctx1 cp ctx2 cq))
    (many ABPredatesSubtermType : (erased (Ctx) ctx1) (erased (Term) cp) (erased (Ctx) ctx2) (erased (Term) cq) (erased (Term) ty) (erased (Term) a) (erased (Term) l) (erased (Term) tb) (erased (Term) b) (erased (Term) ty2) (erased (Term) a2)
       (erased (PredatesShape ctx1 cp ty a l) s1) (erased (SubtermShape ctx2 cq tb b ty2 a2) s2) (erased (Differ ctx2 ty2 ty) d) -> (AxiomBad (KPredatesSubterm) ctx1 cp ctx2 cq))
    (many ABPredatesSubtermLink : (erased (Ctx) ctx1) (erased (Term) cp) (erased (Ctx) ctx2) (erased (Term) cq) (erased (Term) ty) (erased (Term) a) (erased (Term) l) (erased (Term) tb) (erased (Term) b) (erased (Term) ty2) (erased (Term) a2)
       (erased (PredatesShape ctx1 cp ty a l) s1) (erased (SubtermShape ctx2 cq tb b ty2 a2) s2) (erased (Differ ctx2 a2 a) d) -> (AxiomBad (KPredatesSubterm) ctx1 cp ctx2 cq)))
  ((FormerKey : ((Key) k) -> Type)
    enum
    (many FKFn : -> (FormerKey (KFn)))
    (many FKTyCtor : -> (FormerKey (KTyCtor)))
    (many FKValCtor : -> (FormerKey (KValCtor))))
  ; A head of an application is a name or a list, never a keyword.
  ((HeadRaw : ((Raw) h) -> Type)
    enum
    (many HeadAtom : (erased (String) s) -> (HeadRaw (RAtom s)))
    (many HeadList : (erased (List (Raw)) items) -> (HeadRaw (RList items))))
  ((NoTeleNoFn : ((Term) c) -> Type)
    enum
    (many NTNRef : (erased (Nat) x) -> (NoTeleNoFn (Ref x)))
    (many NTNBound : (erased (Nat) k) -> (NoTeleNoFn (Bound k)))
    (many NTNTyApp : (erased (Term) h) (erased (List (Entry)) ps) (erased (List (Term)) as) -> (NoTeleNoFn (TyApp h ps as)))
    (many NTNValApp : (erased (Term) h) (erased (List (Entry)) ps) (erased (Term) r) (erased (List (Term)) as) -> (NoTeleNoFn (ValApp h ps r as)))
    (many NTNUniv : -> (NoTeleNoFn (TUniv))))
  ; A canonical type no match can read: not an application, or one headed by no declared type constructor.
  ((Unmatchable : ((Ctx) ctx) ((Term) c) -> Type)
    enum
    (many UmNotApp : (erased (Ctx) ctx) (erased (Term) c) (erased (NotTyApp c) n) -> (Unmatchable ctx c))
    (many UmHeadVar : (erased (Ctx) ctx) (erased (Term) h) (erased (List (Entry)) hps) (erased (List (Term)) as) (erased (NonRef h) n) -> (Unmatchable ctx (TyApp h hps as)))
    (many UmNoAdt : (erased (Ctx) ctx) (erased (Nat) x) (erased (List (Entry)) hps) (erased (List (Term)) as) (erased (List (Adt)) adts) (erased (Adts ctx adts) ad) (erased (NoAdt adts x) n) -> (Unmatchable ctx (TyApp (Ref x) hps as))))
  ; Items each of size one, the context threaded through.
  ((ElabItems : ((Ctx) ctx) ((List (Raw)) raws) ((AOut) out) -> Type)
    enum
    (many EINil : (erased (Ctx) ctx) -> (ElabItems ctx (Nil (Raw)) (AllOk ctx (Nil (Core)) (Nil (Nat)))))
    (many EICons : (erased (Ctx) ctx) (erased (Raw) r) (erased (List (Raw)) rest) (erased (Ctx) ctx1) (erased (Core) core) (erased (Nat) x) (erased (Ctx) out) (erased (List (Core)) cores) (erased (List (Nat)) ids)
       (erased (ElabExpr ctx r (EOk ctx1 core (Cons (Nat) x (Nil (Nat))))) p) (erased (ElabItems ctx1 rest (AllOk out cores ids)) q)
       -> (ElabItems ctx (Cons (Raw) r rest) (AllOk out (Cons (Core) core cores) (Cons (Nat) x ids))))
    (many EIErr : (erased (Ctx) ctx) (erased (Raw) r) (erased (List (Raw)) rest) (erased (Reason) e) (erased (ElabExpr ctx r (EErr e)) p) -> (ElabItems ctx (Cons (Raw) r rest) (AErr e)))
    (many EISize : (erased (Ctx) ctx) (erased (Raw) r) (erased (List (Raw)) rest) (erased (Ctx) ctx1) (erased (Core) core) (erased (List (Nat)) ids) (erased (ElabExpr ctx r (EOk ctx1 core ids)) p) (erased (NotOne ids) n)
       -> (ElabItems ctx (Cons (Raw) r rest) (AErr (RSize))))
    (many EIRestErr : (erased (Ctx) ctx) (erased (Raw) r) (erased (List (Raw)) rest) (erased (Ctx) ctx1) (erased (Core) core) (erased (Nat) x) (erased (Reason) e)
       (erased (ElabExpr ctx r (EOk ctx1 core (Cons (Nat) x (Nil (Nat))))) p) (erased (ElabItems ctx1 rest (AErr e)) q) -> (ElabItems ctx (Cons (Raw) r rest) (AErr e))))
  ; Arguments, expressions of size one, against a telescope, as mini/elab.sl's ElabTermArgs but threading
  ; the context (section 14's rule with every position non-erased).
  ((ElabExprArgs : ((Ctx) ctx) ((List (Maybe (Term))) acc) ((List (Entry)) tele) ((List (Raw)) args) ((AOut) out) -> Type)
    enum
    (many EANil : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) -> (ElabExprArgs ctx acc (Nil (Entry)) (Nil (Raw)) (AllOk ctx (Nil (Core)) (Nil (Nat)))))
    (many EAArity : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (List (Entry)) tele) (erased (List (Raw)) args) (erased (LenMismatch (Entry) (Raw) tele args) m)
       -> (ElabExprArgs ctx acc tele args (AErr (RArity))))
    (many EATy : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (Bool) s) (erased (Term) t) (erased (List (Entry)) es) (erased (Raw) a) (erased (List (Raw)) args)
       (erased (Ctx) ctx1) (erased (Core) core) (erased (Nat) x) (erased (Term) xty) (erased (Term) t2) (erased (Ctx) out) (erased (List (Core)) cores) (erased (List (Nat)) ids)
       (erased (ElabExpr ctx a (EOk ctx1 core (Cons (Nat) x (Nil (Nat))))) p) (erased (TypeOf ctx1 x xty) ty) (erased (Subst acc t t2) sb) (erased (Same ctx1 xty t2) sm)
       (erased (ElabExprArgs ctx1 (Cons (Maybe (Term)) (Some (Term) (Ref x)) acc) es args (AllOk out cores ids)) q)
       -> (ElabExprArgs ctx acc (Cons (Entry) (MkEntry s (BFalse) t) es) (Cons (Raw) a args) (AllOk out (Cons (Core) core cores) (Cons (Nat) x ids))))
    (many EAIs : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (Bool) s) (erased (Term) t) (erased (List (Entry)) es) (erased (Raw) a) (erased (List (Raw)) args)
       (erased (Ctx) ctx1) (erased (Core) core) (erased (Nat) x) (erased (Term) t2) (erased (Ctx) out) (erased (List (Core)) cores) (erased (List (Nat)) ids)
       (erased (ElabExpr ctx a (EOk ctx1 core (Cons (Nat) x (Nil (Nat))))) p) (erased (Subst acc t t2) sb) (erased (Same ctx1 (Ref x) t2) sm)
       (erased (ElabExprArgs ctx1 (Cons (Maybe (Term)) (Some (Term) (Ref x)) acc) es args (AllOk out cores ids)) q)
       -> (ElabExprArgs ctx acc (Cons (Entry) (MkEntry s (BTrue) t) es) (Cons (Raw) a args) (AllOk out (Cons (Core) core cores) (Cons (Nat) x ids))))
    (many EAErr : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (Entry) e) (erased (List (Entry)) es) (erased (Raw) a) (erased (List (Raw)) args) (erased (Reason) r)
       (erased (ElabExpr ctx a (EErr r)) p) -> (ElabExprArgs ctx acc (Cons (Entry) e es) (Cons (Raw) a args) (AErr r)))
    (many EASize : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (Entry) e) (erased (List (Entry)) es) (erased (Raw) a) (erased (List (Raw)) args) (erased (Ctx) ctx1) (erased (Core) core) (erased (List (Nat)) ids)
       (erased (ElabExpr ctx a (EOk ctx1 core ids)) p) (erased (NotOne ids) n) -> (ElabExprArgs ctx acc (Cons (Entry) e es) (Cons (Raw) a args) (AErr (RSize))))
    (many EATyMismatch : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (Bool) s) (erased (Term) t) (erased (List (Entry)) es) (erased (Raw) a) (erased (List (Raw)) args)
       (erased (Ctx) ctx1) (erased (Core) core) (erased (Nat) x) (erased (Term) xty) (erased (Term) t2)
       (erased (ElabExpr ctx a (EOk ctx1 core (Cons (Nat) x (Nil (Nat))))) p) (erased (TypeOf ctx1 x xty) ty) (erased (Subst acc t t2) sb) (erased (Differ ctx1 xty t2) d)
       -> (ElabExprArgs ctx acc (Cons (Entry) (MkEntry s (BFalse) t) es) (Cons (Raw) a args) (AErr (RMismatch))))
    (many EAIsMismatch : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (Bool) s) (erased (Term) t) (erased (List (Entry)) es) (erased (Raw) a) (erased (List (Raw)) args)
       (erased (Ctx) ctx1) (erased (Core) core) (erased (Nat) x) (erased (Term) t2)
       (erased (ElabExpr ctx a (EOk ctx1 core (Cons (Nat) x (Nil (Nat))))) p) (erased (Subst acc t t2) sb) (erased (Differ ctx1 (Ref x) t2) d)
       -> (ElabExprArgs ctx acc (Cons (Entry) (MkEntry s (BTrue) t) es) (Cons (Raw) a args) (AErr (RMismatch))))
    (many EARestErr : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (Bool) s) (erased (Bool) i) (erased (Term) t) (erased (List (Entry)) es) (erased (Raw) a) (erased (List (Raw)) args)
       (erased (Ctx) ctx1) (erased (Core) core) (erased (Nat) x) (erased (Reason) r)
       (erased (ElabExpr ctx a (EOk ctx1 core (Cons (Nat) x (Nil (Nat))))) p) (erased (ElabExprArgs ctx1 (Cons (Maybe (Term)) (Some (Term) (Ref x)) acc) es args (AErr r)) q)
       -> (ElabExprArgs ctx acc (Cons (Entry) (MkEntry s i t) es) (Cons (Raw) a args) (AErr r))))
  ; The call-site proof (section 19): none at the top level (section 20); a Predates proof from the callee's
  ; level to the current one; or a Subterm proof for the j-th subterm-marked argument, every earlier marked
  ; argument the same as the enclosing function's, and the levels the same.
  ((Decrease : ((Ctx) ctx) ((Term) l) ((List (Entry)) ps) ((List (Nat)) ids) ((Ann) ann) ((DOut) out) -> Type)
    enum
    (many DTop : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Nat)) ids) (erased (LevelOf ctx (None (Term))) lv) -> (Decrease ctx l ps ids (ANone) (DOk ctx)))
    (many DTopPredates : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Nat)) ids) (erased (Raw) p) (erased (LevelOf ctx (None (Term))) lv) -> (Decrease ctx l ps ids (APredates p) (DErr (RBadProof))))
    (many DTopSubterm : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Nat)) ids) (erased (Nat) i) (erased (Raw) p) (erased (LevelOf ctx (None (Term))) lv)
       -> (Decrease ctx l ps ids (ASubterm i p) (DErr (RBadProof))))
    (many DNone : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Nat)) ids) (erased (Term) cur) (erased (LevelOf ctx (Some (Term) cur)) lv) -> (Decrease ctx l ps ids (ANone) (DErr (RNoProof))))
    (many DPredates : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Nat)) ids) (erased (Raw) pr) (erased (Term) cur) (erased (Ctx) ctx1) (erased (Core) pc) (erased (Nat) p) (erased (Term) pty)
       (erased (Term) h) (erased (List (Entry)) hps) (erased (Term) ty) (erased (Term) a) (erased (Term) lv2)
       (erased (LevelOf ctx (Some (Term) cur)) lv) (erased (ElabExpr ctx pr (EOk ctx1 pc (Cons (Nat) p (Nil (Nat))))) ep) (erased (TypeOf ctx1 p pty) t)
       (erased (CanonAt ctx1 pty (TyApp h hps (Cons (Term) ty (Cons (Term) a (Cons (Term) lv2 (Nil (Term))))))) c)
       (erased (Same ctx1 h (Ref (Succ (Zero)))) sh) (erased (Same ctx1 ty level-ty) sty) (erased (Same ctx1 a l) sa) (erased (Same ctx1 lv2 cur) sc)
       -> (Decrease ctx l ps ids (APredates pr) (DOk ctx1)))
    (many DPredatesErr : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Nat)) ids) (erased (Raw) pr) (erased (Term) cur) (erased (Reason) r)
       (erased (LevelOf ctx (Some (Term) cur)) lv) (erased (ElabExpr ctx pr (EErr r)) ep) -> (Decrease ctx l ps ids (APredates pr) (DErr r)))
    (many DPredatesSize : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Nat)) ids) (erased (Raw) pr) (erased (Term) cur) (erased (Ctx) ctx1) (erased (Core) pc) (erased (List (Nat)) pids)
       (erased (LevelOf ctx (Some (Term) cur)) lv) (erased (ElabExpr ctx pr (EOk ctx1 pc pids)) ep) (erased (NotOne pids) n) -> (Decrease ctx l ps ids (APredates pr) (DErr (RSize))))
    (many DPredatesBad : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Nat)) ids) (erased (Raw) pr) (erased (Term) cur) (erased (Ctx) ctx1) (erased (Core) pc) (erased (Nat) p) (erased (Term) pty) (erased (Term) c)
       (erased (LevelOf ctx (Some (Term) cur)) lv) (erased (ElabExpr ctx pr (EOk ctx1 pc (Cons (Nat) p (Nil (Nat))))) ep) (erased (TypeOf ctx1 p pty) t) (erased (CanonAt ctx1 pty c) cn) (erased (NotPredates ctx1 c l cur) np)
       -> (Decrease ctx l ps ids (APredates pr) (DErr (RBadProof))))
    (many DSubterm : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Nat)) ids) (erased (Nat) i) (erased (Raw) pr) (erased (Term) cur) (erased (Nat) j) (erased (Nat) xi) (erased (List (Term)) cargs)
       (erased (List (Term)) subargs) (erased (Term) b) (erased (Ctx) ctx1) (erased (Core) pc) (erased (Nat) p) (erased (Term) pty) (erased (Term) h) (erased (List (Entry)) hps) (erased (Term) ta) (erased (Term) a0) (erased (Term) tb) (erased (Term) b0)
       (erased (LevelOf ctx (Some (Term) cur)) lv) (erased (Same ctx l cur) sl) (erased (MarkedIndex ps i j) mi) (erased (Nth (Nat) ids i xi) ni) (erased (Marked ps ids cargs) mk)
       (erased (SubArgs ctx subargs) sa) (erased (SamePrefix ctx j cargs subargs b) sp)
       (erased (ElabExpr ctx pr (EOk ctx1 pc (Cons (Nat) p (Nil (Nat))))) ep) (erased (TypeOf ctx1 p pty) t)
       (erased (CanonAt ctx1 pty (TyApp h hps (Cons (Term) ta (Cons (Term) a0 (Cons (Term) tb (Cons (Term) b0 (Nil (Term)))))))) c)
       (erased (Same ctx1 h (Ref (Succ (Succ (Zero))))) sh) (erased (Same ctx1 a0 (Ref xi)) sa0) (erased (Same ctx1 b0 b) sb0)
       -> (Decrease ctx l ps ids (ASubterm i pr) (DOk ctx1)))
    (many DSubtermLevel : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Nat)) ids) (erased (Nat) i) (erased (Raw) pr) (erased (Term) cur)
       (erased (LevelOf ctx (Some (Term) cur)) lv) (erased (Differ ctx l cur) d) -> (Decrease ctx l ps ids (ASubterm i pr) (DErr (RBadProof))))
    (many DSubtermErr : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Nat)) ids) (erased (Nat) i) (erased (Raw) pr) (erased (Term) cur) (erased (Reason) r)
       (erased (LevelOf ctx (Some (Term) cur)) lv) (erased (Same ctx l cur) sl) (erased (ElabExpr ctx pr (EErr r)) ep) -> (Decrease ctx l ps ids (ASubterm i pr) (DErr r)))
    (many DSubtermSize : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Nat)) ids) (erased (Nat) i) (erased (Raw) pr) (erased (Term) cur) (erased (Ctx) ctx1) (erased (Core) pc) (erased (List (Nat)) pids)
       (erased (LevelOf ctx (Some (Term) cur)) lv) (erased (Same ctx l cur) sl) (erased (ElabExpr ctx pr (EOk ctx1 pc pids)) ep) (erased (NotOne pids) n) -> (Decrease ctx l ps ids (ASubterm i pr) (DErr (RSize))))
    (many DSubtermBad : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Nat)) ids) (erased (Nat) i) (erased (Raw) pr) (erased (Term) cur) (erased (Nat) j) (erased (Nat) xi) (erased (List (Term)) cargs)
       (erased (List (Term)) subargs) (erased (Term) b) (erased (Ctx) ctx1) (erased (Core) pc) (erased (Nat) p) (erased (Term) pty) (erased (Term) c)
       (erased (LevelOf ctx (Some (Term) cur)) lv) (erased (Same ctx l cur) sl) (erased (MarkedIndex ps i j) mi) (erased (Nth (Nat) ids i xi) ni) (erased (Marked ps ids cargs) mk)
       (erased (SubArgs ctx subargs) sa) (erased (SamePrefix ctx j cargs subargs b) sp)
       (erased (ElabExpr ctx pr (EOk ctx1 pc (Cons (Nat) p (Nil (Nat))))) ep) (erased (TypeOf ctx1 p pty) t) (erased (CanonAt ctx1 pty c) cn) (erased (NotSubtermOf ctx1 c (Ref xi) b) ns)
       -> (Decrease ctx l ps ids (ASubterm i pr) (DErr (RBadProof))))
    (many DSubtermUnmarked : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Nat)) ids) (erased (Nat) i) (erased (Raw) pr) (erased (Term) cur)
       (erased (LevelOf ctx (Some (Term) cur)) lv) (erased (Same ctx l cur) sl) (erased (Unmarked ps i) um) -> (Decrease ctx l ps ids (ASubterm i pr) (DErr (RBadProof))))
    (many DSubtermPrefix : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Nat)) ids) (erased (Nat) i) (erased (Raw) pr) (erased (Term) cur) (erased (Nat) j) (erased (List (Term)) cargs) (erased (List (Term)) subargs)
       (erased (LevelOf ctx (Some (Term) cur)) lv) (erased (Same ctx l cur) sl) (erased (MarkedIndex ps i j) mi) (erased (Marked ps ids cargs) mk) (erased (SubArgs ctx subargs) sa) (erased (DifferPrefix ctx j cargs subargs) dp)
       -> (Decrease ctx l ps ids (ASubterm i pr) (DErr (RBadProof)))))
  ((Unmarked : ((List (Entry)) ps) ((Nat) i) -> Type)
    enum
    (many UmNil : (erased (Nat) i) -> (Unmarked (Nil (Entry)) i))
    (many UmHere : (erased (Bool) has-is) (erased (Term) t) (erased (List (Entry)) es) -> (Unmarked (Cons (Entry) (MkEntry (BFalse) has-is t) es) (Zero)))
    (many UmThere : (erased (Entry) e) (erased (List (Entry)) es) (erased (Nat) i) (erased (Unmarked es i) p) -> (Unmarked (Cons (Entry) e es) (Succ i))))
  ; The first j pairs are not all the same: one differs, or the lists run out.
  ((DifferPrefix : ((Ctx) ctx) ((Nat) j) ((List (Term)) as) ((List (Term)) bs) -> Type)
    enum
    (many DPNilA : (erased (Ctx) ctx) (erased (Nat) j) (erased (List (Term)) bs) -> (DifferPrefix ctx j (Nil (Term)) bs))
    (many DPNilB : (erased (Ctx) ctx) (erased (Nat) j) (erased (List (Term)) as) -> (DifferPrefix ctx j as (Nil (Term))))
    (many DPHere : (erased (Ctx) ctx) (erased (Nat) j) (erased (Term) a) (erased (List (Term)) as) (erased (Term) b) (erased (List (Term)) bs) (erased (Differ ctx a b) d)
       -> (DifferPrefix ctx (Succ j) (Cons (Term) a as) (Cons (Term) b bs)))
    (many DPThere : (erased (Ctx) ctx) (erased (Nat) j) (erased (Term) a) (erased (List (Term)) as) (erased (Term) b) (erased (List (Term)) bs) (erased (Same ctx a b) s) (erased (DifferPrefix ctx j as bs) p)
       -> (DifferPrefix ctx (Succ j) (Cons (Term) a as) (Cons (Term) b bs))))
  ; The results of a body against a return telescope (section 26): each the same as its entry, instantiated
  ; with the entries before it.
  ((CheckRets : ((Ctx) ctx) ((List (Maybe (Term))) acc) ((List (Entry)) rets) ((List (Nat)) ids) ((ROut) out) -> Type)
    enum
    (many CRNil : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) -> (CheckRets ctx acc (Nil (Entry)) (Nil (Nat)) (ROk)))
    (many CRSize : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (List (Entry)) rets) (erased (List (Nat)) ids) (erased (LenMismatch (Entry) (Nat) rets ids) m) -> (CheckRets ctx acc rets ids (RErr (RSize))))
    (many CRTy : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (Bool) s) (erased (Term) t) (erased (List (Entry)) es) (erased (Nat) x) (erased (List (Nat)) ids) (erased (Term) xty) (erased (Term) t2) (erased (ROut) out)
       (erased (TypeOf ctx x xty) ty) (erased (Subst acc t t2) sb) (erased (Same ctx xty t2) sm) (erased (CheckRets ctx (Cons (Maybe (Term)) (Some (Term) (Ref x)) acc) es ids out) p)
       -> (CheckRets ctx acc (Cons (Entry) (MkEntry s (BFalse) t) es) (Cons (Nat) x ids) out))
    (many CRIs : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (Bool) s) (erased (Term) t) (erased (List (Entry)) es) (erased (Nat) x) (erased (List (Nat)) ids) (erased (Term) t2) (erased (ROut) out)
       (erased (Subst acc t t2) sb) (erased (Same ctx (Ref x) t2) sm) (erased (CheckRets ctx (Cons (Maybe (Term)) (Some (Term) (Ref x)) acc) es ids out) p)
       -> (CheckRets ctx acc (Cons (Entry) (MkEntry s (BTrue) t) es) (Cons (Nat) x ids) out))
    (many CRTyMismatch : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (Bool) s) (erased (Term) t) (erased (List (Entry)) es) (erased (Nat) x) (erased (List (Nat)) ids) (erased (Term) xty) (erased (Term) t2)
       (erased (TypeOf ctx x xty) ty) (erased (Subst acc t t2) sb) (erased (Differ ctx xty t2) d) -> (CheckRets ctx acc (Cons (Entry) (MkEntry s (BFalse) t) es) (Cons (Nat) x ids) (RErr (RMismatch))))
    (many CRIsMismatch : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (Bool) s) (erased (Term) t) (erased (List (Entry)) es) (erased (Nat) x) (erased (List (Nat)) ids) (erased (Term) t2)
       (erased (Subst acc t t2) sb) (erased (Differ ctx (Ref x) t2) d) -> (CheckRets ctx acc (Cons (Entry) (MkEntry s (BTrue) t) es) (Cons (Nat) x ids) (RErr (RMismatch)))))
  ; Branches (section 21): each names a constructor of the type, once; its fields are minted, the scrutinee
  ; and its type are forced against the pattern and its type (section 7), the body is checked against the
  ; annotation, and the branch's scope is left. A branch the facts refute is an error (MINIMAL.md).
  ((ElabBranches : ((Ctx) ctx) ((Nat) s) ((Nat) tc) ((List (Nat)) ctors) ((List (Nat)) seen) ((List (Entry)) rt) ((List (Raw)) brs) ((BrOut) out) -> Type)
    enum
    (many EBNil : (erased (Ctx) ctx) (erased (Nat) s) (erased (Nat) tc) (erased (List (Nat)) ctors) (erased (List (Nat)) seen) (erased (List (Entry)) rt) -> (ElabBranches ctx s tc ctors seen rt (Nil (Raw)) (BrOk ctx (Nil (Branch)) seen)))
    (many EBCons : (erased (Ctx) ctx) (erased (Nat) s) (erased (Nat) tc) (erased (List (Nat)) ctors) (erased (List (Nat)) seen) (erased (List (Entry)) rt) (erased (String) cs) (erased (List (Raw)) fnames) (erased (List (Raw)) items) (erased (List (Raw)) rest)
       (erased (List (Name)) scope) (erased (Nat) c) (erased (Term) cty) (erased (List (Entry)) fs) (erased (Term) ret) (erased (List (Maybe (String))) names) (erased (Ctx) ctxF) (erased (List (Nat)) fids) (erased (List (Term)) frefs)
       (erased (Ctx) ctxR) (erased (Ctx) ctxB) (erased (Core) core) (erased (List (Nat)) ids) (erased (Ctx) ctx1) (erased (Ctx) out) (erased (List (Branch)) cbs) (erased (List (Nat)) seen2)
       (erased (Scope ctx scope) sc) (erased (NameOf scope cs c) n) (erased (Mem c ctors) mc) (erased (NotMem c seen) ns) (erased (TypeOf ctx c cty) t) (erased (CanonAt ctx cty (TValCtor fs ret)) cn)
       (erased (AtomNames fnames names) an) (erased (MintTele ctx (Nil (Maybe (Term))) fs names ctxF fids) m) (erased (Refs fids frefs) rf)
       (erased (Refine ctxF (Ref s) (ValApp (Ref c) fs ret frefs) ctxR) rf2)
       (erased (ElabBody ctxR items (EOk ctxB core ids)) eb) (erased (CheckRets ctxB (Nil (Maybe (Term))) rt ids (ROk)) cr) (erased (Leave ctxB ctx ctx1) lv)
       (erased (ElabBranches ctx1 s tc ctors (Cons (Nat) c seen) rt rest (BrOk out cbs seen2)) q)
       -> (ElabBranches ctx s tc ctors seen rt (Cons (Raw) (RList (Cons (Raw) (RList (Cons (Raw) (RAtom cs) fnames)) items)) rest) (BrOk out (Cons (Branch) (MkBranch c fids core) cbs) seen2)))
    (many EBUnbound : (erased (Ctx) ctx) (erased (Nat) s) (erased (Nat) tc) (erased (List (Nat)) ctors) (erased (List (Nat)) seen) (erased (List (Entry)) rt) (erased (String) cs) (erased (List (Raw)) fnames) (erased (List (Raw)) items) (erased (List (Raw)) rest)
       (erased (List (Name)) scope) (erased (Scope ctx scope) sc) (erased (NoName scope cs) n)
       -> (ElabBranches ctx s tc ctors seen rt (Cons (Raw) (RList (Cons (Raw) (RList (Cons (Raw) (RAtom cs) fnames)) items)) rest) (BrErr (RUnbound))))
    (many EBNotCtor : (erased (Ctx) ctx) (erased (Nat) s) (erased (Nat) tc) (erased (List (Nat)) ctors) (erased (List (Nat)) seen) (erased (List (Entry)) rt) (erased (String) cs) (erased (List (Raw)) fnames) (erased (List (Raw)) items) (erased (List (Raw)) rest)
       (erased (List (Name)) scope) (erased (Nat) c) (erased (Scope ctx scope) sc) (erased (NameOf scope cs c) n) (erased (NotMem c ctors) nm)
       -> (ElabBranches ctx s tc ctors seen rt (Cons (Raw) (RList (Cons (Raw) (RList (Cons (Raw) (RAtom cs) fnames)) items)) rest) (BrErr (RNotCtor))))
    (many EBDuplicate : (erased (Ctx) ctx) (erased (Nat) s) (erased (Nat) tc) (erased (List (Nat)) ctors) (erased (List (Nat)) seen) (erased (List (Entry)) rt) (erased (String) cs) (erased (List (Raw)) fnames) (erased (List (Raw)) items) (erased (List (Raw)) rest)
       (erased (List (Name)) scope) (erased (Nat) c) (erased (Scope ctx scope) sc) (erased (NameOf scope cs c) n) (erased (Mem c ctors) mc) (erased (Mem c seen) ms)
       -> (ElabBranches ctx s tc ctors seen rt (Cons (Raw) (RList (Cons (Raw) (RList (Cons (Raw) (RAtom cs) fnames)) items)) rest) (BrErr (RDuplicateBranch))))
    (many EBRefuted : (erased (Ctx) ctx) (erased (Nat) s) (erased (Nat) tc) (erased (List (Nat)) ctors) (erased (List (Nat)) seen) (erased (List (Entry)) rt) (erased (String) cs) (erased (List (Raw)) fnames) (erased (List (Raw)) items) (erased (List (Raw)) rest)
       (erased (List (Name)) scope) (erased (Nat) c) (erased (Term) cty) (erased (List (Entry)) fs) (erased (Term) ret) (erased (List (Maybe (String))) names) (erased (Ctx) ctxF) (erased (List (Nat)) fids) (erased (List (Term)) frefs)
       (erased (Scope ctx scope) sc) (erased (NameOf scope cs c) n) (erased (Mem c ctors) mc) (erased (NotMem c seen) ns) (erased (TypeOf ctx c cty) t) (erased (CanonAt ctx cty (TValCtor fs ret)) cn)
       (erased (AtomNames fnames names) an) (erased (MintTele ctx (Nil (Maybe (Term))) fs names ctxF fids) m) (erased (Refs fids frefs) rf)
       (erased (Contradict ctxF (Ref s) (ValApp (Ref c) fs ret frefs)) cd)
       -> (ElabBranches ctx s tc ctors seen rt (Cons (Raw) (RList (Cons (Raw) (RList (Cons (Raw) (RAtom cs) fnames)) items)) rest) (BrErr (RRefutedBranch))))
    (many EBBodyErr : (erased (Ctx) ctx) (erased (Nat) s) (erased (Nat) tc) (erased (List (Nat)) ctors) (erased (List (Nat)) seen) (erased (List (Entry)) rt) (erased (String) cs) (erased (List (Raw)) fnames) (erased (List (Raw)) items) (erased (List (Raw)) rest)
       (erased (List (Name)) scope) (erased (Nat) c) (erased (Term) cty) (erased (List (Entry)) fs) (erased (Term) ret) (erased (List (Maybe (String))) names) (erased (Ctx) ctxF) (erased (List (Nat)) fids) (erased (List (Term)) frefs)
       (erased (Ctx) ctxR) (erased (Reason) r)
       (erased (Scope ctx scope) sc) (erased (NameOf scope cs c) n) (erased (Mem c ctors) mc) (erased (NotMem c seen) ns) (erased (TypeOf ctx c cty) t) (erased (CanonAt ctx cty (TValCtor fs ret)) cn)
       (erased (AtomNames fnames names) an) (erased (MintTele ctx (Nil (Maybe (Term))) fs names ctxF fids) m) (erased (Refs fids frefs) rf)
       (erased (Refine ctxF (Ref s) (ValApp (Ref c) fs ret frefs) ctxR) rf2)
       (erased (ElabBody ctxR items (EErr r)) eb)
       -> (ElabBranches ctx s tc ctors seen rt (Cons (Raw) (RList (Cons (Raw) (RList (Cons (Raw) (RAtom cs) fnames)) items)) rest) (BrErr r)))
    (many EBRetsErr : (erased (Ctx) ctx) (erased (Nat) s) (erased (Nat) tc) (erased (List (Nat)) ctors) (erased (List (Nat)) seen) (erased (List (Entry)) rt) (erased (String) cs) (erased (List (Raw)) fnames) (erased (List (Raw)) items) (erased (List (Raw)) rest)
       (erased (List (Name)) scope) (erased (Nat) c) (erased (Term) cty) (erased (List (Entry)) fs) (erased (Term) ret) (erased (List (Maybe (String))) names) (erased (Ctx) ctxF) (erased (List (Nat)) fids) (erased (List (Term)) frefs)
       (erased (Ctx) ctxR) (erased (Ctx) ctxB) (erased (Core) core) (erased (List (Nat)) ids) (erased (Reason) r)
       (erased (Scope ctx scope) sc) (erased (NameOf scope cs c) n) (erased (Mem c ctors) mc) (erased (NotMem c seen) ns) (erased (TypeOf ctx c cty) t) (erased (CanonAt ctx cty (TValCtor fs ret)) cn)
       (erased (AtomNames fnames names) an) (erased (MintTele ctx (Nil (Maybe (Term))) fs names ctxF fids) m) (erased (Refs fids frefs) rf)
       (erased (Refine ctxF (Ref s) (ValApp (Ref c) fs ret frefs) ctxR) rf2)
       (erased (ElabBody ctxR items (EOk ctxB core ids)) eb) (erased (CheckRets ctxB (Nil (Maybe (Term))) rt ids (RErr r)) cr)
       -> (ElabBranches ctx s tc ctors seen rt (Cons (Raw) (RList (Cons (Raw) (RList (Cons (Raw) (RAtom cs) fnames)) items)) rest) (BrErr r)))
    (many EBRestErr : (erased (Ctx) ctx) (erased (Nat) s) (erased (Nat) tc) (erased (List (Nat)) ctors) (erased (List (Nat)) seen) (erased (List (Entry)) rt) (erased (String) cs) (erased (List (Raw)) fnames) (erased (List (Raw)) items) (erased (List (Raw)) rest)
       (erased (List (Name)) scope) (erased (Nat) c) (erased (Term) cty) (erased (List (Entry)) fs) (erased (Term) ret) (erased (List (Maybe (String))) names) (erased (Ctx) ctxF) (erased (List (Nat)) fids) (erased (List (Term)) frefs)
       (erased (Ctx) ctxR) (erased (Ctx) ctxB) (erased (Core) core) (erased (List (Nat)) ids) (erased (Ctx) ctx1) (erased (Reason) r)
       (erased (Scope ctx scope) sc) (erased (NameOf scope cs c) n) (erased (Mem c ctors) mc) (erased (NotMem c seen) ns) (erased (TypeOf ctx c cty) t) (erased (CanonAt ctx cty (TValCtor fs ret)) cn)
       (erased (AtomNames fnames names) an) (erased (MintTele ctx (Nil (Maybe (Term))) fs names ctxF fids) m) (erased (Refs fids frefs) rf)
       (erased (Refine ctxF (Ref s) (ValApp (Ref c) fs ret frefs) ctxR) rf2)
       (erased (ElabBody ctxR items (EOk ctxB core ids)) eb) (erased (CheckRets ctxB (Nil (Maybe (Term))) rt ids (ROk)) cr) (erased (Leave ctxB ctx ctx1) lv)
       (erased (ElabBranches ctx1 s tc ctors (Cons (Nat) c seen) rt rest (BrErr r)) q)
       -> (ElabBranches ctx s tc ctors seen rt (Cons (Raw) (RList (Cons (Raw) (RList (Cons (Raw) (RAtom cs) fnames)) items)) rest) (BrErr r))))
  ; Every constructor has a branch or is refuted by the facts (section 21), with anonymous fields.
  ((Covered : ((Ctx) ctx) ((Nat) s) ((List (Nat)) ctors) ((List (Nat)) seen) -> Type)
    enum
    (many CvNil : (erased (Ctx) ctx) (erased (Nat) s) (erased (List (Nat)) seen) -> (Covered ctx s (Nil (Nat)) seen))
    (many CvSeen : (erased (Ctx) ctx) (erased (Nat) s) (erased (Nat) c) (erased (List (Nat)) ctors) (erased (List (Nat)) seen) (erased (Mem c seen) m) (erased (Covered ctx s ctors seen) p) -> (Covered ctx s (Cons (Nat) c ctors) seen))
    (many CvRefuted : (erased (Ctx) ctx) (erased (Nat) s) (erased (Nat) c) (erased (List (Nat)) ctors) (erased (List (Nat)) seen) (erased (NotMem c seen) nm) (erased (Refuted ctx s c) r) (erased (Covered ctx s ctors seen) p)
       -> (Covered ctx s (Cons (Nat) c ctors) seen)))
  ((Uncovered : ((Ctx) ctx) ((Nat) s) ((List (Nat)) ctors) ((List (Nat)) seen) -> Type)
    enum
    (many UcHere : (erased (Ctx) ctx) (erased (Nat) s) (erased (Nat) c) (erased (List (Nat)) ctors) (erased (List (Nat)) seen) (erased (NotMem c seen) nm) (erased (Reachable ctx s c) r) -> (Uncovered ctx s (Cons (Nat) c ctors) seen))
    (many UcThere : (erased (Ctx) ctx) (erased (Nat) s) (erased (Nat) c) (erased (List (Nat)) ctors) (erased (List (Nat)) seen) (erased (Uncovered ctx s ctors seen) p) -> (Uncovered ctx s (Cons (Nat) c ctors) seen)))
  ((Refuted : ((Ctx) ctx) ((Nat) s) ((Nat) c) -> Type)
    enum
    (many RefutedBy : (erased (Ctx) ctx) (erased (Nat) s) (erased (Nat) c) (erased (Term) cty) (erased (List (Entry)) fs) (erased (Term) ret) (erased (List (Maybe (String))) names) (erased (Ctx) ctxF) (erased (List (Nat)) fids)
       (erased (List (Term)) frefs)
       (erased (TypeOf ctx c cty) t) (erased (CanonAt ctx cty (TValCtor fs ret)) cn) (erased (Nones fs names) nn) (erased (MintTele ctx (Nil (Maybe (Term))) fs names ctxF fids) m) (erased (Refs fids frefs) rf)
       (erased (Contradict ctxF (Ref s) (ValApp (Ref c) fs ret frefs)) cd) -> (Refuted ctx s c)))
  ((Reachable : ((Ctx) ctx) ((Nat) s) ((Nat) c) -> Type)
    enum
    (many ReachableBy : (erased (Ctx) ctx) (erased (Nat) s) (erased (Nat) c) (erased (Term) cty) (erased (List (Entry)) fs) (erased (Term) ret) (erased (List (Maybe (String))) names) (erased (Ctx) ctxF) (erased (List (Nat)) fids)
       (erased (List (Term)) frefs) (erased (Ctx) ctxR)
       (erased (TypeOf ctx c cty) t) (erased (CanonAt ctx cty (TValCtor fs ret)) cn) (erased (Nones fs names) nn) (erased (MintTele ctx (Nil (Maybe (Term))) fs names ctxF fids) m) (erased (Refs fids frefs) rf)
       (erased (Refine ctxF (Ref s) (ValApp (Ref c) fs ret frefs) ctxR) rf2) -> (Reachable ctx s c)))
  ; A body: statements, then the final expression (section 27).
  ((ElabBody : ((Ctx) ctx) ((List (Raw)) items) ((EOut) out) -> Type)
    enum
    (many BodyFinal : (erased (Ctx) ctx) (erased (Raw) r) (erased (EOut) out) (erased (ElabExpr ctx r out) p) -> (ElabBody ctx (Cons (Raw) r (Nil (Raw))) out))
    (many BodyStmt : (erased (Ctx) ctx) (erased (Raw) s) (erased (Raw) r) (erased (List (Raw)) rest) (erased (Ctx) ctx1) (erased (Stmt) st) (erased (Ctx) out) (erased (Core) core) (erased (List (Nat)) ids)
       (erased (ElabStmt ctx s (SOk ctx1 st)) p) (erased (ElabBody ctx1 (Cons (Raw) r rest) (EOk out core ids)) q) -> (ElabBody ctx (Cons (Raw) s (Cons (Raw) r rest)) (EOk out (CStmt st core) ids)))
    (many BodyStmtErr : (erased (Ctx) ctx) (erased (Raw) s) (erased (Raw) r) (erased (List (Raw)) rest) (erased (Reason) e) (erased (ElabStmt ctx s (SErr e)) p) -> (ElabBody ctx (Cons (Raw) s (Cons (Raw) r rest)) (EErr e)))
    (many BodyRestErr : (erased (Ctx) ctx) (erased (Raw) s) (erased (Raw) r) (erased (List (Raw)) rest) (erased (Ctx) ctx1) (erased (Stmt) st) (erased (Reason) e)
       (erased (ElabStmt ctx s (SOk ctx1 st)) p) (erased (ElabBody ctx1 (Cons (Raw) r rest) (EErr e)) q) -> (ElabBody ctx (Cons (Raw) s (Cons (Raw) r rest)) (EErr e))))
  ; Statements (sections 27, 54): let, def-lvl, def-fns, def-adts.
  ((ElabStmt : ((Ctx) ctx) ((Raw) raw) ((SOut) out) -> Type)
    enum
    ; (let (binders) items...): the right-hand side's names are hidden, its entries and facts kept; each
    ; binder is an alias of its value's entry, its type or is clause a checked redundancy (section 19)
    (many STLet : (erased (Ctx) ctx) (erased (List (Raw)) binders) (erased (List (Raw)) items) (erased (Ctx) ctx1) (erased (Core) core) (erased (List (Nat)) ids) (erased (List (Name)) scope) (erased (Ctx) ctxH) (erased (Ctx) out) (erased (List (Nat)) aids)
       (erased (ElabBody ctx items (EOk ctx1 core ids)) p) (erased (Scope ctx scope) sc) (erased (Hide ctx1 scope ctxH) h) (erased (BindLet ctxH binders ids (AllOk out (Nil (Core)) aids)) b)
       -> (ElabStmt ctx (RList (Cons (Raw) (RKey (KLet)) (Cons (Raw) (RList binders) items))) (SOk out (SLet aids core))))
    (many STLetErr : (erased (Ctx) ctx) (erased (List (Raw)) binders) (erased (List (Raw)) items) (erased (Reason) r) (erased (ElabBody ctx items (EErr r)) p)
       -> (ElabStmt ctx (RList (Cons (Raw) (RKey (KLet)) (Cons (Raw) (RList binders) items))) (SErr r)))
    (many STLetBindErr : (erased (Ctx) ctx) (erased (List (Raw)) binders) (erased (List (Raw)) items) (erased (Ctx) ctx1) (erased (Core) core) (erased (List (Nat)) ids) (erased (List (Name)) scope) (erased (Ctx) ctxH) (erased (Reason) r)
       (erased (ElabBody ctx items (EOk ctx1 core ids)) p) (erased (Scope ctx scope) sc) (erased (Hide ctx1 scope ctxH) h) (erased (BindLet ctxH binders ids (AErr r)) b)
       -> (ElabStmt ctx (RList (Cons (Raw) (RKey (KLet)) (Cons (Raw) (RList binders) items))) (SErr r)))
    ; (def-lvl L)
    (many STDefLvl : (erased (Ctx) ctx) (erased (String) ls) (erased (Nat) x) (erased (Ctx) out) (erased (Mint ctx (Some (String) ls) level-ty (KLevel) (None (Term)) x out) m)
       -> (ElabStmt ctx (RList (Cons (Raw) (RKey (KDefLvl)) (Cons (Raw) (RAtom ls) (Nil (Raw))))) (SOk out (SDefLvl x))))
    ; (def-fns L (f (params) (rets) items...)...): the signatures minted first, then each body at level L
    (many STDefFns : (erased (Ctx) ctx) (erased (Raw) lr) (erased (List (Raw)) defs) (erased (Term) l) (erased (Term) lty) (erased (Ctx) ctx1) (erased (List (Sig)) sigs) (erased (Ctx) out) (erased (List (FnDef)) fds)
       (erased (ElabTerm ctx lr (TOk l lty)) p) (erased (Same ctx lty level-ty) sl) (erased (MintFns ctx l defs (FOk ctx1 sigs)) mf) (erased (ElabBodies ctx1 l sigs defs (BsOk out fds)) eb)
       -> (ElabStmt ctx (RList (Cons (Raw) (RKey (KDefFns)) (Cons (Raw) lr defs))) (SOk out (SDefFns fds))))
    (many STDefFnsLevelErr : (erased (Ctx) ctx) (erased (Raw) lr) (erased (List (Raw)) defs) (erased (Reason) r) (erased (ElabTerm ctx lr (TErr r)) p)
       -> (ElabStmt ctx (RList (Cons (Raw) (RKey (KDefFns)) (Cons (Raw) lr defs))) (SErr r)))
    (many STDefFnsNotLevel : (erased (Ctx) ctx) (erased (Raw) lr) (erased (List (Raw)) defs) (erased (Term) l) (erased (Term) lty) (erased (ElabTerm ctx lr (TOk l lty)) p) (erased (Differ ctx lty level-ty) d)
       -> (ElabStmt ctx (RList (Cons (Raw) (RKey (KDefFns)) (Cons (Raw) lr defs))) (SErr (RNotLevel))))
    (many STDefFnsSigErr : (erased (Ctx) ctx) (erased (Raw) lr) (erased (List (Raw)) defs) (erased (Term) l) (erased (Term) lty) (erased (Reason) r)
       (erased (ElabTerm ctx lr (TOk l lty)) p) (erased (Same ctx lty level-ty) sl) (erased (MintFns ctx l defs (FErr r)) mf)
       -> (ElabStmt ctx (RList (Cons (Raw) (RKey (KDefFns)) (Cons (Raw) lr defs))) (SErr r)))
    (many STDefFnsBodyErr : (erased (Ctx) ctx) (erased (Raw) lr) (erased (List (Raw)) defs) (erased (Term) l) (erased (Term) lty) (erased (Ctx) ctx1) (erased (List (Sig)) sigs) (erased (Reason) r)
       (erased (ElabTerm ctx lr (TOk l lty)) p) (erased (Same ctx lty level-ty) sl) (erased (MintFns ctx l defs (FOk ctx1 sigs)) mf) (erased (ElabBodies ctx1 l sigs defs (BsErr r)) eb)
       -> (ElabStmt ctx (RList (Cons (Raw) (RKey (KDefFns)) (Cons (Raw) lr defs))) (SErr r)))
    ; (def-adts (T (params) (C (fields) ret)...)...), at the top level only (MINIMAL.md): the type
    ; constructors minted first, then every constructor, whose return must be its own type applied
    (many STDefAdts : (erased (Ctx) ctx) (erased (List (Raw)) decls) (erased (Ctx) ctx1) (erased (List (Nat)) tids) (erased (Ctx) out) (erased (List (Nat)) ids)
       (erased (LevelOf ctx (None (Term))) lv) (erased (MintTycons ctx decls (FOkT ctx1 tids)) mt) (erased (MintCtors ctx1 decls tids (FOkT out ids)) mc)
       -> (ElabStmt ctx (RList (Cons (Raw) (RKey (KDefAdts)) decls)) (SOk out (SDefAdts ids))))
    (many STDefAdtsNested : (erased (Ctx) ctx) (erased (List (Raw)) decls) (erased (Term) cur) (erased (LevelOf ctx (Some (Term) cur)) lv) -> (ElabStmt ctx (RList (Cons (Raw) (RKey (KDefAdts)) decls)) (SErr (RTopLevelOnly))))
    (many STDefAdtsTyconErr : (erased (Ctx) ctx) (erased (List (Raw)) decls) (erased (Reason) r) (erased (LevelOf ctx (None (Term))) lv) (erased (MintTycons ctx decls (FErrT r)) mt)
       -> (ElabStmt ctx (RList (Cons (Raw) (RKey (KDefAdts)) decls)) (SErr r)))
    (many STDefAdtsCtorErr : (erased (Ctx) ctx) (erased (List (Raw)) decls) (erased (Ctx) ctx1) (erased (List (Nat)) tids) (erased (Reason) r)
       (erased (LevelOf ctx (None (Term))) lv) (erased (MintTycons ctx decls (FOkT ctx1 tids)) mt) (erased (MintCtors ctx1 decls tids (FErrT r)) mc)
       -> (ElabStmt ctx (RList (Cons (Raw) (RKey (KDefAdts)) decls)) (SErr r))))
  ; The binders of a let, each aliasing one value.
  ((BindLet : ((Ctx) ctx) ((List (Raw)) binders) ((List (Nat)) ids) ((AOut) out) -> Type)
    enum
    (many BLNil : (erased (Ctx) ctx) -> (BindLet ctx (Nil (Raw)) (Nil (Nat)) (AllOk ctx (Nil (Core)) (Nil (Nat)))))
    (many BLSize : (erased (Ctx) ctx) (erased (List (Raw)) binders) (erased (List (Nat)) ids) (erased (LenMismatch (Raw) (Nat) binders ids) m) -> (BindLet ctx binders ids (AErr (RSize))))
    (many BLName : (erased (Ctx) ctx) (erased (String) x) (erased (List (Raw)) binders) (erased (Nat) id) (erased (List (Nat)) ids) (erased (Term) ty) (erased (Nat) a) (erased (Ctx) ctx1) (erased (Ctx) out) (erased (List (Nat)) aids)
       (erased (TypeOf ctx id ty) t) (erased (Mint ctx (Some (String) x) ty (KPlain) (Some (Term) (Ref id)) a ctx1) m) (erased (BindLet ctx1 binders ids (AllOk out (Nil (Core)) aids)) p)
       -> (BindLet ctx (Cons (Raw) (RAtom x) binders) (Cons (Nat) id ids) (AllOk out (Nil (Core)) (Cons (Nat) a aids))))
    (many BLTy : (erased (Ctx) ctx) (erased (Raw) b) (erased (Raw) tr) (erased (String) x) (erased (List (Raw)) binders) (erased (Nat) id) (erased (List (Nat)) ids) (erased (Term) t) (erased (Term) tty) (erased (Term) ty)
       (erased (Nat) a) (erased (Ctx) ctx1) (erased (Ctx) out) (erased (List (Nat)) aids)
       (erased (EntryRaw b (BFalse) (BFalse) tr x) shape) (erased (ElabTerm ctx tr (TOk t tty)) et) (erased (TypeOf ctx id ty) ty1) (erased (Same ctx ty t) sm)
       (erased (Mint ctx (Some (String) x) ty (KPlain) (Some (Term) (Ref id)) a ctx1) m) (erased (BindLet ctx1 binders ids (AllOk out (Nil (Core)) aids)) p)
       -> (BindLet ctx (Cons (Raw) b binders) (Cons (Nat) id ids) (AllOk out (Nil (Core)) (Cons (Nat) a aids))))
    (many BLIs : (erased (Ctx) ctx) (erased (Raw) b) (erased (Raw) er) (erased (String) x) (erased (List (Raw)) binders) (erased (Nat) id) (erased (List (Nat)) ids) (erased (Term) t) (erased (Term) tty) (erased (Term) ty)
       (erased (Nat) a) (erased (Ctx) ctx1) (erased (Ctx) out) (erased (List (Nat)) aids)
       (erased (EntryRaw b (BFalse) (BTrue) er x) shape) (erased (ElabTerm ctx er (TOk t tty)) et) (erased (TypeOf ctx id ty) ty1) (erased (Same ctx (Ref id) t) sm)
       (erased (Mint ctx (Some (String) x) ty (KPlain) (Some (Term) (Ref id)) a ctx1) m) (erased (BindLet ctx1 binders ids (AllOk out (Nil (Core)) aids)) p)
       -> (BindLet ctx (Cons (Raw) b binders) (Cons (Nat) id ids) (AllOk out (Nil (Core)) (Cons (Nat) a aids))))
    (many BLTermErr : (erased (Ctx) ctx) (erased (Raw) b) (erased (Bool) i) (erased (Raw) tr) (erased (String) x) (erased (List (Raw)) binders) (erased (Nat) id) (erased (List (Nat)) ids) (erased (Reason) r)
       (erased (EntryRaw b (BFalse) i tr x) shape) (erased (ElabTerm ctx tr (TErr r)) et) -> (BindLet ctx (Cons (Raw) b binders) (Cons (Nat) id ids) (AErr r)))
    (many BLTyMismatch : (erased (Ctx) ctx) (erased (Raw) b) (erased (Raw) tr) (erased (String) x) (erased (List (Raw)) binders) (erased (Nat) id) (erased (List (Nat)) ids) (erased (Term) t) (erased (Term) tty) (erased (Term) ty)
       (erased (EntryRaw b (BFalse) (BFalse) tr x) shape) (erased (ElabTerm ctx tr (TOk t tty)) et) (erased (TypeOf ctx id ty) ty1) (erased (Differ ctx ty t) d)
       -> (BindLet ctx (Cons (Raw) b binders) (Cons (Nat) id ids) (AErr (RMismatch))))
    (many BLIsMismatch : (erased (Ctx) ctx) (erased (Raw) b) (erased (Raw) er) (erased (String) x) (erased (List (Raw)) binders) (erased (Nat) id) (erased (List (Nat)) ids) (erased (Term) t) (erased (Term) tty)
       (erased (EntryRaw b (BFalse) (BTrue) er x) shape) (erased (ElabTerm ctx er (TOk t tty)) et) (erased (Differ ctx (Ref id) t) d)
       -> (BindLet ctx (Cons (Raw) b binders) (Cons (Nat) id ids) (AErr (RMismatch))))
    (many BLRestErr : (erased (Ctx) ctx) (erased (Raw) b) (erased (List (Raw)) binders) (erased (Nat) id) (erased (List (Nat)) ids) (erased (String) x) (erased (Term) ty) (erased (Nat) a) (erased (Ctx) ctx1) (erased (Reason) r)
       (erased (BinderName b x) bn) (erased (TypeOf ctx id ty) t) (erased (Mint ctx (Some (String) x) ty (KPlain) (Some (Term) (Ref id)) a ctx1) m) (erased (BindLet ctx1 binders ids (AErr r)) p)
       -> (BindLet ctx (Cons (Raw) b binders) (Cons (Nat) id ids) (AErr r))))
  ((BinderName : ((Raw) b) ((String) x) -> Type)
    enum
    (many BNAtom : (erased (String) x) -> (BinderName (RAtom x) x))
    (many BNEntry : (erased (Raw) b) (erased (Bool) i) (erased (Raw) tr) (erased (String) x) (erased (EntryRaw b (BFalse) i tr x) shape) -> (BinderName b x)))
  ; A def-fns signature: the function's entry and its telescopes with their names.
  ((MintFns : ((Ctx) ctx) ((Term) l) ((List (Raw)) defs) ((FOut) out) -> Type)
    enum
    (many MFNil : (erased (Ctx) ctx) (erased (Term) l) -> (MintFns ctx l (Nil (Raw)) (FOk ctx (Nil (Sig)))))
    (many MFCons : (erased (Ctx) ctx) (erased (Term) l) (erased (String) f) (erased (List (Raw)) ps) (erased (List (Raw)) rs) (erased (List (Raw)) items) (erased (List (Raw)) rest)
       (erased (Ctx) ctxP) (erased (List (Entry)) pt) (erased (List (Nat)) pids) (erased (List (Maybe (String))) pn) (erased (List (Maybe (Nat))) acc) (erased (Ctx) ctxR) (erased (List (Entry)) rt) (erased (List (Nat)) rids) (erased (List (Maybe (String))) rn)
       (erased (Nat) fid) (erased (Ctx) ctx1) (erased (Ctx) out) (erased (List (Sig)) sigs)
       (erased (ElabTele ctx (Nil (Maybe (Nat))) ps (TeleOk ctxP pt pids pn)) ep) (erased (Binders pids acc) b) (erased (ElabTele ctxP acc rs (TeleOk ctxR rt rids rn)) er)
       (erased (Mint ctx (Some (String) f) (TFn l pt rt) (KPlain) (None (Term)) fid ctx1) m) (erased (MintFns ctx1 l rest (FOk out sigs)) q)
       -> (MintFns ctx l (Cons (Raw) (RList (Cons (Raw) (RAtom f) (Cons (Raw) (RList ps) (Cons (Raw) (RList rs) items)))) rest) (FOk out (Cons (Sig) (MkSig fid pt pn rt) sigs))))
    (many MFParamsErr : (erased (Ctx) ctx) (erased (Term) l) (erased (String) f) (erased (List (Raw)) ps) (erased (List (Raw)) rs) (erased (List (Raw)) items) (erased (List (Raw)) rest) (erased (Reason) r)
       (erased (ElabTele ctx (Nil (Maybe (Nat))) ps (TeleErr r)) ep) -> (MintFns ctx l (Cons (Raw) (RList (Cons (Raw) (RAtom f) (Cons (Raw) (RList ps) (Cons (Raw) (RList rs) items)))) rest) (FErr r)))
    (many MFRetsErr : (erased (Ctx) ctx) (erased (Term) l) (erased (String) f) (erased (List (Raw)) ps) (erased (List (Raw)) rs) (erased (List (Raw)) items) (erased (List (Raw)) rest)
       (erased (Ctx) ctxP) (erased (List (Entry)) pt) (erased (List (Nat)) pids) (erased (List (Maybe (String))) pn) (erased (List (Maybe (Nat))) acc) (erased (Reason) r)
       (erased (ElabTele ctx (Nil (Maybe (Nat))) ps (TeleOk ctxP pt pids pn)) ep) (erased (Binders pids acc) b) (erased (ElabTele ctxP acc rs (TeleErr r)) er)
       -> (MintFns ctx l (Cons (Raw) (RList (Cons (Raw) (RAtom f) (Cons (Raw) (RList ps) (Cons (Raw) (RList rs) items)))) rest) (FErr r)))
    (many MFRestErr : (erased (Ctx) ctx) (erased (Term) l) (erased (String) f) (erased (List (Raw)) ps) (erased (List (Raw)) rs) (erased (List (Raw)) items) (erased (List (Raw)) rest)
       (erased (Ctx) ctxP) (erased (List (Entry)) pt) (erased (List (Nat)) pids) (erased (List (Maybe (String))) pn) (erased (List (Maybe (Nat))) acc) (erased (Ctx) ctxR) (erased (List (Entry)) rt) (erased (List (Nat)) rids) (erased (List (Maybe (String))) rn)
       (erased (Nat) fid) (erased (Ctx) ctx1) (erased (Reason) r)
       (erased (ElabTele ctx (Nil (Maybe (Nat))) ps (TeleOk ctxP pt pids pn)) ep) (erased (Binders pids acc) b) (erased (ElabTele ctxP acc rs (TeleOk ctxR rt rids rn)) er)
       (erased (Mint ctx (Some (String) f) (TFn l pt rt) (KPlain) (None (Term)) fid ctx1) m) (erased (MintFns ctx1 l rest (FErr r)) q)
       -> (MintFns ctx l (Cons (Raw) (RList (Cons (Raw) (RAtom f) (Cons (Raw) (RList ps) (Cons (Raw) (RList rs) items)))) rest) (FErr r))))
  ; Each body: the parameters minted with their names, the level and subterm arguments set (section 5), the
  ; body checked against the returns, the scope left.
  ((ElabBodies : ((Ctx) ctx) ((Term) l) ((List (Sig)) sigs) ((List (Raw)) defs) ((BsOut) out) -> Type)
    enum
    (many BdNil : (erased (Ctx) ctx) (erased (Term) l) -> (ElabBodies ctx l (Nil (Sig)) (Nil (Raw)) (BsOk ctx (Nil (FnDef)))))
    (many BdCons : (erased (Ctx) ctx) (erased (Term) l) (erased (Nat) fid) (erased (List (Entry)) pt) (erased (List (Maybe (String))) pn) (erased (List (Entry)) rt) (erased (List (Sig)) sigs)
       (erased (String) f) (erased (List (Raw)) ps) (erased (List (Raw)) rs) (erased (List (Raw)) items) (erased (List (Raw)) rest)
       (erased (Ctx) ctxP) (erased (List (Nat)) pids) (erased (List (Term)) subargs) (erased (Ctx) ctxE) (erased (Ctx) ctxB) (erased (Core) core) (erased (List (Nat)) ids) (erased (List (Term)) prefs) (erased (List (Maybe (Term))) subs)
       (erased (Ctx) ctx1) (erased (Ctx) out) (erased (List (FnDef)) fds)
       (erased (MintTele ctx (Nil (Maybe (Term))) pt pn ctxP pids) m) (erased (Marked pt pids subargs) mk) (erased (Enter ctxP l subargs ctxE) en) (erased (ElabBody ctxE items (EOk ctxB core ids)) eb)
       (erased (Refs pids prefs) rf) (erased (Somes prefs subs) so) (erased (CheckRets ctxB subs rt ids (ROk)) cr) (erased (Leave ctxB ctx ctx1) lv) (erased (ElabBodies ctx1 l sigs rest (BsOk out fds)) q)
       -> (ElabBodies ctx l (Cons (Sig) (MkSig fid pt pn rt) sigs) (Cons (Raw) (RList (Cons (Raw) (RAtom f) (Cons (Raw) (RList ps) (Cons (Raw) (RList rs) items)))) rest) (BsOk out (Cons (FnDef) (MkFnDef fid pids core) fds))))
    (many BdBodyErr : (erased (Ctx) ctx) (erased (Term) l) (erased (Nat) fid) (erased (List (Entry)) pt) (erased (List (Maybe (String))) pn) (erased (List (Entry)) rt) (erased (List (Sig)) sigs)
       (erased (String) f) (erased (List (Raw)) ps) (erased (List (Raw)) rs) (erased (List (Raw)) items) (erased (List (Raw)) rest)
       (erased (Ctx) ctxP) (erased (List (Nat)) pids) (erased (List (Term)) subargs) (erased (Ctx) ctxE) (erased (Reason) r)
       (erased (MintTele ctx (Nil (Maybe (Term))) pt pn ctxP pids) m) (erased (Marked pt pids subargs) mk) (erased (Enter ctxP l subargs ctxE) en) (erased (ElabBody ctxE items (EErr r)) eb)
       -> (ElabBodies ctx l (Cons (Sig) (MkSig fid pt pn rt) sigs) (Cons (Raw) (RList (Cons (Raw) (RAtom f) (Cons (Raw) (RList ps) (Cons (Raw) (RList rs) items)))) rest) (BsErr r)))
    (many BdRetsErr : (erased (Ctx) ctx) (erased (Term) l) (erased (Nat) fid) (erased (List (Entry)) pt) (erased (List (Maybe (String))) pn) (erased (List (Entry)) rt) (erased (List (Sig)) sigs)
       (erased (String) f) (erased (List (Raw)) ps) (erased (List (Raw)) rs) (erased (List (Raw)) items) (erased (List (Raw)) rest)
       (erased (Ctx) ctxP) (erased (List (Nat)) pids) (erased (List (Term)) subargs) (erased (Ctx) ctxE) (erased (Ctx) ctxB) (erased (Core) core) (erased (List (Nat)) ids) (erased (List (Term)) prefs) (erased (List (Maybe (Term))) subs) (erased (Reason) r)
       (erased (MintTele ctx (Nil (Maybe (Term))) pt pn ctxP pids) m) (erased (Marked pt pids subargs) mk) (erased (Enter ctxP l subargs ctxE) en) (erased (ElabBody ctxE items (EOk ctxB core ids)) eb)
       (erased (Refs pids prefs) rf) (erased (Somes prefs subs) so) (erased (CheckRets ctxB subs rt ids (RErr r)) cr)
       -> (ElabBodies ctx l (Cons (Sig) (MkSig fid pt pn rt) sigs) (Cons (Raw) (RList (Cons (Raw) (RAtom f) (Cons (Raw) (RList ps) (Cons (Raw) (RList rs) items)))) rest) (BsErr r)))
    (many BdRestErr : (erased (Ctx) ctx) (erased (Term) l) (erased (Nat) fid) (erased (List (Entry)) pt) (erased (List (Maybe (String))) pn) (erased (List (Entry)) rt) (erased (List (Sig)) sigs)
       (erased (String) f) (erased (List (Raw)) ps) (erased (List (Raw)) rs) (erased (List (Raw)) items) (erased (List (Raw)) rest)
       (erased (Ctx) ctxP) (erased (List (Nat)) pids) (erased (List (Term)) subargs) (erased (Ctx) ctxE) (erased (Ctx) ctxB) (erased (Core) core) (erased (List (Nat)) ids) (erased (List (Term)) prefs) (erased (List (Maybe (Term))) subs)
       (erased (Ctx) ctx1) (erased (Reason) r)
       (erased (MintTele ctx (Nil (Maybe (Term))) pt pn ctxP pids) m) (erased (Marked pt pids subargs) mk) (erased (Enter ctxP l subargs ctxE) en) (erased (ElabBody ctxE items (EOk ctxB core ids)) eb)
       (erased (Refs pids prefs) rf) (erased (Somes prefs subs) so) (erased (CheckRets ctxB subs rt ids (ROk)) cr) (erased (Leave ctxB ctx ctx1) lv) (erased (ElabBodies ctx1 l sigs rest (BsErr r)) q)
       -> (ElabBodies ctx l (Cons (Sig) (MkSig fid pt pn rt) sigs) (Cons (Raw) (RList (Cons (Raw) (RAtom f) (Cons (Raw) (RList ps) (Cons (Raw) (RList rs) items)))) rest) (BsErr r))))
  ; def-adts: the type constructors, then the constructors, each declaration adding its ADT.
  ((MintTycons : ((Ctx) ctx) ((List (Raw)) decls) ((FOutT) out) -> Type)
    enum
    (many MTyNil : (erased (Ctx) ctx) -> (MintTycons ctx (Nil (Raw)) (FOkT ctx (Nil (Nat)))))
    (many MTyCons : (erased (Ctx) ctx) (erased (String) tn) (erased (List (Raw)) ps) (erased (List (Raw)) ctors) (erased (List (Raw)) rest) (erased (Ctx) ctxP) (erased (List (Entry)) pt) (erased (List (Nat)) pids) (erased (List (Maybe (String))) pn)
       (erased (Nat) tid) (erased (Ctx) ctx1) (erased (Ctx) out) (erased (List (Nat)) tids)
       (erased (ElabTele ctx (Nil (Maybe (Nat))) ps (TeleOk ctxP pt pids pn)) ep) (erased (Mint ctx (Some (String) tn) (TTyCtor pt) (KDecl) (None (Term)) tid ctx1) m) (erased (MintTycons ctx1 rest (FOkT out tids)) q)
       -> (MintTycons ctx (Cons (Raw) (RList (Cons (Raw) (RAtom tn) (Cons (Raw) (RList ps) ctors))) rest) (FOkT out (Cons (Nat) tid tids))))
    (many MTyErr : (erased (Ctx) ctx) (erased (String) tn) (erased (List (Raw)) ps) (erased (List (Raw)) ctors) (erased (List (Raw)) rest) (erased (Reason) r)
       (erased (ElabTele ctx (Nil (Maybe (Nat))) ps (TeleErr r)) ep) -> (MintTycons ctx (Cons (Raw) (RList (Cons (Raw) (RAtom tn) (Cons (Raw) (RList ps) ctors))) rest) (FErrT r)))
    (many MTyRestErr : (erased (Ctx) ctx) (erased (String) tn) (erased (List (Raw)) ps) (erased (List (Raw)) ctors) (erased (List (Raw)) rest) (erased (Ctx) ctxP) (erased (List (Entry)) pt) (erased (List (Nat)) pids) (erased (List (Maybe (String))) pn)
       (erased (Nat) tid) (erased (Ctx) ctx1) (erased (Reason) r)
       (erased (ElabTele ctx (Nil (Maybe (Nat))) ps (TeleOk ctxP pt pids pn)) ep) (erased (Mint ctx (Some (String) tn) (TTyCtor pt) (KDecl) (None (Term)) tid ctx1) m) (erased (MintTycons ctx1 rest (FErrT r)) q)
       -> (MintTycons ctx (Cons (Raw) (RList (Cons (Raw) (RAtom tn) (Cons (Raw) (RList ps) ctors))) rest) (FErrT r))))
  ((MintCtors : ((Ctx) ctx) ((List (Raw)) decls) ((List (Nat)) tids) ((FOutT) out) -> Type)
    enum
    (many MCNil : (erased (Ctx) ctx) -> (MintCtors ctx (Nil (Raw)) (Nil (Nat)) (FOkT ctx (Nil (Nat)))))
    (many MCCons : (erased (Ctx) ctx) (erased (String) tn) (erased (List (Raw)) ps) (erased (List (Raw)) ctors) (erased (List (Raw)) rest) (erased (Nat) tid) (erased (List (Nat)) tids)
       (erased (Term) tty) (erased (List (Entry)) pt) (erased (Nat) n) (erased (Ctx) ctx1) (erased (List (Nat)) cids) (erased (Ctx) ctx2) (erased (Ctx) out) (erased (List (Nat)) ids) (erased (List (Nat)) all)
       (erased (TypeOf ctx tid tty) t) (erased (CanonAt ctx tty (TTyCtor pt)) cn) (erased (Length (Entry) pt n) ln) (erased (MintDeclCtors ctx tid n ctors (FOkT ctx1 cids)) mc) (erased (AddAdt ctx1 (MkAdt tid cids) ctx2) aa)
       (erased (MintCtors ctx2 rest tids (FOkT out ids)) q) (erased (AppendNats (Cons (Nat) tid cids) ids all) ap)
       -> (MintCtors ctx (Cons (Raw) (RList (Cons (Raw) (RAtom tn) (Cons (Raw) (RList ps) ctors))) rest) (Cons (Nat) tid tids) (FOkT out all)))
    (many MCErr : (erased (Ctx) ctx) (erased (String) tn) (erased (List (Raw)) ps) (erased (List (Raw)) ctors) (erased (List (Raw)) rest) (erased (Nat) tid) (erased (List (Nat)) tids)
       (erased (Term) tty) (erased (List (Entry)) pt) (erased (Nat) n) (erased (Reason) r)
       (erased (TypeOf ctx tid tty) t) (erased (CanonAt ctx tty (TTyCtor pt)) cn) (erased (Length (Entry) pt n) ln) (erased (MintDeclCtors ctx tid n ctors (FErrT r)) mc)
       -> (MintCtors ctx (Cons (Raw) (RList (Cons (Raw) (RAtom tn) (Cons (Raw) (RList ps) ctors))) rest) (Cons (Nat) tid tids) (FErrT r)))
    (many MCRestErr : (erased (Ctx) ctx) (erased (String) tn) (erased (List (Raw)) ps) (erased (List (Raw)) ctors) (erased (List (Raw)) rest) (erased (Nat) tid) (erased (List (Nat)) tids)
       (erased (Term) tty) (erased (List (Entry)) pt) (erased (Nat) n) (erased (Ctx) ctx1) (erased (List (Nat)) cids) (erased (Ctx) ctx2) (erased (Reason) r)
       (erased (TypeOf ctx tid tty) t) (erased (CanonAt ctx tty (TTyCtor pt)) cn) (erased (Length (Entry) pt n) ln) (erased (MintDeclCtors ctx tid n ctors (FOkT ctx1 cids)) mc) (erased (AddAdt ctx1 (MkAdt tid cids) ctx2) aa)
       (erased (MintCtors ctx2 rest tids (FErrT r)) q)
       -> (MintCtors ctx (Cons (Raw) (RList (Cons (Raw) (RAtom tn) (Cons (Raw) (RList ps) ctors))) rest) (Cons (Nat) tid tids) (FErrT r))))
  ; A declaration's constructors: (C (fields) ret), the return the declaration's own type constructor applied
  ; to as many arguments as it has parameters (section 21).
  ((MintDeclCtors : ((Ctx) ctx) ((Nat) tid) ((Nat) n) ((List (Raw)) ctors) ((FOutT) out) -> Type)
    enum
    (many MDNil : (erased (Ctx) ctx) (erased (Nat) tid) (erased (Nat) n) -> (MintDeclCtors ctx tid n (Nil (Raw)) (FOkT ctx (Nil (Nat)))))
    (many MDCons : (erased (Ctx) ctx) (erased (Nat) tid) (erased (Nat) n) (erased (String) cn) (erased (List (Raw)) fs) (erased (Raw) rr) (erased (List (Raw)) rest)
       (erased (Ctx) ctxF) (erased (List (Entry)) ft) (erased (List (Nat)) fids) (erased (List (Maybe (String))) fn) (erased (Term) ret) (erased (Term) rty) (erased (List (Entry)) tps) (erased (List (Term)) args) (erased (List (Maybe (Nat))) acc) (erased (Term) ret2)
       (erased (Nat) cid) (erased (Ctx) ctx1) (erased (Ctx) out) (erased (List (Nat)) cids)
       (erased (ElabTele ctx (Nil (Maybe (Nat))) fs (TeleOk ctxF ft fids fn)) ef) (erased (ElabTerm ctxF rr (TOk ret rty)) er) (erased (CanonAt ctxF ret (TyApp (Ref tid) tps args)) cr) (erased (Length (Term) args n) ln)
       (erased (Binders fids acc) b) (erased (Abstract acc ret ret2) ab) (erased (Mint ctx (Some (String) cn) (TValCtor ft ret2) (KDecl) (None (Term)) cid ctx1) m) (erased (MintDeclCtors ctx1 tid n rest (FOkT out cids)) q)
       -> (MintDeclCtors ctx tid n (Cons (Raw) (RList (Cons (Raw) (RAtom cn) (Cons (Raw) (RList fs) (Cons (Raw) rr (Nil (Raw)))))) rest) (FOkT out (Cons (Nat) cid cids))))
    (many MDFieldsErr : (erased (Ctx) ctx) (erased (Nat) tid) (erased (Nat) n) (erased (String) cn) (erased (List (Raw)) fs) (erased (Raw) rr) (erased (List (Raw)) rest) (erased (Reason) r)
       (erased (ElabTele ctx (Nil (Maybe (Nat))) fs (TeleErr r)) ef) -> (MintDeclCtors ctx tid n (Cons (Raw) (RList (Cons (Raw) (RAtom cn) (Cons (Raw) (RList fs) (Cons (Raw) rr (Nil (Raw)))))) rest) (FErrT r)))
    (many MDRetErr : (erased (Ctx) ctx) (erased (Nat) tid) (erased (Nat) n) (erased (String) cn) (erased (List (Raw)) fs) (erased (Raw) rr) (erased (List (Raw)) rest)
       (erased (Ctx) ctxF) (erased (List (Entry)) ft) (erased (List (Nat)) fids) (erased (List (Maybe (String))) fn) (erased (Reason) r)
       (erased (ElabTele ctx (Nil (Maybe (Nat))) fs (TeleOk ctxF ft fids fn)) ef) (erased (ElabTerm ctxF rr (TErr r)) er)
       -> (MintDeclCtors ctx tid n (Cons (Raw) (RList (Cons (Raw) (RAtom cn) (Cons (Raw) (RList fs) (Cons (Raw) rr (Nil (Raw)))))) rest) (FErrT r)))
    (many MDBadRet : (erased (Ctx) ctx) (erased (Nat) tid) (erased (Nat) n) (erased (String) cn) (erased (List (Raw)) fs) (erased (Raw) rr) (erased (List (Raw)) rest)
       (erased (Ctx) ctxF) (erased (List (Entry)) ft) (erased (List (Nat)) fids) (erased (List (Maybe (String))) fn) (erased (Term) ret) (erased (Term) rty) (erased (Term) c)
       (erased (ElabTele ctx (Nil (Maybe (Nat))) fs (TeleOk ctxF ft fids fn)) ef) (erased (ElabTerm ctxF rr (TOk ret rty)) er) (erased (CanonAt ctxF ret c) cr) (erased (BadRet ctxF tid n c) br)
       -> (MintDeclCtors ctx tid n (Cons (Raw) (RList (Cons (Raw) (RAtom cn) (Cons (Raw) (RList fs) (Cons (Raw) rr (Nil (Raw)))))) rest) (FErrT (RBadReturn))))
    (many MDRestErr : (erased (Ctx) ctx) (erased (Nat) tid) (erased (Nat) n) (erased (String) cn) (erased (List (Raw)) fs) (erased (Raw) rr) (erased (List (Raw)) rest)
       (erased (Ctx) ctxF) (erased (List (Entry)) ft) (erased (List (Nat)) fids) (erased (List (Maybe (String))) fn) (erased (Term) ret) (erased (Term) rty) (erased (List (Entry)) tps) (erased (List (Term)) args) (erased (List (Maybe (Nat))) acc) (erased (Term) ret2)
       (erased (Nat) cid) (erased (Ctx) ctx1) (erased (Reason) r)
       (erased (ElabTele ctx (Nil (Maybe (Nat))) fs (TeleOk ctxF ft fids fn)) ef) (erased (ElabTerm ctxF rr (TOk ret rty)) er) (erased (CanonAt ctxF ret (TyApp (Ref tid) tps args)) cr) (erased (Length (Term) args n) ln)
       (erased (Binders fids acc) b) (erased (Abstract acc ret ret2) ab) (erased (Mint ctx (Some (String) cn) (TValCtor ft ret2) (KDecl) (None (Term)) cid ctx1) m) (erased (MintDeclCtors ctx1 tid n rest (FErrT r)) q)
       -> (MintDeclCtors ctx tid n (Cons (Raw) (RList (Cons (Raw) (RAtom cn) (Cons (Raw) (RList fs) (Cons (Raw) rr (Nil (Raw)))))) rest) (FErrT r))))
  ((BadRet : ((Ctx) ctx) ((Nat) tid) ((Nat) n) ((Term) c) -> Type)
    enum
    (many BRNotApp : (erased (Ctx) ctx) (erased (Nat) tid) (erased (Nat) n) (erased (Term) c) (erased (NotTyApp c) na) -> (BadRet ctx tid n c))
    (many BRHead : (erased (Ctx) ctx) (erased (Nat) tid) (erased (Nat) n) (erased (Term) h) (erased (List (Entry)) hps) (erased (List (Term)) as) (erased (Differ ctx h (Ref tid)) d) -> (BadRet ctx tid n (TyApp h hps as)))
    (many BRArity : (erased (Ctx) ctx) (erased (Nat) tid) (erased (Nat) n) (erased (Term) h) (erased (List (Entry)) hps) (erased (List (Term)) as) (erased (NotLen n as) nl) -> (BadRet ctx tid n (TyApp h hps as))))
  ((AppendNats : ((List (Nat)) xs) ((List (Nat)) ys) ((List (Nat)) out) -> Type)
    enum
    (many AppendNil : (erased (List (Nat)) ys) -> (AppendNats (Nil (Nat)) ys ys))
    (many AppendCons : (erased (Nat) x) (erased (List (Nat)) xs) (erased (List (Nat)) ys) (erased (List (Nat)) out) (erased (AppendNats xs ys out) p) -> (AppendNats (Cons (Nat) x xs) ys (Cons (Nat) x out)))))

; ---- A program: its items as a body in the initial context, of size one (section 27).
(def-adts
  ((POut : -> Type)
    enum
    (many POk : (many (Core) core) (many (Term) ty) -> (POut))
    (many PErr : (many (Reason) r) -> (POut)))
  ((ElabProgram : ((List (Raw)) items) ((POut) out) -> Type)
    enum
    (many ProgramOk : (erased (List (Raw)) items) (erased (Ctx) ctx) (erased (Core) core) (erased (Nat) x) (erased (Term) ty)
       (erased (ElabBody init-ctx items (EOk ctx core (Cons (Nat) x (Nil (Nat))))) p) (erased (TypeOf ctx x ty) t) -> (ElabProgram items (POk core ty)))
    (many ProgramSize : (erased (List (Raw)) items) (erased (Ctx) ctx) (erased (Core) core) (erased (List (Nat)) ids) (erased (ElabBody init-ctx items (EOk ctx core ids)) p) (erased (NotOne ids) n)
       -> (ElabProgram items (PErr (RSize))))
    (many ProgramErr : (erased (List (Raw)) items) (erased (Reason) r) (erased (ElabBody init-ctx items (EErr r)) p) -> (ElabProgram items (PErr r)))))

; A program fails when it elaborates to an error: the positive record of why it is refused.
(def-adts
  ((Fails : ((List (Raw)) items) ((Reason) r) -> Type)
    enum
    (many FailsBy : (erased (List (Raw)) items) (erased (Reason) r) (erased (ElabProgram items (PErr r)) p) -> (Fails items r))))

(MkUnit)
