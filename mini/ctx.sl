; mini/ctx.sl -- the scope environment and fact table of DESIGN.md sections 5 and 7 for the minimal
; language: entries with a type and a kind, names, the declared ADTs, and the rules of mini/canon.sl, in one
; record with the ambient level and subterm arguments. Lookups come with evidence. One session's proposal.

; An entry's kind: [KDecl] is a type or value constructor declared by def-adts or built in, rigid for
; unification; [KLevel] an entry def-lvl minted (section 18's marker).
(def-adts
  ((Kind : -> Type)
    enum
    (many KPlain : -> (Kind))
    (many KLevel : -> (Kind))
    (many KDecl : -> (Kind)))
  ((Ent : -> Type)
    enum
    (many MkEnt : (many (Nat) id) (many (Term) ty) (many (Kind) kind) -> (Ent)))
  ((Name : -> Type)
    enum
    (many MkName : (many (String) name) (many (Nat) id) -> (Name)))
  ((Adt : -> Type)
    enum
    (many MkAdt : (many (Nat) tycon) (many (List (Nat)) ctors) -> (Adt)))
  ; [next] is the first unused id: ids are never reused, so leaving a scope restores the lists and keeps it.
  ; [level] is the current function's level, or [None] at the top level (section 20); [subargs] the
  ; enclosing function's subterm-marked parameters (section 5).
  ((Ctx : -> Type)
    enum
    (many MkCtx : (many (Nat) next) (many (List (Name)) scope) (many (List (Ent)) ents) (many (List (Rule)) rules) (many (List (Adt)) adts)
       (many (Maybe (Term)) level) (many (List (Term)) subargs) -> (Ctx))))

(def-adts
  ((EntOf : ((List (Ent)) ents) ((Nat) x) ((Term) ty) ((Kind) k) -> Type)
    enum
    (many EntHere : (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (List (Ent)) rest) -> (EntOf (Cons (Ent) (MkEnt x ty k) rest) x ty k))
    (many EntThere : (erased (Nat) x) (erased (Nat) y) (erased (Term) ty) (erased (Term) ty2) (erased (Kind) k) (erased (Kind) k2) (erased (List (Ent)) rest)
       (erased (Neq x y) n) (erased (EntOf rest x ty k) p) -> (EntOf (Cons (Ent) (MkEnt y ty2 k2) rest) x ty k)))
  ((NoEnt : ((List (Ent)) ents) ((Nat) x) -> Type)
    enum
    (many NoEntNil : (erased (Nat) x) -> (NoEnt (Nil (Ent)) x))
    (many NoEntCons : (erased (Nat) x) (erased (Nat) y) (erased (Term) ty2) (erased (Kind) k2) (erased (List (Ent)) rest) (erased (Neq x y) n) (erased (NoEnt rest x) p)
       -> (NoEnt (Cons (Ent) (MkEnt y ty2 k2) rest) x)))
  ((EntDec : ((List (Ent)) ents) ((Nat) x) -> Type)
    enum
    (many EntHit : (erased (List (Ent)) ents) (erased (Nat) x) (many (Term) ty) (many (Kind) k) (erased (EntOf ents x ty k) p) -> (EntDec ents x))
    (many EntMiss : (erased (List (Ent)) ents) (erased (Nat) x) (erased (NoEnt ents x) p) -> (EntDec ents x))))

(def-fns _ $ (many ent-dec : (subterm many (List (Ent)) ents) (many (Nat) x) -> (many (EntDec ents x) r))
  (let-match many ents (Cons _ e rest) ((Nil _) (EntMiss _ _ $ NoEntNil x)))
  (let-match many e (MkEnt y ty2 k2))
  (let-match many (nat-dec x y) (NDDiff _ _ n) ((NDSame _) (EntHit _ _ ty2 k2 $ EntHere x ty2 k2 rest)))
  (match many (notail $ ent-dec rest x) _
    ((EntHit _ _ ty k p) (EntHit _ _ ty k $ EntThere x y ty ty2 k k2 rest n p))
    ((EntMiss _ _ p) (EntMiss _ _ $ NoEntCons x y ty2 k2 rest n p))))

(def-adts
  ((StrNeq : ((String) a) ((String) b) -> Type)
    enum
    (many StrNeqLt : (erased (String) a) (erased (String) b) (erased (StrLt a b) p) -> (StrNeq a b))
    (many StrNeqGt : (erased (String) a) (erased (String) b) (erased (StrLt b a) p) -> (StrNeq a b)))
  ((NameOf : ((List (Name)) scope) ((String) s) ((Nat) x) -> Type)
    enum
    (many NameHere : (erased (String) s) (erased (Nat) x) (erased (List (Name)) rest) -> (NameOf (Cons (Name) (MkName s x) rest) s x))
    (many NameThere : (erased (String) s) (erased (String) s2) (erased (Nat) x) (erased (Nat) y) (erased (List (Name)) rest) (erased (StrNeq s s2) n) (erased (NameOf rest s x) p)
       -> (NameOf (Cons (Name) (MkName s2 y) rest) s x)))
  ((NoName : ((List (Name)) scope) ((String) s) -> Type)
    enum
    (many NoNameNil : (erased (String) s) -> (NoName (Nil (Name)) s))
    (many NoNameCons : (erased (String) s) (erased (String) s2) (erased (Nat) y) (erased (List (Name)) rest) (erased (StrNeq s s2) n) (erased (NoName rest s) p)
       -> (NoName (Cons (Name) (MkName s2 y) rest) s)))
  ((NameDec : ((List (Name)) scope) ((String) s) -> Type)
    enum
    (many NameHit : (erased (List (Name)) scope) (erased (String) s) (many (Nat) x) (erased (NameOf scope s x) p) -> (NameDec scope s))
    (many NameMiss : (erased (List (Name)) scope) (erased (String) s) (erased (NoName scope s) p) -> (NameDec scope s))))

(def-fns _ $ (many name-dec : (subterm many (List (Name)) scope) (many (String) s) -> (many (NameDec scope s) r))
  (let-match many scope (Cons _ e rest) ((Nil _) (NameMiss _ _ $ NoNameNil s)))
  (let-match many e (MkName s2 y))
  (match many (str-cmp s s2) _
    ((CEq _ _ _) (NameHit _ _ y $ NameHere s y rest))
    ((CLt _ _ _ _ p)
      (match many (notail $ name-dec rest s) _
        ((NameHit _ _ x q) (NameHit _ _ x $ NameThere s s2 x y rest (StrNeqLt s s2 p) q))
        ((NameMiss _ _ q) (NameMiss _ _ $ NoNameCons s s2 y rest (StrNeqLt s s2 p) q))))
    ((CGt _ _ _ _ p)
      (match many (notail $ name-dec rest s) _
        ((NameHit _ _ x q) (NameHit _ _ x $ NameThere s s2 x y rest (StrNeqGt s s2 p) q))
        ((NameMiss _ _ q) (NameMiss _ _ $ NoNameCons s s2 y rest (StrNeqGt s s2 p) q))))))

; The constructors a declared type constructor has, or evidence that none was declared, which is what
; makes a type unmatchable (MINIMAL.md's rule for match).
(def-adts
  ((AdtOf : ((List (Adt)) adts) ((Nat) t) ((List (Nat)) ctors) -> Type)
    enum
    (many AdtHere : (erased (Nat) t) (erased (List (Nat)) ctors) (erased (List (Adt)) rest) -> (AdtOf (Cons (Adt) (MkAdt t ctors) rest) t ctors))
    (many AdtThere : (erased (Nat) t) (erased (Nat) t2) (erased (List (Nat)) ctors) (erased (List (Nat)) ctors2) (erased (List (Adt)) rest) (erased (Neq t t2) n) (erased (AdtOf rest t ctors) p)
       -> (AdtOf (Cons (Adt) (MkAdt t2 ctors2) rest) t ctors)))
  ((NoAdt : ((List (Adt)) adts) ((Nat) t) -> Type)
    enum
    (many NoAdtNil : (erased (Nat) t) -> (NoAdt (Nil (Adt)) t))
    (many NoAdtCons : (erased (Nat) t) (erased (Nat) t2) (erased (List (Nat)) ctors2) (erased (List (Adt)) rest) (erased (Neq t t2) n) (erased (NoAdt rest t) p)
       -> (NoAdt (Cons (Adt) (MkAdt t2 ctors2) rest) t)))
  ((AdtDec : ((List (Adt)) adts) ((Nat) t) -> Type)
    enum
    (many AdtHit : (erased (List (Adt)) adts) (erased (Nat) t) (many (List (Nat)) ctors) (erased (AdtOf adts t ctors) p) -> (AdtDec adts t))
    (many AdtMiss : (erased (List (Adt)) adts) (erased (Nat) t) (erased (NoAdt adts t) p) -> (AdtDec adts t))))

(def-fns _ $ (many adt-dec : (subterm many (List (Adt)) adts) (many (Nat) t) -> (many (AdtDec adts t) r))
  (let-match many adts (Cons _ e rest) ((Nil _) (AdtMiss _ _ $ NoAdtNil t)))
  (let-match many e (MkAdt t2 ctors2))
  (let-match many (nat-dec t t2) (NDDiff _ _ n) ((NDSame _) (AdtHit _ _ ctors2 $ AdtHere t ctors2 rest)))
  (match many (notail $ adt-dec rest t) _
    ((AdtHit _ _ ctors p) (AdtHit _ _ ctors $ AdtThere t t2 ctors ctors2 rest n p))
    ((AdtMiss _ _ p) (AdtMiss _ _ $ NoAdtCons t t2 ctors2 rest n p))))


; ---- Scope of terms: every entry a term mentions is one of the context's entries, and every binder it
; mentions is one of the [d] it sits under; [ScopedTele ents d es out] threads the depth through a telescope
; and gives the depth after it. Substitution, abstraction and canonicalization keep it, and it weakens to a
; context with more entries and to a deeper position.
(def-adts
  ((HasEnt : ((List (Ent)) ents) ((Nat) x) -> Type)
    enum
    (many HEHere : (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (List (Ent)) rest) -> (HasEnt (Cons (Ent) (MkEnt x ty k) rest) x))
    (many HEThere : (erased (Nat) x) (erased (Ent) e) (erased (List (Ent)) rest) (erased (HasEnt rest x) p) -> (HasEnt (Cons (Ent) e rest) x)))
  ((Scoped : ((List (Ent)) ents) ((Nat) d) ((Term) t) -> Type)
    enum
    (many ScRef : (erased (List (Ent)) ents) (erased (Nat) d) (erased (Nat) x) (erased (HasEnt ents x) p) -> (Scoped ents d (Ref x)))
    (many ScBound : (erased (List (Ent)) ents) (erased (Nat) d) (erased (Nat) k) (erased (Lt k d) p) -> (Scoped ents d (Bound k)))
    (many ScTyApp : (erased (List (Ent)) ents) (erased (Nat) d) (erased (Term) h) (erased (List (Entry)) ps) (erased (List (Term)) as) (erased (Nat) out)
       (erased (Scoped ents d h) p) (erased (ScopedTele ents d ps out) t) (erased (ScopedList ents d as) q) (erased (LenEq (Term) (Entry) as ps) n) -> (Scoped ents d (TyApp h ps as)))
    (many ScValApp : (erased (List (Ent)) ents) (erased (Nat) d) (erased (Term) h) (erased (List (Entry)) ps) (erased (Term) r) (erased (List (Term)) as) (erased (Nat) out)
       (erased (Scoped ents d h) p) (erased (ScopedTele ents d ps out) t) (erased (Scoped ents out r) pr) (erased (ScopedList ents d as) q) (erased (LenEq (Term) (Entry) as ps) n) -> (Scoped ents d (ValApp h ps r as)))
    (many ScUniv : (erased (List (Ent)) ents) (erased (Nat) d) -> (Scoped ents d (TUniv)))
    (many ScFn : (erased (List (Ent)) ents) (erased (Nat) d) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs) (erased (Nat) d1) (erased (Nat) d2)
       (erased (Scoped ents d l) p) (erased (ScopedTele ents d ps d1) q) (erased (ScopedTele ents d1 rs d2) r) -> (Scoped ents d (TFn l ps rs)))
    (many ScTyCtor : (erased (List (Ent)) ents) (erased (Nat) d) (erased (List (Entry)) ps) (erased (Nat) d1) (erased (ScopedTele ents d ps d1) q) -> (Scoped ents d (TTyCtor ps)))
    (many ScValCtor : (erased (List (Ent)) ents) (erased (Nat) d) (erased (List (Entry)) ps) (erased (Term) r) (erased (Nat) d1) (erased (ScopedTele ents d ps d1) q) (erased (Scoped ents d1 r) p)
       -> (Scoped ents d (TValCtor ps r))))
  ((ScopedList : ((List (Ent)) ents) ((Nat) d) ((List (Term)) ts) -> Type)
    enum
    (many ScNil : (erased (List (Ent)) ents) (erased (Nat) d) -> (ScopedList ents d (Nil (Term))))
    (many ScCons : (erased (List (Ent)) ents) (erased (Nat) d) (erased (Term) t) (erased (List (Term)) ts) (erased (Scoped ents d t) p) (erased (ScopedList ents d ts) q)
       -> (ScopedList ents d (Cons (Term) t ts))))
  ((ScopedTele : ((List (Ent)) ents) ((Nat) d) ((List (Entry)) es) ((Nat) out) -> Type)
    enum
    (many ScTNil : (erased (List (Ent)) ents) (erased (Nat) d) -> (ScopedTele ents d (Nil (Entry)) d))
    (many ScTCons : (erased (List (Ent)) ents) (erased (Nat) d) (erased (Bool) s) (erased (Bool) i) (erased (Term) t) (erased (List (Entry)) es) (erased (Nat) out)
       (erased (Scoped ents d t) p) (erased (ScopedTele ents (Succ d) es out) q) -> (ScopedTele ents d (Cons (Entry) (MkEntry s i t) es) out)))
  ; The terms a substitution or a rule holds are closed.
  ((ScopedSub : ((List (Ent)) ents) ((List (Maybe (Term))) subs) -> Type)
    enum
    (many ScSNil : (erased (List (Ent)) ents) -> (ScopedSub ents (Nil (Maybe (Term)))))
    (many ScSNone : (erased (List (Ent)) ents) (erased (List (Maybe (Term))) rest) (erased (ScopedSub ents rest) q) -> (ScopedSub ents (Cons (Maybe (Term)) (None (Term)) rest)))
    (many ScSSome : (erased (List (Ent)) ents) (erased (Term) t) (erased (List (Maybe (Term))) rest) (erased (Scoped ents (Zero) t) p) (erased (ScopedSub ents rest) q)
       -> (ScopedSub ents (Cons (Maybe (Term)) (Some (Term) t) rest))))
  ((ScopedRules : ((List (Ent)) ents) ((List (Rule)) rules) -> Type)
    enum
    (many SRNil : (erased (List (Ent)) ents) -> (ScopedRules ents (Nil (Rule))))
    (many SRCons : (erased (List (Ent)) ents) (erased (Nat) x) (erased (Term) r) (erased (List (Rule)) rest) (erased (Scoped ents (Zero) r) p) (erased (ScopedRules ents rest) q)
       -> (ScopedRules ents (Cons (Rule) (MkRule x r) rest)))))

; Substitution, abstraction and canonicalization keep an application's arity.
(def-fns _ $ (erased subst-len-eq : (erased (List (Maybe (Term))) subs) (erased (List (Maybe (Term))) sub2) (erased (List (Term)) as) (erased (List (Term)) as2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2)
    (erased (List (Maybe (Term))) out) (erased (SubstList subs as as2) q) (erased (SubstTele sub2 ps ps2 out) t) (subterm erased (LenEq (Term) (Entry) as ps) n) -> (erased (LenEq (Term) (Entry) as2 ps2) m))
  (let-match erased n (LECons _ _ _ _ xs ys n2)
    ((LENil _ _)
      (let-match erased q (SubNil _))
      (match erased t _ ((SubTNil _) (LENil _ _)))))
  (let-match erased q (SubCons _ _ u _ us _ q2))
  (match erased t _ ((SubTCons _ s i _ u2 _ fs out2 _ t2) (LECons _ _ u (MkEntry s i u2) us fs (subst-len-eq subs (Cons _ (None _) sub2) xs us ys fs out2 q2 t2 n2)))))
(def-fns _ $ (erased abstract-len-eq : (erased (List (Maybe (Nat))) ids) (erased (List (Maybe (Nat))) ids2) (erased (List (Term)) as) (erased (List (Term)) as2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2)
    (erased (List (Maybe (Nat))) out) (erased (AbstractList ids as as2) q) (erased (AbstractTele ids2 ps ps2 out) t) (subterm erased (LenEq (Term) (Entry) as ps) n) -> (erased (LenEq (Term) (Entry) as2 ps2) m))
  (let-match erased n (LECons _ _ _ _ xs ys n2)
    ((LENil _ _)
      (let-match erased q (AbsNil _))
      (match erased t _ ((AbsTNil _) (LENil _ _)))))
  (let-match erased q (AbsCons _ _ u _ us _ q2))
  (match erased t _ ((AbsTCons _ s i _ u2 _ fs out2 _ t2) (LECons _ _ u (MkEntry s i u2) us fs (abstract-len-eq ids (Cons _ (None _) ids2) xs us ys fs out2 q2 t2 n2)))))
(def-fns _ $ (erased canon-len-eq : (erased (List (Rule)) rules) (erased (List (Term)) as) (erased (List (Term)) as2) (erased (List (Entry)) ps) (erased (CanonList rules as as2) q) (subterm erased (LenEq (Term) (Entry) as ps) n) ->
    (erased (LenEq (Term) (Entry) as2 ps) m))
  (match erased n _
    ((LENil _ _) (match erased q _ ((CanNil _) (LENil _ _))))
    ((LECons _ _ _ y xs ys n2) (match erased q _ ((CanCons _ _ u _ us _ q2) (LECons _ _ u y us ys (canon-len-eq rules xs us ys q2 n2)))))))

(def-fns _
  ((erased scoped-weaken : (erased (List (Ent)) ents) (erased (Ent) e) (erased (Nat) d) (erased (Term) t) (subterm erased (Scoped ents d t) b) -> (erased (Scoped (Cons (Ent) e ents) d t) c))
    (match erased b _
      ((ScRef _ _ x p) (ScRef _ d x (HEThere x e ents p)))
      ((ScBound _ _ k p) (ScBound _ d k p))
      ((ScTyApp _ _ h ps as out p t3 q n) (ScTyApp _ d h ps as out (scoped-weaken ents e d h p) (scoped-weaken-tele ents e d ps out t3) (scoped-weaken-list ents e d as q) n))
      ((ScValApp _ _ h ps r as out p t3 pr q n) (ScValApp _ d h ps r as out (scoped-weaken ents e d h p) (scoped-weaken-tele ents e d ps out t3) (scoped-weaken ents e out r pr) (scoped-weaken-list ents e d as q) n))
      ((ScUniv _ _) (ScUniv _ d))
      ((ScFn _ _ l ps rs d1 d2 p q r) (ScFn _ d l ps rs d1 d2 (scoped-weaken ents e d l p) (scoped-weaken-tele ents e d ps d1 q) (scoped-weaken-tele ents e d1 rs d2 r)))
      ((ScTyCtor _ _ ps d1 q) (ScTyCtor _ d ps d1 (scoped-weaken-tele ents e d ps d1 q)))
      ((ScValCtor _ _ ps r d1 q p) (ScValCtor _ d ps r d1 (scoped-weaken-tele ents e d ps d1 q) (scoped-weaken ents e d1 r p)))))
  ((erased scoped-weaken-list : (erased (List (Ent)) ents) (erased (Ent) e) (erased (Nat) d) (erased (List (Term)) ts) (subterm erased (ScopedList ents d ts) b) -> (erased (ScopedList (Cons (Ent) e ents) d ts) c))
    (match erased b _
      ((ScNil _ _) (ScNil _ d))
      ((ScCons _ _ t ts2 p q) (ScCons _ d t ts2 (scoped-weaken ents e d t p) (scoped-weaken-list ents e d ts2 q)))))
  ((erased scoped-weaken-tele : (erased (List (Ent)) ents) (erased (Ent) e) (erased (Nat) d) (erased (List (Entry)) es) (erased (Nat) out) (subterm erased (ScopedTele ents d es out) b) ->
      (erased (ScopedTele (Cons (Ent) e ents) d es out) c))
    (match erased b _
      ((ScTNil _ _) (ScTNil _ d))
      ((ScTCons _ _ s i t es2 _ p q) (ScTCons _ d s i t es2 out (scoped-weaken ents e d t p) (scoped-weaken-tele ents e (Succ d) es2 out q))))))

(def-fns _ $ (erased scoped-weaken-sub : (erased (List (Ent)) ents) (erased (Ent) e) (erased (List (Maybe (Term))) subs) (subterm erased (ScopedSub ents subs) b) -> (erased (ScopedSub (Cons (Ent) e ents) subs) c))
  (match erased b _
    ((ScSNil _) (ScSNil _))
    ((ScSNone _ rest q) (ScSNone _ rest (scoped-weaken-sub ents e rest q)))
    ((ScSSome _ t rest p q) (ScSSome _ t rest (scoped-weaken ents e (Zero) t p) (scoped-weaken-sub ents e rest q)))))

(def-fns _ $ (erased scoped-rules-weaken : (erased (List (Ent)) ents) (erased (Ent) e) (erased (List (Rule)) rules) (subterm erased (ScopedRules ents rules) b) -> (erased (ScopedRules (Cons (Ent) e ents) rules) c))
  (match erased b _
    ((SRNil _) (SRNil _))
    ((SRCons _ x r rest p q) (SRCons _ x r rest (scoped-weaken ents e (Zero) r p) (scoped-rules-weaken ents e rest q)))))

; Deeper is weaker: a term scoped under [d] binders is scoped under any [d2] at or above it.
(def-fns _
  ((erased scoped-mono : (erased (List (Ent)) ents) (erased (Nat) d) (erased (Nat) d2) (erased (Term) t) (erased (Lt d (Succ d2)) le) (subterm erased (Scoped ents d t) b) -> (erased (Scoped ents d2 t) c))
    (match erased b _
      ((ScRef _ _ x p) (ScRef ents d2 x p))
      ((ScBound _ _ k p) (ScBound ents d2 k (lt-le k d d2 p le)))
      ((ScTyApp _ _ h ps as out p t3 q n)
        (let ((erased o2) (erased _) (erased t2)) (scoped-mono-tele ents d d2 ps out le t3))
        (ScTyApp ents d2 h ps as o2 (scoped-mono ents d d2 h le p) t2 (scoped-mono-list ents d d2 as le q) n))
      ((ScValApp _ _ h ps r as out p t3 pr q n)
        (let ((erased o2) (erased le2) (erased t2)) (scoped-mono-tele ents d d2 ps out le t3))
        (ScValApp ents d2 h ps r as o2 (scoped-mono ents d d2 h le p) t2 (scoped-mono ents out o2 r le2 pr) (scoped-mono-list ents d d2 as le q) n))
      ((ScUniv _ _) (ScUniv ents d2))
      ((ScFn _ _ l ps rs d1 dd2 p q r)
        (let ((erased e1) (erased le1) (erased q2)) (scoped-mono-tele ents d d2 ps d1 le q))
        (let ((erased e2) (erased _) (erased r2)) (scoped-mono-tele ents d1 e1 rs dd2 le1 r))
        (ScFn ents d2 l ps rs e1 e2 (scoped-mono ents d d2 l le p) q2 r2))
      ((ScTyCtor _ _ ps d1 q)
        (let ((erased e1) (erased _) (erased q2)) (scoped-mono-tele ents d d2 ps d1 le q))
        (ScTyCtor ents d2 ps e1 q2))
      ((ScValCtor _ _ ps r d1 q p)
        (let ((erased e1) (erased le1) (erased q2)) (scoped-mono-tele ents d d2 ps d1 le q))
        (ScValCtor ents d2 ps r e1 q2 (scoped-mono ents d1 e1 r le1 p)))))
  ((erased scoped-mono-list : (erased (List (Ent)) ents) (erased (Nat) d) (erased (Nat) d2) (erased (List (Term)) ts) (erased (Lt d (Succ d2)) le) (subterm erased (ScopedList ents d ts) b) -> (erased (ScopedList ents d2 ts) c))
    (match erased b _
      ((ScNil _ _) (ScNil ents d2))
      ((ScCons _ _ t ts2 p q) (ScCons ents d2 t ts2 (scoped-mono ents d d2 t le p) (scoped-mono-list ents d d2 ts2 le q)))))
  ((erased scoped-mono-tele : (erased (List (Ent)) ents) (erased (Nat) d) (erased (Nat) d2) (erased (List (Entry)) es) (erased (Nat) out) (erased (Lt d (Succ d2)) le) (subterm erased (ScopedTele ents d es out) b) ->
      (erased (Nat) out2) (erased (Lt out (Succ out2)) le2) (erased (ScopedTele ents d2 es out2) c))
    (let-match erased b (ScTCons _ _ s i t es2 _ p q) ((ScTNil _ _) (values d2 le (ScTNil ents d2))))
    (let ((erased out2) (erased le2) (erased q2)) (scoped-mono-tele ents (Succ d) (Succ d2) es2 out (LtS d (Succ d2) le) q))
    (values out2 le2 (ScTCons ents d2 s i t es2 out2 (scoped-mono ents d d2 t le p) q2))))

; Scoped under [d] binders means closed under them, and scoped anywhere and closed under [d2] means scoped
; under [d2].
(def-fns _
  ((erased scoped-closed : (erased (List (Ent)) ents) (erased (Nat) d) (erased (Term) t) (subterm erased (Scoped ents d t) b) -> (erased (Closed d t) c))
    (match erased b _
      ((ScRef _ _ x _) (ClRef d x))
      ((ScBound _ _ k p) (ClBound d k p))
      ((ScTyApp _ _ h ps as out p t3 q _) (ClTyApp d h ps as out (scoped-closed ents d h p) (scoped-closed-tele ents d ps out t3) (scoped-closed-list ents d as q)))
      ((ScValApp _ _ h ps r as out p t3 pr q _) (ClValApp d h ps r as out (scoped-closed ents d h p) (scoped-closed-tele ents d ps out t3) (scoped-closed ents out r pr) (scoped-closed-list ents d as q)))
      ((ScUniv _ _) (ClUniv d))
      ((ScFn _ _ l ps rs d1 d2 p q r) (ClFn d l ps rs d1 d2 (scoped-closed ents d l p) (scoped-closed-tele ents d ps d1 q) (scoped-closed-tele ents d1 rs d2 r)))
      ((ScTyCtor _ _ ps d1 q) (ClTyCtor d ps d1 (scoped-closed-tele ents d ps d1 q)))
      ((ScValCtor _ _ ps r d1 q p) (ClValCtor d ps r d1 (scoped-closed-tele ents d ps d1 q) (scoped-closed ents d1 r p)))))
  ((erased scoped-closed-list : (erased (List (Ent)) ents) (erased (Nat) d) (erased (List (Term)) ts) (subterm erased (ScopedList ents d ts) b) -> (erased (ClosedList d ts) c))
    (match erased b _
      ((ScNil _ _) (ClNil d))
      ((ScCons _ _ t ts2 p q) (ClCons d t ts2 (scoped-closed ents d t p) (scoped-closed-list ents d ts2 q)))))
  ((erased scoped-closed-tele : (erased (List (Ent)) ents) (erased (Nat) d) (erased (List (Entry)) es) (erased (Nat) out) (subterm erased (ScopedTele ents d es out) b) -> (erased (ClosedTele d es out) c))
    (match erased b _
      ((ScTNil _ _) (ClTNil d))
      ((ScTCons _ _ s i t es2 _ p q) (ClTCons d s i t es2 out (scoped-closed ents d t p) (scoped-closed-tele ents (Succ d) es2 out q))))))
(def-fns _
  ((erased scoped-tighten : (erased (List (Ent)) ents) (erased (Nat) d) (erased (Nat) d2) (erased (Term) t) (erased (Scoped ents d t) b) (subterm erased (Closed d2 t) c) -> (erased (Scoped ents d2 t) s))
    (match erased c _
      ((ClRef _ x) (match erased b _ ((ScRef _ _ _ p) (ScRef ents d2 x p))))
      ((ClBound _ k p) (ScBound ents d2 k p))
      ((ClTyApp _ h ps as e1 p t3 q)
        (match erased b _ ((ScTyApp _ _ _ _ _ out0 bh bt bas n) (ScTyApp ents d2 h ps as e1 (scoped-tighten ents d d2 h bh p) (scoped-tighten-tele ents d d2 ps out0 e1 bt t3) (scoped-tighten-list ents d d2 as bas q) n))))
      ((ClValApp _ h ps r as e1 p t3 pr q)
        (match erased b _
          ((ScValApp _ _ _ _ _ _ out0 bh bt br bas n)
            (ScValApp ents d2 h ps r as e1 (scoped-tighten ents d d2 h bh p) (scoped-tighten-tele ents d d2 ps out0 e1 bt t3) (scoped-tighten ents out0 e1 r br pr) (scoped-tighten-list ents d d2 as bas q) n))))
      ((ClUniv _) (ScUniv ents d2))
      ((ClFn _ l ps rs e1 e2 p q r)
        (match erased b _
          ((ScFn _ _ _ _ _ d1 dd2 bl bps brs)
            (ScFn ents d2 l ps rs e1 e2 (scoped-tighten ents d d2 l bl p) (scoped-tighten-tele ents d d2 ps d1 e1 bps q) (scoped-tighten-tele ents d1 e1 rs dd2 e2 brs r)))))
      ((ClTyCtor _ ps e1 q) (match erased b _ ((ScTyCtor _ _ _ d1 bps) (ScTyCtor ents d2 ps e1 (scoped-tighten-tele ents d d2 ps d1 e1 bps q)))))
      ((ClValCtor _ ps r e1 q p)
        (match erased b _ ((ScValCtor _ _ _ _ d1 bps br) (ScValCtor ents d2 ps r e1 (scoped-tighten-tele ents d d2 ps d1 e1 bps q) (scoped-tighten ents d1 e1 r br p)))))))
  ((erased scoped-tighten-list : (erased (List (Ent)) ents) (erased (Nat) d) (erased (Nat) d2) (erased (List (Term)) ts) (erased (ScopedList ents d ts) b) (subterm erased (ClosedList d2 ts) c) -> (erased (ScopedList ents d2 ts) s))
    (let-match erased c (ClCons _ t ts2 p q)
      ((ClNil _) (ScNil ents d2)))
    (match erased b _ ((ScCons _ _ _ _ b1 b2) (ScCons ents d2 t ts2 (scoped-tighten ents d d2 t b1 p) (scoped-tighten-list ents d d2 ts2 b2 q)))))
  ((erased scoped-tighten-tele : (erased (List (Ent)) ents) (erased (Nat) d) (erased (Nat) d2) (erased (List (Entry)) es) (erased (Nat) out) (erased (Nat) out2) (erased (ScopedTele ents d es out) b)
      (subterm erased (ClosedTele d2 es out2) c) -> (erased (ScopedTele ents d2 es out2) s))
    (let-match erased c (ClTCons _ s i t es2 _ p q)
      ((ClTNil _) (ScTNil ents d2)))
    (match erased b _ ((ScTCons _ _ _ _ _ _ _ b1 b2) (ScTCons ents d2 s i t es2 out2 (scoped-tighten ents d d2 t b1 p) (scoped-tighten-tele ents (Succ d) (Succ d2) es2 out out2 b2 q))))))

(def-fns _ $ (erased nth-scoped : (erased (List (Ent)) ents) (erased (List (Maybe (Term))) subs) (erased (Nat) k) (erased (Term) v) (erased (ScopedSub ents subs) b) (subterm erased (Nth (Maybe (Term)) subs k (Some (Term) v)) p) ->
    (erased (Scoped ents (Zero) v) c))
  (match erased p _
    ((NthHere _ _ _) (match erased b _ ((ScSSome _ _ _ q _) q)))
    ((NthThere _ _ _ i _ q) (match erased b _ ((ScSNone _ rest2 r) (nth-scoped ents rest2 i v r q)) ((ScSSome _ _ rest2 _ s) (nth-scoped ents rest2 i v s q))))))

(def-fns _ $ (erased snoc-scoped : (erased (List (Ent)) e) (erased (List (Maybe (Term))) subs) (erased (Term) t) (erased (List (Maybe (Term))) out) (erased (ScopedSub e subs) p) (erased (Scoped e (Zero) t) st)
    (subterm erased (Snoc subs (Some (Term) t) out) sn) -> (erased (ScopedSub e out) q))
  (let-match erased sn (SnocCons _ ys _ out2 p2) ((SnocNil _) (ScSSome e t (Nil _) st (ScSNil e))))
  (match erased p _
    ((ScSNone _ _ q2) (ScSNone e out2 (snoc-scoped e ys t out2 q2 st p2)))
    ((ScSSome _ t2 _ st2 q2) (ScSSome e t2 out2 st2 (snoc-scoped e ys t out2 q2 st p2)))))
(def-fns _ $ (erased somes-scoped : (erased (List (Ent)) ents) (erased (List (Term)) as) (erased (List (Maybe (Term))) subs) (erased (ScopedList ents (Zero) as) p) (subterm erased (Somes as subs) so) -> (erased (ScopedSub ents subs) q))
  (let-match erased so (SomesCons a as2 sub2 out p2 sn)
    ((SomesNil) (ScSNil ents)))
  (match erased p _ ((ScCons _ _ _ _ st sts) (snoc-scoped ents sub2 a out (somes-scoped ents as2 sub2 sts p2) st sn))))

; Substituting through a list of [r] kept binders and then closed terms, [n] in all, takes a term scoped
; under [n] binders to one scoped under [r].
(def-fns _
  ((erased subst-scoped : (erased (List (Ent)) ents) (erased (List (Maybe (Term))) subs) (erased (Nat) r) (erased (Nat) n) (erased (Term) t) (erased (Term) u) (erased (ScopedSub ents subs) bs) (erased (Layout (Term) subs r n) ly)
      (erased (Scoped ents n t) bt) (subterm erased (Subst subs t u) d) -> (erased (Scoped ents r u) c))
    (match erased d _
      ((SubRef _ x) (match erased bt _ ((ScRef _ _ _ p) (ScRef ents r x p))))
      ((SubHit _ k v p) (scoped-mono ents (Zero) r v (LtZ r) (nth-scoped ents subs k v bs p)))
      ((SubSkip _ k p) (ScBound ents r k (nth-none-lt _ subs r n k ly p)))
      ((SubTyApp _ h h2 ps ps2 as as2 sub1 p t3 q)
        (let-match erased bt (ScTyApp _ _ _ _ _ nout bh bps bas ln))
        (let ((erased r1) (erased bps2) (erased _) (erased _)) (subst-scoped-tele ents subs r n ps ps2 sub1 nout bs ly bps t3))
        (ScTyApp ents r h2 ps2 as2 r1 (subst-scoped ents subs r n h h2 bs ly bh p) bps2 (subst-scoped-list ents subs r n as as2 bs ly bas q) (subst-len-eq subs subs as as2 ps ps2 sub1 q t3 ln)))
      ((SubValApp _ h h2 ps ps2 rt rt2 as as2 sub1 p t3 pr q)
        (let-match erased bt (ScValApp _ _ _ _ _ _ nout bh bps brt bas ln))
        (let ((erased r1) (erased bps2) (erased bs1) (erased ly1)) (subst-scoped-tele ents subs r n ps ps2 sub1 nout bs ly bps t3))
        (ScValApp ents r h2 ps2 rt2 as2 r1 (subst-scoped ents subs r n h h2 bs ly bh p) bps2 (subst-scoped ents sub1 r1 nout rt rt2 bs1 ly1 brt pr) (subst-scoped-list ents subs r n as as2 bs ly bas q) (subst-len-eq subs subs as as2 ps ps2 sub1 q t3 ln)))
      ((SubUniv _) (ScUniv ents r))
      ((SubFn _ l l2 ps ps2 rs rs2 sub1 sub2 p q r2)
        (let-match erased bt (ScFn _ _ _ _ _ n1 n2 bl bps brs))
        (let ((erased r1) (erased bps2) (erased bs1) (erased ly1)) (subst-scoped-tele ents subs r n ps ps2 sub1 n1 bs ly bps q))
        (let ((erased rr2) (erased brs2) (erased _) (erased _)) (subst-scoped-tele ents sub1 r1 n1 rs rs2 sub2 n2 bs1 ly1 brs r2))
        (ScFn ents r l2 ps2 rs2 r1 rr2 (subst-scoped ents subs r n l l2 bs ly bl p) bps2 brs2))
      ((SubTyCtor _ ps ps2 sub1 q)
        (let-match erased bt (ScTyCtor _ _ _ n1 bps))
        (let ((erased r1) (erased bps2) (erased _) (erased _)) (subst-scoped-tele ents subs r n ps ps2 sub1 n1 bs ly bps q))
        (ScTyCtor ents r ps2 r1 bps2))
      ((SubValCtor _ ps ps2 r0 r2 sub1 q p)
        (let-match erased bt (ScValCtor _ _ _ _ n1 bps br))
        (let ((erased r1) (erased bps2) (erased bs1) (erased ly1)) (subst-scoped-tele ents subs r n ps ps2 sub1 n1 bs ly bps q))
        (ScValCtor ents r ps2 r2 r1 bps2 (subst-scoped ents sub1 r1 n1 r0 r2 bs1 ly1 br p)))))
  ((erased subst-scoped-list : (erased (List (Ent)) ents) (erased (List (Maybe (Term))) subs) (erased (Nat) r) (erased (Nat) n) (erased (List (Term)) ts) (erased (List (Term)) us) (erased (ScopedSub ents subs) bs)
      (erased (Layout (Term) subs r n) ly) (erased (ScopedList ents n ts) bt) (subterm erased (SubstList subs ts us) d) -> (erased (ScopedList ents r us) c))
    (let-match erased d (SubCons _ t u ts2 us2 p q)
      ((SubNil _) (ScNil ents r)))
    (match erased bt _ ((ScCons _ _ _ _ b1 b2) (ScCons ents r u us2 (subst-scoped ents subs r n t u bs ly b1 p) (subst-scoped-list ents subs r n ts2 us2 bs ly b2 q)))))
  ((erased subst-scoped-tele : (erased (List (Ent)) ents) (erased (List (Maybe (Term))) subs) (erased (Nat) r) (erased (Nat) n) (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (List (Maybe (Term))) out)
      (erased (Nat) nout) (erased (ScopedSub ents subs) bs) (erased (Layout (Term) subs r n) ly) (erased (ScopedTele ents n es nout) bt) (subterm erased (SubstTele subs es fs out) d) ->
      (erased (Nat) rout) (erased (ScopedTele ents r fs rout) c) (erased (ScopedSub ents out) c2) (erased (Layout (Term) out rout nout) ly2))
    (let-match erased d (SubTCons _ s i t u es2 fs2 out2 p q)
      ((SubTNil _) (match erased bt _ ((ScTNil _ _) (values r (ScTNil ents r) bs ly)))))
    (let-match erased bt (ScTCons _ _ _ _ _ _ _ b1 b2))
    (let ((erased rout) (erased bfs) (erased bout) (erased lyout)) (subst-scoped-tele ents (Cons _ (None _) subs) (Succ r) (Succ n) es2 fs2 out2 nout (ScSNone ents subs bs) (LayNone _ subs r n ly) b2 q))
    (values rout (ScTCons ents r s i u fs2 rout (subst-scoped ents subs r n t u bs ly b1 p) bfs) bout lyout)))


(def-fns _ $ (erased rule-of-scoped : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) (erased (Term) r) (erased (ScopedRules ents rules) b) (subterm erased (RuleOf rules x r) p) -> (erased (Scoped ents (Zero) r) c))
  (match erased p _
    ((RuleHere _ _ _) (match erased b _ ((SRCons _ _ _ _ q _) q)))
    ((RuleThere _ _ _ _ rest _ p2) (match erased b _ ((SRCons _ _ _ _ _ s2) (rule-of-scoped ents rest x r s2 p2))))))

(def-fns _
  ((erased canon-scoped : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) d) (erased (Term) t) (erased (Term) u) (erased (ScopedRules ents rules) br) (erased (Scoped ents d t) bt) (subterm erased (Canon rules t u) c) ->
      (erased (Scoped ents d u) s))
    (match erased c _
      ((CanRule _ x r _ p q) (canon-scoped ents rules d r u br (scoped-mono ents (Zero) d r (LtZ d) (rule-of-scoped ents rules x r br p)) q))
      ((CanFree _ _ _) bt)
      ((CanBound _ _) bt)
      ((CanTyApp _ h h2 ps as as2 p q)
        (match erased bt _ ((ScTyApp _ _ _ _ _ out bh bps bas n) (ScTyApp ents d h2 ps as2 out (canon-scoped ents rules d h h2 br bh p) bps (canon-scoped-list ents rules d as as2 br bas q) (canon-len-eq rules as as2 ps q n)))))
      ((CanValApp _ h h2 ps r as as2 p q)
        (match erased bt _ ((ScValApp _ _ _ _ _ _ out bh bps bpr bas n) (ScValApp ents d h2 ps r as2 out (canon-scoped ents rules d h h2 br bh p) bps bpr (canon-scoped-list ents rules d as as2 br bas q) (canon-len-eq rules as as2 ps q n)))))
      ((CanUniv _) (ScUniv ents d))
      ((CanFn _ l l2 ps ps2 rs rs2 p q r)
        (match erased bt _
          ((ScFn _ _ _ _ _ d1 d2 bl bps brs)
            (ScFn ents d l2 ps2 rs2 d1 d2 (canon-scoped ents rules d l l2 br bl p) (canon-scoped-tele ents rules d ps ps2 d1 br bps q) (canon-scoped-tele ents rules d1 rs rs2 d2 br brs r)))))
      ((CanTyCtor _ ps ps2 q) (match erased bt _ ((ScTyCtor _ _ _ d1 bps) (ScTyCtor ents d ps2 d1 (canon-scoped-tele ents rules d ps ps2 d1 br bps q)))))
      ((CanValCtor _ ps ps2 r r2 q p)
        (match erased bt _ ((ScValCtor _ _ _ _ d1 bps b2) (ScValCtor ents d ps2 r2 d1 (canon-scoped-tele ents rules d ps ps2 d1 br bps q) (canon-scoped ents rules d1 r r2 br b2 p)))))))
  ((erased canon-scoped-list : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) d) (erased (List (Term)) ts) (erased (List (Term)) us) (erased (ScopedRules ents rules) br) (erased (ScopedList ents d ts) bt)
      (subterm erased (CanonList rules ts us) c) -> (erased (ScopedList ents d us) s))
    (let-match erased c (CanCons _ t u ts2 us2 p q)
      ((CanNil _) (ScNil ents d)))
    (match erased bt _ ((ScCons _ _ _ _ b1 b2) (ScCons ents d u us2 (canon-scoped ents rules d t u br b1 p) (canon-scoped-list ents rules d ts2 us2 br b2 q)))))
  ((erased canon-scoped-tele : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) d) (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (Nat) out) (erased (ScopedRules ents rules) br)
      (erased (ScopedTele ents d es out) bt) (subterm erased (CanonTele rules es fs) c) -> (erased (ScopedTele ents d fs out) s))
    (match erased c _
      ((CanTNil _) (match erased bt _ ((ScTNil _ _) (ScTNil ents d))))
      ((CanTCons _ s i t u es2 fs2 p q)
        (match erased bt _ ((ScTCons _ _ _ _ _ _ _ b1 b2) (ScTCons ents d s i u fs2 out (canon-scoped ents rules d t u br b1 p) (canon-scoped-tele ents rules (Succ d) es2 fs2 out br b2 q))))))))


; ---- Well-formedness of a context, which the functions carry beside it: a ranking of its rules
; (mini/canon.sl); its entries' ids below its next id; and its scope, its entries' types, its rules' terms,
; its declared ADTs, its level and its subterm arguments mentioning only its entries, with the built-in
; entries present, so that a rule minted for a fresh entry never mentions that entry, a term in play never
; mentions an entry the context lacks, and a declared constructor's type is a value-constructor former.
(def-adts
  ((BoundedEnts : ((Nat) n) ((List (Ent)) ents) -> Type)
    enum
    (many BENil : (erased (Nat) n) -> (BoundedEnts n (Nil (Ent))))
    (many BECons : (erased (Nat) n) (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (List (Ent)) rest) (erased (Lt x n) lt) (erased (BoundedEnts n rest) q)
       -> (BoundedEnts n (Cons (Ent) (MkEnt x ty k) rest))))
  ((ScopedEnts : ((List (Ent)) ents) ((List (Ent)) es) -> Type)
    enum
    (many SENil : (erased (List (Ent)) ents) -> (ScopedEnts ents (Nil (Ent))))
    (many SECons : (erased (List (Ent)) ents) (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (List (Ent)) rest) (erased (Scoped ents (Zero) ty) b) (erased (ScopedEnts ents rest) q)
       -> (ScopedEnts ents (Cons (Ent) (MkEnt x ty k) rest))))
  ((ScopedScope : ((List (Ent)) ents) ((List (Name)) scope) -> Type)
    enum
    (many SSNil : (erased (List (Ent)) ents) -> (ScopedScope ents (Nil (Name))))
    (many SSCons : (erased (List (Ent)) ents) (erased (String) s) (erased (Nat) x) (erased (List (Name)) rest) (erased (HasEnt ents x) h) (erased (ScopedScope ents rest) q) -> (ScopedScope ents (Cons (Name) (MkName s x) rest))))
  ((AllHasEnt : ((List (Ent)) ents) ((List (Nat)) ids) -> Type)
    enum
    (many AHNil : (erased (List (Ent)) ents) -> (AllHasEnt ents (Nil (Nat))))
    (many AHCons : (erased (List (Ent)) ents) (erased (Nat) x) (erased (List (Nat)) ids) (erased (HasEnt ents x) h) (erased (AllHasEnt ents ids) q) -> (AllHasEnt ents (Cons (Nat) x ids))))
  ((AllCtor : ((List (Ent)) ents) ((List (Nat)) ids) -> Type)
    enum
    (many ACNil : (erased (List (Ent)) ents) -> (AllCtor ents (Nil (Nat))))
    (many ACCons : (erased (List (Ent)) ents) (erased (Nat) x) (erased (List (Nat)) ids) (erased (List (Entry)) fs) (erased (Term) r) (erased (EntOf ents x (TValCtor fs r) (KDecl)) e) (erased (AllCtor ents ids) q)
       -> (AllCtor ents (Cons (Nat) x ids))))
  ((ScopedAdts : ((List (Ent)) ents) ((List (Adt)) adts) -> Type)
    enum
    (many SANil : (erased (List (Ent)) ents) -> (ScopedAdts ents (Nil (Adt))))
    (many SACons : (erased (List (Ent)) ents) (erased (Nat) t) (erased (List (Nat)) ctors) (erased (List (Adt)) rest) (erased (HasEnt ents t) h) (erased (AllCtor ents ctors) cs) (erased (ScopedAdts ents rest) q)
       -> (ScopedAdts ents (Cons (Adt) (MkAdt t ctors) rest))))
  ((ScopedMaybe : ((List (Ent)) ents) ((Maybe (Term)) m) -> Type)
    enum
    (many SMNone : (erased (List (Ent)) ents) -> (ScopedMaybe ents (None (Term))))
    (many SMSome : (erased (List (Ent)) ents) (erased (Term) t) (erased (Scoped ents (Zero) t) p) -> (ScopedMaybe ents (Some (Term) t))))
  ((Builtins : ((List (Ent)) ents) -> Type)
    enum
    (many MkBuiltins : (erased (List (Ent)) ents) (erased (HasEnt ents (Zero)) h0) (erased (HasEnt ents (Succ (Zero))) h1) (erased (HasEnt ents (Succ (Succ (Zero)))) h2) -> (Builtins ents)))
  ; One list of entries extending another with ids at or above a bound, and a context grown from another:
  ; its next id no lower and its entries extending, everything a term mentions still in play.
  ((Ext : ((Nat) n) ((List (Ent)) e0) ((List (Ent)) e1) -> Type)
    enum
    (many ExtRefl : (erased (Nat) n) (erased (List (Ent)) e) -> (Ext n e e))
    (many ExtCons : (erased (Nat) n) (erased (List (Ent)) e0) (erased (List (Ent)) e1) (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (Lt n (Succ x)) le) (erased (Ext n e0 e1) p)
       -> (Ext n e0 (Cons (Ent) (MkEnt x ty k) e1))))
  ((Grew : ((Ctx) ctx) ((Ctx) out) -> Type)
    enum
    (many GrewBy : (erased (Nat) n0) (erased (List (Name)) s0) (erased (List (Ent)) e0) (erased (List (Rule)) r0) (erased (List (Adt)) a0) (erased (Maybe (Term)) l0) (erased (List (Term)) sa0)
       (erased (Nat) n1) (erased (List (Name)) s1) (erased (List (Ent)) e1) (erased (List (Rule)) r1) (erased (List (Adt)) a1) (erased (Maybe (Term)) l1) (erased (List (Term)) sa1)
       (erased (Lt n0 (Succ n1)) le) (erased (Ext n0 e0 e1) ext) -> (Grew (MkCtx n0 s0 e0 r0 a0 l0 sa0) (MkCtx n1 s1 e1 r1 a1 l1 sa1))))
  ; The facts above stated of a context rather than of its entries.
  ((Has : ((Ctx) ctx) ((Nat) x) -> Type)
    enum
    (many MkHas : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (Nat) x) (erased (HasEnt e x) p) -> (Has (MkCtx n s e r a l sa) x)))
  ((HasAll : ((Ctx) ctx) ((List (Nat)) ids) -> Type)
    enum
    (many MkHasAll : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (List (Nat)) ids) (erased (AllHasEnt e ids) p) -> (HasAll (MkCtx n s e r a l sa) ids)))
  ((Ctors : ((Ctx) ctx) ((List (Nat)) ids) -> Type)
    enum
    (many MkCtors : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (List (Nat)) ids) (erased (AllCtor e ids) p) -> (Ctors (MkCtx n s e r a l sa) ids)))
  ((EntIs : ((Ctx) ctx) ((Nat) x) ((Term) ty) ((Kind) k) -> Type)
    enum
    (many MkEntIs : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (EntOf e x ty k) p) -> (EntIs (MkCtx n s e r a l sa) x ty k)))
  ((Ctor : ((Ctx) ctx) ((Nat) c) -> Type)
    enum
    (many MkCtor : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (Nat) c) (erased (List (Entry)) fs) (erased (Term) ret) (erased (EntOf e c (TValCtor fs ret) (KDecl)) p) -> (Ctor (MkCtx n s e r a l sa) c)))
  ((Tycon : ((Ctx) ctx) ((Nat) tid) -> Type)
    enum
    (many MkTycon : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (Nat) tid) (erased (List (Entry)) pt) (erased (EntOf e tid (TTyCtor pt) (KDecl)) p) -> (Tycon (MkCtx n s e r a l sa) tid)))
  ((Tycons : ((Ctx) ctx) ((List (Nat)) tids) -> Type)
    enum
    (many TyNil : (erased (Ctx) ctx) -> (Tycons ctx (Nil (Nat))))
    (many TyCons : (erased (Ctx) ctx) (erased (Nat) tid) (erased (List (Nat)) tids) (erased (Tycon ctx tid) p) (erased (Tycons ctx tids) q) -> (Tycons ctx (Cons (Nat) tid tids))))
  ((Sc : ((Ctx) ctx) ((Nat) d) ((Term) t) -> Type)
    enum
    (many MkSc : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (Nat) d) (erased (Term) t) (erased (Scoped e d t) p) -> (Sc (MkCtx n s e r a l sa) d t)))
  ((ScL : ((Ctx) ctx) ((Nat) d) ((List (Term)) ts) -> Type)
    enum
    (many MkScL : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (Nat) d) (erased (List (Term)) ts) (erased (ScopedList e d ts) p) -> (ScL (MkCtx n s e r a l sa) d ts)))
  ((ScT : ((Ctx) ctx) ((Nat) d) ((List (Entry)) es) ((Nat) out) -> Type)
    enum
    (many MkScT : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (Nat) d) (erased (Nat) out) (erased (List (Entry)) es) (erased (ScopedTele e d es out) p) -> (ScT (MkCtx n s e r a l sa) d es out)))
  ((ScM : ((Ctx) ctx) ((Maybe (Term)) m) -> Type)
    enum
    (many MkScM : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (Maybe (Term)) m) (erased (ScopedMaybe e m) p) -> (ScM (MkCtx n s e r a l sa) m)))
  ((ScS : ((Ctx) ctx) ((List (Maybe (Term))) subs) ((Nat) m) -> Type)
    enum
    (many MkScS : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (List (Maybe (Term))) subs) (erased (Nat) m) (erased (ScopedSub e subs) p) (erased (Layout (Term) subs (Zero) m) ly) -> (ScS (MkCtx n s e r a l sa) subs m)))
  ; The entries a telescope's binders stand for, innermost first, on top of the entries of the context the
  ; telescope was entered from: what abstracting over the binders leaves is scoped there.
  ((Covers : ((Nat) n0) ((List (Ent)) e0) ((List (Maybe (Nat))) acc) ((List (Ent)) e1) -> Type)
    enum
    (many CovNil : (erased (Nat) n0) (erased (List (Ent)) e) -> (Covers n0 e (Nil (Maybe (Nat))) e))
    (many CovSome : (erased (Nat) n0) (erased (List (Ent)) e0) (erased (List (Maybe (Nat))) acc) (erased (List (Ent)) e1) (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (Lt n0 (Succ x)) le)
       (erased (Covers n0 e0 acc e1) p) -> (Covers n0 e0 (Cons (Maybe (Nat)) (Some (Nat) x) acc) (Cons (Ent) (MkEnt x ty k) e1)))
    (many CovNone : (erased (Nat) n0) (erased (List (Ent)) e0) (erased (List (Maybe (Nat))) acc) (erased (List (Ent)) e1) (erased (Covers n0 e0 acc e1) p)
       -> (Covers n0 e0 (Cons (Maybe (Nat)) (None (Nat)) acc) e1)))
  ((Cov : ((Ctx) ctx0) ((List (Maybe (Nat))) acc) ((Ctx) ctx) ((Nat) m) -> Type)
    enum
    (many MkCov : (erased (Nat) n0) (erased (List (Name)) s0) (erased (List (Ent)) e0) (erased (List (Rule)) r0) (erased (List (Adt)) a0) (erased (Maybe (Term)) l0) (erased (List (Term)) sa0)
       (erased (Nat) n1) (erased (List (Name)) s1) (erased (List (Ent)) e1) (erased (List (Rule)) r1) (erased (List (Adt)) a1) (erased (Maybe (Term)) l1) (erased (List (Term)) sa1)
       (erased (List (Maybe (Nat))) acc) (erased (Nat) m) (erased (Lt n0 (Succ n1)) le) (erased (Covers n0 e0 acc e1) c) (erased (Layout (Nat) acc (Zero) m) ly)
       -> (Cov (MkCtx n0 s0 e0 r0 a0 l0 sa0) acc (MkCtx n1 s1 e1 r1 a1 l1 sa1) m)))
  ((SameEnt : ((Term) ty) ((Kind) k) ((Term) ty2) ((Kind) k2) -> Type)
    enum
    (many SameEntRefl : (erased (Term) ty) (erased (Kind) k) -> (SameEnt ty k ty k))))

(def-adts
  ((LenMismatch : (Type A) (Type B) ((List A) xs) ((List B) ys) -> Type)
    enum
    (many LMNilCons : (erased Type A) (erased Type B) (erased B y) (erased (List B) ys) -> (LenMismatch A B (Nil A) (Cons B y ys)))
    (many LMConsNil : (erased Type A) (erased Type B) (erased A x) (erased (List A) xs) -> (LenMismatch A B (Cons A x xs) (Nil B)))
    (many LMCons : (erased Type A) (erased Type B) (erased A x) (erased B y) (erased (List A) xs) (erased (List B) ys) (erased (LenMismatch A B xs ys) p)
       -> (LenMismatch A B (Cons A x xs) (Cons B y ys))))
  ((LenDec : (Type A) (Type B) ((List A) xs) ((List B) ys) -> Type)
    enum
    (many LenSame : (erased Type A) (erased Type B) (erased (List A) xs) (erased (List B) ys) (erased (LenEq A B xs ys) p) -> (LenDec A B xs ys))
    (many LenDiff : (erased Type A) (erased Type B) (erased (List A) xs) (erased (List B) ys) (erased (LenMismatch A B xs ys) p) -> (LenDec A B xs ys))))
(def-fns _ $ (many len-dec : (erased Type A) (erased Type B) (subterm many (List A) xs) (many (List B) ys) -> (many (LenDec A B xs ys) r))
  (let-match many xs (Cons _ x xs2)
    ((Nil _) (match many ys _ ((Nil _) (LenSame _ _ _ _ (LENil _ _))) ((Cons _ y ys2) (LenDiff _ _ _ _ (LMNilCons _ _ y ys2))))))
  (let-match many ys (Cons _ y ys2) ((Nil _) (LenDiff _ _ _ _ (LMConsNil _ _ x xs2))))
  (match many (notail $ len-dec _ _ xs2 ys2) _
    ((LenSame _ _ _ _ p) (LenSame _ _ _ _ (LECons _ _ x y xs2 ys2 p)))
    ((LenDiff _ _ _ _ p) (LenDiff _ _ _ _ (LMCons _ _ x y xs2 ys2 p)))))
(def-fns _ $ (erased ext-trans : (erased (Nat) n0) (erased (Nat) n1) (erased (List (Ent)) e0) (erased (List (Ent)) e1) (erased (List (Ent)) e2) (erased (Lt n0 (Succ n1)) le) (erased (Ext n0 e0 e1) p)
    (subterm erased (Ext n1 e1 e2) q) -> (erased (Ext n0 e0 e2) r))
  (match erased q _
    ((ExtRefl _ _) p)
    ((ExtCons _ _ c x ty k le2 q2) (ExtCons n0 e0 c x ty k (le-trans n0 n1 x le le2) (ext-trans n0 n1 e0 e1 c le p q2)))))

(def-fns _ $ (erased grew-trans : (erased (Ctx) c1) (erased (Ctx) c2) (erased (Ctx) c3) (erased (Grew c1 c2) g) (erased (Grew c2 c3) h) -> (erased (Grew c1 c3) k))
  (let-match erased g (GrewBy n0 s0 e0 r0 a0 l0 sa0 n1 _ e1 _ _ _ _ le ext))
  (match erased h _
    ((GrewBy _ _ _ _ _ _ _ n2 s2 e2 r2 a2 l2 sa2 le2 ext2)
      (GrewBy n0 s0 e0 r0 a0 l0 sa0 n2 s2 e2 r2 a2 l2 sa2 (le-trans n0 n1 n2 le le2) (ext-trans n0 n1 e0 e1 e2 le ext ext2)))))

(def-fns _ $ (erased grew-refl : (erased (Ctx) ctx) -> (erased (Grew ctx ctx) g))
  (match erased ctx _ ((MkCtx n s e r a l sa) (GrewBy n s e r a l sa n s e r a l sa (lt-succ n) (ExtRefl n e)))))

(def-fns _ $ (erased bounded-ents-weaken : (erased (Nat) n) (erased (Nat) m) (erased (List (Ent)) ents) (erased (Lt n (Succ m)) le) (subterm erased (BoundedEnts n ents) b) -> (erased (BoundedEnts m ents) c))
  (match erased b _
    ((BENil _) (BENil m))
    ((BECons _ x ty k rest lt q) (BECons m x ty k rest (lt-le x n m lt le) (bounded-ents-weaken n m rest le q)))))

(def-fns _ $ (erased all-lt-weaken : (erased (Nat) n) (erased (Nat) m) (erased (List (Nat)) ks) (erased (Lt n (Succ m)) le) (subterm erased (AllLt ks n) b) -> (erased (AllLt ks m) c))
  (match erased b _
    ((ALNil _) (ALNil m))
    ((ALCons k ks2 _ lt q) (ALCons k ks2 m (lt-le k n m lt le) (all-lt-weaken n m ks2 le q)))))

; What the scope, the entries and the ADTs give about the entries they name.
(def-fns _ $ (erased scope-has : (erased (List (Ent)) ents) (erased (List (Name)) scope) (erased (String) s) (erased (Nat) x) (erased (ScopedScope ents scope) b) (subterm erased (NameOf scope s x) p) -> (erased (HasEnt ents x) h))
  (match erased p _
    ((NameHere _ _ _) (match erased b _ ((SSCons _ _ _ _ h _) h)))
    ((NameThere _ _ _ _ rest _ p2) (match erased b _ ((SSCons _ _ _ _ _ q) (scope-has ents rest s x q p2))))))

(def-fns _ $ (erased ent-of-has : (erased (List (Ent)) ents) (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (subterm erased (EntOf ents x ty k) p) -> (erased (HasEnt ents x) h))
  (match erased p _
    ((EntHere _ _ _ rest) (HEHere x ty k rest))
    ((EntThere _ y _ ty2 _ k2 rest _ p2) (HEThere x (MkEnt y ty2 k2) rest (ent-of-has rest x ty k p2)))))

(def-fns _ $ (erased ent-of-scoped : (erased (List (Ent)) all) (erased (List (Ent)) ents) (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (ScopedEnts all ents) b) (subterm erased (EntOf ents x ty k) p) ->
    (erased (Scoped all (Zero) ty) c))
  (match erased p _
    ((EntHere _ _ _ _) (match erased b _ ((SECons _ _ _ _ _ bt _) bt)))
    ((EntThere _ _ _ _ _ _ rest _ p2) (match erased b _ ((SECons _ _ _ _ _ _ q) (ent-of-scoped all rest x ty k q p2))))))

(def-fns _ $ (erased ent-of-unique : (erased (List (Ent)) ents) (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (Term) ty2) (erased (Kind) k2) (subterm erased (EntOf ents x ty k) p) (erased (EntOf ents x ty2 k2) q) ->
    (erased (SameEnt ty k ty2 k2) s))
  (match erased p _
    ((EntHere _ _ _ _)
      (match erased q _
        ((EntHere _ _ _ _) (SameEntRefl ty k))
        (absurd (EntThere _ _ _ _ _ _ _ nq _) (neq-irrefl x nq))))
    ((EntThere _ _ _ _ _ _ rest nq p2)
      (match erased q _
        (absurd (EntHere _ _ _ _) (neq-irrefl x nq))
        ((EntThere _ _ _ _ _ _ _ _ q2) (ent-of-unique rest x ty k ty2 k2 p2 q2))))))

(def-fns _ $ (erased has-ent-lt : (erased (Nat) n) (erased (List (Ent)) ents) (erased (Nat) x) (erased (BoundedEnts n ents) b) (subterm erased (HasEnt ents x) h) -> (erased (Lt x n) lt))
  (match erased h _
    ((HEHere _ _ _ _) (match erased b _ ((BECons _ _ _ _ _ lt _) lt)))
    ((HEThere _ _ rest p) (match erased b _ ((BECons _ _ _ _ _ _ q) (has-ent-lt n rest x q p))))))

(def-fns _ $ (erased absurd has-ent-no-ent : (erased (List (Ent)) ents) (erased (Nat) x) (subterm erased (HasEnt ents x) h) (erased (NoEnt ents x) m) -> (erased (False) f))
  (match erased h _
    (absurd (HEHere _ _ _ _) (let-match erased m (NoEntCons _ _ _ _ _ nq _)) (neq-irrefl x nq))
    (absurd (HEThere _ _ rest p) (let-match erased m (NoEntCons _ _ _ _ _ _ q)) (has-ent-no-ent rest x p q))))

(def-fns _ $ (erased adt-of-scoped : (erased (List (Ent)) ents) (erased (List (Adt)) adts) (erased (Nat) t) (erased (List (Nat)) ctors) (erased (ScopedAdts ents adts) b) (subterm erased (AdtOf adts t ctors) p) ->
    (erased (HasEnt ents t) h) (erased (AllCtor ents ctors) cs))
  (match erased p _
    ((AdtHere _ _ _) (match erased b _ ((SACons _ _ _ _ h cs _) (values h cs))))
    ((AdtThere _ _ _ _ rest _ p2) (match erased b _ ((SACons _ _ _ _ _ _ q) (adt-of-scoped ents rest t ctors q p2))))))

; Everything scoped in a list of entries is scoped in one extending it.
(def-fns _ $ (erased scoped-ents-weaken : (erased (List (Ent)) ents) (erased (Ent) e) (erased (List (Ent)) es) (subterm erased (ScopedEnts ents es) b) -> (erased (ScopedEnts (Cons (Ent) e ents) es) c))
  (match erased b _
    ((SENil _) (SENil _))
    ((SECons _ x ty k rest p q) (SECons _ x ty k rest (scoped-weaken ents e (Zero) ty p) (scoped-ents-weaken ents e rest q)))))
(def-fns _ $ (erased scoped-scope-weaken : (erased (List (Ent)) ents) (erased (Ent) e) (erased (List (Name)) scope) (subterm erased (ScopedScope ents scope) b) -> (erased (ScopedScope (Cons (Ent) e ents) scope) c))
  (match erased b _
    ((SSNil _) (SSNil _))
    ((SSCons _ s x rest h q) (SSCons _ s x rest (HEThere x e ents h) (scoped-scope-weaken ents e rest q)))))
(def-fns _ $ (erased all-has-weaken : (erased (List (Ent)) ents) (erased (Ent) e) (erased (List (Nat)) ids) (subterm erased (AllHasEnt ents ids) b) -> (erased (AllHasEnt (Cons (Ent) e ents) ids) c))
  (match erased b _
    ((AHNil _) (AHNil _))
    ((AHCons _ x rest h q) (AHCons _ x rest (HEThere x e ents h) (all-has-weaken ents e rest q)))))
(def-fns _ $ (erased all-ctor-weaken : (erased (Nat) n) (erased (List (Ent)) ents) (erased (Nat) y) (erased (Term) ty) (erased (Kind) k) (erased (List (Nat)) ids) (erased (BoundedEnts n ents) be) (erased (Lt n (Succ y)) le)
    (subterm erased (AllCtor ents ids) b) -> (erased (AllCtor (Cons (Ent) (MkEnt y ty k) ents) ids) c))
  (match erased b _
    ((ACNil _) (ACNil _))
    ((ACCons _ x rest fs r p q)
      (ACCons _ x rest fs r (EntThere x y (TValCtor fs r) ty (KDecl) k ents (lt-neq x y (lt-le x n y (has-ent-lt n ents x be (ent-of-has ents x (TValCtor fs r) (KDecl) p)) le)) p) (all-ctor-weaken n ents y ty k rest be le q)))))
(def-fns _ $ (erased scoped-adts-weaken : (erased (Nat) n) (erased (List (Ent)) ents) (erased (Nat) y) (erased (Term) ty) (erased (Kind) k) (erased (List (Adt)) adts) (erased (BoundedEnts n ents) be) (erased (Lt n (Succ y)) le)
    (subterm erased (ScopedAdts ents adts) b) -> (erased (ScopedAdts (Cons (Ent) (MkEnt y ty k) ents) adts) c))
  (match erased b _
    ((SANil _) (SANil _))
    ((SACons _ t ctors rest h cs q) (SACons _ t ctors rest (HEThere t (MkEnt y ty k) ents h) (all-ctor-weaken n ents y ty k ctors be le cs) (scoped-adts-weaken n ents y ty k rest be le q)))))
(def-fns _ $ (erased scoped-maybe-weaken : (erased (List (Ent)) ents) (erased (Ent) e) (erased (Maybe (Term)) m) (erased (ScopedMaybe ents m) b) -> (erased (ScopedMaybe (Cons (Ent) e ents) m) c))
  (match erased b _
    ((SMNone _) (SMNone _))
    ((SMSome _ t p) (SMSome _ t (scoped-weaken ents e (Zero) t p)))))
(def-fns _ $ (erased builtins-weaken : (erased (List (Ent)) ents) (erased (Ent) e) (erased (Builtins ents) b) -> (erased (Builtins (Cons (Ent) e ents)) c))
  (match erased b _ ((MkBuiltins _ h0 h1 h2) (MkBuiltins _ (HEThere _ e ents h0) (HEThere _ e ents h1) (HEThere _ e ents h2)))))

(def-fns _ $ (erased has-ent-ext : (erased (Nat) n) (erased (List (Ent)) e0) (erased (List (Ent)) e1) (erased (Nat) x) (erased (HasEnt e0 x) p) (subterm erased (Ext n e0 e1) ex) -> (erased (HasEnt e1 x) q))
  (match erased ex _
    ((ExtRefl _ _) p)
    ((ExtCons _ _ c y ty k _ ex2) (HEThere x (MkEnt y ty k) c (has-ent-ext n e0 c x p ex2)))))
(def-fns _ $ (erased all-has-ext : (erased (Nat) n) (erased (List (Ent)) e0) (erased (List (Ent)) e1) (erased (List (Nat)) ids) (erased (AllHasEnt e0 ids) p) (subterm erased (Ext n e0 e1) ex) -> (erased (AllHasEnt e1 ids) q))
  (match erased ex _
    ((ExtRefl _ _) p)
    ((ExtCons _ _ c y ty k _ ex2) (all-has-weaken c (MkEnt y ty k) ids (all-has-ext n e0 c ids p ex2)))))
(def-fns _ $ (erased ent-of-ext : (erased (Nat) n) (erased (List (Ent)) e0) (erased (List (Ent)) e1) (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (BoundedEnts n e0) be) (erased (EntOf e0 x ty k) p)
    (subterm erased (Ext n e0 e1) ex) -> (erased (EntOf e1 x ty k) q))
  (match erased ex _
    ((ExtRefl _ _) p)
    ((ExtCons _ _ c y ty2 k2 le ex2)
      (EntThere x y ty ty2 k k2 c (lt-neq x y (lt-le x n y (has-ent-lt n e0 x be (ent-of-has e0 x ty k p)) le)) (ent-of-ext n e0 c x ty k be p ex2)))))
(def-fns _ $ (erased all-ctor-ext : (erased (Nat) n) (erased (List (Ent)) e0) (erased (List (Ent)) e1) (erased (List (Nat)) ids) (erased (BoundedEnts n e0) be) (subterm erased (AllCtor e0 ids) p) (erased (Ext n e0 e1) ex) ->
    (erased (AllCtor e1 ids) q))
  (match erased p _
    ((ACNil _) (ACNil _))
    ((ACCons _ x rest fs r e q) (ACCons _ x rest fs r (ent-of-ext n e0 e1 x (TValCtor fs r) (KDecl) be e ex) (all-ctor-ext n e0 e1 rest be q ex)))))
(def-fns _ $ (erased scoped-ext : (erased (Nat) n) (erased (List (Ent)) e0) (erased (List (Ent)) e1) (erased (Nat) d) (erased (Term) t) (erased (Scoped e0 d t) p) (subterm erased (Ext n e0 e1) ex) -> (erased (Scoped e1 d t) q))
  (match erased ex _
    ((ExtRefl _ _) p)
    ((ExtCons _ _ c y ty k _ ex2) (scoped-weaken c (MkEnt y ty k) d t (scoped-ext n e0 c d t p ex2)))))
(def-fns _ $ (erased scoped-ext-list : (erased (Nat) n) (erased (List (Ent)) e0) (erased (List (Ent)) e1) (erased (Nat) d) (erased (List (Term)) ts) (erased (ScopedList e0 d ts) p) (subterm erased (Ext n e0 e1) ex) ->
    (erased (ScopedList e1 d ts) q))
  (match erased ex _
    ((ExtRefl _ _) p)
    ((ExtCons _ _ c y ty k _ ex2) (scoped-weaken-list c (MkEnt y ty k) d ts (scoped-ext-list n e0 c d ts p ex2)))))
(def-fns _ $ (erased scoped-ext-tele : (erased (Nat) n) (erased (List (Ent)) e0) (erased (List (Ent)) e1) (erased (Nat) d) (erased (List (Entry)) es) (erased (Nat) out) (erased (ScopedTele e0 d es out) p)
    (subterm erased (Ext n e0 e1) ex) -> (erased (ScopedTele e1 d es out) q))
  (match erased ex _
    ((ExtRefl _ _) p)
    ((ExtCons _ _ c y ty k _ ex2) (scoped-weaken-tele c (MkEnt y ty k) d es out (scoped-ext-tele n e0 c d es out p ex2)))))
(def-fns _ $ (erased scoped-ext-sub : (erased (Nat) n) (erased (List (Ent)) e0) (erased (List (Ent)) e1) (erased (List (Maybe (Term))) subs) (erased (ScopedSub e0 subs) p) (subterm erased (Ext n e0 e1) ex) -> (erased (ScopedSub e1 subs) q))
  (match erased ex _
    ((ExtRefl _ _) p)
    ((ExtCons _ _ c y ty k _ ex2) (scoped-weaken-sub c (MkEnt y ty k) subs (scoped-ext-sub n e0 c subs p ex2)))))
(def-fns _ $ (erased scoped-ext-maybe : (erased (Nat) n) (erased (List (Ent)) e0) (erased (List (Ent)) e1) (erased (Maybe (Term)) m) (erased (ScopedMaybe e0 m) p) (subterm erased (Ext n e0 e1) ex) -> (erased (ScopedMaybe e1 m) q))
  (match erased ex _
    ((ExtRefl _ _) p)
    ((ExtCons _ _ c y ty k _ ex2) (scoped-maybe-weaken c (MkEnt y ty k) m (scoped-ext-maybe n e0 c m p ex2)))))
(def-fns _ $ (erased scoped-scope-ext : (erased (Nat) n) (erased (List (Ent)) e0) (erased (List (Ent)) e1) (erased (List (Name)) scope) (erased (ScopedScope e0 scope) p) (subterm erased (Ext n e0 e1) ex) -> (erased (ScopedScope e1 scope) q))
  (match erased ex _
    ((ExtRefl _ _) p)
    ((ExtCons _ _ c y ty k _ ex2) (scoped-scope-weaken c (MkEnt y ty k) scope (scoped-scope-ext n e0 c scope p ex2)))))

; A covering extends the entries, and what it says of a free reference.
(def-fns _ $ (erased covers-ext : (erased (Nat) n0) (erased (List (Ent)) e0) (erased (List (Maybe (Nat))) acc) (erased (List (Ent)) e1) (subterm erased (Covers n0 e0 acc e1) c) -> (erased (Ext n0 e0 e1) x))
  (match erased c _
    ((CovNil _ _) (ExtRefl n0 e0))
    ((CovSome _ _ acc2 e2 y ty k le c2) (ExtCons n0 e0 e2 y ty k le (covers-ext n0 e0 acc2 e2 c2)))
    ((CovNone _ _ acc2 e2 c2) (covers-ext n0 e0 acc2 e2 c2))))
(def-fns _ $ (erased covers-has : (erased (Nat) n0) (erased (List (Ent)) e0) (erased (List (Maybe (Nat))) acc) (erased (List (Ent)) e1) (erased (Nat) x) (erased (NotIn acc x) ni) (subterm erased (Covers n0 e0 acc e1) c)
    (erased (HasEnt e1 x) h) -> (erased (HasEnt e0 x) h2))
  (let-match erased c (CovSome _ _ acc2 e2 _ _ _ _ c2)
    ((CovNil _ _) h)
    ((CovNone _ _ acc2 e2 c2) (match erased ni _ ((NotInNone _ _ p) (covers-has n0 e0 acc2 e2 x p c2 h)))))
  (match erased h _
    (absurd (HEHere _ _ _ _) (let-match erased ni (NotInSome _ _ _ nq _)) (neq-irrefl x nq))
    ((HEThere _ _ _ p) (match erased ni _ ((NotInSome _ _ _ _ p2) (covers-has n0 e0 acc2 e2 x p2 c2 p))))))

(def-fns _
  ((erased abstract-covers : (erased (Nat) n0) (erased (List (Ent)) e0) (erased (List (Maybe (Nat))) ids) (erased (List (Ent)) e1) (erased (Nat) d) (erased (Nat) m) (erased (Term) t) (erased (Term) u)
      (erased (Covers n0 e0 ids e1) c) (erased (Layout (Nat) ids d m) ly) (erased (Scoped e1 d t) bt) (subterm erased (Abstract ids t u) ab) -> (erased (Scoped e0 m u) su))
    (match erased ab _
      ((AbsFree _ x p) (match erased bt _ ((ScRef _ _ _ h) (ScRef e0 m x (covers-has n0 e0 ids e1 x p c h)))))
      ((AbsHit _ x k p) (ScBound e0 m k (index-of-lt ids x k m p (layout-length _ ids d m ly))))
      ((AbsBound _ k) (match erased bt _ ((ScBound _ _ _ lt) (ScBound e0 m k (lt-le k d m lt (layout-le _ ids d m ly))))))
      ((AbsTyApp _ h h2 ps ps2 as as2 ids1 p t3 q)
        (let-match erased bt (ScTyApp _ _ _ _ _ dout bh bps bas n))
        (let ((erased m1) (erased sps) (erased _) (erased _)) (abstract-covers-tele n0 e0 ids e1 d m ps ps2 ids1 dout c ly bps t3))
        (ScTyApp e0 m h2 ps2 as2 m1 (abstract-covers n0 e0 ids e1 d m h h2 c ly bh p) sps (abstract-covers-list n0 e0 ids e1 d m as as2 c ly bas q) (abstract-len-eq ids ids as as2 ps ps2 ids1 q t3 n)))
      ((AbsValApp _ h h2 ps ps2 r r2 as as2 ids1 p t3 pr q)
        (let-match erased bt (ScValApp _ _ _ _ _ _ dout bh bps br bas n))
        (let ((erased m1) (erased sps) (erased c1) (erased ly1)) (abstract-covers-tele n0 e0 ids e1 d m ps ps2 ids1 dout c ly bps t3))
        (ScValApp e0 m h2 ps2 r2 as2 m1 (abstract-covers n0 e0 ids e1 d m h h2 c ly bh p) sps (abstract-covers n0 e0 ids1 e1 dout m1 r r2 c1 ly1 br pr) (abstract-covers-list n0 e0 ids e1 d m as as2 c ly bas q) (abstract-len-eq ids ids as as2 ps ps2 ids1 q t3 n)))
      ((AbsUniv _) (ScUniv e0 m))
      ((AbsFn _ l l2 ps ps2 rs rs2 ids1 ids2 p q r)
        (let-match erased bt (ScFn _ _ _ _ _ d1 d2 bl bps brs))
        (let ((erased m1) (erased sps) (erased c1) (erased ly1)) (abstract-covers-tele n0 e0 ids e1 d m ps ps2 ids1 d1 c ly bps q))
        (let ((erased m2) (erased srs) (erased _) (erased _)) (abstract-covers-tele n0 e0 ids1 e1 d1 m1 rs rs2 ids2 d2 c1 ly1 brs r))
        (ScFn e0 m l2 ps2 rs2 m1 m2 (abstract-covers n0 e0 ids e1 d m l l2 c ly bl p) sps srs))
      ((AbsTyCtor _ ps ps2 ids1 q)
        (let-match erased bt (ScTyCtor _ _ _ d1 bps))
        (let ((erased m1) (erased sps) (erased _) (erased _)) (abstract-covers-tele n0 e0 ids e1 d m ps ps2 ids1 d1 c ly bps q))
        (ScTyCtor e0 m ps2 m1 sps))
      ((AbsValCtor _ ps ps2 r r2 ids1 q p)
        (let-match erased bt (ScValCtor _ _ _ _ d1 bps br))
        (let ((erased m1) (erased sps) (erased c1) (erased ly1)) (abstract-covers-tele n0 e0 ids e1 d m ps ps2 ids1 d1 c ly bps q))
        (ScValCtor e0 m ps2 r2 m1 sps (abstract-covers n0 e0 ids1 e1 d1 m1 r r2 c1 ly1 br p)))))
  ((erased abstract-covers-list : (erased (Nat) n0) (erased (List (Ent)) e0) (erased (List (Maybe (Nat))) ids) (erased (List (Ent)) e1) (erased (Nat) d) (erased (Nat) m) (erased (List (Term)) ts) (erased (List (Term)) us)
      (erased (Covers n0 e0 ids e1) c) (erased (Layout (Nat) ids d m) ly) (erased (ScopedList e1 d ts) bt) (subterm erased (AbstractList ids ts us) ab) -> (erased (ScopedList e0 m us) su))
    (let-match erased ab (AbsCons _ t u ts2 us2 p q)
      ((AbsNil _) (ScNil e0 m)))
    (match erased bt _ ((ScCons _ _ _ _ b1 b2) (ScCons e0 m u us2 (abstract-covers n0 e0 ids e1 d m t u c ly b1 p) (abstract-covers-list n0 e0 ids e1 d m ts2 us2 c ly b2 q)))))
  ((erased abstract-covers-tele : (erased (Nat) n0) (erased (List (Ent)) e0) (erased (List (Maybe (Nat))) ids) (erased (List (Ent)) e1) (erased (Nat) d) (erased (Nat) m) (erased (List (Entry)) es) (erased (List (Entry)) fs)
      (erased (List (Maybe (Nat))) out) (erased (Nat) dout) (erased (Covers n0 e0 ids e1) c) (erased (Layout (Nat) ids d m) ly) (erased (ScopedTele e1 d es dout) bt) (subterm erased (AbstractTele ids es fs out) ab) ->
      (erased (Nat) mout) (erased (ScopedTele e0 m fs mout) su) (erased (Covers n0 e0 out e1) c2) (erased (Layout (Nat) out dout mout) ly2))
    (let-match erased ab (AbsTCons _ s i t u es2 fs2 out2 p q)
      ((AbsTNil _) (match erased bt _ ((ScTNil _ _) (values m (ScTNil e0 m) c ly)))))
    (let-match erased bt (ScTCons _ _ _ _ _ _ _ b1 b2))
    (let ((erased mout) (erased sfs) (erased c2) (erased ly2)) (abstract-covers-tele n0 e0 (Cons _ (None _) ids) e1 (Succ d) (Succ m) es2 fs2 out2 dout (CovNone n0 e0 ids e1 c) (LayNone _ ids d m ly) b2 q))
    (values mout (ScTCons e0 m s i u fs2 mout (abstract-covers n0 e0 ids e1 d m t u c ly b1 p) sfs) c2 ly2)))

(def-fns _
  ((erased below-cons : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (Term) t) (erased (Nat) k) (erased (Term) s) (erased (Nat) top)
      (erased (BoundedEnts n ents) be) (erased (Nat) d) (erased (Scoped ents d t) bt) (subterm erased (Below rules ranks t k) b) -> (erased (Below (Cons (Rule) (MkRule n s) rules) (Cons (Nat) top ranks) t k) c))
    (match erased b _
      ((BlFree _ _ x _ p) (match erased bt _ ((ScRef _ _ _ h) (BlFree _ _ x k (NoRuleCons x n s rules (lt-neq x n (has-ent-lt n ents x be h)) p)))))
      ((BlRuled _ _ x _ r j p lt) (match erased bt _ ((ScRef _ _ _ h) (BlRuled _ _ x k r j (RRThere x n r s j top rules ranks (lt-neq x n (has-ent-lt n ents x be h)) p) lt))))
      ((BlBound _ _ i _) (BlBound _ _ i k))
      ((BlTyApp _ _ h ps as _ p q) (match erased bt _ ((ScTyApp _ _ _ _ _ _ bh _ bas _) (BlTyApp _ _ h ps as k (below-cons n ents rules ranks h k s top be d bh p) (below-cons-list n ents rules ranks as k s top be d bas q)))))
      ((BlValApp _ _ h ps r as _ p q) (match erased bt _ ((ScValApp _ _ _ _ _ _ _ bh _ _ bas _) (BlValApp _ _ h ps r as k (below-cons n ents rules ranks h k s top be d bh p) (below-cons-list n ents rules ranks as k s top be d bas q)))))
      ((BlUniv _ _ _) (BlUniv _ _ k))
      ((BlFn _ _ l ps rs _ p q r)
        (match erased bt _
          ((ScFn _ _ _ _ _ d1 dd2 bl bps brs)
            (BlFn _ _ l ps rs k (below-cons n ents rules ranks l k s top be d bl p) (below-cons-tele n ents rules ranks ps k s top be d d1 bps q) (below-cons-tele n ents rules ranks rs k s top be d1 dd2 brs r)))))
      ((BlTyCtor _ _ ps _ q) (match erased bt _ ((ScTyCtor _ _ _ d1 bps) (BlTyCtor _ _ ps k (below-cons-tele n ents rules ranks ps k s top be d d1 bps q)))))
      ((BlValCtor _ _ ps r _ q p)
        (match erased bt _ ((ScValCtor _ _ _ _ d1 bps br) (BlValCtor _ _ ps r k (below-cons-tele n ents rules ranks ps k s top be d d1 bps q) (below-cons n ents rules ranks r k s top be d1 br p)))))))
  ((erased below-cons-list : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (List (Term)) ts) (erased (Nat) k) (erased (Term) s) (erased (Nat) top)
      (erased (BoundedEnts n ents) be) (erased (Nat) d) (erased (ScopedList ents d ts) bt) (subterm erased (BelowList rules ranks ts k) b) -> (erased (BelowList (Cons (Rule) (MkRule n s) rules) (Cons (Nat) top ranks) ts k) c))
    (let-match erased b (BlCons _ _ t ts2 _ p q)
      ((BlNil _ _ _) (BlNil _ _ k)))
    (match erased bt _ ((ScCons _ _ _ _ b1 b2) (BlCons _ _ t ts2 k (below-cons n ents rules ranks t k s top be d b1 p) (below-cons-list n ents rules ranks ts2 k s top be d b2 q)))))
  ((erased below-cons-tele : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (List (Entry)) es) (erased (Nat) k) (erased (Term) s) (erased (Nat) top)
      (erased (BoundedEnts n ents) be) (erased (Nat) d) (erased (Nat) out) (erased (ScopedTele ents d es out) bt) (subterm erased (BelowTele rules ranks es k) b) ->
      (erased (BelowTele (Cons (Rule) (MkRule n s) rules) (Cons (Nat) top ranks) es k) c))
    (let-match erased b (BlTCons _ _ s0 i t es2 _ p q)
      ((BlTNil _ _ _) (BlTNil _ _ k)))
    (match erased bt _ ((ScTCons _ _ _ _ _ _ _ b1 b2) (BlTCons _ _ s0 i t es2 k (below-cons n ents rules ranks t k s top be d b1 p) (below-cons-tele n ents rules ranks es2 k s top be (Succ d) out b2 q))))))

(def-fns _ $ (erased valid-cons : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) all) (erased (List (Nat)) ar) (erased (List (Rule)) rs) (erased (List (Nat)) ks) (erased (Term) s) (erased (Nat) top)
    (erased (BoundedEnts n ents) be) (erased (ScopedRules ents rs) sr) (subterm erased (ValidFrom all ar rs ks) v) -> (erased (ValidFrom (Cons (Rule) (MkRule n s) all) (Cons (Nat) top ar) rs ks) w))
  (let-match erased v (VFCons _ _ x r k rs2 ks2 bl p)
    ((VFNil _ _) (VFNil _ _)))
  (match erased sr _ ((SRCons _ _ _ _ bt q) (VFCons _ _ x r k rs2 ks2 (below-cons n ents all ar r k s top be (Zero) bt bl) (valid-cons n ents all ar rs2 ks2 s top be q p)))))

(def-fns _
  ((erased below-lift : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (Term) t) (erased (Nat) k) (subterm erased (Below rules ranks t k) b) -> (erased (Below rules ranks t (Succ k)) c))
    (match erased b _
      ((BlFree _ _ x _ p) (BlFree rules ranks x (Succ k) p))
      ((BlRuled _ _ x _ r j p lt) (BlRuled rules ranks x (Succ k) r j p (lt-weaken j k lt)))
      ((BlBound _ _ i _) (BlBound rules ranks i (Succ k)))
      ((BlTyApp _ _ h ps as _ p q) (BlTyApp rules ranks h ps as (Succ k) (below-lift rules ranks h k p) (below-lift-list rules ranks as k q)))
      ((BlValApp _ _ h ps r as _ p q) (BlValApp rules ranks h ps r as (Succ k) (below-lift rules ranks h k p) (below-lift-list rules ranks as k q)))
      ((BlUniv _ _ _) (BlUniv rules ranks (Succ k)))
      ((BlFn _ _ l ps rs _ p q r) (BlFn rules ranks l ps rs (Succ k) (below-lift rules ranks l k p) (below-lift-tele rules ranks ps k q) (below-lift-tele rules ranks rs k r)))
      ((BlTyCtor _ _ ps _ q) (BlTyCtor rules ranks ps (Succ k) (below-lift-tele rules ranks ps k q)))
      ((BlValCtor _ _ ps r _ q p) (BlValCtor rules ranks ps r (Succ k) (below-lift-tele rules ranks ps k q) (below-lift rules ranks r k p)))))
  ((erased below-lift-list : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (List (Term)) ts) (erased (Nat) k) (subterm erased (BelowList rules ranks ts k) b) -> (erased (BelowList rules ranks ts (Succ k)) c))
    (match erased b _
      ((BlNil _ _ _) (BlNil rules ranks (Succ k)))
      ((BlCons _ _ t ts2 _ p q) (BlCons rules ranks t ts2 (Succ k) (below-lift rules ranks t k p) (below-lift-list rules ranks ts2 k q)))))
  ((erased below-lift-tele : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (List (Entry)) es) (erased (Nat) k) (subterm erased (BelowTele rules ranks es k) b) -> (erased (BelowTele rules ranks es (Succ k)) c))
    (match erased b _
      ((BlTNil _ _ _) (BlTNil rules ranks (Succ k)))
      ((BlTCons _ _ s i t es2 _ p q) (BlTCons rules ranks s i t es2 (Succ k) (below-lift rules ranks t k p) (below-lift-tele rules ranks es2 k q))))))

; The new rule's own term, below the top rank under the old ranking, sits below its rank, the top plus one.
(def-fns _ $ (erased below-top : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (Term) s) (erased (Nat) top)
    (erased (BoundedEnts n ents) be) (erased (Scoped ents (Zero) s) bs) (erased (Below rules ranks s top) b) -> (erased (Below (Cons (Rule) (MkRule n s) rules) (Cons (Nat) top ranks) s (Succ top)) c))
  (below-cons n ents rules ranks s (Succ top) s top be (Zero) bs (below-lift rules ranks s top b)))

; The depth a telescope ends at from [Zero] is its length, so a telescope's arguments, as many as its
; entries, instantiate its return: [inst-ret] does what [TotValApp] and [ETValApp] premise.
(def-fns _ $ (erased stele-plus : (erased (List (Ent)) ents) (erased (Nat) d) (erased (List (Entry)) es) (erased (Nat) out) (erased (Nat) m) (subterm erased (ScopedTele ents d es out) b) (erased (Length (Entry) es m) ln) ->
    (erased (Plus d m out) p))
  (match erased b _
    ((ScTNil _ _) (match erased ln _ ((LengthNil _) (plus-zero d))))
    ((ScTCons _ _ _ _ _ es2 _ _ q) (match erased ln _ ((LengthCons _ _ _ m2 l2) (plus-shift d m2 out (stele-plus ents (Succ d) es2 out m2 q l2)))))))
(def-fns _ $ (erased snoc-length : (erased (List (Maybe (Term))) xs) (erased (Maybe (Term)) x) (erased (List (Maybe (Term))) out) (erased (Nat) m) (subterm erased (Snoc xs x out) sn) (erased (Length (Maybe (Term)) xs m) ln) ->
    (erased (Length (Maybe (Term)) out (Succ m)) q))
  (match erased sn _
    ((SnocNil _) (match erased ln _ ((LengthNil _) (LengthCons _ x (Nil _) (Zero) (LengthNil _)))))
    ((SnocCons y ys _ out2 p) (match erased ln _ ((LengthCons _ _ _ m2 l2) (LengthCons _ y out2 (Succ m2) (snoc-length ys x out2 m2 p l2)))))))
(def-fns _ $ (erased somes-length : (erased (List (Term)) as) (erased (List (Maybe (Term))) subs) (erased (Nat) m) (subterm erased (Somes as subs) so) (erased (Length (Term) as m) ln) -> (erased (Length (Maybe (Term)) subs m) q))
  (match erased so _
    ((SomesNil) (match erased ln _ ((LengthNil _) (LengthNil _))))
    ((SomesCons a as2 sub2 out p sn) (match erased ln _ ((LengthCons _ _ _ m2 l2) (snoc-length sub2 (Some _ a) out m2 sn (somes-length as2 sub2 m2 p l2)))))))
(def-fns _ $ (erased len-eq-length : (erased Type A) (erased Type B) (erased (List A) xs) (erased (List B) ys) (erased (Nat) m) (subterm erased (LenEq A B xs ys) le) (erased (Length B ys m) ln) -> (erased (Length A xs m) q))
  (match erased le _
    ((LENil _ _) (match erased ln _ ((LengthNil _) (LengthNil _))))
    ((LECons _ _ x _ xs2 ys2 p) (match erased ln _ ((LengthCons _ _ _ m2 l2) (LengthCons _ x xs2 m2 (len-eq-length _ _ xs2 ys2 m2 p l2)))))))
(def-fns _ $ (erased snoc-layout : (erased (List (Maybe (Term))) xs) (erased (Term) a) (erased (List (Maybe (Term))) out) (erased (Nat) m) (subterm erased (Snoc xs (Some (Term) a) out) sn) (erased (Layout (Term) xs (Zero) m) ly) ->
    (erased (Layout (Term) out (Zero) (Succ m)) q))
  (match erased sn _
    ((SnocNil _) (match erased ly _ ((LayNil _) (LaySome _ a (Nil _) (Zero) (LayNil _)))))
    ((SnocCons _ ys _ out2 p) (match erased ly _ ((LaySome _ y0 _ m2 l2) (LaySome _ y0 out2 (Succ m2) (snoc-layout ys a out2 m2 p l2)))))))
(def-fns _ $ (erased somes-layout : (erased (List (Term)) as) (erased (List (Maybe (Term))) subs) (erased (Nat) m) (subterm erased (Somes as subs) so) (erased (Length (Term) as m) ln) -> (erased (Layout (Term) subs (Zero) m) q))
  (match erased so _
    ((SomesNil) (match erased ln _ ((LengthNil _) (LayNil _))))
    ((SomesCons a as2 sub2 out p sn) (match erased ln _ ((LengthCons _ _ _ m2 l2) (snoc-layout sub2 a out m2 sn (somes-layout as2 sub2 m2 p l2)))))))
(def-fns _ $ (many inst-ret : (erased (List (Ent)) ents) (erased (Nat) out) (erased (List (Entry)) ps) (many (Term) ret) (many (List (Term)) as) (erased (ScopedTele ents (Zero) ps out) sps) (erased (Scoped ents out ret) sret)
    (erased (ScopedList ents (Zero) as) sas) (erased (LenEq (Term) (Entry) as ps) le) ->
    (many (List (Maybe (Term))) subs) (erased (Somes as subs) so) (many (Term) ty) (erased (Subst subs ret ty) q) (erased (Scoped ents (Zero) ty) sty))
  (let ((many sub3) (erased so)) (somes as))
  (let ((erased m) (erased lp)) (list-len _ ps))
  (let ((erased la)) (len-eq-length _ _ as ps m le lp))
  (let ((erased ln)) (somes-length as sub3 m so la))
  (let ((erased lo)) (match erased (stele-plus ents (Zero) ps out m sps lp) (((Length (Maybe (Term)) sub3 out) l)) ((PlusZ _) ln)))
  (let ((many ty) (erased q)) (subst sub3 out lo ret (scoped-closed ents out ret sret)))
  (let ((erased ly)) (match erased (stele-plus ents (Zero) ps out m sps lp) (((Layout (Term) sub3 (Zero) out) l)) ((PlusZ _) (somes-layout as sub3 m so la))))
  (values sub3 so ty q (subst-scoped ents sub3 (Zero) out ret ty (somes-scoped ents as sub3 sas so) ly sret q)))

(MkUnit)
