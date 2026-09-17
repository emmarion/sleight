; mini/ctx.sl -- the scope environment and fact table of DESIGN.md sections 3 and 18 for the minimal
; language: entries with a type and a kind, names, the declared ADTs, and the rules of mini/canon.sl, in one
; record with the ambient level and subterm arguments. Lookups come with evidence. One session's proposal.

; An entry's kind: [KDecl] is a type or value constructor declared by def-adts or built in, rigid for
; unification (ASSUMPTIONS 40); [KLevel] an entry def-lvl minted (section 8's marker).
(def-adts
  (Kind : -> Type
    enum
    (many KPlain : -> (Kind))
    (many KLevel : -> (Kind))
    (many KDecl : -> (Kind)))
  (Ent : -> Type
    enum
    (many MkEnt : (many (Nat) id) (many (Term) ty) (many (Kind) kind) -> (Ent)))
  (Name : -> Type
    enum
    (many MkName : (many (String) name) (many (Nat) id) -> (Name)))
  (Adt : -> Type
    enum
    (many MkAdt : (many (Nat) tycon) (many (List (Nat)) ctors) -> (Adt)))
  ; [next] is the first unused id: ids are never reused, so leaving a scope restores the lists and keeps it.
  ; [level] is the current function's level, or [None] at the top level (section 24); [subargs] the
  ; enclosing function's subterm-marked parameters (section 3).
  (Ctx : -> Type
    enum
    (many MkCtx : (many (Nat) next) (many (List (Name)) scope) (many (List (Ent)) ents) (many (List (Rule)) rules) (many (List (Adt)) adts)
       (many (Maybe (Term)) level) (many (List (Term)) subargs) -> (Ctx))))

(def-adts
  (EntOf : ((List (Ent)) ents) ((Nat) x) ((Term) ty) ((Kind) k) -> Type
    enum
    (many EntHere : (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (List (Ent)) rest) -> (EntOf (Cons (Ent) (MkEnt x ty k) rest) x ty k))
    (many EntThere : (erased (Nat) x) (erased (Nat) y) (erased (Term) ty) (erased (Term) ty2) (erased (Kind) k) (erased (Kind) k2) (erased (List (Ent)) rest)
       (erased (Neq x y) n) (erased (EntOf rest x ty k) p) -> (EntOf (Cons (Ent) (MkEnt y ty2 k2) rest) x ty k)))
  (NoEnt : ((List (Ent)) ents) ((Nat) x) -> Type
    enum
    (many NoEntNil : (erased (Nat) x) -> (NoEnt (Nil (Ent)) x))
    (many NoEntCons : (erased (Nat) x) (erased (Nat) y) (erased (Term) ty2) (erased (Kind) k2) (erased (List (Ent)) rest) (erased (Neq x y) n) (erased (NoEnt rest x) p) ->
       (NoEnt (Cons (Ent) (MkEnt y ty2 k2) rest) x)))
  (EntDec : ((List (Ent)) ents) ((Nat) x) -> Type
    enum
    (many EntHit : (erased (List (Ent)) ents) (erased (Nat) x) (many (Term) ty) (many (Kind) k) (erased (EntOf ents x ty k) p) -> (EntDec ents x))
    (many EntMiss : (erased (List (Ent)) ents) (erased (Nat) x) (erased (NoEnt ents x) p) -> (EntDec ents x))))

(def-fns _ $ many ent-dec : (subterm many (List (Ent)) ents) (many (Nat) x) -> (many (EntDec ents x) r)
  (match many ents _
    ((Nil a) (EntMiss _ _ $ NoEntNil x))
    ((Cons a e rest)
      (match many e _
        ((MkEnt y ty2 k2)
          (match many (nat-dec x y) _
            ((NDSame z) (EntHit _ _ ty2 k2 $ EntHere x ty2 k2 rest))
            ((NDDiff z w n)
              (match many (ent-dec rest x) _
                ((EntHit l z2 ty k p) (EntHit _ _ ty k $ EntThere x y ty ty2 k k2 rest n p))
                ((EntMiss l z2 p) (EntMiss _ _ $ NoEntCons x y ty2 k2 rest n p))))))))))

(def-adts
  (StrNeq : ((String) a) ((String) b) -> Type
    enum
    (many StrNeqLt : (erased (String) a) (erased (String) b) (erased (StrLt a b) p) -> (StrNeq a b))
    (many StrNeqGt : (erased (String) a) (erased (String) b) (erased (StrLt b a) p) -> (StrNeq a b)))
  (NameOf : ((List (Name)) scope) ((String) s) ((Nat) x) -> Type
    enum
    (many NameHere : (erased (String) s) (erased (Nat) x) (erased (List (Name)) rest) -> (NameOf (Cons (Name) (MkName s x) rest) s x))
    (many NameThere : (erased (String) s) (erased (String) s2) (erased (Nat) x) (erased (Nat) y) (erased (List (Name)) rest) (erased (StrNeq s s2) n) (erased (NameOf rest s x) p) ->
       (NameOf (Cons (Name) (MkName s2 y) rest) s x)))
  (NoName : ((List (Name)) scope) ((String) s) -> Type
    enum
    (many NoNameNil : (erased (String) s) -> (NoName (Nil (Name)) s))
    (many NoNameCons : (erased (String) s) (erased (String) s2) (erased (Nat) y) (erased (List (Name)) rest) (erased (StrNeq s s2) n) (erased (NoName rest s) p) ->
       (NoName (Cons (Name) (MkName s2 y) rest) s)))
  (NameDec : ((List (Name)) scope) ((String) s) -> Type
    enum
    (many NameHit : (erased (List (Name)) scope) (erased (String) s) (many (Nat) x) (erased (NameOf scope s x) p) -> (NameDec scope s))
    (many NameMiss : (erased (List (Name)) scope) (erased (String) s) (erased (NoName scope s) p) -> (NameDec scope s))))

(def-fns _ $ many name-dec : (subterm many (List (Name)) scope) (many (String) s) -> (many (NameDec scope s) r)
  (match many scope _
    ((Nil a) (NameMiss _ _ $ NoNameNil s))
    ((Cons a e rest)
      (match many e _
        ((MkName s2 y)
          (match many (str-cmp s s2) _
            ((CEq t r z) (NameHit _ _ y $ NameHere s y rest))
            ((CLt t r z w p)
              (match many (name-dec rest s) _
                ((NameHit l z2 x q) (NameHit _ _ x $ NameThere s s2 x y rest (StrNeqLt s s2 p) q))
                ((NameMiss l z2 q) (NameMiss _ _ $ NoNameCons s s2 y rest (StrNeqLt s s2 p) q))))
            ((CGt t r z w p)
              (match many (name-dec rest s) _
                ((NameHit l z2 x q) (NameHit _ _ x $ NameThere s s2 x y rest (StrNeqGt s s2 p) q))
                ((NameMiss l z2 q) (NameMiss _ _ $ NoNameCons s s2 y rest (StrNeqGt s s2 p) q))))))))))

; The constructors a declared type constructor has, or evidence that none was declared, which is what
; makes a type unmatchable (MINIMAL.md's rule for match).
(def-adts
  (AdtOf : ((List (Adt)) adts) ((Nat) t) ((List (Nat)) ctors) -> Type
    enum
    (many AdtHere : (erased (Nat) t) (erased (List (Nat)) ctors) (erased (List (Adt)) rest) -> (AdtOf (Cons (Adt) (MkAdt t ctors) rest) t ctors))
    (many AdtThere : (erased (Nat) t) (erased (Nat) t2) (erased (List (Nat)) ctors) (erased (List (Nat)) ctors2) (erased (List (Adt)) rest) (erased (Neq t t2) n) (erased (AdtOf rest t ctors) p) ->
       (AdtOf (Cons (Adt) (MkAdt t2 ctors2) rest) t ctors)))
  (NoAdt : ((List (Adt)) adts) ((Nat) t) -> Type
    enum
    (many NoAdtNil : (erased (Nat) t) -> (NoAdt (Nil (Adt)) t))
    (many NoAdtCons : (erased (Nat) t) (erased (Nat) t2) (erased (List (Nat)) ctors2) (erased (List (Adt)) rest) (erased (Neq t t2) n) (erased (NoAdt rest t) p) ->
       (NoAdt (Cons (Adt) (MkAdt t2 ctors2) rest) t)))
  (AdtDec : ((List (Adt)) adts) ((Nat) t) -> Type
    enum
    (many AdtHit : (erased (List (Adt)) adts) (erased (Nat) t) (many (List (Nat)) ctors) (erased (AdtOf adts t ctors) p) -> (AdtDec adts t))
    (many AdtMiss : (erased (List (Adt)) adts) (erased (Nat) t) (erased (NoAdt adts t) p) -> (AdtDec adts t))))

(def-fns _ $ many adt-dec : (subterm many (List (Adt)) adts) (many (Nat) t) -> (many (AdtDec adts t) r)
  (match many adts _
    ((Nil a) (AdtMiss _ _ $ NoAdtNil t))
    ((Cons a e rest)
      (match many e _
        ((MkAdt t2 ctors2)
          (match many (nat-dec t t2) _
            ((NDSame z) (AdtHit _ _ ctors2 $ AdtHere t ctors2 rest))
            ((NDDiff z w n)
              (match many (adt-dec rest t) _
                ((AdtHit l z2 ctors p) (AdtHit _ _ ctors $ AdtThere t t2 ctors ctors2 rest n p))
                ((AdtMiss l z2 p) (AdtMiss _ _ $ NoAdtCons t t2 ctors2 rest n p))))))))))


; ---- Scope of terms: every entry a term mentions is one of the context's entries. Substitution,
; abstraction and canonicalization keep it, and it weakens to a context with more entries.
(def-adts
  (HasEnt : ((List (Ent)) ents) ((Nat) x) -> Type
    enum
    (many HEHere : (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (List (Ent)) rest) -> (HasEnt (Cons (Ent) (MkEnt x ty k) rest) x))
    (many HEThere : (erased (Nat) x) (erased (Ent) e) (erased (List (Ent)) rest) (erased (HasEnt rest x) p) -> (HasEnt (Cons (Ent) e rest) x)))
  (Scoped : ((List (Ent)) ents) ((Term) t) -> Type
    enum
    (many ScRef : (erased (List (Ent)) ents) (erased (Nat) x) (erased (HasEnt ents x) p) -> (Scoped ents (Ref x)))
    (many ScBound : (erased (List (Ent)) ents) (erased (Nat) k) -> (Scoped ents (Bound k)))
    (many ScApp : (erased (List (Ent)) ents) (erased (Term) h) (erased (List (Term)) as) (erased (Scoped ents h) p) (erased (ScopedList ents as) q) -> (Scoped ents (App h as)))
    (many ScUniv : (erased (List (Ent)) ents) -> (Scoped ents (Univ)))
    (many ScFn : (erased (List (Ent)) ents) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs) (erased (Scoped ents l) p) (erased (ScopedTele ents ps) q) (erased (ScopedTele ents rs) r) ->
       (Scoped ents (Fn l ps rs)))
    (many ScTyCtor : (erased (List (Ent)) ents) (erased (List (Entry)) ps) (erased (ScopedTele ents ps) q) -> (Scoped ents (TyCtor ps)))
    (many ScValCtor : (erased (List (Ent)) ents) (erased (List (Entry)) ps) (erased (Term) r) (erased (ScopedTele ents ps) q) (erased (Scoped ents r) p) -> (Scoped ents (ValCtor ps r))))
  (ScopedList : ((List (Ent)) ents) ((List (Term)) ts) -> Type
    enum
    (many ScNil : (erased (List (Ent)) ents) -> (ScopedList ents (Nil (Term))))
    (many ScCons : (erased (List (Ent)) ents) (erased (Term) t) (erased (List (Term)) ts) (erased (Scoped ents t) p) (erased (ScopedList ents ts) q) -> (ScopedList ents (Cons (Term) t ts))))
  (ScopedTele : ((List (Ent)) ents) ((List (Entry)) es) -> Type
    enum
    (many ScTNil : (erased (List (Ent)) ents) -> (ScopedTele ents (Nil (Entry))))
    (many ScTCons : (erased (List (Ent)) ents) (erased (Bool) s) (erased (Bool) i) (erased (Term) t) (erased (List (Entry)) es) (erased (Scoped ents t) p) (erased (ScopedTele ents es) q) ->
       (ScopedTele ents (Cons (Entry) (MkEntry s i t) es))))
  (ScopedSub : ((List (Ent)) ents) ((List (Maybe (Term))) sub) -> Type
    enum
    (many ScSNil : (erased (List (Ent)) ents) -> (ScopedSub ents (Nil (Maybe (Term)))))
    (many ScSNone : (erased (List (Ent)) ents) (erased (List (Maybe (Term))) rest) (erased (ScopedSub ents rest) q) -> (ScopedSub ents (Cons (Maybe (Term)) (None (Term)) rest)))
    (many ScSSome : (erased (List (Ent)) ents) (erased (Term) t) (erased (List (Maybe (Term))) rest) (erased (Scoped ents t) p) (erased (ScopedSub ents rest) q) ->
       (ScopedSub ents (Cons (Maybe (Term)) (Some (Term) t) rest))))
  (ScopedRules : ((List (Ent)) ents) ((List (Rule)) rules) -> Type
    enum
    (many SRNil : (erased (List (Ent)) ents) -> (ScopedRules ents (Nil (Rule))))
    (many SRCons : (erased (List (Ent)) ents) (erased (Nat) x) (erased (Term) r) (erased (List (Rule)) rest) (erased (Scoped ents r) p) (erased (ScopedRules ents rest) q) ->
       (ScopedRules ents (Cons (Rule) (MkRule x r) rest)))))

(def-fns _
  (erased scoped-weaken : (erased (List (Ent)) ents) (erased (Ent) e) (erased (Term) t) (subterm erased (Scoped ents t) b) -> (erased (Scoped (Cons (Ent) e ents) t) c)
    (match erased b _
      ((ScRef a x p) (ScRef _ x (HEThere x e ents p)))
      ((ScBound a k) (ScBound _ k))
      ((ScApp a h as p q) (ScApp _ h as (scoped-weaken ents e h p) (scoped-weaken-list ents e as q)))
      ((ScUniv a) (ScUniv _))
      ((ScFn a l ps rs p q r) (ScFn _ l ps rs (scoped-weaken ents e l p) (scoped-weaken-tele ents e ps q) (scoped-weaken-tele ents e rs r)))
      ((ScTyCtor a ps q) (ScTyCtor _ ps (scoped-weaken-tele ents e ps q)))
      ((ScValCtor a ps r q p) (ScValCtor _ ps r (scoped-weaken-tele ents e ps q) (scoped-weaken ents e r p)))))
  (erased scoped-weaken-list : (erased (List (Ent)) ents) (erased (Ent) e) (erased (List (Term)) ts) (subterm erased (ScopedList ents ts) b) -> (erased (ScopedList (Cons (Ent) e ents) ts) c)
    (match erased b _
      ((ScNil a) (ScNil _))
      ((ScCons a t ts2 p q) (ScCons _ t ts2 (scoped-weaken ents e t p) (scoped-weaken-list ents e ts2 q)))))
  (erased scoped-weaken-tele : (erased (List (Ent)) ents) (erased (Ent) e) (erased (List (Entry)) es) (subterm erased (ScopedTele ents es) b) -> (erased (ScopedTele (Cons (Ent) e ents) es) c)
    (match erased b _
      ((ScTNil a) (ScTNil _))
      ((ScTCons a s i t es2 p q) (ScTCons _ s i t es2 (scoped-weaken ents e t p) (scoped-weaken-tele ents e es2 q))))))

(def-fns _ $ erased scoped-weaken-sub : (erased (List (Ent)) ents) (erased (Ent) e) (erased (List (Maybe (Term))) sub) (subterm erased (ScopedSub ents sub) b) -> (erased (ScopedSub (Cons (Ent) e ents) sub) c)
  (match erased b _
    ((ScSNil a) (ScSNil _))
    ((ScSNone a rest q) (ScSNone _ rest (scoped-weaken-sub ents e rest q)))
    ((ScSSome a t rest p q) (ScSSome _ t rest (scoped-weaken ents e t p) (scoped-weaken-sub ents e rest q)))))

(def-fns _ $ erased scoped-rules-weaken : (erased (List (Ent)) ents) (erased (Ent) e) (erased (List (Rule)) rules) (subterm erased (ScopedRules ents rules) b) -> (erased (ScopedRules (Cons (Ent) e ents) rules) c)
  (match erased b _
    ((SRNil a) (SRNil _))
    ((SRCons a x r rest p q) (SRCons _ x r rest (scoped-weaken ents e r p) (scoped-rules-weaken ents e rest q)))))

(def-fns _ $ erased nth-scoped : (erased (List (Ent)) ents) (erased (List (Maybe (Term))) sub) (erased (Nat) k) (erased (Term) v) (erased (ScopedSub ents sub) b) (subterm erased (Nth (Maybe (Term)) sub k (Some (Term) v)) p) ->
    (erased (Scoped ents v) c)
  (match erased p _
    ((NthHere a x rest) (match erased b _ ((ScSSome a2 t rest2 q r) q)))
    ((NthThere a y rest i x q) (match erased b _ ((ScSNone a2 rest2 r) (nth-scoped ents rest2 i v r q)) ((ScSSome a2 t rest2 r s) (nth-scoped ents rest2 i v s q))))))

(def-fns _ $ erased snoc-scoped : (erased (List (Ent)) e) (erased (List (Maybe (Term))) sub) (erased (Term) t) (erased (List (Maybe (Term))) out) (erased (ScopedSub e sub) p) (erased (Scoped e t) st)
    (subterm erased (Snoc sub (Some (Term) t) out) sn) -> (erased (ScopedSub e out) q)
  (match erased sn _
    ((SnocNil x) (ScSSome e t (Nil _) st (ScSNil e)))
    ((SnocCons y ys x out2 p2)
      (match erased p _
        ((ScSNone a rest q2) (ScSNone e out2 (snoc-scoped e ys t out2 q2 st p2)))
        ((ScSSome a t2 rest st2 q2) (ScSSome e t2 out2 st2 (snoc-scoped e ys t out2 q2 st p2)))))))
(def-fns _ $ erased somes-scoped : (erased (List (Ent)) ents) (erased (List (Term)) as) (erased (List (Maybe (Term))) sub) (erased (ScopedList ents as) p) (subterm erased (Somes as sub) so) -> (erased (ScopedSub ents sub) q)
  (match erased so _
    ((SomesNil) (ScSNil ents))
    ((SomesCons a as2 sub2 out p2 sn) (match erased p _ ((ScCons b t0 ts0 st sts) (snoc-scoped ents sub2 a out (somes-scoped ents as2 sub2 sts p2) st sn))))))

(def-fns _
  (erased subst-scoped : (erased (List (Ent)) ents) (erased (List (Maybe (Term))) sub) (erased (Term) t) (erased (Term) u) (erased (ScopedSub ents sub) bs) (erased (Scoped ents t) bt) (subterm erased (Subst sub t u) d) ->
      (erased (Scoped ents u) c)
    (match erased d _
      ((SubRef a x) bt)
      ((SubHit a k v p) (nth-scoped ents sub k v bs p))
      ((SubSkip a k p) (ScBound ents k))
      ((SubBeyond a k p) (ScBound ents k))
      ((SubApp a h h2 as as2 p q) (match erased bt _ ((ScApp b h0 as0 bh bas) (ScApp ents h2 as2 (subst-scoped ents sub h h2 bs bh p) (subst-scoped-list ents sub as as2 bs bas q)))))
      ((SubUniv a) (ScUniv ents))
      ((SubFn a l l2 ps ps2 rs rs2 sub1 sub2 p q r)
        (match erased bt _
          ((ScFn b l0 ps0 rs0 bl bps brs)
            (let (erased bps2) (erased bsub1) (subst-scoped-tele ents sub ps ps2 sub1 bs bps q))
            (let (erased brs2) (erased bsub2) (subst-scoped-tele ents sub1 rs rs2 sub2 bsub1 brs r))
            (ScFn ents l2 ps2 rs2 (subst-scoped ents sub l l2 bs bl p) bps2 brs2))))
      ((SubTyCtor a ps ps2 sub1 q)
        (match erased bt _ ((ScTyCtor b ps0 bps) (let (erased bps2) (erased bsub1) (subst-scoped-tele ents sub ps ps2 sub1 bs bps q)) (ScTyCtor ents ps2 bps2))))
      ((SubValCtor a ps ps2 r r2 sub1 q p)
        (match erased bt _
          ((ScValCtor b ps0 r0 bps br)
            (let (erased bps2) (erased bsub1) (subst-scoped-tele ents sub ps ps2 sub1 bs bps q))
            (ScValCtor ents ps2 r2 bps2 (subst-scoped ents sub1 r r2 bsub1 br p)))))))
  (erased subst-scoped-list : (erased (List (Ent)) ents) (erased (List (Maybe (Term))) sub) (erased (List (Term)) ts) (erased (List (Term)) us) (erased (ScopedSub ents sub) bs) (erased (ScopedList ents ts) bt)
      (subterm erased (SubstList sub ts us) d) -> (erased (ScopedList ents us) c)
    (match erased d _
      ((SubNil a) (ScNil ents))
      ((SubCons a t u ts2 us2 p q) (match erased bt _ ((ScCons b t0 ts0 b1 b2) (ScCons ents u us2 (subst-scoped ents sub t u bs b1 p) (subst-scoped-list ents sub ts2 us2 bs b2 q)))))))
  (erased subst-scoped-tele : (erased (List (Ent)) ents) (erased (List (Maybe (Term))) sub) (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (List (Maybe (Term))) out)
      (erased (ScopedSub ents sub) bs) (erased (ScopedTele ents es) bt) (subterm erased (SubstTele sub es fs out) d) -> (erased (ScopedTele ents fs) c) (erased (ScopedSub ents out) c2)
    (match erased d _
      ((SubTNil a) (values (ScTNil ents) bs))
      ((SubTCons a s i t u es2 fs2 out2 p q)
        (match erased bt _
          ((ScTCons b s0 i0 t0 es0 b1 b2)
            (let (erased bfs) (erased bout) (subst-scoped-tele ents (Cons _ (None _) sub) es2 fs2 out2 (ScSNone ents sub bs) b2 q))
            (values (ScTCons ents s i u fs2 (subst-scoped ents sub t u bs b1 p) bfs) bout)))))))


(def-fns _ $ erased rule-of-scoped : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) (erased (Term) r) (erased (ScopedRules ents rules) b) (subterm erased (RuleOf rules x r) p) -> (erased (Scoped ents r) c)
  (match erased p _
    ((RuleHere a c rest) (match erased b _ ((SRCons d e g h q s) q)))
    ((RuleThere a y c s rest nq p2) (match erased b _ ((SRCons d e g h q s2) (rule-of-scoped ents rest x r s2 p2))))))

(def-fns _
  (erased canon-scoped : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) t) (erased (Term) u) (erased (ScopedRules ents rules) br) (erased (Scoped ents t) bt) (subterm erased (Canon rules t u) d) ->
      (erased (Scoped ents u) c)
    (match erased d _
      ((CanRule a x r u2 p q) (canon-scoped ents rules r u br (rule-of-scoped ents rules x r br p) q))
      ((CanFree a x p) bt)
      ((CanBound a k) (ScBound ents k))
      ((CanApp a h h2 as as2 p q) (match erased bt _ ((ScApp b h0 as0 bh bas) (ScApp ents h2 as2 (canon-scoped ents rules h h2 br bh p) (canon-scoped-list ents rules as as2 br bas q)))))
      ((CanUniv a) (ScUniv ents))
      ((CanFn a l l2 ps ps2 rs rs2 p q r)
        (match erased bt _ ((ScFn b l0 ps0 rs0 bl bps brs) (ScFn ents l2 ps2 rs2 (canon-scoped ents rules l l2 br bl p) (canon-scoped-tele ents rules ps ps2 br bps q) (canon-scoped-tele ents rules rs rs2 br brs r)))))
      ((CanTyCtor a ps ps2 q) (match erased bt _ ((ScTyCtor b ps0 bps) (ScTyCtor ents ps2 (canon-scoped-tele ents rules ps ps2 br bps q)))))
      ((CanValCtor a ps ps2 r r2 q p) (match erased bt _ ((ScValCtor b ps0 r0 bps b2) (ScValCtor ents ps2 r2 (canon-scoped-tele ents rules ps ps2 br bps q) (canon-scoped ents rules r r2 br b2 p)))))))
  (erased canon-scoped-list : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Term)) ts) (erased (List (Term)) us) (erased (ScopedRules ents rules) br) (erased (ScopedList ents ts) bt)
      (subterm erased (CanonList rules ts us) d) -> (erased (ScopedList ents us) c)
    (match erased d _
      ((CanNil a) (ScNil ents))
      ((CanCons a t u ts2 us2 p q) (match erased bt _ ((ScCons b t0 ts0 b1 b2) (ScCons ents u us2 (canon-scoped ents rules t u br b1 p) (canon-scoped-list ents rules ts2 us2 br b2 q)))))))
  (erased canon-scoped-tele : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (ScopedRules ents rules) br) (erased (ScopedTele ents es) bt)
      (subterm erased (CanonTele rules es fs) d) -> (erased (ScopedTele ents fs) c)
    (match erased d _
      ((CanTNil a) (ScTNil ents))
      ((CanTCons a s i t u es2 fs2 p q) (match erased bt _ ((ScTCons b s0 i0 t0 es0 b1 b2) (ScTCons ents s i u fs2 (canon-scoped ents rules t u br b1 p) (canon-scoped-tele ents rules es2 fs2 br b2 q))))))))


; ---- Well-formedness of a context, which the functions carry beside it: a ranking of its rules
; (mini/canon.sl); its entries' ids below its next id; and its scope, its entries' types, its rules' terms,
; its declared ADTs, its level and its subterm arguments mentioning only its entries, with the built-in
; entries present, so that a rule minted for a fresh entry never mentions that entry, a term in play never
; mentions an entry the context lacks, and a declared constructor's type is a value-constructor former.
(def-adts
  (BoundedEnts : ((Nat) n) ((List (Ent)) ents) -> Type
    enum
    (many BENil : (erased (Nat) n) -> (BoundedEnts n (Nil (Ent))))
    (many BECons : (erased (Nat) n) (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (List (Ent)) rest) (erased (Lt x n) lt) (erased (BoundedEnts n rest) q) ->
       (BoundedEnts n (Cons (Ent) (MkEnt x ty k) rest))))
  (ScopedEnts : ((List (Ent)) ents) ((List (Ent)) es) -> Type
    enum
    (many SENil : (erased (List (Ent)) ents) -> (ScopedEnts ents (Nil (Ent))))
    (many SECons : (erased (List (Ent)) ents) (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (List (Ent)) rest) (erased (Scoped ents ty) b) (erased (ScopedEnts ents rest) q) ->
       (ScopedEnts ents (Cons (Ent) (MkEnt x ty k) rest))))
  (ScopedScope : ((List (Ent)) ents) ((List (Name)) scope) -> Type
    enum
    (many SSNil : (erased (List (Ent)) ents) -> (ScopedScope ents (Nil (Name))))
    (many SSCons : (erased (List (Ent)) ents) (erased (String) s) (erased (Nat) x) (erased (List (Name)) rest) (erased (HasEnt ents x) h) (erased (ScopedScope ents rest) q) -> (ScopedScope ents (Cons (Name) (MkName s x) rest))))
  (AllHasEnt : ((List (Ent)) ents) ((List (Nat)) ids) -> Type
    enum
    (many AHNil : (erased (List (Ent)) ents) -> (AllHasEnt ents (Nil (Nat))))
    (many AHCons : (erased (List (Ent)) ents) (erased (Nat) x) (erased (List (Nat)) ids) (erased (HasEnt ents x) h) (erased (AllHasEnt ents ids) q) -> (AllHasEnt ents (Cons (Nat) x ids))))
  (AllCtor : ((List (Ent)) ents) ((List (Nat)) ids) -> Type
    enum
    (many ACNil : (erased (List (Ent)) ents) -> (AllCtor ents (Nil (Nat))))
    (many ACCons : (erased (List (Ent)) ents) (erased (Nat) x) (erased (List (Nat)) ids) (erased (List (Entry)) fs) (erased (Term) r) (erased (EntOf ents x (ValCtor fs r) (KDecl)) e) (erased (AllCtor ents ids) q) ->
       (AllCtor ents (Cons (Nat) x ids))))
  (ScopedAdts : ((List (Ent)) ents) ((List (Adt)) adts) -> Type
    enum
    (many SANil : (erased (List (Ent)) ents) -> (ScopedAdts ents (Nil (Adt))))
    (many SACons : (erased (List (Ent)) ents) (erased (Nat) t) (erased (List (Nat)) ctors) (erased (List (Adt)) rest) (erased (HasEnt ents t) h) (erased (AllCtor ents ctors) cs) (erased (ScopedAdts ents rest) q) ->
       (ScopedAdts ents (Cons (Adt) (MkAdt t ctors) rest))))
  (ScopedMaybe : ((List (Ent)) ents) ((Maybe (Term)) m) -> Type
    enum
    (many SMNone : (erased (List (Ent)) ents) -> (ScopedMaybe ents (None (Term))))
    (many SMSome : (erased (List (Ent)) ents) (erased (Term) t) (erased (Scoped ents t) p) -> (ScopedMaybe ents (Some (Term) t))))
  (Builtins : ((List (Ent)) ents) -> Type
    enum
    (many MkBuiltins : (erased (List (Ent)) ents) (erased (HasEnt ents (Zero)) h0) (erased (HasEnt ents (Succ (Zero))) h1) (erased (HasEnt ents (Succ (Succ (Zero)))) h2) -> (Builtins ents)))
  ; One list of entries extending another with ids at or above a bound, and a context grown from another:
  ; its next id no lower and its entries extending, everything a term mentions still in play.
  (Ext : ((Nat) n) ((List (Ent)) e0) ((List (Ent)) e1) -> Type
    enum
    (many ExtRefl : (erased (Nat) n) (erased (List (Ent)) e) -> (Ext n e e))
    (many ExtCons : (erased (Nat) n) (erased (List (Ent)) e0) (erased (List (Ent)) e1) (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (Lt n (Succ x)) le) (erased (Ext n e0 e1) p) ->
       (Ext n e0 (Cons (Ent) (MkEnt x ty k) e1))))
  (Grew : ((Ctx) ctx) ((Ctx) out) -> Type
    enum
    (many GrewBy : (erased (Nat) n0) (erased (List (Name)) s0) (erased (List (Ent)) e0) (erased (List (Rule)) r0) (erased (List (Adt)) a0) (erased (Maybe (Term)) l0) (erased (List (Term)) sa0)
       (erased (Nat) n1) (erased (List (Name)) s1) (erased (List (Ent)) e1) (erased (List (Rule)) r1) (erased (List (Adt)) a1) (erased (Maybe (Term)) l1) (erased (List (Term)) sa1)
       (erased (Lt n0 (Succ n1)) le) (erased (Ext n0 e0 e1) ext) -> (Grew (MkCtx n0 s0 e0 r0 a0 l0 sa0) (MkCtx n1 s1 e1 r1 a1 l1 sa1))))
  ; The facts above stated of a context rather than of its entries.
  (Has : ((Ctx) ctx) ((Nat) x) -> Type
    enum
    (many MkHas : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (Nat) x) (erased (HasEnt e x) p) -> (Has (MkCtx n s e r a l sa) x)))
  (HasAll : ((Ctx) ctx) ((List (Nat)) ids) -> Type
    enum
    (many MkHasAll : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (List (Nat)) ids) (erased (AllHasEnt e ids) p) -> (HasAll (MkCtx n s e r a l sa) ids)))
  (Ctors : ((Ctx) ctx) ((List (Nat)) ids) -> Type
    enum
    (many MkCtors : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (List (Nat)) ids) (erased (AllCtor e ids) p) -> (Ctors (MkCtx n s e r a l sa) ids)))
  (EntIs : ((Ctx) ctx) ((Nat) x) ((Term) ty) ((Kind) k) -> Type
    enum
    (many MkEntIs : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (EntOf e x ty k) p) -> (EntIs (MkCtx n s e r a l sa) x ty k)))
  (Ctor : ((Ctx) ctx) ((Nat) c) -> Type
    enum
    (many MkCtor : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (Nat) c) (erased (List (Entry)) fs) (erased (Term) ret) (erased (EntOf e c (ValCtor fs ret) (KDecl)) p) -> (Ctor (MkCtx n s e r a l sa) c)))
  (Tycon : ((Ctx) ctx) ((Nat) tid) -> Type
    enum
    (many MkTycon : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (Nat) tid) (erased (List (Entry)) pt) (erased (EntOf e tid (TyCtor pt) (KDecl)) p) -> (Tycon (MkCtx n s e r a l sa) tid)))
  (Tycons : ((Ctx) ctx) ((List (Nat)) tids) -> Type
    enum
    (many TyNil : (erased (Ctx) ctx) -> (Tycons ctx (Nil (Nat))))
    (many TyCons : (erased (Ctx) ctx) (erased (Nat) tid) (erased (List (Nat)) tids) (erased (Tycon ctx tid) p) (erased (Tycons ctx tids) q) -> (Tycons ctx (Cons (Nat) tid tids))))
  (Sc : ((Ctx) ctx) ((Term) t) -> Type
    enum
    (many MkSc : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (Term) t) (erased (Scoped e t) p) -> (Sc (MkCtx n s e r a l sa) t)))
  (ScL : ((Ctx) ctx) ((List (Term)) ts) -> Type
    enum
    (many MkScL : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (List (Term)) ts) (erased (ScopedList e ts) p) -> (ScL (MkCtx n s e r a l sa) ts)))
  (ScT : ((Ctx) ctx) ((List (Entry)) es) -> Type
    enum
    (many MkScT : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (List (Entry)) es) (erased (ScopedTele e es) p) -> (ScT (MkCtx n s e r a l sa) es)))
  (ScM : ((Ctx) ctx) ((Maybe (Term)) m) -> Type
    enum
    (many MkScM : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (Maybe (Term)) m) (erased (ScopedMaybe e m) p) -> (ScM (MkCtx n s e r a l sa) m)))
  (ScS : ((Ctx) ctx) ((List (Maybe (Term))) sub) -> Type
    enum
    (many MkScS : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (erased (List (Maybe (Term))) sub) (erased (ScopedSub e sub) p) -> (ScS (MkCtx n s e r a l sa) sub)))
  ; The entries a telescope's binders stand for, innermost first, on top of the entries of the context the
  ; telescope was entered from: what abstracting over the binders leaves is scoped there.
  (Covers : ((Nat) n0) ((List (Ent)) e0) ((List (Maybe (Nat))) acc) ((List (Ent)) e1) -> Type
    enum
    (many CovNil : (erased (Nat) n0) (erased (List (Ent)) e) -> (Covers n0 e (Nil (Maybe (Nat))) e))
    (many CovSome : (erased (Nat) n0) (erased (List (Ent)) e0) (erased (List (Maybe (Nat))) acc) (erased (List (Ent)) e1) (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (Lt n0 (Succ x)) le)
       (erased (Covers n0 e0 acc e1) p) -> (Covers n0 e0 (Cons (Maybe (Nat)) (Some (Nat) x) acc) (Cons (Ent) (MkEnt x ty k) e1)))
    (many CovNone : (erased (Nat) n0) (erased (List (Ent)) e0) (erased (List (Maybe (Nat))) acc) (erased (List (Ent)) e1) (erased (Covers n0 e0 acc e1) p) ->
       (Covers n0 e0 (Cons (Maybe (Nat)) (None (Nat)) acc) e1)))
  (Cov : ((Ctx) ctx0) ((List (Maybe (Nat))) acc) ((Ctx) ctx) -> Type
    enum
    (many MkCov : (erased (Nat) n0) (erased (List (Name)) s0) (erased (List (Ent)) e0) (erased (List (Rule)) r0) (erased (List (Adt)) a0) (erased (Maybe (Term)) l0) (erased (List (Term)) sa0)
       (erased (Nat) n1) (erased (List (Name)) s1) (erased (List (Ent)) e1) (erased (List (Rule)) r1) (erased (List (Adt)) a1) (erased (Maybe (Term)) l1) (erased (List (Term)) sa1)
       (erased (List (Maybe (Nat))) acc) (erased (Lt n0 (Succ n1)) le) (erased (Covers n0 e0 acc e1) c) -> (Cov (MkCtx n0 s0 e0 r0 a0 l0 sa0) acc (MkCtx n1 s1 e1 r1 a1 l1 sa1))))
  ; Two lists of one length.
  (LenEq : (Type A) (Type B) ((List A) xs) ((List B) ys) -> Type
    enum
    (many LENil : (erased Type A) (erased Type B) -> (LenEq A B (Nil A) (Nil B)))
    (many LECons : (erased Type A) (erased Type B) (erased A x) (erased B y) (erased (List A) xs) (erased (List B) ys) (erased (LenEq A B xs ys) p) -> (LenEq A B (Cons A x xs) (Cons B y ys))))
  (SameEnt : ((Term) ty) ((Kind) k) ((Term) ty2) ((Kind) k2) -> Type
    enum
    (many SameEntRefl : (erased (Term) ty) (erased (Kind) k) -> (SameEnt ty k ty k))))

(def-fns _ $ erased ext-trans : (erased (Nat) n0) (erased (Nat) n1) (erased (List (Ent)) e0) (erased (List (Ent)) e1) (erased (List (Ent)) e2) (erased (Lt n0 (Succ n1)) le) (erased (Ext n0 e0 e1) p)
    (subterm erased (Ext n1 e1 e2) q) -> (erased (Ext n0 e0 e2) r)
  (match erased q _
    ((ExtRefl a b) p)
    ((ExtCons a b c x ty k le2 q2) (ExtCons n0 e0 c x ty k (le-trans n0 n1 x le le2) (ext-trans n0 n1 e0 e1 c le p q2)))))

(def-fns _ $ erased grew-trans : (erased (Ctx) c1) (erased (Ctx) c2) (erased (Ctx) c3) (erased (Grew c1 c2) g) (erased (Grew c2 c3) h) -> (erased (Grew c1 c3) k)
  (match erased g _
    ((GrewBy n0 s0 e0 r0 a0 l0 sa0 n1 s1 e1 r1 a1 l1 sa1 le ext)
      (match erased h _
        ((GrewBy m1 t1 f1 q1 b1 m1l m1sa n2 s2 e2 r2 a2 l2 sa2 le2 ext2)
          (GrewBy n0 s0 e0 r0 a0 l0 sa0 n2 s2 e2 r2 a2 l2 sa2 (le-trans n0 n1 n2 le le2) (ext-trans n0 n1 e0 e1 e2 le ext ext2)))))))

(def-fns _ $ erased grew-refl : (erased (Ctx) ctx) -> (erased (Grew ctx ctx) g)
  (match erased ctx _ ((MkCtx n s e r a l sa) (GrewBy n s e r a l sa n s e r a l sa (lt-succ n) (ExtRefl n e)))))

(def-fns _ $ erased bounded-ents-weaken : (erased (Nat) n) (erased (Nat) m) (erased (List (Ent)) ents) (erased (Lt n (Succ m)) le) (subterm erased (BoundedEnts n ents) b) -> (erased (BoundedEnts m ents) c)
  (match erased b _
    ((BENil a) (BENil m))
    ((BECons a x ty k rest lt q) (BECons m x ty k rest (lt-le x n m lt le) (bounded-ents-weaken n m rest le q)))))

(def-fns _ $ erased all-lt-weaken : (erased (Nat) n) (erased (Nat) m) (erased (List (Nat)) ks) (erased (Lt n (Succ m)) le) (subterm erased (AllLt ks n) b) -> (erased (AllLt ks m) c)
  (match erased b _
    ((ALNil a) (ALNil m))
    ((ALCons k ks2 a lt q) (ALCons k ks2 m (lt-le k n m lt le) (all-lt-weaken n m ks2 le q)))))

; What the scope, the entries and the ADTs give about the entries they name.
(def-fns _ $ erased scope-has : (erased (List (Ent)) ents) (erased (List (Name)) scope) (erased (String) s) (erased (Nat) x) (erased (ScopedScope ents scope) b) (subterm erased (NameOf scope s x) p) -> (erased (HasEnt ents x) h)
  (match erased p _
    ((NameHere a c rest) (match erased b _ ((SSCons d e g i h q) h)))
    ((NameThere a s2 c y rest nq p2) (match erased b _ ((SSCons d e g i h q) (scope-has ents rest s x q p2))))))

(def-fns _ $ erased ent-of-has : (erased (List (Ent)) ents) (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (subterm erased (EntOf ents x ty k) p) -> (erased (HasEnt ents x) h)
  (match erased p _
    ((EntHere a c d rest) (HEHere x ty k rest))
    ((EntThere a y c ty2 d k2 rest nq p2) (HEThere x (MkEnt y ty2 k2) rest (ent-of-has rest x ty k p2)))))

(def-fns _ $ erased ent-of-scoped : (erased (List (Ent)) all) (erased (List (Ent)) ents) (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (ScopedEnts all ents) b) (subterm erased (EntOf ents x ty k) p) ->
    (erased (Scoped all ty) c)
  (match erased p _
    ((EntHere a c d rest) (match erased b _ ((SECons e g h i j bt q) bt)))
    ((EntThere a y c ty2 d k2 rest nq p2) (match erased b _ ((SECons e g h i j bt q) (ent-of-scoped all rest x ty k q p2))))))

(def-fns _ $ erased ent-of-unique : (erased (List (Ent)) ents) (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (Term) ty2) (erased (Kind) k2) (subterm erased (EntOf ents x ty k) p) (erased (EntOf ents x ty2 k2) q) ->
    (erased (SameEnt ty k ty2 k2) s)
  (match erased p _
    ((EntHere a c d rest)
      (match erased q _
        ((EntHere a2 c2 d2 rest2) (SameEntRefl ty k))
        ((EntThere a2 y c2 ty3 d2 k3 rest2 nq q2) (match erased (neq-irrefl x nq) _))))
    ((EntThere a y c ty3 d k3 rest nq p2)
      (match erased q _
        ((EntHere a2 c2 d2 rest2) (match erased (neq-irrefl x nq) _))
        ((EntThere a2 y2 c2 ty4 d2 k4 rest2 nq2 q2) (ent-of-unique rest x ty k ty2 k2 p2 q2))))))

(def-fns _ $ erased has-ent-lt : (erased (Nat) n) (erased (List (Ent)) ents) (erased (Nat) x) (erased (BoundedEnts n ents) b) (subterm erased (HasEnt ents x) h) -> (erased (Lt x n) lt)
  (match erased h _
    ((HEHere a ty k rest) (match erased b _ ((BECons c d e g i lt q) lt)))
    ((HEThere a e rest p) (match erased b _ ((BECons c d g i j lt q) (has-ent-lt n rest x q p))))))

(def-fns _ $ erased has-ent-no-ent : (erased (List (Ent)) ents) (erased (Nat) x) (subterm erased (HasEnt ents x) h) (erased (NoEnt ents x) m) -> (erased (False) f)
  (match erased h _
    ((HEHere a ty k rest) (match erased m _ ((NoEntCons c y d e g nq p) (neq-irrefl x nq))))
    ((HEThere a e rest p) (match erased m _ ((NoEntCons c y d g i nq q) (has-ent-no-ent rest x p q))))))

(def-fns _ $ erased adt-of-scoped : (erased (List (Ent)) ents) (erased (List (Adt)) adts) (erased (Nat) t) (erased (List (Nat)) ctors) (erased (ScopedAdts ents adts) b) (subterm erased (AdtOf adts t ctors) p) ->
    (erased (HasEnt ents t) h) (erased (AllCtor ents ctors) cs)
  (match erased p _
    ((AdtHere a c rest) (match erased b _ ((SACons d e g i h cs q) (values h cs))))
    ((AdtThere a t2 c ctors2 rest nq p2) (match erased b _ ((SACons d e g i h cs q) (adt-of-scoped ents rest t ctors q p2))))))

; Everything scoped in a list of entries is scoped in one extending it.
(def-fns _ $ erased scoped-ents-weaken : (erased (List (Ent)) ents) (erased (Ent) e) (erased (List (Ent)) es) (subterm erased (ScopedEnts ents es) b) -> (erased (ScopedEnts (Cons (Ent) e ents) es) c)
  (match erased b _
    ((SENil a) (SENil _))
    ((SECons a x ty k rest p q) (SECons _ x ty k rest (scoped-weaken ents e ty p) (scoped-ents-weaken ents e rest q)))))
(def-fns _ $ erased scoped-scope-weaken : (erased (List (Ent)) ents) (erased (Ent) e) (erased (List (Name)) scope) (subterm erased (ScopedScope ents scope) b) -> (erased (ScopedScope (Cons (Ent) e ents) scope) c)
  (match erased b _
    ((SSNil a) (SSNil _))
    ((SSCons a s x rest h q) (SSCons _ s x rest (HEThere x e ents h) (scoped-scope-weaken ents e rest q)))))
(def-fns _ $ erased all-has-weaken : (erased (List (Ent)) ents) (erased (Ent) e) (erased (List (Nat)) ids) (subterm erased (AllHasEnt ents ids) b) -> (erased (AllHasEnt (Cons (Ent) e ents) ids) c)
  (match erased b _
    ((AHNil a) (AHNil _))
    ((AHCons a x rest h q) (AHCons _ x rest (HEThere x e ents h) (all-has-weaken ents e rest q)))))
(def-fns _ $ erased all-ctor-weaken : (erased (Nat) n) (erased (List (Ent)) ents) (erased (Nat) y) (erased (Term) ty) (erased (Kind) k) (erased (List (Nat)) ids) (erased (BoundedEnts n ents) be) (erased (Lt n (Succ y)) le)
    (subterm erased (AllCtor ents ids) b) -> (erased (AllCtor (Cons (Ent) (MkEnt y ty k) ents) ids) c)
  (match erased b _
    ((ACNil a) (ACNil _))
    ((ACCons a x rest fs r p q)
      (ACCons _ x rest fs r (EntThere x y (ValCtor fs r) ty (KDecl) k ents (lt-neq x y (lt-le x n y (has-ent-lt n ents x be (ent-of-has ents x (ValCtor fs r) (KDecl) p)) le)) p) (all-ctor-weaken n ents y ty k rest be le q)))))
(def-fns _ $ erased scoped-adts-weaken : (erased (Nat) n) (erased (List (Ent)) ents) (erased (Nat) y) (erased (Term) ty) (erased (Kind) k) (erased (List (Adt)) adts) (erased (BoundedEnts n ents) be) (erased (Lt n (Succ y)) le)
    (subterm erased (ScopedAdts ents adts) b) -> (erased (ScopedAdts (Cons (Ent) (MkEnt y ty k) ents) adts) c)
  (match erased b _
    ((SANil a) (SANil _))
    ((SACons a t ctors rest h cs q) (SACons _ t ctors rest (HEThere t (MkEnt y ty k) ents h) (all-ctor-weaken n ents y ty k ctors be le cs) (scoped-adts-weaken n ents y ty k rest be le q)))))
(def-fns _ $ erased scoped-maybe-weaken : (erased (List (Ent)) ents) (erased (Ent) e) (erased (Maybe (Term)) m) (erased (ScopedMaybe ents m) b) -> (erased (ScopedMaybe (Cons (Ent) e ents) m) c)
  (match erased b _
    ((SMNone a) (SMNone _))
    ((SMSome a t p) (SMSome _ t (scoped-weaken ents e t p)))))
(def-fns _ $ erased builtins-weaken : (erased (List (Ent)) ents) (erased (Ent) e) (erased (Builtins ents) b) -> (erased (Builtins (Cons (Ent) e ents)) c)
  (match erased b _ ((MkBuiltins a h0 h1 h2) (MkBuiltins _ (HEThere _ e ents h0) (HEThere _ e ents h1) (HEThere _ e ents h2)))))

(def-fns _ $ erased has-ent-ext : (erased (Nat) n) (erased (List (Ent)) e0) (erased (List (Ent)) e1) (erased (Nat) x) (erased (HasEnt e0 x) p) (subterm erased (Ext n e0 e1) ex) -> (erased (HasEnt e1 x) q)
  (match erased ex _
    ((ExtRefl a b) p)
    ((ExtCons a b c y ty k le ex2) (HEThere x (MkEnt y ty k) c (has-ent-ext n e0 c x p ex2)))))
(def-fns _ $ erased all-has-ext : (erased (Nat) n) (erased (List (Ent)) e0) (erased (List (Ent)) e1) (erased (List (Nat)) ids) (erased (AllHasEnt e0 ids) p) (subterm erased (Ext n e0 e1) ex) -> (erased (AllHasEnt e1 ids) q)
  (match erased ex _
    ((ExtRefl a b) p)
    ((ExtCons a b c y ty k le ex2) (all-has-weaken c (MkEnt y ty k) ids (all-has-ext n e0 c ids p ex2)))))
(def-fns _ $ erased ent-of-ext : (erased (Nat) n) (erased (List (Ent)) e0) (erased (List (Ent)) e1) (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (BoundedEnts n e0) be) (erased (EntOf e0 x ty k) p)
    (subterm erased (Ext n e0 e1) ex) -> (erased (EntOf e1 x ty k) q)
  (match erased ex _
    ((ExtRefl a b) p)
    ((ExtCons a b c y ty2 k2 le ex2)
      (EntThere x y ty ty2 k k2 c (lt-neq x y (lt-le x n y (has-ent-lt n e0 x be (ent-of-has e0 x ty k p)) le)) (ent-of-ext n e0 c x ty k be p ex2)))))
(def-fns _ $ erased all-ctor-ext : (erased (Nat) n) (erased (List (Ent)) e0) (erased (List (Ent)) e1) (erased (List (Nat)) ids) (erased (BoundedEnts n e0) be) (subterm erased (AllCtor e0 ids) p) (erased (Ext n e0 e1) ex) ->
    (erased (AllCtor e1 ids) q)
  (match erased p _
    ((ACNil a) (ACNil _))
    ((ACCons a x rest fs r e q) (ACCons _ x rest fs r (ent-of-ext n e0 e1 x (ValCtor fs r) (KDecl) be e ex) (all-ctor-ext n e0 e1 rest be q ex)))))
(def-fns _ $ erased scoped-ext : (erased (Nat) n) (erased (List (Ent)) e0) (erased (List (Ent)) e1) (erased (Term) t) (erased (Scoped e0 t) p) (subterm erased (Ext n e0 e1) ex) -> (erased (Scoped e1 t) q)
  (match erased ex _
    ((ExtRefl a b) p)
    ((ExtCons a b c y ty k le ex2) (scoped-weaken c (MkEnt y ty k) t (scoped-ext n e0 c t p ex2)))))
(def-fns _ $ erased scoped-ext-list : (erased (Nat) n) (erased (List (Ent)) e0) (erased (List (Ent)) e1) (erased (List (Term)) ts) (erased (ScopedList e0 ts) p) (subterm erased (Ext n e0 e1) ex) -> (erased (ScopedList e1 ts) q)
  (match erased ex _
    ((ExtRefl a b) p)
    ((ExtCons a b c y ty k le ex2) (scoped-weaken-list c (MkEnt y ty k) ts (scoped-ext-list n e0 c ts p ex2)))))
(def-fns _ $ erased scoped-ext-tele : (erased (Nat) n) (erased (List (Ent)) e0) (erased (List (Ent)) e1) (erased (List (Entry)) es) (erased (ScopedTele e0 es) p) (subterm erased (Ext n e0 e1) ex) -> (erased (ScopedTele e1 es) q)
  (match erased ex _
    ((ExtRefl a b) p)
    ((ExtCons a b c y ty k le ex2) (scoped-weaken-tele c (MkEnt y ty k) es (scoped-ext-tele n e0 c es p ex2)))))
(def-fns _ $ erased scoped-ext-sub : (erased (Nat) n) (erased (List (Ent)) e0) (erased (List (Ent)) e1) (erased (List (Maybe (Term))) sub) (erased (ScopedSub e0 sub) p) (subterm erased (Ext n e0 e1) ex) -> (erased (ScopedSub e1 sub) q)
  (match erased ex _
    ((ExtRefl a b) p)
    ((ExtCons a b c y ty k le ex2) (scoped-weaken-sub c (MkEnt y ty k) sub (scoped-ext-sub n e0 c sub p ex2)))))
(def-fns _ $ erased scoped-ext-maybe : (erased (Nat) n) (erased (List (Ent)) e0) (erased (List (Ent)) e1) (erased (Maybe (Term)) m) (erased (ScopedMaybe e0 m) p) (subterm erased (Ext n e0 e1) ex) -> (erased (ScopedMaybe e1 m) q)
  (match erased ex _
    ((ExtRefl a b) p)
    ((ExtCons a b c y ty k le ex2) (scoped-maybe-weaken c (MkEnt y ty k) m (scoped-ext-maybe n e0 c m p ex2)))))
(def-fns _ $ erased scoped-scope-ext : (erased (Nat) n) (erased (List (Ent)) e0) (erased (List (Ent)) e1) (erased (List (Name)) scope) (erased (ScopedScope e0 scope) p) (subterm erased (Ext n e0 e1) ex) -> (erased (ScopedScope e1 scope) q)
  (match erased ex _
    ((ExtRefl a b) p)
    ((ExtCons a b c y ty k le ex2) (scoped-scope-weaken c (MkEnt y ty k) scope (scoped-scope-ext n e0 c scope p ex2)))))

; A covering extends the entries, and what it says of a free reference.
(def-fns _ $ erased covers-ext : (erased (Nat) n0) (erased (List (Ent)) e0) (erased (List (Maybe (Nat))) acc) (erased (List (Ent)) e1) (subterm erased (Covers n0 e0 acc e1) c) -> (erased (Ext n0 e0 e1) x)
  (match erased c _
    ((CovNil a b) (ExtRefl n0 e0))
    ((CovSome a b acc2 e2 y ty k le c2) (ExtCons n0 e0 e2 y ty k le (covers-ext n0 e0 acc2 e2 c2)))
    ((CovNone a b acc2 e2 c2) (covers-ext n0 e0 acc2 e2 c2))))
(def-fns _ $ erased covers-has : (erased (Nat) n0) (erased (List (Ent)) e0) (erased (List (Maybe (Nat))) acc) (erased (List (Ent)) e1) (erased (Nat) x) (erased (NotIn acc x) ni) (subterm erased (Covers n0 e0 acc e1) c)
    (erased (HasEnt e1 x) h) -> (erased (HasEnt e0 x) h2)
  (match erased c _
    ((CovNil a b) h)
    ((CovSome a b acc2 e2 y ty k le c2)
      (match erased h _
        ((HEHere a2 ty2 k2 rest) (match erased ni _ ((NotInSome x2 y2 rest2 nq p) (match erased (neq-irrefl x nq) _))))
        ((HEThere a2 ent rest p) (match erased ni _ ((NotInSome x2 y2 rest2 nq p2) (covers-has n0 e0 acc2 e2 x p2 c2 p))))))
    ((CovNone a b acc2 e2 c2) (match erased ni _ ((NotInNone x2 rest p) (covers-has n0 e0 acc2 e2 x p c2 h))))))

(def-fns _
  (erased abstract-covers : (erased (Nat) n0) (erased (List (Ent)) e0) (erased (List (Maybe (Nat))) ids) (erased (List (Ent)) e1) (erased (Term) t) (erased (Term) u) (erased (Covers n0 e0 ids e1) c)
      (erased (Scoped e1 t) bt) (subterm erased (Abstract ids t u) d) -> (erased (Scoped e0 u) su)
    (match erased d _
      ((AbsFree a x p) (match erased bt _ ((ScRef b x0 h) (ScRef e0 x (covers-has n0 e0 ids e1 x p c h)))))
      ((AbsHit a x k p) (ScBound e0 k))
      ((AbsBound a k) (ScBound e0 k))
      ((AbsApp a h h2 as as2 p q) (match erased bt _ ((ScApp b h0 as0 bh bas) (ScApp e0 h2 as2 (abstract-covers n0 e0 ids e1 h h2 c bh p) (abstract-covers-list n0 e0 ids e1 as as2 c bas q)))))
      ((AbsUniv a) (ScUniv e0))
      ((AbsFn a l l2 ps ps2 rs rs2 ids1 ids2 p q r)
        (match erased bt _
          ((ScFn b l0 ps0 rs0 bl bps brs)
            (let (erased sps) (erased c1) (abstract-covers-tele n0 e0 ids e1 ps ps2 ids1 c bps q))
            (let (erased srs) (erased c2) (abstract-covers-tele n0 e0 ids1 e1 rs rs2 ids2 c1 brs r))
            (ScFn e0 l2 ps2 rs2 (abstract-covers n0 e0 ids e1 l l2 c bl p) sps srs))))
      ((AbsTyCtor a ps ps2 ids1 q)
        (match erased bt _ ((ScTyCtor b ps0 bps) (let (erased sps) (erased c1) (abstract-covers-tele n0 e0 ids e1 ps ps2 ids1 c bps q)) (ScTyCtor e0 ps2 sps))))
      ((AbsValCtor a ps ps2 r r2 ids1 q p)
        (match erased bt _
          ((ScValCtor b ps0 r0 bps br)
            (let (erased sps) (erased c1) (abstract-covers-tele n0 e0 ids e1 ps ps2 ids1 c bps q))
            (ScValCtor e0 ps2 r2 sps (abstract-covers n0 e0 ids1 e1 r r2 c1 br p)))))))
  (erased abstract-covers-list : (erased (Nat) n0) (erased (List (Ent)) e0) (erased (List (Maybe (Nat))) ids) (erased (List (Ent)) e1) (erased (List (Term)) ts) (erased (List (Term)) us) (erased (Covers n0 e0 ids e1) c)
      (erased (ScopedList e1 ts) bt) (subterm erased (AbstractList ids ts us) d) -> (erased (ScopedList e0 us) su)
    (match erased d _
      ((AbsNil a) (ScNil e0))
      ((AbsCons a t u ts2 us2 p q) (match erased bt _ ((ScCons b t0 ts0 b1 b2) (ScCons e0 u us2 (abstract-covers n0 e0 ids e1 t u c b1 p) (abstract-covers-list n0 e0 ids e1 ts2 us2 c b2 q)))))))
  (erased abstract-covers-tele : (erased (Nat) n0) (erased (List (Ent)) e0) (erased (List (Maybe (Nat))) ids) (erased (List (Ent)) e1) (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (List (Maybe (Nat))) out)
      (erased (Covers n0 e0 ids e1) c) (erased (ScopedTele e1 es) bt) (subterm erased (AbstractTele ids es fs out) d) -> (erased (ScopedTele e0 fs) su) (erased (Covers n0 e0 out e1) c2)
    (match erased d _
      ((AbsTNil a) (values (ScTNil e0) c))
      ((AbsTCons a s i t u es2 fs2 out2 p q)
        (match erased bt _
          ((ScTCons b s0 i0 t0 es0 b1 b2)
            (let (erased sfs) (erased c2) (abstract-covers-tele n0 e0 (Cons _ (None _) ids) e1 es2 fs2 out2 (CovNone n0 e0 ids e1 c) b2 q))
            (values (ScTCons e0 s i u fs2 (abstract-covers n0 e0 ids e1 t u c b1 p) sfs) c2)))))))

(def-fns _
  (erased below-cons : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (Term) t) (erased (Nat) k) (erased (Term) s) (erased (Nat) top)
      (erased (BoundedEnts n ents) be) (erased (Scoped ents t) bt) (subterm erased (Below rules ranks t k) b) -> (erased (Below (Cons (Rule) (MkRule n s) rules) (Cons (Nat) top ranks) t k) c)
    (match erased b _
      ((BlFree a c x d p) (match erased bt _ ((ScRef e g h) (BlFree _ _ x k (NoRuleCons x n s rules (lt-neq x n (has-ent-lt n ents x be h)) p)))))
      ((BlRuled a c x d r j p lt) (match erased bt _ ((ScRef e g h) (BlRuled _ _ x k r j (RRThere x n r s j top rules ranks (lt-neq x n (has-ent-lt n ents x be h)) p) lt))))
      ((BlBound a c i d) (BlBound _ _ i k))
      ((BlApp a c h as d p q) (match erased bt _ ((ScApp e h0 as0 bh bas) (BlApp _ _ h as k (below-cons n ents rules ranks h k s top be bh p) (below-cons-list n ents rules ranks as k s top be bas q)))))
      ((BlUniv a c d) (BlUniv _ _ k))
      ((BlFn a c l ps rs d p q r)
        (match erased bt _
          ((ScFn e l0 ps0 rs0 bl bps brs)
            (BlFn _ _ l ps rs k (below-cons n ents rules ranks l k s top be bl p) (below-cons-tele n ents rules ranks ps k s top be bps q) (below-cons-tele n ents rules ranks rs k s top be brs r)))))
      ((BlTyCtor a c ps d q) (match erased bt _ ((ScTyCtor e ps0 bps) (BlTyCtor _ _ ps k (below-cons-tele n ents rules ranks ps k s top be bps q)))))
      ((BlValCtor a c ps r d q p)
        (match erased bt _ ((ScValCtor e ps0 r0 bps br) (BlValCtor _ _ ps r k (below-cons-tele n ents rules ranks ps k s top be bps q) (below-cons n ents rules ranks r k s top be br p)))))))
  (erased below-cons-list : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (List (Term)) ts) (erased (Nat) k) (erased (Term) s) (erased (Nat) top)
      (erased (BoundedEnts n ents) be) (erased (ScopedList ents ts) bt) (subterm erased (BelowList rules ranks ts k) b) -> (erased (BelowList (Cons (Rule) (MkRule n s) rules) (Cons (Nat) top ranks) ts k) c)
    (match erased b _
      ((BlNil a c d) (BlNil _ _ k))
      ((BlCons a c t ts2 d p q) (match erased bt _ ((ScCons e t0 ts0 b1 b2) (BlCons _ _ t ts2 k (below-cons n ents rules ranks t k s top be b1 p) (below-cons-list n ents rules ranks ts2 k s top be b2 q)))))))
  (erased below-cons-tele : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (List (Entry)) es) (erased (Nat) k) (erased (Term) s) (erased (Nat) top)
      (erased (BoundedEnts n ents) be) (erased (ScopedTele ents es) bt) (subterm erased (BelowTele rules ranks es k) b) -> (erased (BelowTele (Cons (Rule) (MkRule n s) rules) (Cons (Nat) top ranks) es k) c)
    (match erased b _
      ((BlTNil a c d) (BlTNil _ _ k))
      ((BlTCons a c s0 i t es2 d p q)
        (match erased bt _ ((ScTCons e s1 i1 t0 es0 b1 b2) (BlTCons _ _ s0 i t es2 k (below-cons n ents rules ranks t k s top be b1 p) (below-cons-tele n ents rules ranks es2 k s top be b2 q))))))))

(def-fns _ $ erased valid-cons : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) all) (erased (List (Nat)) ar) (erased (List (Rule)) rs) (erased (List (Nat)) ks) (erased (Term) s) (erased (Nat) top)
    (erased (BoundedEnts n ents) be) (erased (ScopedRules ents rs) sr) (subterm erased (ValidFrom all ar rs ks) v) -> (erased (ValidFrom (Cons (Rule) (MkRule n s) all) (Cons (Nat) top ar) rs ks) w)
  (match erased v _
    ((VFNil a c) (VFNil _ _))
    ((VFCons a c x r k rs2 ks2 bl p) (match erased sr _ ((SRCons d e g h bt q) (VFCons _ _ x r k rs2 ks2 (below-cons n ents all ar r k s top be bt bl) (valid-cons n ents all ar rs2 ks2 s top be q p)))))))

(def-fns _
  (erased below-lift : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (Term) t) (erased (Nat) k) (subterm erased (Below rules ranks t k) b) -> (erased (Below rules ranks t (Succ k)) c)
    (match erased b _
      ((BlFree a c x d p) (BlFree rules ranks x (Succ k) p))
      ((BlRuled a c x d r j p lt) (BlRuled rules ranks x (Succ k) r j p (lt-weaken j k lt)))
      ((BlBound a c i d) (BlBound rules ranks i (Succ k)))
      ((BlApp a c h as d p q) (BlApp rules ranks h as (Succ k) (below-lift rules ranks h k p) (below-lift-list rules ranks as k q)))
      ((BlUniv a c d) (BlUniv rules ranks (Succ k)))
      ((BlFn a c l ps rs d p q r) (BlFn rules ranks l ps rs (Succ k) (below-lift rules ranks l k p) (below-lift-tele rules ranks ps k q) (below-lift-tele rules ranks rs k r)))
      ((BlTyCtor a c ps d q) (BlTyCtor rules ranks ps (Succ k) (below-lift-tele rules ranks ps k q)))
      ((BlValCtor a c ps r d q p) (BlValCtor rules ranks ps r (Succ k) (below-lift-tele rules ranks ps k q) (below-lift rules ranks r k p)))))
  (erased below-lift-list : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (List (Term)) ts) (erased (Nat) k) (subterm erased (BelowList rules ranks ts k) b) -> (erased (BelowList rules ranks ts (Succ k)) c)
    (match erased b _
      ((BlNil a c d) (BlNil rules ranks (Succ k)))
      ((BlCons a c t ts2 d p q) (BlCons rules ranks t ts2 (Succ k) (below-lift rules ranks t k p) (below-lift-list rules ranks ts2 k q)))))
  (erased below-lift-tele : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (List (Entry)) es) (erased (Nat) k) (subterm erased (BelowTele rules ranks es k) b) -> (erased (BelowTele rules ranks es (Succ k)) c)
    (match erased b _
      ((BlTNil a c d) (BlTNil rules ranks (Succ k)))
      ((BlTCons a c s i t es2 d p q) (BlTCons rules ranks s i t es2 (Succ k) (below-lift rules ranks t k p) (below-lift-tele rules ranks es2 k q))))))

; The new rule's own term, below the top rank under the old ranking, sits below its rank, the top plus one.
(def-fns _ $ erased below-top : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (Term) s) (erased (Nat) top)
    (erased (BoundedEnts n ents) be) (erased (Scoped ents s) bs) (erased (Below rules ranks s top) b) -> (erased (Below (Cons (Rule) (MkRule n s) rules) (Cons (Nat) top ranks) s (Succ top)) c)
  (below-cons n ents rules ranks s (Succ top) s top be bs (below-lift rules ranks s top b)))

(MkUnit)
