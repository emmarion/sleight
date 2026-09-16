; mini/elabfn.sl -- the functions that derive mini/elab.sl's relations: for every judgment, a function that,
; given fuel, computes the outcome and its derivation, or answers stuck. Helpers first, in the order the
; relations were declared. One session's proposal.

; ---- Helpers over the context and lists, each returning what it built with its derivation.

(def-fns _ $ many mint : (many (Ctx) ctx) (many (Maybe (String)) name) (many (Term) ty) (many (Kind) k) (many (Maybe (Term)) rule) -> (many (Nat) id) (many (Ctx) out) (erased (Mint ctx name ty k rule id out) p)
  (match many ctx _
    ((MkCtx n s e r a l sa)
      (let (many s2) (erased an)
        (match many name (((List (Name)) s2) ((AddName s name n s2) an))
          ((None b) (values s (AddNameNone s n)))
          ((Some b nm) (values (Cons _ (MkName nm n) s) (AddNameSome s nm n)))))
      (let (many r2) (erased ar)
        (match many rule (((List (Rule)) r2) ((AddRule r rule n r2) ar))
          ((None b) (values r (AddRuleNone r n)))
          ((Some b t) (values (Cons _ (MkRule n t) r) (AddRuleSome r t n)))))
      (values n (MkCtx (Succ n) s2 (Cons _ (MkEnt n ty k) e) r2 a l sa) (MintTo n s e r a l sa name ty k rule s2 r2 an ar)))))

(def-fns _ $ many ctx-ents : (many (Ctx) ctx) -> (many (List (Ent)) ents) (erased (Ents ctx ents) p)
  (match many ctx _ ((MkCtx n s e r a l sa) (values e (EntsOf n s e r a l sa)))))
(def-fns _ $ many ctx-rules : (many (Ctx) ctx) -> (many (List (Rule)) rules) (erased (Rules ctx rules) p)
  (match many ctx _ ((MkCtx n s e r a l sa) (values r (RulesOf n s e r a l sa)))))
(def-fns _ $ many ctx-scope : (many (Ctx) ctx) -> (many (List (Name)) scope) (erased (Scope ctx scope) p)
  (match many ctx _ ((MkCtx n s e r a l sa) (values s (ScopeOf n s e r a l sa)))))
(def-fns _ $ many ctx-adts : (many (Ctx) ctx) -> (many (List (Adt)) adts) (erased (Adts ctx adts) p)
  (match many ctx _ ((MkCtx n s e r a l sa) (values a (AdtsOf n s e r a l sa)))))
(def-fns _ $ many ctx-level : (many (Ctx) ctx) -> (many (Maybe (Term)) level) (erased (Level ctx level) p)
  (match many ctx _ ((MkCtx n s e r a l sa) (values l (LevelOf n s e r a l sa)))))
(def-fns _ $ many ctx-subargs : (many (Ctx) ctx) -> (many (List (Term)) subargs) (erased (SubArgs ctx subargs) p)
  (match many ctx _ ((MkCtx n s e r a l sa) (values sa (SubArgsOf n s e r a l sa)))))
(def-fns _ $ many leave : (many (Ctx) inner) (many (Ctx) outer) -> (many (Ctx) out) (erased (Leave inner outer out) p)
  (match many inner _
    ((MkCtx n s e r a l sa)
      (match many outer _
        ((MkCtx n0 s0 e0 r0 a0 l0 sa0) (values (MkCtx n s0 e0 r0 a0 l0 sa0) (LeaveTo n s e r a l sa n0 s0 e0 r0 a0 l0 sa0)))))))
(def-fns _ $ many hide : (many (Ctx) inner) (many (List (Name)) s0) -> (many (Ctx) out) (erased (Hide inner s0 out) p)
  (match many inner _ ((MkCtx n s e r a l sa) (values (MkCtx n s0 e r a l sa) (HideTo n s e r a l sa s0)))))
(def-fns _ $ many enter : (many (Ctx) ctx) (many (Term) l2) (many (List (Term)) sa2) -> (many (Ctx) out) (erased (Enter ctx l2 sa2 out) p)
  (match many ctx _ ((MkCtx n s e r a l sa) (values (MkCtx n s e r a (Some _ l2) sa2) (EnterTo n s e r a l sa l2 sa2)))))
(def-fns _ $ many with-rules : (many (Ctx) ctx) (many (List (Rule)) r2) -> (many (Ctx) out) (erased (WithRules ctx r2 out) p)
  (match many ctx _ ((MkCtx n s e r a l sa) (values (MkCtx n s e r2 a l sa) (WithRulesTo n s e r a l sa r2)))))
(def-fns _ $ many add-adt : (many (Ctx) ctx) (many (Adt) adt) -> (many (Ctx) out) (erased (AddAdt ctx adt out) p)
  (match many ctx _ ((MkCtx n s e r a l sa) (values (MkCtx n s e r (Cons _ adt a) l sa) (AddAdtTo n s e r a l sa adt)))))

(def-fns _ $ many snoc : (subterm many (List (Maybe (Term))) xs) (many (Maybe (Term)) x) -> (many (List (Maybe (Term))) out) (erased (Snoc xs x out) p)
  (match many xs _
    ((Nil a) (values (Cons _ x (Nil _)) (SnocNil x)))
    ((Cons a y ys) (let (many out) (erased p) (snoc ys x)) (values (Cons _ y out) (SnocCons y ys x out p)))))
(def-fns _ $ many somes : (subterm many (List (Term)) as) -> (many (List (Maybe (Term))) sub) (erased (Somes as sub) p)
  (match many as _
    ((Nil a) (values (Nil _) (SomesNil)))
    ((Cons a t ts) (let (many sub) (erased p) (somes ts)) (let (many out) (erased q) (snoc sub (Some _ t))) (values out (SomesCons t ts sub out p q)))))
(def-fns _ $ many snoc-id : (subterm many (List (Maybe (Nat))) xs) (many (Maybe (Nat)) x) -> (many (List (Maybe (Nat))) out) (erased (SnocId xs x out) p)
  (match many xs _
    ((Nil a) (values (Cons _ x (Nil _)) (SnocIdNil x)))
    ((Cons a y ys) (let (many out) (erased p) (snoc-id ys x)) (values (Cons _ y out) (SnocIdCons y ys x out p)))))
(def-fns _ $ many binders : (subterm many (List (Nat)) ids) -> (many (List (Maybe (Nat))) acc) (erased (Binders ids acc) p)
  (match many ids _
    ((Nil a) (values (Nil _) (BindersNil)))
    ((Cons a x rest) (let (many acc) (erased p) (binders rest)) (let (many out) (erased q) (snoc-id acc (Some _ x))) (values out (BindersCons x rest acc out p q)))))
(def-fns _ $ many refs : (subterm many (List (Nat)) ids) -> (many (List (Term)) ts) (erased (Refs ids ts) p)
  (match many ids _
    ((Nil a) (values (Nil _) (RefsNil)))
    ((Cons a x rest) (let (many ts) (erased p) (refs rest)) (values (Cons _ (Ref x) ts) (RefsCons x rest ts p)))))
(def-fns _ $ many nones : (subterm many (List (Entry)) es) -> (many (List (Maybe (String))) names) (erased (Nones es names) p)
  (match many es _
    ((Nil a) (values (Nil _) (NonesNil)))
    ((Cons a e rest) (let (many names) (erased p) (nones rest)) (values (Cons _ (None _) names) (NonesCons e rest names p)))))
(def-fns _ $ many list-len : (erased Type A) (subterm many (List A) xs) -> (many (Nat) n) (erased (Length A xs n) p)
  (match many xs _
    ((Nil a) (values (Zero) (LenNil _)))
    ((Cons a x rest) (let (many n) (erased p) (list-len _ rest)) (values (Succ n) (LenCons _ x rest n p)))))
(def-fns _ $ many append : (subterm many (List (Nat)) xs) (many (List (Nat)) ys) -> (many (List (Nat)) out) (erased (Append xs ys out) p)
  (match many xs _
    ((Nil a) (values ys (AppendNil ys)))
    ((Cons a x rest) (let (many out) (erased p) (append rest ys)) (values (Cons _ x out) (AppendCons x rest ys out p)))))

(def-adts
  (MarkedDec : ((List (Entry)) tele) ((List (Nat)) ids) -> Type
    enum
    (many MkMarked : (erased (List (Entry)) tele) (erased (List (Nat)) ids) (many (List (Term)) out) (erased (Marked tele ids out) p) -> (MarkedDec tele ids))
    (many MarkedStuck : (erased (List (Entry)) tele) (erased (List (Nat)) ids) -> (MarkedDec tele ids))))
(def-fns _ $ many marked : (subterm many (List (Entry)) tele) (many (List (Nat)) ids) -> (many (MarkedDec tele ids) r)
  (match many tele _
    ((Nil a) (match many ids _ ((Nil b) (MkMarked _ _ (Nil _) (MarkedNil))) ((Cons b x rest) (MarkedStuck _ _))))
    ((Cons a e es)
      (match many ids _
        ((Nil b) (MarkedStuck _ _))
        ((Cons b x rest)
          (match many e _
            ((MkEntry s i t)
              (match many (marked es rest) _
                ((MarkedStuck c d) (MarkedStuck _ _))
                ((MkMarked c d out p)
                  (match many s _
                    ((BTrue) (MkMarked _ _ (Cons _ (Ref x) out) (MarkedYes i t es x rest out p)))
                    ((BFalse) (MkMarked _ _ out (MarkedNo i t es x rest out p)))))))))))))

(def-adts
  (AtomNamesDec : ((List (Raw)) raws) -> Type
    enum
    (many MkAtomNames : (erased (List (Raw)) raws) (many (List (Maybe (String))) names) (erased (AtomNames raws names) p) -> (AtomNamesDec raws))
    (many AtomNamesStuck : (erased (List (Raw)) raws) -> (AtomNamesDec raws))))
(def-fns _ $ many atom-names : (subterm many (List (Raw)) raws) -> (many (AtomNamesDec raws) r)
  (match many raws _
    ((Nil a) (MkAtomNames _ (Nil _) (ANNil)))
    ((Cons a r rest)
      (match many r _
        ((RAtom x)
          (match many (atom-names rest) _
            ((AtomNamesStuck b) (AtomNamesStuck _))
            ((MkAtomNames b names p) (MkAtomNames _ (Cons _ (Some _ x) names) (ANCons x rest names p)))))
        (else (AtomNamesStuck _))))))

; Membership of an id in a list, decided.
(def-adts
  (MemDec : ((Nat) x) ((List (Nat)) xs) -> Type
    enum
    (many MemYes : (erased (Nat) x) (erased (List (Nat)) xs) (erased (Mem x xs) p) -> (MemDec x xs))
    (many MemNo : (erased (Nat) x) (erased (List (Nat)) xs) (erased (NotMem x xs) p) -> (MemDec x xs))))
(def-fns _ $ many mem-dec : (many (Nat) x) (subterm many (List (Nat)) xs) -> (many (MemDec x xs) r)
  (match many xs _
    ((Nil a) (MemNo _ _ (NotMemNil x)))
    ((Cons a y rest)
      (match many (nat-dec x y) _
        ((NDSame z) (MemYes _ _ (MemHere x rest)))
        ((NDDiff z w n)
          (match many (mem-dec x rest) _
            ((MemYes b c p) (MemYes _ _ (MemThere x y rest p)))
            ((MemNo b c p) (MemNo _ _ (NotMemCons x y rest n p)))))))))

; Whether a list has exactly one entry.
(def-adts
  (OneDec : ((List (Nat)) ids) -> Type
    enum
    (many OneYes : (many (Nat) x) -> (OneDec (Cons (Nat) x (Nil (Nat)))))
    (many OneNo : (erased (List (Nat)) ids) (erased (NotOne ids) p) -> (OneDec ids))))
(def-fns _ $ many one-dec : (many (List (Nat)) ids) -> (many (OneDec ids) r)
  (match many ids _
    ((Nil a) (OneNo _ (NotOneNil)))
    ((Cons a x rest)
      (match many rest _
        ((Nil b) (OneYes x))
        ((Cons b y more) (OneNo _ (NotOneMore x y more)))))))

; Two lists of one length, or evidence that they differ.
(def-adts
  (LenDec : (Type A) (Type B) ((List A) xs) ((List B) ys) -> Type
    enum
    (many LenSame : (erased Type A) (erased Type B) (erased (List A) xs) (erased (List B) ys) -> (LenDec A B xs ys))
    (many LenDiff : (erased Type A) (erased Type B) (erased (List A) xs) (erased (List B) ys) (erased (LenMismatch A B xs ys) p) -> (LenDec A B xs ys))))
(def-fns _ $ many len-dec : (erased Type A) (erased Type B) (subterm many (List A) xs) (many (List B) ys) -> (many (LenDec A B xs ys) r)
  (match many xs _
    ((Nil a) (match many ys _ ((Nil b) (LenSame _ _ _ _)) ((Cons b y ys2) (LenDiff _ _ _ _ (LMNilCons _ _ y ys2)))))
    ((Cons a x xs2)
      (match many ys _
        ((Nil b) (LenDiff _ _ _ _ (LMConsNil _ _ x xs2)))
        ((Cons b y ys2)
          (match many (len-dec _ _ xs2 ys2) _
            ((LenSame c d e f) (LenSame _ _ _ _))
            ((LenDiff c d e f p) (LenDiff _ _ _ _ (LMCons _ _ x y xs2 ys2 p)))))))))

; A list's length against a number.
(def-adts
  (NotLenDec : ((Nat) n) ((List (Term)) as) -> Type
    enum
    (many LenIs : (erased (Nat) n) (erased (List (Term)) as) (erased (Length (Term) as n) p) -> (NotLenDec n as))
    (many LenIsNot : (erased (Nat) n) (erased (List (Term)) as) (erased (NotLen n as) p) -> (NotLenDec n as))))
(def-fns _ $ many not-len-dec : (many (Nat) n) (subterm many (List (Term)) as) -> (many (NotLenDec n as) r)
  (match many as _
    ((Nil a) (match many n _ ((Zero) (LenIs _ _ (LenNil _))) ((Succ m) (LenIsNot _ _ (NLNilSucc m)))))
    ((Cons a t rest)
      (match many n _
        ((Zero) (LenIsNot _ _ (NLConsZero t rest)))
        ((Succ m)
          (match many (not-len-dec m rest) _
            ((LenIs b c p) (LenIs _ _ (LenCons _ t rest m p)))
            ((LenIsNot b c p) (LenIsNot _ _ (NLCons m t rest p)))))))))

; ---- Context-level decisions: the type and kind of an entry, canonical forms, identity, refinement.

(def-adts
  (TypeOfDec : ((Ctx) ctx) ((Nat) x) -> Type
    enum
    (many TypeIs : (erased (Ctx) ctx) (erased (Nat) x) (many (Term) ty) (many (Kind) k) (erased (TypeOf ctx x ty) p) (erased (KindOf ctx x k) q) -> (TypeOfDec ctx x))
    (many TypeOfStuck : (erased (Ctx) ctx) (erased (Nat) x) -> (TypeOfDec ctx x))))
(def-fns _ $ many type-of : (many (Ctx) ctx) (many (Nat) x) -> (many (TypeOfDec ctx x) r)
  (let (many ents) (erased pe) (ctx-ents ctx))
  (match many (ent-dec ents x) _
    ((EntMiss a b m) (TypeOfStuck _ _))
    ((EntHit a b ty k p) (TypeIs _ _ ty k (TypeOfBy ctx x ty k ents pe p) (KindOfBy ctx x ty k ents pe p)))))

(def-adts
  (CanonicalDec : ((Ctx) ctx) ((Term) t) -> Type
    enum
    (many CanonicalIs : (erased (Ctx) ctx) (erased (Term) t) (many (Term) u) (erased (Canonical ctx t u) p) -> (CanonicalDec ctx t))
    (many CanonicalStuck : (erased (Ctx) ctx) (erased (Term) t) -> (CanonicalDec ctx t))))
(def-fns _ $ many canonical : (many (Nat) fuel) (many (Ctx) ctx) (many (Term) t) -> (many (CanonicalDec ctx t) r)
  (let (many rules) (erased pr) (ctx-rules ctx))
  (match many (canon fuel rules t) _
    ((CanonStuck a b) (CanonicalStuck _ _))
    ((MkCanoned a b u p) (CanonicalIs _ _ u (CanonicalBy ctx t u rules pr p)))))

(def-adts
  (SameDec : ((Ctx) ctx) ((Term) t) ((Term) u) -> Type
    enum
    (many SDSame : (erased (Ctx) ctx) (erased (Term) t) (erased (Term) u) (erased (Same ctx t u) p) -> (SameDec ctx t u))
    (many SDDiffer : (erased (Ctx) ctx) (erased (Term) t) (erased (Term) u) (erased (Differ ctx t u) p) -> (SameDec ctx t u))
    (many SDStuck : (erased (Ctx) ctx) (erased (Term) t) (erased (Term) u) -> (SameDec ctx t u))))
(def-fns _ $ many same-dec : (many (Nat) fuel) (many (Ctx) ctx) (many (Term) t) (many (Term) u) -> (many (SameDec ctx t u) r)
  (let (many ents) (erased pe) (ctx-ents ctx))
  (let (many rules) (erased pr) (ctx-rules ctx))
  (match many (unify fuel (Check) ents rules (Cons _ (MkEqn t u) (Nil _))) _
    ((UnifyStuck a b c d) (SDStuck _ _ _))
    ((MkUnified a b c d out p)
      (match many out _
        ((UFail) (SDDiffer _ _ _ (DifferBy ctx t u ents rules pe pr p)))
        ((UOk rules2) (SDSame _ _ _ (SameBy ctx t u ents rules rules2 pe pr p)))))))

(def-adts
  (RefineDec : ((Ctx) ctx) ((List (Eqn)) eqs) -> Type
    enum
    (many RDRefined : (erased (Ctx) ctx) (erased (List (Eqn)) eqs) (many (Ctx) out) (erased (Refine ctx eqs out) p) -> (RefineDec ctx eqs))
    (many RDContradicted : (erased (Ctx) ctx) (erased (List (Eqn)) eqs) (erased (Contradict ctx eqs) p) -> (RefineDec ctx eqs))
    (many RDStuck : (erased (Ctx) ctx) (erased (List (Eqn)) eqs) -> (RefineDec ctx eqs))))
(def-fns _ $ many refine-dec : (many (Nat) fuel) (many (Ctx) ctx) (many (List (Eqn)) eqs) -> (many (RefineDec ctx eqs) r)
  (let (many ents) (erased pe) (ctx-ents ctx))
  (let (many rules) (erased pr) (ctx-rules ctx))
  (match many (unify fuel (Force) ents rules eqs) _
    ((UnifyStuck a b c d) (RDStuck _ _))
    ((MkUnified a b c d out p)
      (match many out _
        ((UFail) (RDContradicted _ _ (ContradictBy ctx eqs ents rules pe pr p)))
        ((UOk rules2)
          (let (many ctx2) (erased w) (with-rules ctx rules2))
          (RDRefined _ _ ctx2 (RefineBy ctx eqs ctx2 ents rules rules2 pe pr p w)))))))

; The type of a closed term of the grammar.
(def-adts
  (TypeOfTermDec : ((Ctx) ctx) ((Term) t) -> Type
    enum
    (many TotIs : (erased (Ctx) ctx) (erased (Term) t) (many (Term) ty) (erased (TypeOfTerm ctx t ty) p) -> (TypeOfTermDec ctx t))
    (many TotStuck : (erased (Ctx) ctx) (erased (Term) t) -> (TypeOfTermDec ctx t))))
(def-fns _ $ many type-of-term : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Term) t) -> (many (TypeOfTermDec ctx t) r)
  (match many fuel _
    ((Zero) (TotStuck _ _))
    ((Succ f)
      (match many t _
        ((Ref x)
          (match many (type-of ctx x) _
            ((TypeOfStuck a b) (TotStuck _ _))
            ((TypeIs a b ty k p q) (TotIs _ _ ty (TotRef ctx x ty p)))))
        ((Bound k) (TotStuck _ _))
        ((App h as)
          (match many (type-of-term f ctx h) _
            ((TotStuck a b) (TotStuck _ _))
            ((TotIs a b hty p)
              (match many (canonical f ctx hty) _
                ((CanonicalStuck c d) (TotStuck _ _))
                ((CanonicalIs c d hc cn)
                  (match many hc _
                    ((TyCtor ps) (TotIs _ _ (Univ) (TotTyApp ctx h as hty ps p cn)))
                    ((ValCtor ps ret)
                      (let (many sub) (erased so) (somes as))
                      (match many (subst f sub ret) _
                        ((SubstStuck e g) (TotStuck _ _))
                        ((MkSubsted e g ty q) (TotIs _ _ ty (TotValApp ctx h as hty ps ret sub ty p cn so q)))))
                    (else (TotStuck _ _))))))))
        ((Univ) (TotIs _ _ (Univ) (TotUniv ctx)))
        ((Fn l ps rs) (TotIs _ _ (Univ) (TotFn ctx l ps rs)))
        ((TyCtor ps) (TotIs _ _ (Univ) (TotTyCtor ctx ps)))
        ((ValCtor ps r) (TotIs _ _ (Univ) (TotValCtor ctx ps r)))))))

; Minting a telescope's entries with the names given.
(def-adts
  (MintTeleDec : ((Ctx) ctx) ((List (Maybe (Term))) acc) ((List (Entry)) tele) ((List (Maybe (String))) names) -> Type
    enum
    (many MTMinted : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (List (Entry)) tele) (erased (List (Maybe (String))) names) (many (Ctx) out) (many (List (Nat)) ids)
       (erased (MintTele ctx acc tele names out ids) p) -> (MintTeleDec ctx acc tele names))
    (many MTStuck : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (List (Entry)) tele) (erased (List (Maybe (String))) names) -> (MintTeleDec ctx acc tele names))))
(def-fns _ $ many mint-tele : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (List (Maybe (Term))) acc) (many (List (Entry)) tele) (many (List (Maybe (String))) names) -> (many (MintTeleDec ctx acc tele names) r)
  (match many fuel _
    ((Zero) (MTStuck _ _ _ _))
    ((Succ f)
      (match many tele _
        ((Nil a) (match many names _ ((Nil b) (MTMinted _ _ _ _ ctx (Nil _) (MTNil ctx acc))) ((Cons b n ns) (MTStuck _ _ _ _))))
        ((Cons a e es)
          (match many names _
            ((Nil b) (MTStuck _ _ _ _))
            ((Cons b name ns)
              (match many e _
                ((MkEntry s i t)
                  (match many (subst f acc t) _
                    ((SubstStuck c d) (MTStuck _ _ _ _))
                    ((MkSubsted c d t2 sb)
                      (match many i _
                        ((BFalse)
                          (let (many x) (many ctx1) (erased m) (mint ctx name t2 (KPlain) (None _)))
                          (match many (mint-tele f ctx1 (Cons _ (Some _ (Ref x)) acc) es ns) _
                            ((MTStuck g h k l) (MTStuck _ _ _ _))
                            ((MTMinted g h k l out ids p) (MTMinted _ _ _ _ out (Cons _ x ids) (MTTy ctx acc s t es name ns t2 x ctx1 out ids sb m p)))))
                        ((BTrue)
                          (match many (type-of-term f ctx t2) _
                            ((TotStuck g h) (MTStuck _ _ _ _))
                            ((TotIs g h ty tt)
                              (let (many x) (many ctx1) (erased m) (mint ctx name ty (KPlain) (Some _ t2)))
                              (match many (mint-tele f ctx1 (Cons _ (Some _ (Ref x)) acc) es ns) _
                                ((MTStuck g2 h2 k2 l2) (MTStuck _ _ _ _))
                                ((MTMinted g2 h2 k2 l2 out ids p) (MTMinted _ _ _ _ out (Cons _ x ids) (MTIs ctx acc s t es name ns t2 ty x ctx1 out ids sb tt m p)))))))))))))))))))

; A strict subterm, decided on canonical terms.
(def-adts
  (SubDec : ((Ctx) ctx) ((Term) a) ((Term) b) -> Type
    enum
    (many SubYes : (erased (Ctx) ctx) (erased (Term) a) (erased (Term) b) (erased (StrictSub ctx a b) p) -> (SubDec ctx a b))
    (many SubNo : (erased (Ctx) ctx) (erased (Term) a) (erased (Term) b) (erased (NotSub ctx a b) p) -> (SubDec ctx a b))
    (many SubStuck : (erased (Ctx) ctx) (erased (Term) a) (erased (Term) b) -> (SubDec ctx a b)))
  (SubListDec : ((Ctx) ctx) ((Term) a) ((List (Term)) as) -> Type
    enum
    (many SubLYes : (erased (Ctx) ctx) (erased (Term) a) (erased (List (Term)) as) (erased (SubOfList ctx a as) p) -> (SubListDec ctx a as))
    (many SubLNo : (erased (Ctx) ctx) (erased (Term) a) (erased (List (Term)) as) (erased (NotSubList ctx a as) p) -> (SubListDec ctx a as))
    (many SubLStuck : (erased (Ctx) ctx) (erased (Term) a) (erased (List (Term)) as) -> (SubListDec ctx a as))))
(def-fns _
  (many sub-dec : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Term) a) (many (Term) b) -> (many (SubDec ctx a b) r)
    (match many fuel _
      ((Zero) (SubStuck _ _ _))
      ((Succ f)
        (match many b _
          ((App h as)
            (match many (same-dec f ctx a h) _
              ((SDStuck c d e) (SubStuck _ _ _))
              ((SDSame c d e s) (SubYes _ _ _ (SSHead ctx a h as s)))
              ((SDDiffer c d e df)
                (match many (sub-list-dec f ctx a as) _
                  ((SubLStuck c2 d2 e2) (SubStuck _ _ _))
                  ((SubLYes c2 d2 e2 p) (SubYes _ _ _ (SSArg ctx a h as p)))
                  ((SubLNo c2 d2 e2 p) (SubNo _ _ _ (NSApp ctx a h as df p)))))))
          ((Ref x) (SubNo _ _ _ (NSNotApp ctx a (Ref x) (NotAppRef x))))
          ((Bound k) (SubNo _ _ _ (NSNotApp ctx a (Bound k) (NotAppBound k))))
          ((Univ) (SubNo _ _ _ (NSNotApp ctx a (Univ) (NotAppUniv))))
          ((Fn l ps rs) (SubNo _ _ _ (NSNotApp ctx a (Fn l ps rs) (NotAppFn l ps rs))))
          ((TyCtor ps) (SubNo _ _ _ (NSNotApp ctx a (TyCtor ps) (NotAppTyCtor ps))))
          ((ValCtor ps ret) (SubNo _ _ _ (NSNotApp ctx a (ValCtor ps ret) (NotAppValCtor ps ret))))))))
  (many sub-list-dec : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Term) a) (many (List (Term)) as) -> (many (SubListDec ctx a as) r)
    (match many fuel _
      ((Zero) (SubLStuck _ _ _))
      ((Succ f)
        (match many as _
          ((Nil c) (SubLNo _ _ _ (NSLNil ctx a)))
          ((Cons c b rest)
            (match many (same-dec f ctx a b) _
              ((SDStuck c1 d1 e1) (SubLStuck _ _ _))
              ((SDSame c1 d1 e1 s) (SubLYes _ _ _ (SLSame ctx a b rest s)))
              ((SDDiffer c1 d1 e1 df)
                (match many (sub-dec f ctx a b) _
                  ((SubStuck c2 d2 e2) (SubLStuck _ _ _))
                  ((SubYes c2 d2 e2 p) (SubLYes _ _ _ (SLDeep ctx a b rest p)))
                  ((SubNo c2 d2 e2 n)
                    (match many (sub-list-dec f ctx a rest) _
                      ((SubLStuck c3 d3 e3) (SubLStuck _ _ _))
                      ((SubLYes c3 d3 e3 p) (SubLYes _ _ _ (SLThere ctx a b rest p)))
                      ((SubLNo c3 d3 e3 p) (SubLNo _ _ _ (NSLCons ctx a b rest df n p))))))))))))))

; ---- Terms of the grammar, telescopes, and their arguments.

(def-adts
  (EntryDec : ((Raw) raw) -> Type
    enum
    (many EntryShape : (erased (Raw) raw) (many (Bool) s) (many (Bool) i) (many (Raw) tr) (many (String) x) (erased (EntryRaw raw s i tr x) p) -> (EntryDec raw))
    (many EntryNot : (erased (Raw) raw) -> (EntryDec raw))))
(def-fns _ $ many entry-dec : (many (Raw) raw) -> (many (EntryDec raw) r)
  (match many raw _
    ((RList items)
      (match many items _
        ((Cons a r1 rest1)
          (match many rest1 _
            ((Cons b r2 rest2)
              (match many rest2 _
                ((Nil c)
                  (match many r2 _
                    ((RAtom x) (EntryShape _ (BFalse) (BFalse) r1 x (EntryTy r1 x)))
                    (else (EntryNot _))))
                ((Cons c r3 rest3)
                  (match many rest3 _
                    ((Nil d)
                      (match many r3 _
                        ((RAtom x)
                          (match many r1 _
                            ((RKey k)
                              (match many k _
                                ((KSubterm) (EntryShape _ (BTrue) (BFalse) r2 x (EntrySub r2 x)))
                                (else (EntryNot _))))
                            (else
                              (match many r2 _
                                ((RKey k2)
                                  (match many k2 _
                                    ((KIs) (EntryShape _ (BFalse) (BTrue) r1 x (EntryIs r1 x)))
                                    (else (EntryNot _))))
                                (else (EntryNot _))))))
                        (else (EntryNot _))))
                    (else (EntryNot _))))))
            (else (EntryNot _))))
        (else (EntryNot _))))
    (else (EntryNot _))))

(def-adts
  (TermDec : ((Ctx) ctx) ((Raw) raw) -> Type
    enum
    (many MkTermDec : (erased (Ctx) ctx) (erased (Raw) raw) (many (TOut) out) (erased (ElabTerm ctx raw out) p) -> (TermDec ctx raw))
    (many TermStuck : (erased (Ctx) ctx) (erased (Raw) raw) -> (TermDec ctx raw)))
  (ArgsDec : ((Ctx) ctx) ((List (Maybe (Term))) acc) ((List (Entry)) tele) ((List (Raw)) args) -> Type
    enum
    (many MkArgsDec : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (List (Entry)) tele) (erased (List (Raw)) args) (many (ArgsOut) out) (erased (ElabTermArgs ctx acc tele args out) p) ->
       (ArgsDec ctx acc tele args))
    (many ArgsStuck : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (List (Entry)) tele) (erased (List (Raw)) args) -> (ArgsDec ctx acc tele args)))
  (TeleDec : ((Ctx) ctx) ((List (Maybe (Nat))) acc) ((List (Raw)) raws) -> Type
    enum
    (many MkTeleDec : (erased (Ctx) ctx) (erased (List (Maybe (Nat))) acc) (erased (List (Raw)) raws) (many (TeleOut) out) (erased (ElabTele ctx acc raws out) p) -> (TeleDec ctx acc raws))
    (many TeleStuck : (erased (Ctx) ctx) (erased (List (Maybe (Nat))) acc) (erased (List (Raw)) raws) -> (TeleDec ctx acc raws))))

(def-fns _
  (many elab-term : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Raw) raw) -> (many (TermDec ctx raw) r)
    (match many fuel _
      ((Zero) (TermStuck _ _))
      ((Succ f)
        (match many raw _
          ((RAtom s)
            (let (many scope) (erased sc) (ctx-scope ctx))
            (match many (name-dec scope s) _
              ((NameMiss a b n) (MkTermDec _ _ (TErr (RUnbound)) (ETUnbound ctx s scope sc n)))
              ((NameHit a b x n)
                (match many (type-of ctx x) _
                  ((TypeOfStuck c d) (TermStuck _ _))
                  ((TypeIs c d ty k p q) (MkTermDec _ _ (TOk (Ref x) ty) (ETName ctx s x ty scope sc n p)))))))
          ((RKey k) (TermStuck _ _))
          ((RList items)
            (match many items _
              ((Nil a) (TermStuck _ _))
              ((Cons a h args)
                (match many h _
                  ((RKey k) (elab-former f ctx k args))
                  ((RAtom s) (elab-term-app f ctx h args (HeadAtom s)))
                  ((RList inner) (elab-term-app f ctx h args (HeadList inner)))))))))))
  ; (h args...) with a name or a list at the head
  (many elab-term-app : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Raw) h) (many (List (Raw)) args) (erased (HeadRaw h) hr) -> (many (TermDec ctx (RList (Cons (Raw) h args))) r)
    (match many fuel _
      ((Zero) (TermStuck _ _))
      ((Succ f)
        (match many (elab-term f ctx h) _
          ((TermStuck a b) (TermStuck _ _))
          ((MkTermDec a b hout p)
            (match many hout _
              ((TErr r) (MkTermDec _ _ (TErr r) (ETAppHeadErr ctx h args r p)))
              ((TOk ht hty)
                (match many (canonical f ctx hty) _
                  ((CanonicalStuck c d) (TermStuck _ _))
                  ((CanonicalIs c d hc cn)
                    (match many hc _
                      ((TyCtor ps)
                        (match many (elab-term-args f ctx (Nil _) ps args) _
                          ((ArgsStuck e g k l) (TermStuck _ _))
                          ((MkArgsDec e g k l aout ap)
                            (match many aout _
                              ((ArgsErr r) (MkTermDec _ _ (TErr r) (ETAppArgsErr ctx h args ht hty ps r p (HeadTy ctx hty ps cn) ap)))
                              ((ArgsOk ts) (MkTermDec _ _ (TOk (App ht ts) (Univ)) (ETTyApp ctx h args ht hty ps ts p cn ap)))))))
                      ((ValCtor ps ret)
                        (match many (elab-term-args f ctx (Nil _) ps args) _
                          ((ArgsStuck e g k l) (TermStuck _ _))
                          ((MkArgsDec e g k l aout ap)
                            (match many aout _
                              ((ArgsErr r) (MkTermDec _ _ (TErr r) (ETAppArgsErr ctx h args ht hty ps r p (HeadVal ctx hty ps ret cn) ap)))
                              ((ArgsOk ts)
                                (let (many sub) (erased so) (somes ts))
                                (match many (subst f sub ret) _
                                  ((SubstStuck e2 g2) (TermStuck _ _))
                                  ((MkSubsted e2 g2 ty sb) (MkTermDec _ _ (TOk (App ht ts) ty) (ETValApp ctx h args ht hty ps ret ts sub ty p cn ap so sb)))))))))
                      ((Ref x) (MkTermDec _ _ (TErr (RNotApplicable)) (ETNotApplicable ctx h args ht hty (Ref x) p cn (NoTeleRef x))))
                      ((Bound k) (MkTermDec _ _ (TErr (RNotApplicable)) (ETNotApplicable ctx h args ht hty (Bound k) p cn (NoTeleBound k))))
                      ((App h2 as2) (MkTermDec _ _ (TErr (RNotApplicable)) (ETNotApplicable ctx h args ht hty (App h2 as2) p cn (NoTeleApp h2 as2))))
                      ((Univ) (MkTermDec _ _ (TErr (RNotApplicable)) (ETNotApplicable ctx h args ht hty (Univ) p cn (NoTeleUniv))))
                      ((Fn l ps rs) (MkTermDec _ _ (TErr (RNotApplicable)) (ETNotApplicable ctx h args ht hty (Fn l ps rs) p cn (NoTeleFn l ps rs))))))))))))))
  ; the formers: (Fn L (params) (rets)), (TyCtor (params)), (ValCtor (params) ret)
  (many elab-former : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Key) k) (many (List (Raw)) items) -> (many (TermDec ctx (RList (Cons (Raw) (RKey k) items))) r)
    (match many fuel _
      ((Zero) (TermStuck _ _))
      ((Succ f)
        (match many k _
          ((KFn)
            (match many items _
              ((Cons a lr rest1)
                (match many rest1 _
                  ((Cons b pr rest2)
                    (match many rest2 _
                      ((Cons c rr rest3)
                        (match many rest3 _
                          ((Nil d)
                            (match many pr _
                              ((RList ps)
                                (match many rr _
                                  ((RList rs) (elab-fn f ctx lr ps rs))
                                  (else (TermStuck _ _))))
                              (else (TermStuck _ _))))
                          (else (TermStuck _ _))))
                      (else (TermStuck _ _))))
                  (else (TermStuck _ _))))
              (else (TermStuck _ _))))
          ((KTyCtor)
            (match many items _
              ((Cons a pr rest1)
                (match many rest1 _
                  ((Nil b)
                    (match many pr _
                      ((RList ps)
                        (match many (elab-tele f ctx (Nil _) ps) _
                          ((TeleStuck c d e) (TermStuck _ _))
                          ((MkTeleDec c d e tout ep)
                            (match many tout _
                              ((TeleErr r) (MkTermDec _ _ (TErr r) (ETTyCtorErr ctx ps r ep)))
                              ((TeleOk ctx1 pt pids pn) (MkTermDec _ _ (TOk (TyCtor pt) (Univ)) (ETTyCtor ctx ps ctx1 pt pids pn ep)))))))
                      (else (TermStuck _ _))))
                  (else (TermStuck _ _))))
              (else (TermStuck _ _))))
          ((KValCtor)
            (match many items _
              ((Cons a pr rest1)
                (match many rest1 _
                  ((Cons b rr rest2)
                    (match many rest2 _
                      ((Nil c)
                        (match many pr _
                          ((RList ps) (elab-valctor f ctx ps rr))
                          (else (TermStuck _ _))))
                      (else (TermStuck _ _))))
                  (else (TermStuck _ _))))
              (else (TermStuck _ _))))
          (else (TermStuck _ _))))))
  (many elab-fn : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Raw) lr) (many (List (Raw)) ps) (many (List (Raw)) rs) ->
      (many (TermDec ctx (RList (Cons (Raw) (RKey (KFn)) (Cons (Raw) lr (Cons (Raw) (RList ps) (Cons (Raw) (RList rs) (Nil (Raw)))))))) r)
    (match many fuel _
      ((Zero) (TermStuck _ _))
      ((Succ f)
        (match many (elab-term f ctx lr) _
          ((TermStuck a b) (TermStuck _ _))
          ((MkTermDec a b lout p)
            (match many lout _
              ((TErr r) (MkTermDec _ _ (TErr r) (ETFnLevelErr ctx lr ps rs r p)))
              ((TOk l lty)
                (match many (same-dec f ctx lty (App (Ref (Zero)) (Nil _))) _
                  ((SDStuck c d e) (TermStuck _ _))
                  ((SDDiffer c d e df) (MkTermDec _ _ (TErr (RNotLevel)) (ETFnNotLevel ctx lr ps rs l lty p df)))
                  ((SDSame c d e sl)
                    (match many (elab-tele f ctx (Nil _) ps) _
                      ((TeleStuck c2 d2 e2) (TermStuck _ _))
                      ((MkTeleDec c2 d2 e2 pout ep)
                        (match many pout _
                          ((TeleErr r) (MkTermDec _ _ (TErr r) (ETFnParamsErr ctx lr ps rs l lty r p sl ep)))
                          ((TeleOk ctx1 pt pids pn)
                            (let (many acc) (erased bd) (binders pids))
                            (match many (elab-tele f ctx1 acc rs) _
                              ((TeleStuck c3 d3 e3) (TermStuck _ _))
                              ((MkTeleDec c3 d3 e3 rout er)
                                (match many rout _
                                  ((TeleErr r) (MkTermDec _ _ (TErr r) (ETFnRetsErr ctx lr ps rs l lty ctx1 pt pids pn acc r p sl ep bd er)))
                                  ((TeleOk ctx2 rt rids rn) (MkTermDec _ _ (TOk (Fn l pt rt) (Univ)) (ETFn ctx lr ps rs l lty ctx1 pt pids pn acc ctx2 rt rids rn p sl ep bd er)))))))))))))))))))
  (many elab-valctor : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (List (Raw)) ps) (many (Raw) rr) ->
      (many (TermDec ctx (RList (Cons (Raw) (RKey (KValCtor)) (Cons (Raw) (RList ps) (Cons (Raw) rr (Nil (Raw))))))) r)
    (match many fuel _
      ((Zero) (TermStuck _ _))
      ((Succ f)
        (match many (elab-tele f ctx (Nil _) ps) _
          ((TeleStuck c2 d2 e2) (TermStuck _ _))
          ((MkTeleDec c2 d2 e2 pout ep)
            (match many pout _
              ((TeleErr r) (MkTermDec _ _ (TErr r) (ETValCtorParamsErr ctx ps rr r ep)))
              ((TeleOk ctx1 pt pids pn)
                (match many (elab-term f ctx1 rr) _
                  ((TermStuck a b) (TermStuck _ _))
                  ((MkTermDec a b rout er)
                    (match many rout _
                      ((TErr r) (MkTermDec _ _ (TErr r) (ETValCtorRetErr ctx ps rr ctx1 pt pids pn r ep er)))
                      ((TOk ret rty)
                        (match many (same-dec f ctx1 rty (Univ)) _
                          ((SDStuck c d e) (TermStuck _ _))
                          ((SDDiffer c d e du) (MkTermDec _ _ (TErr (RMismatch)) (ETValCtorRetNotType ctx ps rr ctx1 pt pids pn ret rty ep er du)))
                          ((SDSame c d e su)
                            (let (many acc) (erased bd) (binders pids))
                            (match many (abstract f acc ret) _
                              ((AbstractStuck g h) (TermStuck _ _))
                              ((MkAbstracted g h ret2 ab) (MkTermDec _ _ (TOk (ValCtor pt ret2) (Univ)) (ETValCtor ctx ps rr ctx1 pt pids pn acc ret rty ret2 ep er su bd ab)))))))))))))))))
  (many elab-term-args : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (List (Maybe (Term))) acc) (many (List (Entry)) tele) (many (List (Raw)) args) -> (many (ArgsDec ctx acc tele args) r)
    (match many fuel _
      ((Zero) (ArgsStuck _ _ _ _))
      ((Succ f)
        (match many (len-dec _ _ tele args) _
          ((LenDiff a b c d m) (MkArgsDec _ _ _ _ (ArgsErr (RArity)) (ETAArity ctx acc tele args m)))
          ((LenSame a b c d)
            (match many tele _
              ((Nil e) (match many args _ ((Nil g) (MkArgsDec _ _ _ _ (ArgsOk (Nil _)) (ETANil ctx acc))) ((Cons g x y) (ArgsStuck _ _ _ _))))
              ((Cons e entry es)
                (match many args _
                  ((Nil g) (ArgsStuck _ _ _ _))
                  ((Cons g ar rest)
                    (match many entry _
                      ((MkEntry s i t)
                        (match many (elab-term f ctx ar) _
                          ((TermStuck h k) (ArgsStuck _ _ _ _))
                          ((MkTermDec h k aout p)
                            (match many aout _
                              ((TErr r) (MkArgsDec _ _ _ _ (ArgsErr r) (ETAErr ctx acc (MkEntry s i t) es ar rest r p)))
                              ((TOk at aty)
                                (match many (subst f acc t) _
                                  ((SubstStuck h2 k2) (ArgsStuck _ _ _ _))
                                  ((MkSubsted h2 k2 t2 sb)
                                    (match many i _
                                      ((BFalse)
                                        (match many (same-dec f ctx aty t2) _
                                          ((SDStuck h3 k3 l3) (ArgsStuck _ _ _ _))
                                          ((SDDiffer h3 k3 l3 d) (MkArgsDec _ _ _ _ (ArgsErr (RMismatch)) (ETATyMismatch ctx acc s t es ar rest at aty t2 p sb d)))
                                          ((SDSame h3 k3 l3 sm)
                                            (match many (elab-term-args f ctx (Cons _ (Some _ at) acc) es rest) _
                                              ((ArgsStuck h4 k4 l4 m4) (ArgsStuck _ _ _ _))
                                              ((MkArgsDec h4 k4 l4 m4 rout q)
                                                (match many rout _
                                                  ((ArgsErr r) (MkArgsDec _ _ _ _ (ArgsErr r) (ETARestErr ctx acc s (BFalse) t es ar rest at aty r p q)))
                                                  ((ArgsOk ts) (MkArgsDec _ _ _ _ (ArgsOk (Cons _ at ts)) (ETATy ctx acc s t es ar rest at aty t2 ts p sb sm q)))))))))
                                      ((BTrue)
                                        (match many (same-dec f ctx at t2) _
                                          ((SDStuck h3 k3 l3) (ArgsStuck _ _ _ _))
                                          ((SDDiffer h3 k3 l3 d) (MkArgsDec _ _ _ _ (ArgsErr (RMismatch)) (ETAIsMismatch ctx acc s t es ar rest at aty t2 p sb d)))
                                          ((SDSame h3 k3 l3 sm)
                                            (match many (elab-term-args f ctx (Cons _ (Some _ at) acc) es rest) _
                                              ((ArgsStuck h4 k4 l4 m4) (ArgsStuck _ _ _ _))
                                              ((MkArgsDec h4 k4 l4 m4 rout q)
                                                (match many rout _
                                                  ((ArgsErr r) (MkArgsDec _ _ _ _ (ArgsErr r) (ETARestErr ctx acc s (BTrue) t es ar rest at aty r p q)))
                                                  ((ArgsOk ts) (MkArgsDec _ _ _ _ (ArgsOk (Cons _ at ts)) (ETAIs ctx acc s t es ar rest at aty t2 ts p sb sm q)))))))))))))))))))))))))))
  (many elab-tele : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (List (Maybe (Nat))) acc) (many (List (Raw)) raws) -> (many (TeleDec ctx acc raws) r)
    (match many fuel _
      ((Zero) (TeleStuck _ _ _))
      ((Succ f)
        (match many raws _
          ((Nil a) (MkTeleDec _ _ _ (TeleOk ctx (Nil _) (Nil _) (Nil _)) (ELNil ctx acc)))
          ((Cons a e rest)
            (match many (entry-dec e) _
              ((EntryNot b) (TeleStuck _ _ _))
              ((EntryShape b s i tr x shape)
                (match many (elab-term f ctx tr) _
                  ((TermStuck c d) (TeleStuck _ _ _))
                  ((MkTermDec c d tout p)
                    (match many tout _
                      ((TErr r) (MkTeleDec _ _ _ (TeleErr r) (ELTermErr ctx acc e s i tr x rest r shape p)))
                      ((TOk t tty)
                        (match many i _
                          ((BFalse)
                            (match many (same-dec f ctx tty (Univ)) _
                              ((SDStuck g h k) (TeleStuck _ _ _))
                              ((SDDiffer g h k d) (MkTeleDec _ _ _ (TeleErr (RMismatch)) (ELNotType ctx acc e s tr x rest t tty shape p d)))
                              ((SDSame g h k su)
                                (let (many id) (many ctx1) (erased m) (mint ctx (Some _ x) t (KPlain) (None _)))
                                (match many (abstract f acc t) _
                                  ((AbstractStuck g2 h2) (TeleStuck _ _ _))
                                  ((MkAbstracted g2 h2 t2 ab)
                                    (match many (elab-tele f ctx1 (Cons _ (Some _ id) acc) rest) _
                                      ((TeleStuck g3 h3 k3) (TeleStuck _ _ _))
                                      ((MkTeleDec g3 h3 k3 rout q)
                                        (match many rout _
                                          ((TeleErr r) (MkTeleDec _ _ _ (TeleErr r) (ELRestErr ctx acc e s (BFalse) tr x rest t tty id ctx1 t (None _) r shape p (EMTy t tty) m q)))
                                          ((TeleOk out es ids names)
                                            (MkTeleDec _ _ _ (TeleOk out (Cons _ (MkEntry s (BFalse) t2) es) (Cons _ id ids) (Cons _ (Some _ x) names)) (ELTy ctx acc e s tr x rest t tty id ctx1 t2 out es ids names shape p su m ab q)))))))))))
                          ((BTrue)
                            (let (many id) (many ctx1) (erased m) (mint ctx (Some _ x) tty (KPlain) (Some _ t)))
                            (match many (abstract f acc t) _
                              ((AbstractStuck g2 h2) (TeleStuck _ _ _))
                              ((MkAbstracted g2 h2 t2 ab)
                                (match many (elab-tele f ctx1 (Cons _ (Some _ id) acc) rest) _
                                  ((TeleStuck g3 h3 k3) (TeleStuck _ _ _))
                                  ((MkTeleDec g3 h3 k3 rout q)
                                    (match many rout _
                                      ((TeleErr r) (MkTeleDec _ _ _ (TeleErr r) (ELRestErr ctx acc e s (BTrue) tr x rest t tty id ctx1 tty (Some _ t) r shape p (EMIs t tty) m q)))
                                      ((TeleOk out es ids names)
                                        (MkTeleDec _ _ _ (TeleOk out (Cons _ (MkEntry s (BTrue) t2) es) (Cons _ id ids) (Cons _ (Some _ x) names)) (ELIs ctx acc e s tr x rest t tty id ctx1 t2 out es ids names shape p m ab q))))))))))))))))))))))

; ---- Decisions for calls: the annotation among the arguments, the marked positions, the prefix check, and
; the shapes a proof's type must have.

(def-adts
  (PlainDec : ((List (Raw)) args) -> Type
    enum
    (many PlainYes : (erased (List (Raw)) args) (erased (Plain args) p) -> (PlainDec args))
    (many PlainNo : (erased (List (Raw)) args) -> (PlainDec args)))
  (AnnKeyDec : ((Key) k) -> Type
    enum
    (many AKNot : (erased (Key) k) (erased (NotAnnKey k) p) -> (AnnKeyDec k))
    (many AKPredates : -> (AnnKeyDec (KPredates)))
    (many AKSubterm : -> (AnnKeyDec (KSubterm)))
    (many AKOther : (erased (Key) k) -> (AnnKeyDec k))))
(def-fns _ $ many ann-key-dec : (many (Key) k) -> (many (AnnKeyDec k) r)
  (match many k _
    ((KFn) (AKNot _ (NAKFn))) ((KTyCtor) (AKNot _ (NAKTyCtor))) ((KValCtor) (AKNot _ (NAKValCtor))) ((KMatch) (AKNot _ (NAKMatch))) ((KValues) (AKNot _ (NAKValues)))
    ((KProveSubterm) (AKNot _ (NAKProveSubterm))) ((KProvePredates) (AKNot _ (NAKProvePredates))) ((KPredatesTrans) (AKNot _ (NAKPredatesTrans)))
    ((KSubtermTrans) (AKNot _ (NAKSubtermTrans))) ((KPredatesSubterm) (AKNot _ (NAKPredatesSubterm)))
    ((KPredates) (AKPredates)) ((KSubterm) (AKSubterm))
    (else (AKOther _))))
(def-fns _ $ many plain-dec : (subterm many (List (Raw)) args) -> (many (PlainDec args) r)
  (match many args _
    ((Nil a) (PlainYes _ (PlainNil)))
    ((Cons a x rest)
      (match many (plain-dec rest) _
        ((PlainNo b) (PlainNo _))
        ((PlainYes b p)
          (match many x _
            ((RAtom s) (PlainYes _ (PlainAtom s rest p)))
            ((RKey k) (PlainNo _))
            ((RList items)
              (match many items _
                ((Nil c) (PlainYes _ (PlainNilList rest p)))
                ((Cons c h more)
                  (match many h _
                    ((RAtom s) (PlainYes _ (PlainAtomList s more rest p)))
                    ((RList inner) (PlainYes _ (PlainListList inner more rest p)))
                    ((RKey k)
                      (match many (ann-key-dec k) _
                        ((AKNot d nk) (PlainYes _ (PlainKeyList k more rest nk p)))
                        (else (PlainNo _))))))))))))))

; An item that is (predates p) or (subterm p), or neither.
(def-adts
  (AnnItem : ((Raw) item) -> Type
    enum
    (many AIPredates : (many (Raw) p) -> (AnnItem (RList (Cons (Raw) (RKey (KPredates)) (Cons (Raw) p (Nil (Raw)))))))
    (many AISubterm : (many (Raw) p) -> (AnnItem (RList (Cons (Raw) (RKey (KSubterm)) (Cons (Raw) p (Nil (Raw)))))))
    (many AINone : (erased (Raw) item) -> (AnnItem item))))
(def-fns _ $ many ann-item : (many (Raw) item) -> (many (AnnItem item) r)
  (match many item _
    ((RList items)
      (match many items _
        ((Cons a h rest)
          (match many h _
            ((RKey k)
              (match many rest _
                ((Cons b p more)
                  (match many more _
                    ((Nil c)
                      (match many k _
                        ((KPredates) (AIPredates p))
                        ((KSubterm) (AISubterm p))
                        (else (AINone _))))
                    (else (AINone _))))
                (else (AINone _))))
            (else (AINone _))))
        (else (AINone _))))
    (else (AINone _))))

(def-adts
  (SubAtDec : ((List (Raw)) items) -> Type
    enum
    (many SubAtYes : (erased (List (Raw)) items) (many (Nat) i) (many (Raw) p) (many (List (Raw)) args) (erased (SubtermAt items i p args) q) -> (SubAtDec items))
    (many SubAtNo : (erased (List (Raw)) items) -> (SubAtDec items))))
(def-fns _ $ many subterm-at-dec : (subterm many (List (Raw)) items) -> (many (SubAtDec items) r)
  (match many items _
    ((Nil a) (SubAtNo _))
    ((Cons a x rest)
      (match many (ann-item x) _
        ((AISubterm p)
          (match many rest _
            ((Nil b) (SubAtNo _))
            ((Cons b arg args)
              (match many (plain-dec (Cons _ arg args)) _
                ((PlainYes c pl) (SubAtYes _ (Zero) p (Cons _ arg args) (SAHere p arg args pl)))
                ((PlainNo c) (SubAtNo _))))))
        (else
          (match many (plain-dec (Cons _ x (Nil _))) _
            ((PlainNo c) (SubAtNo _))
            ((PlainYes c pl)
              (match many (subterm-at-dec rest) _
                ((SubAtNo d) (SubAtNo _))
                ((SubAtYes d i p args q) (SubAtYes _ (Succ i) p (Cons _ x args) (SAThere x rest i p args pl q)))))))))))

(def-adts
  (CallRawDec : ((List (Raw)) items) -> Type
    enum
    (many MkCallRaw : (erased (List (Raw)) items) (many (Ann) ann) (many (List (Raw)) args) (erased (CallRaw items ann args) p) -> (CallRawDec items))
    (many CallRawStuck : (erased (List (Raw)) items) -> (CallRawDec items))))
(def-fns _ $ many call-raw-dec : (many (List (Raw)) items) -> (many (CallRawDec items) r)
  (match many items _
    ((Nil a) (MkCallRaw _ (ANone) (Nil _) (CRPlain (Nil _) (PlainNil))))
    ((Cons a x rest)
      (match many (ann-item x) _
        ((AIPredates p)
          (match many (plain-dec rest) _
            ((PlainYes b pl) (MkCallRaw _ (APredates p) rest (CRPredates p rest pl)))
            ((PlainNo b) (CallRawStuck _))))
        (else
          (match many (plain-dec (Cons _ x rest)) _
            ((PlainYes b pl) (MkCallRaw _ (ANone) (Cons _ x rest) (CRPlain (Cons _ x rest) pl)))
            ((PlainNo b)
              (match many (subterm-at-dec (Cons _ x rest)) _
                ((SubAtNo c) (CallRawStuck _))
                ((SubAtYes c i p args q) (MkCallRaw _ (ASubterm i p) args (CRSubterm (Cons _ x rest) i p args q)))))))))))

(def-adts
  (MarkedIndexDec : ((List (Entry)) ps) ((Nat) i) -> Type
    enum
    (many MIYesAt : (erased (List (Entry)) ps) (erased (Nat) i) (many (Nat) j) (erased (MarkedIndex ps i j) p) -> (MarkedIndexDec ps i))
    (many MINoAt : (erased (List (Entry)) ps) (erased (Nat) i) (erased (Unmarked ps i) p) -> (MarkedIndexDec ps i))))
(def-fns _ $ many marked-index-dec : (subterm many (List (Entry)) ps) (many (Nat) i) -> (many (MarkedIndexDec ps i) r)
  (match many ps _
    ((Nil a) (MINoAt _ _ (UmNil i)))
    ((Cons a e es)
      (match many e _
        ((MkEntry s is t)
          (match many i _
            ((Zero) (match many s _ ((BTrue) (MIYesAt _ _ (Zero) (MIHere is t es))) ((BFalse) (MINoAt _ _ (UmHere is t es)))))
            ((Succ i2)
              (match many (marked-index-dec es i2) _
                ((MINoAt b c p) (MINoAt _ _ (UmThere (MkEntry s is t) es i2 p)))
                ((MIYesAt b c j p) (match many s _ ((BTrue) (MIYesAt _ _ (Succ j) (MIYes is t es i2 j p))) ((BFalse) (MIYesAt _ _ j (MINo is t es i2 j p)))))))))))))

(def-adts
  (PrefixDec : ((Ctx) ctx) ((Nat) j) ((List (Term)) as) ((List (Term)) bs) -> Type
    enum
    (many PrefixYes : (erased (Ctx) ctx) (erased (Nat) j) (erased (List (Term)) as) (erased (List (Term)) bs) (many (Term) b) (erased (SamePrefix ctx j as bs b) p) -> (PrefixDec ctx j as bs))
    (many PrefixNo : (erased (Ctx) ctx) (erased (Nat) j) (erased (List (Term)) as) (erased (List (Term)) bs) (erased (DifferPrefix ctx j as bs) p) -> (PrefixDec ctx j as bs))
    (many PrefixStuck : (erased (Ctx) ctx) (erased (Nat) j) (erased (List (Term)) as) (erased (List (Term)) bs) -> (PrefixDec ctx j as bs))))
(def-fns _ $ many prefix-dec : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Nat) j) (many (List (Term)) as) (many (List (Term)) bs) -> (many (PrefixDec ctx j as bs) r)
  (match many fuel _
    ((Zero) (PrefixStuck _ _ _ _))
    ((Succ f)
      (match many j _
        ((Zero) (match many bs _ ((Nil a) (PrefixNo _ _ _ _ (DPNilB ctx (Zero) as))) ((Cons a b rest) (PrefixYes _ _ _ _ b (SPZero ctx as b rest)))))
        ((Succ j2)
          (match many as _
            ((Nil a) (PrefixNo _ _ _ _ (DPNilA ctx (Succ j2) bs)))
            ((Cons a x xs)
              (match many bs _
                ((Nil b) (PrefixNo _ _ _ _ (DPNilB ctx (Succ j2) (Cons _ x xs))))
                ((Cons b y ys)
                  (match many (same-dec f ctx x y) _
                    ((SDStuck c d e) (PrefixStuck _ _ _ _))
                    ((SDDiffer c d e df) (PrefixNo _ _ _ _ (DPHere ctx j2 x xs y ys df)))
                    ((SDSame c d e sm)
                      (match many (prefix-dec f ctx j2 xs ys) _
                        ((PrefixStuck c2 d2 e2 g2) (PrefixStuck _ _ _ _))
                        ((PrefixNo c2 d2 e2 g2 p) (PrefixNo _ _ _ _ (DPThere ctx j2 x xs y ys sm p)))
                        ((PrefixYes c2 d2 e2 g2 bb p) (PrefixYes _ _ _ _ bb (SPSucc ctx j2 x xs y ys bb sm p)))))))))))))))

; A canonical term that is not an application, with the evidence.
(def-adts
  (NotAppDec : ((Term) c) -> Type
    enum
    (many IsApp : (many (Term) h) (many (List (Term)) as) -> (NotAppDec (App h as)))
    (many IsNotApp : (erased (Term) c) (erased (NotApp c) p) -> (NotAppDec c))))
(def-fns _ $ many not-app-dec : (many (Term) c) -> (many (NotAppDec c) r)
  (match many c _
    ((App h as) (IsApp h as))
    ((Ref x) (IsNotApp _ (NotAppRef x)))
    ((Bound k) (IsNotApp _ (NotAppBound k)))
    ((Univ) (IsNotApp _ (NotAppUniv)))
    ((Fn l ps rs) (IsNotApp _ (NotAppFn l ps rs)))
    ((TyCtor ps) (IsNotApp _ (NotAppTyCtor ps)))
    ((ValCtor ps r) (IsNotApp _ (NotAppValCtor ps r)))))

; A proof's canonical type as (Predates ty a lv), with each part the same as required, or why not.
(def-adts
  (PredatesDec : ((Ctx) ctx) ((Term) c) ((Term) l) ((Term) cur) -> Type
    enum
    (many PDYes : (erased (Ctx) ctx) (erased (Term) c) (erased (Term) l) (erased (Term) cur) (many (Term) h) (many (Term) ty) (many (Term) a) (many (Term) lv)
       (erased (Same ctx h (Ref (Succ (Zero)))) sh) (erased (Same ctx ty (App (Ref (Zero)) (Nil (Term)))) sty) (erased (Same ctx a l) sa) (erased (Same ctx lv cur) sc) ->
       (PredatesDec ctx (App h (Cons (Term) ty (Cons (Term) a (Cons (Term) lv (Nil (Term)))))) l cur))
    (many PDNo : (erased (Ctx) ctx) (erased (Term) c) (erased (Term) l) (erased (Term) cur) (erased (NotPredates ctx c l cur) p) -> (PredatesDec ctx c l cur))
    (many PDStuck : (erased (Ctx) ctx) (erased (Term) c) (erased (Term) l) (erased (Term) cur) -> (PredatesDec ctx c l cur))))
(def-fns _ $ many predates-dec : (many (Nat) fuel) (many (Ctx) ctx) (many (Term) c) (many (Term) l) (many (Term) cur) -> (many (PredatesDec ctx c l cur) r)
  (match many (not-app-dec c) _
    ((IsNotApp a na) (PDNo _ _ _ _ (NPNotApp ctx c l cur na)))
    ((IsApp h as)
      (match many (not-len-dec (Succ (Succ (Succ (Zero)))) as) _
        ((LenIsNot b d nl) (PDNo _ _ _ _ (NPArity ctx h as l cur nl)))
        ((LenIs b d ln)
          (match many as _
            ((Cons e ty rest1)
              (match many rest1 _
                ((Cons g a rest2)
                  (match many rest2 _
                    ((Cons k lv rest3)
                      (match many rest3 _
                        ((Nil m)
                          (match many (same-dec fuel ctx h (Ref (Succ (Zero)))) _
                            ((SDStuck a1 b1 c1) (PDStuck _ _ _ _))
                            ((SDDiffer a1 b1 c1 df) (PDNo _ _ _ _ (NPHead ctx h as l cur df)))
                            ((SDSame a1 b1 c1 sh)
                              (match many (same-dec fuel ctx ty (App (Ref (Zero)) (Nil _))) _
                                ((SDStuck a2 b2 c2) (PDStuck _ _ _ _))
                                ((SDDiffer a2 b2 c2 df) (PDNo _ _ _ _ (NPType ctx h ty a lv l cur df)))
                                ((SDSame a2 b2 c2 sty)
                                  (match many (same-dec fuel ctx a l) _
                                    ((SDStuck a3 b3 c3) (PDStuck _ _ _ _))
                                    ((SDDiffer a3 b3 c3 df) (PDNo _ _ _ _ (NPLevel ctx h ty a lv l cur df)))
                                    ((SDSame a3 b3 c3 sa)
                                      (match many (same-dec fuel ctx lv cur) _
                                        ((SDStuck a4 b4 c4) (PDStuck _ _ _ _))
                                        ((SDDiffer a4 b4 c4 df) (PDNo _ _ _ _ (NPCur ctx h ty a lv l cur df)))
                                        ((SDSame a4 b4 c4 sc) (PDYes ctx c l cur h ty a lv sh sty sa sc))))))))))
                        (else (PDStuck _ _ _ _))))
                    (else (PDStuck _ _ _ _))))
                (else (PDStuck _ _ _ _))))
            (else (PDStuck _ _ _ _))))))))

(def-adts
  (SubtermDec : ((Ctx) ctx) ((Term) c) ((Term) a) ((Term) b) -> Type
    enum
    (many STYes : (erased (Ctx) ctx) (erased (Term) c) (erased (Term) a) (erased (Term) b) (many (Term) h) (many (Term) ta) (many (Term) a0) (many (Term) tb) (many (Term) b0)
       (erased (Same ctx h (Ref (Succ (Succ (Zero))))) sh) (erased (Same ctx a0 a) sa) (erased (Same ctx b0 b) sb) ->
       (SubtermDec ctx (App h (Cons (Term) ta (Cons (Term) a0 (Cons (Term) tb (Cons (Term) b0 (Nil (Term))))))) a b))
    (many STNo : (erased (Ctx) ctx) (erased (Term) c) (erased (Term) a) (erased (Term) b) (erased (NotSubtermOf ctx c a b) p) -> (SubtermDec ctx c a b))
    (many STStuck : (erased (Ctx) ctx) (erased (Term) c) (erased (Term) a) (erased (Term) b) -> (SubtermDec ctx c a b))))
(def-fns _ $ many subterm-dec : (many (Nat) fuel) (many (Ctx) ctx) (many (Term) c) (many (Term) a) (many (Term) b) -> (many (SubtermDec ctx c a b) r)
  (match many (not-app-dec c) _
    ((IsNotApp x na) (STNo _ _ _ _ (NTNotApp ctx c a b na)))
    ((IsApp h as)
      (match many (not-len-dec (Succ (Succ (Succ (Succ (Zero))))) as) _
        ((LenIsNot x d nl) (STNo _ _ _ _ (NTArity ctx h as a b nl)))
        ((LenIs x d ln)
          (match many as _
            ((Cons e ta rest1)
              (match many rest1 _
                ((Cons g a0 rest2)
                  (match many rest2 _
                    ((Cons k tb rest3)
                      (match many rest3 _
                        ((Cons m b0 rest4)
                          (match many rest4 _
                            ((Nil n)
                              (match many (same-dec fuel ctx h (Ref (Succ (Succ (Zero))))) _
                                ((SDStuck a1 b1 c1) (STStuck _ _ _ _))
                                ((SDDiffer a1 b1 c1 df) (STNo _ _ _ _ (NTHead ctx h as a b df)))
                                ((SDSame a1 b1 c1 sh)
                                  (match many (same-dec fuel ctx a0 a) _
                                    ((SDStuck a3 b3 c3) (STStuck _ _ _ _))
                                    ((SDDiffer a3 b3 c3 df) (STNo _ _ _ _ (NTSmall ctx h ta a0 tb b0 a b df)))
                                    ((SDSame a3 b3 c3 sa)
                                      (match many (same-dec fuel ctx b0 b) _
                                        ((SDStuck a4 b4 c4) (STStuck _ _ _ _))
                                        ((SDDiffer a4 b4 c4 df) (STNo _ _ _ _ (NTBig ctx h ta a0 tb b0 a b df)))
                                        ((SDSame a4 b4 c4 sb) (STYes ctx c a b h ta a0 tb b0 sh sa sb))))))))
                            (else (STStuck _ _ _ _))))
                        (else (STStuck _ _ _ _))))
                    (else (STStuck _ _ _ _))))
                (else (STStuck _ _ _ _))))
            (else (STStuck _ _ _ _))))))))

; A constructor's canonical return against its own type constructor and arity.
(def-adts
  (RetDec : ((Ctx) ctx) ((Nat) tid) ((Nat) n) ((Term) c) -> Type
    enum
    (many RetYes : (erased (Ctx) ctx) (erased (Nat) tid) (erased (Nat) n) (many (List (Term)) args) (erased (Length (Term) args n) ln) -> (RetDec ctx tid n (App (Ref tid) args)))
    (many RetNo : (erased (Ctx) ctx) (erased (Nat) tid) (erased (Nat) n) (erased (Term) c) (erased (BadRet ctx tid n c) p) -> (RetDec ctx tid n c))
    (many RetStuck : (erased (Ctx) ctx) (erased (Nat) tid) (erased (Nat) n) (erased (Term) c) -> (RetDec ctx tid n c))))
(def-fns _ $ many ret-dec : (many (Nat) fuel) (many (Ctx) ctx) (many (Nat) tid) (many (Nat) n) (many (Term) c) -> (many (RetDec ctx tid n c) r)
  (match many (not-app-dec c) _
    ((IsNotApp x na) (RetNo _ _ _ _ (BRNotApp ctx tid n c na)))
    ((IsApp h as)
      (match many h _
        ((Ref y)
          (match many (nat-dec y tid) _
            ((NDSame z)
              (match many (not-len-dec n as) _
                ((LenIsNot b d nl) (RetNo _ _ _ _ (BRArity ctx tid n (Ref y) as nl)))
                ((LenIs b d ln) (RetYes _ _ _ as ln))))
            ((NDDiff z w nq)
              (match many (same-dec fuel ctx (Ref y) (Ref tid)) _
                ((SDDiffer a1 b1 c1 df) (RetNo _ _ _ _ (BRHead ctx tid n (Ref y) as df)))
                (else (RetStuck _ _ _ _))))))
        (else
          (match many (same-dec fuel ctx h (Ref tid)) _
            ((SDDiffer a1 b1 c1 df) (RetNo _ _ _ _ (BRHead ctx tid n h as df)))
            (else (RetStuck _ _ _ _))))))))

; Why a canonical scrutinee type cannot be matched, or the declared type constructor at its head.
(def-adts
  (MatchableDec : ((Ctx) ctx) ((Term) c) -> Type
    enum
    (many MatchableYes : (erased (Ctx) ctx) (many (Nat) tc) (many (List (Term)) targs) (many (List (Adt)) adts) (many (List (Nat)) ctors) (erased (Adts ctx adts) ad) (erased (AdtOf adts tc ctors) ao) ->
       (MatchableDec ctx (App (Ref tc) targs)))
    (many MatchableNo : (erased (Ctx) ctx) (erased (Term) c) (erased (Unmatchable ctx c) p) -> (MatchableDec ctx c))))
(def-fns _ $ many matchable-dec : (many (Ctx) ctx) (many (Term) c) -> (many (MatchableDec ctx c) r)
  (match many (not-app-dec c) _
    ((IsNotApp x na) (MatchableNo _ _ (UmNotApp ctx c na)))
    ((IsApp h as)
      (let (many adts) (erased ad) (ctx-adts ctx))
      (match many h _
        ((Ref tc)
          (match many (adt-dec adts tc) _
            ((AdtMiss a b n) (MatchableNo _ _ (UmNoAdt ctx tc as adts ad n)))
            ((AdtHit a b ctors ao) (MatchableYes _ tc as adts ctors ad ao))))
        ((Bound k) (MatchableNo _ _ (UmHeadVar ctx (Bound k) as (NRBound k))))
        ((App h2 as2) (MatchableNo _ _ (UmHeadVar ctx (App h2 as2) as (NRApp h2 as2))))
        ((Univ) (MatchableNo _ _ (UmHeadVar ctx (Univ) as (NRUniv))))
        ((Fn l ps rs) (MatchableNo _ _ (UmHeadVar ctx (Fn l ps rs) as (NRFn l ps rs))))
        ((TyCtor ps) (MatchableNo _ _ (UmHeadVar ctx (TyCtor ps) as (NRTyCtor ps))))
        ((ValCtor ps rt) (MatchableNo _ _ (UmHeadVar ctx (ValCtor ps rt) as (NRValCtor ps rt))))))))

; A canonical proof type as a Predates or Subterm application, or why not.
(def-adts
  (PShapeDec : ((Ctx) ctx) ((Term) c) -> Type
    enum
    (many PSYes : (erased (Ctx) ctx) (erased (Term) c) (many (Term) ty) (many (Term) a) (many (Term) lv) (erased (PredatesShape ctx c ty a lv) p) -> (PShapeDec ctx c))
    (many PSNo : (erased (Ctx) ctx) (erased (Term) c) (erased (NotPredatesShape ctx c) p) -> (PShapeDec ctx c))
    (many PSStuck : (erased (Ctx) ctx) (erased (Term) c) -> (PShapeDec ctx c)))
  (SShapeDec : ((Ctx) ctx) ((Term) c) -> Type
    enum
    (many SSYes : (erased (Ctx) ctx) (erased (Term) c) (many (Term) ta) (many (Term) a) (many (Term) tb) (many (Term) b) (erased (SubtermShape ctx c ta a tb b) p) -> (SShapeDec ctx c))
    (many SSNo : (erased (Ctx) ctx) (erased (Term) c) (erased (NotSubtermShape ctx c) p) -> (SShapeDec ctx c))
    (many SSStuck : (erased (Ctx) ctx) (erased (Term) c) -> (SShapeDec ctx c))))
(def-fns _ $ many predates-shape : (many (Nat) fuel) (many (Ctx) ctx) (many (Term) c) -> (many (PShapeDec ctx c) r)
  (match many (not-app-dec c) _
    ((IsNotApp x na) (PSNo _ _ (NPSNotApp ctx c na)))
    ((IsApp h as)
      (match many (not-len-dec (Succ (Succ (Succ (Zero)))) as) _
        ((LenIsNot b d nl) (PSNo _ _ (NPSArity ctx h as nl)))
        ((LenIs b d ln)
          (match many (same-dec fuel ctx h (Ref (Succ (Zero)))) _
            ((SDStuck a1 b1 c1) (PSStuck _ _))
            ((SDDiffer a1 b1 c1 df) (PSNo _ _ (NPSHead ctx h as df)))
            ((SDSame a1 b1 c1 sh)
              (match many as _
                ((Cons e ty rest1)
                  (match many rest1 _
                    ((Cons g a rest2)
                      (match many rest2 _
                        ((Cons k2 lv rest3)
                          (match many rest3 _
                            ((Nil m) (PSYes ctx c ty a lv (PSBy ctx h ty a lv sh)))
                            (else (PSStuck _ _))))
                        (else (PSStuck _ _))))
                    (else (PSStuck _ _))))
                (else (PSStuck _ _))))))))))
(def-fns _ $ many subterm-shape : (many (Nat) fuel) (many (Ctx) ctx) (many (Term) c) -> (many (SShapeDec ctx c) r)
  (match many (not-app-dec c) _
    ((IsNotApp x na) (SSNo _ _ (NSSNotApp ctx c na)))
    ((IsApp h as)
      (match many (not-len-dec (Succ (Succ (Succ (Succ (Zero))))) as) _
        ((LenIsNot b d nl) (SSNo _ _ (NSSArity ctx h as nl)))
        ((LenIs b d ln)
          (match many (same-dec fuel ctx h (Ref (Succ (Succ (Zero))))) _
            ((SDStuck a1 b1 c1) (SSStuck _ _))
            ((SDDiffer a1 b1 c1 df) (SSNo _ _ (NSSHead ctx h as df)))
            ((SDSame a1 b1 c1 sh)
              (match many as _
                ((Cons e ta rest1)
                  (match many rest1 _
                    ((Cons g a rest2)
                      (match many rest2 _
                        ((Cons k2 tb rest3)
                          (match many rest3 _
                            ((Cons m b rest4)
                              (match many rest4 _
                                ((Nil n) (SSYes ctx c ta a tb b (SSBy ctx h ta a tb b sh)))
                                (else (SSStuck _ _))))
                            (else (SSStuck _ _))))
                        (else (SSStuck _ _))))
                    (else (SSStuck _ _))))
                (else (SSStuck _ _))))))))))

; What each axiom concludes from two canonical proof types, with the evidence its rule wants; the
; derivation itself is assembled by [axiom-derivation], one case per axiom.
(def-adts
  (AxiomOk : ((Key) k) ((Ctx) ctx1) ((Term) cp) ((Ctx) ctx2) ((Term) cq) ((Term) concl) -> Type
    enum
    (many AOPredatesTrans : (erased (Ctx) ctx1) (erased (Term) cp) (erased (Ctx) ctx2) (erased (Term) cq) (erased (Term) ty) (erased (Term) a) (erased (Term) l1) (erased (Term) ty2) (erased (Term) l1b) (erased (Term) l2)
       (erased (PredatesShape ctx1 cp ty a l1) s1) (erased (PredatesShape ctx2 cq ty2 l1b l2) s2) (erased (Same ctx2 ty2 (App (Ref (Zero)) (Nil (Term)))) st) (erased (Same ctx2 l1b l1) sl) ->
       (AxiomOk (KPredatesTrans) ctx1 cp ctx2 cq (App (Ref (Succ (Zero))) (Cons (Term) ty (Cons (Term) a (Cons (Term) l2 (Nil (Term))))))))
    (many AOSubtermTrans : (erased (Ctx) ctx1) (erased (Term) cp) (erased (Ctx) ctx2) (erased (Term) cq) (erased (Term) ta) (erased (Term) a) (erased (Term) tb) (erased (Term) b) (erased (Term) tb2) (erased (Term) b2) (erased (Term) tc) (erased (Term) c)
       (erased (SubtermShape ctx1 cp ta a tb b) s1) (erased (SubtermShape ctx2 cq tb2 b2 tc c) s2) (erased (Same ctx2 tb2 tb) st) (erased (Same ctx2 b2 b) sb) ->
       (AxiomOk (KSubtermTrans) ctx1 cp ctx2 cq (App (Ref (Succ (Succ (Zero)))) (Cons (Term) ta (Cons (Term) a (Cons (Term) tc (Cons (Term) c (Nil (Term)))))))))
    (many AOPredatesSubterm : (erased (Ctx) ctx1) (erased (Term) cp) (erased (Ctx) ctx2) (erased (Term) cq) (erased (Term) ty) (erased (Term) a) (erased (Term) l) (erased (Term) tb) (erased (Term) b) (erased (Term) ty2) (erased (Term) a2)
       (erased (PredatesShape ctx1 cp ty a l) s1) (erased (SubtermShape ctx2 cq tb b ty2 a2) s2) (erased (Same ctx2 ty2 ty) st) (erased (Same ctx2 a2 a) sa) ->
       (AxiomOk (KPredatesSubterm) ctx1 cp ctx2 cq (App (Ref (Succ (Zero))) (Cons (Term) tb (Cons (Term) b (Cons (Term) l (Nil (Term)))))))))
  (AxiomDec : ((Key) k) ((Ctx) ctx1) ((Term) cp) ((Ctx) ctx2) ((Term) cq) -> Type
    enum
    (many AxOk : (erased (Key) k) (erased (Ctx) ctx1) (erased (Term) cp) (erased (Ctx) ctx2) (erased (Term) cq) (many (Term) concl) (erased (AxiomOk k ctx1 cp ctx2 cq concl) p) -> (AxiomDec k ctx1 cp ctx2 cq))
    (many AxBad : (erased (Key) k) (erased (Ctx) ctx1) (erased (Term) cp) (erased (Ctx) ctx2) (erased (Term) cq) (erased (AxiomBad k ctx1 cp ctx2 cq) p) -> (AxiomDec k ctx1 cp ctx2 cq))
    (many AxStuck : (erased (Key) k) (erased (Ctx) ctx1) (erased (Term) cp) (erased (Ctx) ctx2) (erased (Term) cq) -> (AxiomDec k ctx1 cp ctx2 cq))))

(def-fns _ $ many axiom-check : (many (Nat) fuel) (many (Key) k) (many (Ctx) ctx1) (many (Term) cp) (many (Ctx) ctx2) (many (Term) cq) (erased (AxiomKey k) ak) -> (many (AxiomDec k ctx1 cp ctx2 cq) r)
  (match many k _
    ((KPredatesTrans)
      (match many (predates-shape fuel ctx1 cp) _
        ((PSStuck a b) (AxStuck _ _ _ _ _))
        ((PSNo a b n) (AxBad _ _ _ _ _ (ABPredatesTransP ctx1 cp ctx2 cq n)))
        ((PSYes a b ty a1 l1 s1)
          (match many (predates-shape fuel ctx2 cq) _
            ((PSStuck c d) (AxStuck _ _ _ _ _))
            ((PSNo c d n) (AxBad _ _ _ _ _ (ABPredatesTransQ ctx1 cp ctx2 cq n)))
            ((PSYes c d ty2 l1b l2 s2)
              (match many (same-dec fuel ctx2 ty2 (App (Ref (Zero)) (Nil _))) _
                ((SDStuck e g h) (AxStuck _ _ _ _ _))
                ((SDDiffer e g h df) (AxBad _ _ _ _ _ (ABPredatesTransType ctx1 cp ctx2 cq ty2 l1b l2 s2 df)))
                ((SDSame e g h st)
                  (match many (same-dec fuel ctx2 l1b l1) _
                    ((SDStuck e2 g2 h2) (AxStuck _ _ _ _ _))
                    ((SDDiffer e2 g2 h2 df) (AxBad _ _ _ _ _ (ABPredatesTransLink ctx1 cp ctx2 cq ty a1 l1 ty2 l1b l2 s1 s2 df)))
                    ((SDSame e2 g2 h2 sl) (AxOk _ _ _ _ _ (App (Ref (Succ (Zero))) (Cons _ ty (Cons _ a1 (Cons _ l2 (Nil _))))) (AOPredatesTrans ctx1 cp ctx2 cq ty a1 l1 ty2 l1b l2 s1 s2 st sl)))))))))))
    ((KSubtermTrans)
      (match many (subterm-shape fuel ctx1 cp) _
        ((SSStuck a b) (AxStuck _ _ _ _ _))
        ((SSNo a b n) (AxBad _ _ _ _ _ (ABSubtermTransP ctx1 cp ctx2 cq n)))
        ((SSYes a b ta a1 tb b1 s1)
          (match many (subterm-shape fuel ctx2 cq) _
            ((SSStuck c d) (AxStuck _ _ _ _ _))
            ((SSNo c d n) (AxBad _ _ _ _ _ (ABSubtermTransQ ctx1 cp ctx2 cq n)))
            ((SSYes c d tb2 b2 tc c1 s2)
              (match many (same-dec fuel ctx2 tb2 tb) _
                ((SDStuck e g h) (AxStuck _ _ _ _ _))
                ((SDDiffer e g h df) (AxBad _ _ _ _ _ (ABSubtermTransType ctx1 cp ctx2 cq ta a1 tb b1 tb2 b2 tc c1 s1 s2 df)))
                ((SDSame e g h st)
                  (match many (same-dec fuel ctx2 b2 b1) _
                    ((SDStuck e2 g2 h2) (AxStuck _ _ _ _ _))
                    ((SDDiffer e2 g2 h2 df) (AxBad _ _ _ _ _ (ABSubtermTransLink ctx1 cp ctx2 cq ta a1 tb b1 tb2 b2 tc c1 s1 s2 df)))
                    ((SDSame e2 g2 h2 sb) (AxOk _ _ _ _ _ (App (Ref (Succ (Succ (Zero)))) (Cons _ ta (Cons _ a1 (Cons _ tc (Cons _ c1 (Nil _)))))) (AOSubtermTrans ctx1 cp ctx2 cq ta a1 tb b1 tb2 b2 tc c1 s1 s2 st sb)))))))))))
    ((KPredatesSubterm)
      (match many (predates-shape fuel ctx1 cp) _
        ((PSStuck a b) (AxStuck _ _ _ _ _))
        ((PSNo a b n) (AxBad _ _ _ _ _ (ABPredatesSubtermP ctx1 cp ctx2 cq n)))
        ((PSYes a b ty a1 l s1)
          (match many (subterm-shape fuel ctx2 cq) _
            ((SSStuck c d) (AxStuck _ _ _ _ _))
            ((SSNo c d n) (AxBad _ _ _ _ _ (ABPredatesSubtermQ ctx1 cp ctx2 cq n)))
            ((SSYes c d tb b1 ty2 a2 s2)
              (match many (same-dec fuel ctx2 ty2 ty) _
                ((SDStuck e g h) (AxStuck _ _ _ _ _))
                ((SDDiffer e g h df) (AxBad _ _ _ _ _ (ABPredatesSubtermType ctx1 cp ctx2 cq ty a1 l tb b1 ty2 a2 s1 s2 df)))
                ((SDSame e g h st)
                  (match many (same-dec fuel ctx2 a2 a1) _
                    ((SDStuck e2 g2 h2) (AxStuck _ _ _ _ _))
                    ((SDDiffer e2 g2 h2 df) (AxBad _ _ _ _ _ (ABPredatesSubtermLink ctx1 cp ctx2 cq ty a1 l tb b1 ty2 a2 s1 s2 df)))
                    ((SDSame e2 g2 h2 sa) (AxOk _ _ _ _ _ (App (Ref (Succ (Zero))) (Cons _ tb (Cons _ b1 (Cons _ l (Nil _))))) (AOPredatesSubterm ctx1 cp ctx2 cq ty a1 l tb b1 ty2 a2 s1 s2 st sa)))))))))))
    (else (AxStuck _ _ _ _ _))))

; The ElabExpr derivation of an axiom, from the pieces: one case per axiom, an erased function since only
; the derivation is built.
(def-fns _ $ erased axiom-derivation : (erased (Ctx) ctx) (erased (Key) k) (erased (Raw) pr) (erased (Raw) qr) (erased (Ctx) ctx1) (erased (Core) pc) (erased (Nat) p) (erased (Term) pty) (erased (Term) cp)
    (erased (Ctx) ctx2) (erased (Core) qc) (erased (Nat) q) (erased (Term) qty) (erased (Term) cq) (erased (Nat) e) (erased (Ctx) out) (erased (Term) concl)
    (erased (ElabExpr ctx pr (EOk ctx1 pc (Cons (Nat) p (Nil (Nat))))) ep) (erased (TypeOf ctx1 p pty) tp) (erased (Canonical ctx1 pty cp) c1)
    (erased (ElabExpr ctx1 qr (EOk ctx2 qc (Cons (Nat) q (Nil (Nat))))) eq) (erased (TypeOf ctx2 q qty) tq) (erased (Canonical ctx2 qty cq) c2)
    (erased (AxiomOk k ctx1 cp ctx2 cq concl) ok) (erased (Mint ctx2 (None (String)) concl (KPlain) (None (Term)) e out) m) ->
    (erased (ElabExpr ctx (RList (Cons (Raw) (RKey k) (Cons (Raw) pr (Cons (Raw) qr (Nil (Raw)))))) (EOk out (CToken) (Cons (Nat) e (Nil (Nat))))) d)
  (match erased ok _
    ((AOPredatesTrans x1 x2 x3 x4 ty a l1 ty2 l1b l2 s1 s2 st sl) (EXPredatesTrans ctx pr qr ctx1 pc p pty cp ty a l1 ctx2 qc q qty cq ty2 l1b l2 e out ep tp c1 s1 eq tq c2 s2 st sl m))
    ((AOSubtermTrans x1 x2 x3 x4 ta a tb b tb2 b2 tc c s1 s2 st sb) (EXSubtermTrans ctx pr qr ctx1 pc p pty cp ta a tb b ctx2 qc q qty cq tb2 b2 tc c e out ep tp c1 s1 eq tq c2 s2 st sb m))
    ((AOPredatesSubterm x1 x2 x3 x4 ty a l tb b ty2 a2 s1 s2 st sa) (EXPredatesSubterm ctx pr qr ctx1 pc p pty cp ty a l ctx2 qc q qty cq tb b ty2 a2 e out ep tp c1 s1 eq tq c2 s2 st sa m))))

; ---- Expressions, statements, bodies and declarations: one function per judgment, in one group.

(def-adts
  (ExprDec : ((Ctx) ctx) ((Raw) raw) -> Type
    enum
    (many MkExprDec : (erased (Ctx) ctx) (erased (Raw) raw) (many (EOut) out) (erased (ElabExpr ctx raw out) p) -> (ExprDec ctx raw))
    (many ExprStuck : (erased (Ctx) ctx) (erased (Raw) raw) -> (ExprDec ctx raw)))
  (ItemsDec : ((Ctx) ctx) ((List (Raw)) raws) -> Type
    enum
    (many MkItemsDec : (erased (Ctx) ctx) (erased (List (Raw)) raws) (many (AOut) out) (erased (ElabItems ctx raws out) p) -> (ItemsDec ctx raws))
    (many ItemsStuck : (erased (Ctx) ctx) (erased (List (Raw)) raws) -> (ItemsDec ctx raws)))
  (ExprArgsDec : ((Ctx) ctx) ((List (Maybe (Term))) acc) ((List (Entry)) tele) ((List (Raw)) args) -> Type
    enum
    (many MkExprArgsDec : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (List (Entry)) tele) (erased (List (Raw)) args) (many (AOut) out) (erased (ElabExprArgs ctx acc tele args out) p) ->
       (ExprArgsDec ctx acc tele args))
    (many ExprArgsStuck : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (List (Entry)) tele) (erased (List (Raw)) args) -> (ExprArgsDec ctx acc tele args)))
  (DecreaseDec : ((Ctx) ctx) ((Term) l) ((List (Entry)) ps) ((List (Nat)) ids) ((Ann) ann) -> Type
    enum
    (many MkDecreaseDec : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Nat)) ids) (erased (Ann) ann) (many (DOut) out) (erased (Decrease ctx l ps ids ann out) p) ->
       (DecreaseDec ctx l ps ids ann))
    (many DecreaseStuck : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Nat)) ids) (erased (Ann) ann) -> (DecreaseDec ctx l ps ids ann)))
  (RetsDec : ((Ctx) ctx) ((List (Maybe (Term))) acc) ((List (Entry)) rets) ((List (Nat)) ids) -> Type
    enum
    (many MkRetsDec : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (List (Entry)) rets) (erased (List (Nat)) ids) (many (ROut) out) (erased (CheckRets ctx acc rets ids out) p) -> (RetsDec ctx acc rets ids))
    (many RetsStuck : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (List (Entry)) rets) (erased (List (Nat)) ids) -> (RetsDec ctx acc rets ids)))
  (BranchesDec : ((Ctx) ctx) ((Nat) s) ((Nat) tc) ((List (Nat)) ctors) ((List (Nat)) seen) ((List (Entry)) rt) ((List (Raw)) brs) -> Type
    enum
    (many MkBranchesDec : (erased (Ctx) ctx) (erased (Nat) s) (erased (Nat) tc) (erased (List (Nat)) ctors) (erased (List (Nat)) seen) (erased (List (Entry)) rt) (erased (List (Raw)) brs) (many (BrOut) out)
       (erased (ElabBranches ctx s tc ctors seen rt brs out) p) -> (BranchesDec ctx s tc ctors seen rt brs))
    (many BranchesStuck : (erased (Ctx) ctx) (erased (Nat) s) (erased (Nat) tc) (erased (List (Nat)) ctors) (erased (List (Nat)) seen) (erased (List (Entry)) rt) (erased (List (Raw)) brs) -> (BranchesDec ctx s tc ctors seen rt brs)))
  (CoveredDec : ((Ctx) ctx) ((Nat) s) ((List (Nat)) ctors) ((List (Nat)) seen) -> Type
    enum
    (many CovYes : (erased (Ctx) ctx) (erased (Nat) s) (erased (List (Nat)) ctors) (erased (List (Nat)) seen) (erased (Covered ctx s ctors seen) p) -> (CoveredDec ctx s ctors seen))
    (many CovNo : (erased (Ctx) ctx) (erased (Nat) s) (erased (List (Nat)) ctors) (erased (List (Nat)) seen) (erased (Uncovered ctx s ctors seen) p) -> (CoveredDec ctx s ctors seen))
    (many CovStuck : (erased (Ctx) ctx) (erased (Nat) s) (erased (List (Nat)) ctors) (erased (List (Nat)) seen) -> (CoveredDec ctx s ctors seen)))
  (RefutedDec : ((Ctx) ctx) ((Nat) s) ((Nat) c) -> Type
    enum
    (many RefYes : (erased (Ctx) ctx) (erased (Nat) s) (erased (Nat) c) (erased (Refuted ctx s c) p) -> (RefutedDec ctx s c))
    (many RefNo : (erased (Ctx) ctx) (erased (Nat) s) (erased (Nat) c) (erased (Reachable ctx s c) p) -> (RefutedDec ctx s c))
    (many RefStuck : (erased (Ctx) ctx) (erased (Nat) s) (erased (Nat) c) -> (RefutedDec ctx s c)))
  (BodyDec : ((Ctx) ctx) ((List (Raw)) items) -> Type
    enum
    (many MkBodyDec : (erased (Ctx) ctx) (erased (List (Raw)) items) (many (EOut) out) (erased (ElabBody ctx items out) p) -> (BodyDec ctx items))
    (many BodyStuck : (erased (Ctx) ctx) (erased (List (Raw)) items) -> (BodyDec ctx items)))
  (StmtDec : ((Ctx) ctx) ((Raw) raw) -> Type
    enum
    (many MkStmtDec : (erased (Ctx) ctx) (erased (Raw) raw) (many (SOut) out) (erased (ElabStmt ctx raw out) p) -> (StmtDec ctx raw))
    (many StmtStuck : (erased (Ctx) ctx) (erased (Raw) raw) -> (StmtDec ctx raw)))
  (BindLetDec : ((Ctx) ctx) ((List (Raw)) binders) ((List (Nat)) ids) -> Type
    enum
    (many MkBindLetDec : (erased (Ctx) ctx) (erased (List (Raw)) binders) (erased (List (Nat)) ids) (many (AOut) out) (erased (BindLet ctx binders ids out) p) -> (BindLetDec ctx binders ids))
    (many BindLetStuck : (erased (Ctx) ctx) (erased (List (Raw)) binders) (erased (List (Nat)) ids) -> (BindLetDec ctx binders ids)))
  (FnsDec : ((Ctx) ctx) ((Term) l) ((List (Raw)) defs) -> Type
    enum
    (many MkFnsDec : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Raw)) defs) (many (FOut) out) (erased (MintFns ctx l defs out) p) -> (FnsDec ctx l defs))
    (many FnsStuck : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Raw)) defs) -> (FnsDec ctx l defs)))
  (BodiesDec : ((Ctx) ctx) ((Term) l) ((List (Sig)) sigs) ((List (Raw)) defs) -> Type
    enum
    (many MkBodiesDec : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Sig)) sigs) (erased (List (Raw)) defs) (many (BsOut) out) (erased (ElabBodies ctx l sigs defs out) p) -> (BodiesDec ctx l sigs defs))
    (many BodiesStuck : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Sig)) sigs) (erased (List (Raw)) defs) -> (BodiesDec ctx l sigs defs)))
  (TyconsDec : ((Ctx) ctx) ((List (Raw)) decls) -> Type
    enum
    (many MkTyconsDec : (erased (Ctx) ctx) (erased (List (Raw)) decls) (many (FOutT) out) (erased (MintTycons ctx decls out) p) -> (TyconsDec ctx decls))
    (many TyconsStuck : (erased (Ctx) ctx) (erased (List (Raw)) decls) -> (TyconsDec ctx decls)))
  (CtorsDec : ((Ctx) ctx) ((List (Raw)) decls) ((List (Nat)) tids) -> Type
    enum
    (many MkCtorsDec : (erased (Ctx) ctx) (erased (List (Raw)) decls) (erased (List (Nat)) tids) (many (FOutT) out) (erased (MintCtors ctx decls tids out) p) -> (CtorsDec ctx decls tids))
    (many CtorsStuck : (erased (Ctx) ctx) (erased (List (Raw)) decls) (erased (List (Nat)) tids) -> (CtorsDec ctx decls tids)))
  (DeclCtorsDec : ((Ctx) ctx) ((Nat) tid) ((Nat) n) ((List (Raw)) ctors) -> Type
    enum
    (many MkDeclCtorsDec : (erased (Ctx) ctx) (erased (Nat) tid) (erased (Nat) n) (erased (List (Raw)) ctors) (many (FOutT) out) (erased (MintDeclCtors ctx tid n ctors out) p) -> (DeclCtorsDec ctx tid n ctors))
    (many DeclCtorsStuck : (erased (Ctx) ctx) (erased (Nat) tid) (erased (Nat) n) (erased (List (Raw)) ctors) -> (DeclCtorsDec ctx tid n ctors))))

(def-fns _
  (many elab-expr : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Raw) raw) -> (many (ExprDec ctx raw) r)
    (match many fuel _
      ((Zero) (ExprStuck _ _))
      ((Succ f)
        (match many raw _
          ((RAtom s)
            (let (many scope) (erased sc) (ctx-scope ctx))
            (match many (name-dec scope s) _
              ((NameMiss a b n) (MkExprDec _ _ (EErr (RUnbound)) (EXUnbound ctx s scope sc n)))
              ((NameHit a b x n) (MkExprDec _ _ (EOk ctx (CVar x) (Cons _ x (Nil _))) (EXName ctx s x scope sc n)))))
          ((RKey k) (ExprStuck _ _))
          ((RList items)
            (match many items _
              ((Nil a) (ExprStuck _ _))
              ((Cons a h rest)
                (match many h _
                  ((RAtom s) (elab-app f ctx h rest (HeadAtom s)))
                  ((RList inner) (elab-app f ctx h rest (HeadList inner)))
                  ((RKey k)
                    (match many k _
                      ((KValues)
                        (match many (elab-items f ctx rest) _
                          ((ItemsStuck b c) (ExprStuck _ _))
                          ((MkItemsDec b c out p)
                            (match many out _
                              ((AErr r) (MkExprDec _ _ (EErr r) (EXValuesErr ctx rest r p)))
                              ((AOk out2 cores ids) (MkExprDec _ _ (EOk out2 (CValues cores) ids) (EXValues ctx rest out2 cores ids p)))))))
                      ((KFn) (elab-former-expr f ctx (KFn) rest (FKFn)))
                      ((KTyCtor) (elab-former-expr f ctx (KTyCtor) rest (FKTyCtor)))
                      ((KValCtor) (elab-former-expr f ctx (KValCtor) rest (FKValCtor)))
                      ((KMatch)
                        (match many rest _
                          ((Cons b sr rest2)
                            (match many rest2 _
                              ((Cons c annr brs)
                                (match many annr _
                                  ((RList ann) (elab-match f ctx sr ann brs))
                                  (else (ExprStuck _ _))))
                              (else (ExprStuck _ _))))
                          (else (ExprStuck _ _))))
                      ((KProveSubterm)
                        (match many rest _
                          ((Cons b ar rest2)
                            (match many rest2 _
                              ((Cons c br rest3)
                                (match many rest3 _
                                  ((Nil d) (elab-prove-subterm f ctx ar br))
                                  (else (ExprStuck _ _))))
                              (else (ExprStuck _ _))))
                          (else (ExprStuck _ _))))
                      ((KProvePredates)
                        (match many rest _
                          ((Cons b xr rest2)
                            (match many rest2 _
                              ((Cons c lr rest3)
                                (match many rest3 _
                                  ((Nil d)
                                    (match many xr _
                                      ((RAtom xs)
                                        (match many lr _
                                          ((RAtom ls) (elab-prove-predates f ctx xs ls))
                                          (else (ExprStuck _ _))))
                                      (else (ExprStuck _ _))))
                                  (else (ExprStuck _ _))))
                              (else (ExprStuck _ _))))
                          (else (ExprStuck _ _))))
                      ((KPredatesTrans) (elab-axiom-args f ctx (KPredatesTrans) rest (AKPredatesTrans)))
                      ((KSubtermTrans) (elab-axiom-args f ctx (KSubtermTrans) rest (AKSubtermTrans)))
                      ((KPredatesSubterm) (elab-axiom-args f ctx (KPredatesSubterm) rest (AKPredatesSubterm)))
                      (else (ExprStuck _ _))))))))))))
  ; an axiom's two items
  (many elab-axiom-args : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Key) k) (many (List (Raw)) items) (erased (AxiomKey k) ak) -> (many (ExprDec ctx (RList (Cons (Raw) (RKey k) items))) r)
    (match many fuel _
      ((Zero) (ExprStuck _ _))
      ((Succ f)
        (match many items _
          ((Cons a pr rest1)
            (match many rest1 _
              ((Cons b qr rest2)
                (match many rest2 _
                  ((Nil c) (elab-axiom f ctx k pr qr ak))
                  (else (ExprStuck _ _))))
              (else (ExprStuck _ _))))
          (else (ExprStuck _ _))))))
  ; (axiom p q): both proofs elaborated, their canonical types read, and the axiom's own check applied
  (many elab-axiom : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Key) k) (many (Raw) pr) (many (Raw) qr) (erased (AxiomKey k) ak) ->
      (many (ExprDec ctx (RList (Cons (Raw) (RKey k) (Cons (Raw) pr (Cons (Raw) qr (Nil (Raw))))))) r)
    (match many fuel _
      ((Zero) (ExprStuck _ _))
      ((Succ f)
        (match many (elab-expr f ctx pr) _
          ((ExprStuck a b) (ExprStuck _ _))
          ((MkExprDec a b pout ep)
            (match many pout _
              ((EErr r) (MkExprDec _ _ (EErr r) (EXAxiomErrP ctx k pr qr r ak ep)))
              ((EOk ctx1 pc pids)
                (match many (one-dec pids) _
                  ((OneNo c n) (MkExprDec _ _ (EErr (RSize)) (EXAxiomSizeP ctx k pr qr ctx1 pc pids ak ep n)))
                  ((OneYes p)
                    (match many (elab-expr f ctx1 qr) _
                      ((ExprStuck c d) (ExprStuck _ _))
                      ((MkExprDec c d qout eq)
                        (match many qout _
                          ((EErr r) (MkExprDec _ _ (EErr r) (EXAxiomErrQ ctx k pr qr ctx1 pc p r ak ep eq)))
                          ((EOk ctx2 qc qids)
                            (match many (one-dec qids) _
                              ((OneNo e n) (MkExprDec _ _ (EErr (RSize)) (EXAxiomSizeQ ctx k pr qr ctx1 pc p ctx2 qc qids ak ep eq n)))
                              ((OneYes q)
                                (match many (type-of ctx1 p) _
                                  ((TypeOfStuck e g) (ExprStuck _ _))
                                  ((TypeIs e g pty kp tp kq)
                                    (match many (canonical f ctx1 pty) _
                                      ((CanonicalStuck h1 h2) (ExprStuck _ _))
                                      ((CanonicalIs h1 h2 cp c1)
                                        (match many (type-of ctx2 q) _
                                          ((TypeOfStuck e2 g2) (ExprStuck _ _))
                                          ((TypeIs e2 g2 qty kq2 tq kq3)
                                            (match many (canonical f ctx2 qty) _
                                              ((CanonicalStuck h3 h4) (ExprStuck _ _))
                                              ((CanonicalIs h3 h4 cq c2)
                                                (match many (axiom-check f k ctx1 cp ctx2 cq ak) _
                                                  ((AxStuck a1 b1 c3 d1 e1) (ExprStuck _ _))
                                                  ((AxBad a1 b1 c3 d1 e1 bad) (MkExprDec _ _ (EErr (RBadProof)) (EXAxiomBad ctx k pr qr ctx1 pc p pty cp ctx2 qc q qty cq ep tp c1 eq tq c2 bad)))
                                                  ((AxOk a1 b1 c3 d1 e1 concl ok)
                                                    (let (many e3) (many out) (erased m) (mint ctx2 (None _) concl (KPlain) (None _)))
                                                    (MkExprDec _ _ (EOk out (CToken) (Cons _ e3 (Nil _))) (axiom-derivation ctx k pr qr ctx1 pc p pty cp ctx2 qc q qty cq e3 out concl ep tp c1 eq tq c2 ok m)))))))))))))))))))))))))))
  (many elab-former-expr : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Key) k) (many (List (Raw)) items) (erased (FormerKey k) fk) -> (many (ExprDec ctx (RList (Cons (Raw) (RKey k) items))) r)
    (match many fuel _
      ((Zero) (ExprStuck _ _))
      ((Succ f)
        (match many (elab-term f ctx (RList (Cons _ (RKey k) items))) _
          ((TermStuck a b) (ExprStuck _ _))
          ((MkTermDec a b out p)
            (match many out _
              ((TErr r) (MkExprDec _ _ (EErr r) (EXFormerErr ctx k items r fk p)))
              ((TOk t ty)
                (let (many x) (many out2) (erased m) (mint ctx (None _) ty (KPlain) (Some _ t)))
                (MkExprDec _ _ (EOk out2 (CFormer t) (Cons _ x (Nil _))) (EXFormer ctx k items t ty x out2 fk p m)))))))))
  ; (h items...): a constructor or type-constructor application, or a call
  (many elab-app : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Raw) h) (many (List (Raw)) items) (erased (HeadRaw h) hr) -> (many (ExprDec ctx (RList (Cons (Raw) h items))) r)
    (match many fuel _
      ((Zero) (ExprStuck _ _))
      ((Succ f)
        (match many (elab-expr f ctx h) _
          ((ExprStuck a b) (ExprStuck _ _))
          ((MkExprDec a b hout p)
            (match many hout _
              ((EErr r) (MkExprDec _ _ (EErr r) (EXHeadErr ctx h items r hr p)))
              ((EOk ctx1 hc hids)
                (match many (one-dec hids) _
                  ((OneNo c n) (MkExprDec _ _ (EErr (RSize)) (EXHeadSize ctx h items ctx1 hc hids hr p n)))
                  ((OneYes x)
                    (match many (type-of ctx1 x) _
                      ((TypeOfStuck c d) (ExprStuck _ _))
                      ((TypeIs c d hty k t kq)
                        (match many (canonical f ctx1 hty) _
                          ((CanonicalStuck e g) (ExprStuck _ _))
                          ((CanonicalIs e g hc2 cn)
                            (match many hc2 _
                              ((TyCtor ps)
                                (match many (elab-expr-args f ctx1 (Nil _) ps items) _
                                  ((ExprArgsStuck a1 b1 c1 d1) (ExprStuck _ _))
                                  ((MkExprArgsDec a1 b1 c1 d1 aout ap)
                                    (match many aout _
                                      ((AErr r) (MkExprDec _ _ (EErr r) (EXAppArgsErr ctx h items ctx1 hc x hty ps r hr p t (HeadTy ctx1 hty ps cn) ap)))
                                      ((AOk ctx2 cores ids)
                                        (let (many ts) (erased rf) (refs ids))
                                        (let (many e2) (many out) (erased m) (mint ctx2 (None _) (Univ) (KPlain) (Some _ (App (Ref x) ts))))
                                        (MkExprDec _ _ (EOk out (CApp hc cores) (Cons _ e2 (Nil _))) (EXTyApp ctx h items ctx1 hc x hty ps ctx2 cores ids ts e2 out hr p t cn ap rf m)))))))
                              ((ValCtor ps ret)
                                (match many (elab-expr-args f ctx1 (Nil _) ps items) _
                                  ((ExprArgsStuck a1 b1 c1 d1) (ExprStuck _ _))
                                  ((MkExprArgsDec a1 b1 c1 d1 aout ap)
                                    (match many aout _
                                      ((AErr r) (MkExprDec _ _ (EErr r) (EXAppArgsErr ctx h items ctx1 hc x hty ps r hr p t (HeadVal ctx1 hty ps ret cn) ap)))
                                      ((AOk ctx2 cores ids)
                                        (let (many ts) (erased rf) (refs ids))
                                        (let (many sub) (erased so) (somes ts))
                                        (match many (subst f sub ret) _
                                          ((SubstStuck a2 b2) (ExprStuck _ _))
                                          ((MkSubsted a2 b2 ty sb)
                                            (let (many e2) (many out) (erased m) (mint ctx2 (None _) ty (KPlain) (Some _ (App (Ref x) ts))))
                                            (MkExprDec _ _ (EOk out (CApp hc cores) (Cons _ e2 (Nil _))) (EXValApp ctx h items ctx1 hc x hty ps ret ctx2 cores ids ts sub ty e2 out hr p t cn ap rf so sb m)))))))))
                              ((Fn l ps rs)
                                (match many (call-raw-dec items) _
                                  ((CallRawStuck a1) (ExprStuck _ _))
                                  ((MkCallRaw a1 ann args cr)
                                    (match many (elab-expr-args f ctx1 (Nil _) ps args) _
                                      ((ExprArgsStuck a2 b2 c2 d2) (ExprStuck _ _))
                                      ((MkExprArgsDec a2 b2 c2 d2 aout ap)
                                        (match many aout _
                                          ((AErr r) (MkExprDec _ _ (EErr r) (EXCallArgsErr ctx h items ctx1 hc x hty l ps rs ann args r hr p t cn cr ap)))
                                          ((AOk ctx2 cores ids)
                                            (match many (decrease f ctx2 l ps ids ann) _
                                              ((DecreaseStuck a3 b3 c3 d3 e3) (ExprStuck _ _))
                                              ((MkDecreaseDec a3 b3 c3 d3 e3 dout dp)
                                                (match many dout _
                                                  ((DErr r) (MkExprDec _ _ (EErr r) (EXCallDecreaseErr ctx h items ctx1 hc x hty l ps rs ann args ctx2 cores ids r hr p t cn cr ap dp)))
                                                  ((DOk ctx3)
                                                    (let (many ts) (erased rf) (refs ids))
                                                    (let (many sub) (erased so) (somes ts))
                                                    (let (many names) (erased nn) (nones rs))
                                                    (match many (mint-tele f ctx3 sub rs names) _
                                                      ((MTStuck a4 b4 c4 d4) (ExprStuck _ _))
                                                      ((MTMinted a4 b4 c4 d4 out rids m)
                                                        (MkExprDec _ _ (EOk out (CCall hc cores) rids) (EXCall ctx h items ctx1 hc x hty l ps rs ann args ctx2 cores ids ctx3 ts sub names out rids hr p t cn cr ap dp rf so nn m)))))))))))))))
                              ((Ref y) (MkExprDec _ _ (EErr (RNotApplicable)) (EXNotApplicable ctx h items ctx1 hc x hty (Ref y) hr p t cn (NTNRef y))))
                              ((Bound kk) (MkExprDec _ _ (EErr (RNotApplicable)) (EXNotApplicable ctx h items ctx1 hc x hty (Bound kk) hr p t cn (NTNBound kk))))
                              ((App h2 as2) (MkExprDec _ _ (EErr (RNotApplicable)) (EXNotApplicable ctx h items ctx1 hc x hty (App h2 as2) hr p t cn (NTNApp h2 as2))))
                              ((Univ) (MkExprDec _ _ (EErr (RNotApplicable)) (EXNotApplicable ctx h items ctx1 hc x hty (Univ) hr p t cn (NTNUniv))))))))))))))))))
  ; (match s (rets) branches...)
  (many elab-match : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Raw) sr) (many (List (Raw)) ann) (many (List (Raw)) brs) ->
      (many (ExprDec ctx (RList (Cons (Raw) (RKey (KMatch)) (Cons (Raw) sr (Cons (Raw) (RList ann) brs))))) r)
    (match many fuel _
      ((Zero) (ExprStuck _ _))
      ((Succ f)
        (match many (elab-expr f ctx sr) _
          ((ExprStuck a b) (ExprStuck _ _))
          ((MkExprDec a b sout p)
            (match many sout _
              ((EErr r) (MkExprDec _ _ (EErr r) (EXMatchScrutErr ctx sr ann brs r p)))
              ((EOk ctx1 sc sids)
                (match many (one-dec sids) _
                  ((OneNo c n) (MkExprDec _ _ (EErr (RSize)) (EXMatchScrutSize ctx sr ann brs ctx1 sc sids p n)))
                  ((OneYes s)
                    (match many (type-of ctx1 s) _
                      ((TypeOfStuck c d) (ExprStuck _ _))
                      ((TypeIs c d sty k t kq)
                        (match many (canonical f ctx1 sty) _
                          ((CanonicalStuck e g) (ExprStuck _ _))
                          ((CanonicalIs e g cs cn)
                            (match many (matchable-dec ctx1 cs) _
                              ((MatchableNo a1 b1 um) (MkExprDec _ _ (EErr (RNotMatchable)) (EXNotMatchable ctx sr ann brs ctx1 sc s sty cs p t cn um)))
                              ((MatchableYes a1 tc targs adts ctors ad ao)
                                (match many (elab-tele f ctx1 (Nil _) ann) _
                                  ((TeleStuck a2 b2 c2) (ExprStuck _ _))
                                  ((MkTeleDec a2 b2 c2 tout et)
                                    (match many tout _
                                      ((TeleErr r) (MkExprDec _ _ (EErr r) (EXMatchAnnErr ctx sr ann brs ctx1 sc s r p et)))
                                      ((TeleOk ctxA rt rids rn)
                                        (let (many ctx2) (erased lv) (leave ctxA ctx1))
                                        (match many (elab-branches f ctx2 s tc ctors (Nil _) rt brs) _
                                          ((BranchesStuck a3 b3 c3 d3 e3 g3 h3) (ExprStuck _ _))
                                          ((MkBranchesDec a3 b3 c3 d3 e3 g3 h3 bout eb)
                                            (match many bout _
                                              ((BrErr r) (MkExprDec _ _ (EErr r) (EXMatchBranchesErr ctx sr ann brs ctx1 sc s sty tc targs adts ctors ctxA rt rids rn ctx2 r p t cn ad ao et lv eb)))
                                              ((BrOk ctx3 cbs seen)
                                                (match many (covered f ctx3 s ctors seen) _
                                                  ((CovStuck a4 b4 c4 d4) (ExprStuck _ _))
                                                  ((CovNo a4 b4 c4 d4 uc) (MkExprDec _ _ (EErr (RMissingBranch)) (EXMatchUncovered ctx sr ann brs ctx1 sc s sty tc targs adts ctors ctxA rt rids rn ctx2 ctx3 cbs seen p t cn ad ao et lv eb uc)))
                                                  ((CovYes a4 b4 c4 d4 cv)
                                                    (let (many names) (erased nn) (nones rt))
                                                    (match many (mint-tele f ctx3 (Nil _) rt names) _
                                                      ((MTStuck a5 b5 c5 d5) (ExprStuck _ _))
                                                      ((MTMinted a5 b5 c5 d5 out ids m)
                                                        (MkExprDec _ _ (EOk out (CMatch sc cbs) ids) (EXMatch ctx sr ann brs ctx1 sc s sty tc targs adts ctors ctxA rt rids rn ctx2 ctx3 cbs seen names out ids p t cn ad ao et lv eb cv nn m)))))))))))))))))))))))))))))
  (many elab-prove-subterm : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Raw) ar) (many (Raw) br) ->
      (many (ExprDec ctx (RList (Cons (Raw) (RKey (KProveSubterm)) (Cons (Raw) ar (Cons (Raw) br (Nil (Raw))))))) r)
    (match many fuel _
      ((Zero) (ExprStuck _ _))
      ((Succ f)
        (match many (elab-term f ctx ar) _
          ((TermStuck a b) (ExprStuck _ _))
          ((MkTermDec a b aout p)
            (match many aout _
              ((TErr r) (MkExprDec _ _ (EErr r) (EXProveSubtermErrA ctx ar br r p)))
              ((TOk at aty)
                (match many (elab-term f ctx br) _
                  ((TermStuck c d) (ExprStuck _ _))
                  ((MkTermDec c d bout q)
                    (match many bout _
                      ((TErr r) (MkExprDec _ _ (EErr r) (EXProveSubtermErrB ctx ar br at aty r p q)))
                      ((TOk bt bty)
                        (match many (canonical f ctx at) _
                          ((CanonicalStuck e g) (ExprStuck _ _))
                          ((CanonicalIs e g ca c1)
                            (match many (canonical f ctx bt) _
                              ((CanonicalStuck e2 g2) (ExprStuck _ _))
                              ((CanonicalIs e2 g2 cb c2)
                                (match many (sub-dec f ctx ca cb) _
                                  ((SubStuck a1 b1 c3) (ExprStuck _ _))
                                  ((SubNo a1 b1 c3 ns) (MkExprDec _ _ (EErr (RBadProof)) (EXProveSubtermNot ctx ar br at aty bt bty ca cb p q c1 c2 ns)))
                                  ((SubYes a1 b1 c3 ss)
                                    (let (many e3) (many out) (erased m) (mint ctx (None _) (App (Ref (Succ (Succ (Zero)))) (Cons _ aty (Cons _ at (Cons _ bty (Cons _ bt (Nil _)))))) (KPlain) (None _)))
                                    (MkExprDec _ _ (EOk out (CToken) (Cons _ e3 (Nil _))) (EXProveSubterm ctx ar br at aty bt bty ca cb e3 out p q c1 c2 ss m)))))))))))))))))))
  (many elab-prove-predates : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (String) xs) (many (String) ls) ->
      (many (ExprDec ctx (RList (Cons (Raw) (RKey (KProvePredates)) (Cons (Raw) (RAtom xs) (Cons (Raw) (RAtom ls) (Nil (Raw))))))) r)
    (let (many scope) (erased sc) (ctx-scope ctx))
    (match many (name-dec scope xs) _
      ((NameMiss a b n) (MkExprDec _ _ (EErr (RUnbound)) (EXProvePredatesUnboundX ctx xs ls scope sc n)))
      ((NameHit a b x nx)
        (match many (name-dec scope ls) _
          ((NameMiss c d n) (MkExprDec _ _ (EErr (RUnbound)) (EXProvePredatesUnboundL ctx xs ls scope x sc nx n)))
          ((NameHit c d l nl)
            (match many (type-of ctx x) _
              ((TypeOfStuck e g) (ExprStuck _ _))
              ((TypeIs e g tx kx t kq)
                (match many (type-of ctx l) _
                  ((TypeOfStuck e2 g2) (ExprStuck _ _))
                  ((TypeIs e2 g2 tl kl t2 kd)
                    (match many kl _
                      ((KPlain) (MkExprDec _ _ (EErr (RNotLevel)) (EXProvePredatesNotLevel ctx xs ls scope x l (KPlain) sc nx nl kd (NLKPlain))))
                      ((KDecl) (MkExprDec _ _ (EErr (RNotLevel)) (EXProvePredatesNotLevel ctx xs ls scope x l (KDecl) sc nx nl kd (NLKDecl))))
                      ((KLevel)
                        (match many (nat-cmp x l) _
                          ((CLt a1 b1 c1 d1 lt)
                            (let (many e3) (many out) (erased m) (mint ctx (None _) (App (Ref (Succ (Zero))) (Cons _ tx (Cons _ (Ref x) (Cons _ (Ref l) (Nil _))))) (KPlain) (None _)))
                            (MkExprDec _ _ (EOk out (CToken) (Cons _ e3 (Nil _))) (EXProvePredates ctx xs ls scope x l tx e3 out sc nx nl t kd lt m)))
                          ((CEq a1 b1 c1) (MkExprDec _ _ (EErr (RBadProof)) (EXProvePredatesAfter ctx xs ls scope x l sc nx nl kd (lt-succ x))))
                          ((CGt a1 b1 c1 d1 gt) (MkExprDec _ _ (EErr (RBadProof)) (EXProvePredatesAfter ctx xs ls scope x l sc nx nl kd (lt-weaken l x gt))))))))))))))))
  (many elab-items : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (List (Raw)) raws) -> (many (ItemsDec ctx raws) r)
    (match many fuel _
      ((Zero) (ItemsStuck _ _))
      ((Succ f)
        (match many raws _
          ((Nil a) (MkItemsDec _ _ (AOk ctx (Nil _) (Nil _)) (EINil ctx)))
          ((Cons a r rest)
            (match many (elab-expr f ctx r) _
              ((ExprStuck b c) (ItemsStuck _ _))
              ((MkExprDec b c out p)
                (match many out _
                  ((EErr e) (MkItemsDec _ _ (AErr e) (EIErr ctx r rest e p)))
                  ((EOk ctx1 core ids)
                    (match many (one-dec ids) _
                      ((OneNo d n) (MkItemsDec _ _ (AErr (RSize)) (EISize ctx r rest ctx1 core ids p n)))
                      ((OneYes x)
                        (match many (elab-items f ctx1 rest) _
                          ((ItemsStuck d e) (ItemsStuck _ _))
                          ((MkItemsDec d e rout q)
                            (match many rout _
                              ((AErr e2) (MkItemsDec _ _ (AErr e2) (EIRestErr ctx r rest ctx1 core x e2 p q)))
                              ((AOk out cores ids2) (MkItemsDec _ _ (AOk out (Cons _ core cores) (Cons _ x ids2)) (EICons ctx r rest ctx1 core x out cores ids2 p q)))))))))))))))))
  (many elab-expr-args : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (List (Maybe (Term))) acc) (many (List (Entry)) tele) (many (List (Raw)) args) -> (many (ExprArgsDec ctx acc tele args) r)
    (match many fuel _
      ((Zero) (ExprArgsStuck _ _ _ _))
      ((Succ f)
        (match many (len-dec _ _ tele args) _
          ((LenDiff a b c d m) (MkExprArgsDec _ _ _ _ (AErr (RArity)) (EAArity ctx acc tele args m)))
          ((LenSame a b c d)
            (match many tele _
              ((Nil e) (match many args _ ((Nil g) (MkExprArgsDec _ _ _ _ (AOk ctx (Nil _) (Nil _)) (EANil ctx acc))) ((Cons g x y) (ExprArgsStuck _ _ _ _))))
              ((Cons e entry es)
                (match many args _
                  ((Nil g) (ExprArgsStuck _ _ _ _))
                  ((Cons g ar rest)
                    (match many entry _
                      ((MkEntry s i t)
                        (match many (elab-expr f ctx ar) _
                          ((ExprStuck h k) (ExprArgsStuck _ _ _ _))
                          ((MkExprDec h k aout p)
                            (match many aout _
                              ((EErr r) (MkExprArgsDec _ _ _ _ (AErr r) (EAErr ctx acc (MkEntry s i t) es ar rest r p)))
                              ((EOk ctx1 core ids)
                                (match many (one-dec ids) _
                                  ((OneNo h2 n) (MkExprArgsDec _ _ _ _ (AErr (RSize)) (EASize ctx acc (MkEntry s i t) es ar rest ctx1 core ids p n)))
                                  ((OneYes x)
                                    (match many (subst f acc t) _
                                      ((SubstStuck h2 k2) (ExprArgsStuck _ _ _ _))
                                      ((MkSubsted h2 k2 t2 sb)
                                        (match many i _
                                          ((BFalse)
                                            (match many (type-of ctx1 x) _
                                              ((TypeOfStuck h3 k3) (ExprArgsStuck _ _ _ _))
                                              ((TypeIs h3 k3 xty kx ty kq)
                                                (match many (same-dec f ctx1 xty t2) _
                                                  ((SDStuck h4 k4 l4) (ExprArgsStuck _ _ _ _))
                                                  ((SDDiffer h4 k4 l4 d2) (MkExprArgsDec _ _ _ _ (AErr (RMismatch)) (EATyMismatch ctx acc s t es ar rest ctx1 core x xty t2 p ty sb d2)))
                                                  ((SDSame h4 k4 l4 sm)
                                                    (match many (elab-expr-args f ctx1 (Cons _ (Some _ (Ref x)) acc) es rest) _
                                                      ((ExprArgsStuck h5 k5 l5 m5) (ExprArgsStuck _ _ _ _))
                                                      ((MkExprArgsDec h5 k5 l5 m5 rout q)
                                                        (match many rout _
                                                          ((AErr r) (MkExprArgsDec _ _ _ _ (AErr r) (EARestErr ctx acc s (BFalse) t es ar rest ctx1 core x r p q)))
                                                          ((AOk out cores ids2) (MkExprArgsDec _ _ _ _ (AOk out (Cons _ core cores) (Cons _ x ids2)) (EATy ctx acc s t es ar rest ctx1 core x xty t2 out cores ids2 p ty sb sm q)))))))))))
                                          ((BTrue)
                                            (match many (same-dec f ctx1 (Ref x) t2) _
                                              ((SDStuck h4 k4 l4) (ExprArgsStuck _ _ _ _))
                                              ((SDDiffer h4 k4 l4 d2) (MkExprArgsDec _ _ _ _ (AErr (RMismatch)) (EAIsMismatch ctx acc s t es ar rest ctx1 core x t2 p sb d2)))
                                              ((SDSame h4 k4 l4 sm)
                                                (match many (elab-expr-args f ctx1 (Cons _ (Some _ (Ref x)) acc) es rest) _
                                                  ((ExprArgsStuck h5 k5 l5 m5) (ExprArgsStuck _ _ _ _))
                                                  ((MkExprArgsDec h5 k5 l5 m5 rout q)
                                                    (match many rout _
                                                      ((AErr r) (MkExprArgsDec _ _ _ _ (AErr r) (EARestErr ctx acc s (BTrue) t es ar rest ctx1 core x r p q)))
                                                      ((AOk out cores ids2) (MkExprArgsDec _ _ _ _ (AOk out (Cons _ core cores) (Cons _ x ids2)) (EAIs ctx acc s t es ar rest ctx1 core x t2 out cores ids2 p sb sm q)))))))))))))))))))))))))))))
  (many decrease : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Term) l) (many (List (Entry)) ps) (many (List (Nat)) ids) (many (Ann) ann) -> (many (DecreaseDec ctx l ps ids ann) r)
    (match many fuel _
      ((Zero) (DecreaseStuck _ _ _ _ _))
      ((Succ f)
        (let (many level) (erased lv) (ctx-level ctx))
        (match many level _
          ((None a)
            (match many ann _
              ((ANone) (MkDecreaseDec _ _ _ _ _ (DOk ctx) (DTop ctx l ps ids lv)))
              ((APredates pr) (MkDecreaseDec _ _ _ _ _ (DErr (RBadProof)) (DTopPredates ctx l ps ids pr lv)))
              ((ASubterm i pr) (MkDecreaseDec _ _ _ _ _ (DErr (RBadProof)) (DTopSubterm ctx l ps ids i pr lv)))))
          ((Some a cur)
            (match many ann _
              ((ANone) (MkDecreaseDec _ _ _ _ _ (DErr (RNoProof)) (DNone ctx l ps ids cur lv)))
              ((APredates pr)
                (match many (elab-expr f ctx pr) _
                  ((ExprStuck b c) (DecreaseStuck _ _ _ _ _))
                  ((MkExprDec b c pout ep)
                    (match many pout _
                      ((EErr r) (MkDecreaseDec _ _ _ _ _ (DErr r) (DPredatesErr ctx l ps ids pr cur r lv ep)))
                      ((EOk ctx1 pc pids)
                        (match many (one-dec pids) _
                          ((OneNo d n) (MkDecreaseDec _ _ _ _ _ (DErr (RSize)) (DPredatesSize ctx l ps ids pr cur ctx1 pc pids lv ep n)))
                          ((OneYes p)
                            (match many (type-of ctx1 p) _
                              ((TypeOfStuck d e) (DecreaseStuck _ _ _ _ _))
                              ((TypeIs d e pty kp t kq)
                                (match many (canonical f ctx1 pty) _
                                  ((CanonicalStuck g h) (DecreaseStuck _ _ _ _ _))
                                  ((CanonicalIs g h c cn)
                                    (match many (predates-dec f ctx1 c l cur) _
                                      ((PDStuck a1 b1 c1 d1) (DecreaseStuck _ _ _ _ _))
                                      ((PDNo a1 b1 c1 d1 np) (MkDecreaseDec _ _ _ _ _ (DErr (RBadProof)) (DPredatesBad ctx l ps ids pr cur ctx1 pc p pty c lv ep t cn np)))
                                      ((PDYes a1 b1 c1 d1 hh ty aa lv2 sh sty sa scc)
                                        (MkDecreaseDec _ _ _ _ _ (DOk ctx1) (DPredates ctx l ps ids pr cur ctx1 pc p pty hh ty aa lv2 lv ep t cn sh sty sa scc)))))))))))))))
              ((ASubterm i pr)
                (match many (same-dec f ctx l cur) _
                  ((SDStuck b c d) (DecreaseStuck _ _ _ _ _))
                  ((SDDiffer b c d df) (MkDecreaseDec _ _ _ _ _ (DErr (RBadProof)) (DSubtermLevel ctx l ps ids i pr cur lv df)))
                  ((SDSame b c d sl)
                    (match many (marked-index-dec ps i) _
                      ((MINoAt e g um) (MkDecreaseDec _ _ _ _ _ (DErr (RBadProof)) (DSubtermUnmarked ctx l ps ids i pr cur lv sl um)))
                      ((MIYesAt e g j mi)
                        (match many (nth-dec _ ids i) _
                          ((NthMiss a1 b1 c1 d1) (DecreaseStuck _ _ _ _ _))
                          ((NthHit a1 b1 c1 xi ni)
                            (match many (marked ps ids) _
                              ((MarkedStuck a2 b2) (DecreaseStuck _ _ _ _ _))
                              ((MkMarked a2 b2 cargs mk)
                                (let (many subargs) (erased sa) (ctx-subargs ctx))
                                (match many (prefix-dec f ctx j cargs subargs) _
                                  ((PrefixStuck a3 b3 c3 d3) (DecreaseStuck _ _ _ _ _))
                                  ((PrefixNo a3 b3 c3 d3 dp) (MkDecreaseDec _ _ _ _ _ (DErr (RBadProof)) (DSubtermPrefix ctx l ps ids i pr cur j cargs subargs lv sl mi mk sa dp)))
                                  ((PrefixYes a3 b3 c3 d3 bb sp)
                                    (match many (elab-expr f ctx pr) _
                                      ((ExprStuck a4 b4) (DecreaseStuck _ _ _ _ _))
                                      ((MkExprDec a4 b4 pout ep)
                                        (match many pout _
                                          ((EErr r) (MkDecreaseDec _ _ _ _ _ (DErr r) (DSubtermErr ctx l ps ids i pr cur r lv sl ep)))
                                          ((EOk ctx1 pc pids)
                                            (match many (one-dec pids) _
                                              ((OneNo a5 n) (MkDecreaseDec _ _ _ _ _ (DErr (RSize)) (DSubtermSize ctx l ps ids i pr cur ctx1 pc pids lv sl ep n)))
                                              ((OneYes p)
                                                (match many (type-of ctx1 p) _
                                                  ((TypeOfStuck a5 b5) (DecreaseStuck _ _ _ _ _))
                                                  ((TypeIs a5 b5 pty kp t kq)
                                                    (match many (canonical f ctx1 pty) _
                                                      ((CanonicalStuck a6 b6) (DecreaseStuck _ _ _ _ _))
                                                      ((CanonicalIs a6 b6 c cn)
                                                        (match many (subterm-dec f ctx1 c (Ref xi) bb) _
                                                          ((STStuck a7 b7 c7 d7) (DecreaseStuck _ _ _ _ _))
                                                          ((STNo a7 b7 c7 d7 ns) (MkDecreaseDec _ _ _ _ _ (DErr (RBadProof)) (DSubtermBad ctx l ps ids i pr cur j xi cargs subargs bb ctx1 pc p pty c lv sl mi ni mk sa sp ep t cn ns)))
                                                          ((STYes a7 b7 c7 d7 hh ta a0 tb b0 sh sa0 sb0)
                                                            (MkDecreaseDec _ _ _ _ _ (DOk ctx1) (DSubterm ctx l ps ids i pr cur j xi cargs subargs bb ctx1 pc p pty hh ta a0 tb b0 lv sl mi ni mk sa sp ep t cn sh sa0 sb0)))))))))))))))))))))))))))))))
  (many check-rets : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (List (Maybe (Term))) acc) (many (List (Entry)) rets) (many (List (Nat)) ids) -> (many (RetsDec ctx acc rets ids) r)
    (match many fuel _
      ((Zero) (RetsStuck _ _ _ _))
      ((Succ f)
        (match many (len-dec _ _ rets ids) _
          ((LenDiff a b c d m) (MkRetsDec _ _ _ _ (RErr (RSize)) (CRSize ctx acc rets ids m)))
          ((LenSame a b c d)
            (match many rets _
              ((Nil e) (match many ids _ ((Nil g) (MkRetsDec _ _ _ _ (ROk) (CRNil ctx acc))) ((Cons g x y) (RetsStuck _ _ _ _))))
              ((Cons e entry es)
                (match many ids _
                  ((Nil g) (RetsStuck _ _ _ _))
                  ((Cons g x rest)
                    (match many entry _
                      ((MkEntry s i t)
                        (match many (subst f acc t) _
                          ((SubstStuck h k) (RetsStuck _ _ _ _))
                          ((MkSubsted h k t2 sb)
                            (match many i _
                              ((BFalse)
                                (match many (type-of ctx x) _
                                  ((TypeOfStuck h2 k2) (RetsStuck _ _ _ _))
                                  ((TypeIs h2 k2 xty kx ty kq)
                                    (match many (same-dec f ctx xty t2) _
                                      ((SDStuck h3 k3 l3) (RetsStuck _ _ _ _))
                                      ((SDDiffer h3 k3 l3 d2) (MkRetsDec _ _ _ _ (RErr (RMismatch)) (CRTyMismatch ctx acc s t es x rest xty t2 ty sb d2)))
                                      ((SDSame h3 k3 l3 sm)
                                        (match many (check-rets f ctx (Cons _ (Some _ (Ref x)) acc) es rest) _
                                          ((RetsStuck h4 k4 l4 m4) (RetsStuck _ _ _ _))
                                          ((MkRetsDec h4 k4 l4 m4 out q) (MkRetsDec _ _ _ _ out (CRTy ctx acc s t es x rest xty t2 out ty sb sm q)))))))))
                              ((BTrue)
                                (match many (same-dec f ctx (Ref x) t2) _
                                  ((SDStuck h3 k3 l3) (RetsStuck _ _ _ _))
                                  ((SDDiffer h3 k3 l3 d2) (MkRetsDec _ _ _ _ (RErr (RMismatch)) (CRIsMismatch ctx acc s t es x rest t2 sb d2)))
                                  ((SDSame h3 k3 l3 sm)
                                    (match many (check-rets f ctx (Cons _ (Some _ (Ref x)) acc) es rest) _
                                      ((RetsStuck h4 k4 l4 m4) (RetsStuck _ _ _ _))
                                      ((MkRetsDec h4 k4 l4 m4 out q) (MkRetsDec _ _ _ _ out (CRIs ctx acc s t es x rest t2 out sb sm q)))))))))))))))))))))
  (many elab-branches : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Nat) s) (many (Nat) tc) (many (List (Nat)) ctors) (many (List (Nat)) seen) (many (List (Entry)) rt) (many (List (Raw)) brs) ->
      (many (BranchesDec ctx s tc ctors seen rt brs) r)
    (match many fuel _
      ((Zero) (BranchesStuck _ _ _ _ _ _ _))
      ((Succ f)
        (match many brs _
          ((Nil a) (MkBranchesDec _ _ _ _ _ _ _ (BrOk ctx (Nil _) seen) (EBNil ctx s tc ctors seen rt)))
          ((Cons a br rest)
            (match many br _
              ((RList bitems)
                (match many bitems _
                  ((Cons b pat items)
                    (match many pat _
                      ((RList pitems)
                        (match many pitems _
                          ((Cons c cr fnames)
                            (match many cr _
                              ((RAtom cs) (elab-branch f ctx s tc ctors seen rt cs fnames items rest))
                              (else (BranchesStuck _ _ _ _ _ _ _))))
                          (else (BranchesStuck _ _ _ _ _ _ _))))
                      (else (BranchesStuck _ _ _ _ _ _ _))))
                  (else (BranchesStuck _ _ _ _ _ _ _))))
              (else (BranchesStuck _ _ _ _ _ _ _))))))))
  (many elab-branch : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Nat) s) (many (Nat) tc) (many (List (Nat)) ctors) (many (List (Nat)) seen) (many (List (Entry)) rt)
      (many (String) cs) (many (List (Raw)) fnames) (many (List (Raw)) items) (many (List (Raw)) rest) ->
      (many (BranchesDec ctx s tc ctors seen rt (Cons (Raw) (RList (Cons (Raw) (RList (Cons (Raw) (RAtom cs) fnames)) items)) rest)) r)
    (match many fuel _
      ((Zero) (BranchesStuck _ _ _ _ _ _ _))
      ((Succ f)
        (let (many scope) (erased sc) (ctx-scope ctx))
        (match many (name-dec scope cs) _
          ((NameMiss a b n) (MkBranchesDec _ _ _ _ _ _ _ (BrErr (RUnbound)) (EBUnbound ctx s tc ctors seen rt cs fnames items rest scope sc n)))
          ((NameHit a b c n)
            (match many (mem-dec c ctors) _
              ((MemNo d e nm) (MkBranchesDec _ _ _ _ _ _ _ (BrErr (RNotCtor)) (EBNotCtor ctx s tc ctors seen rt cs fnames items rest scope c sc n nm)))
              ((MemYes d e mc)
                (match many (mem-dec c seen) _
                  ((MemYes g h ms) (MkBranchesDec _ _ _ _ _ _ _ (BrErr (RDuplicateBranch)) (EBDuplicate ctx s tc ctors seen rt cs fnames items rest scope c sc n mc ms)))
                  ((MemNo g h ns)
                    (match many (type-of ctx c) _
                      ((TypeOfStuck k l) (BranchesStuck _ _ _ _ _ _ _))
                      ((TypeIs k l cty kc t kq)
                        (match many (canonical f ctx cty) _
                          ((CanonicalStuck m o) (BranchesStuck _ _ _ _ _ _ _))
                          ((CanonicalIs m o cc cn)
                            (match many cc _
                              ((ValCtor fs ret)
                                (match many (atom-names fnames) _
                                  ((AtomNamesStuck a1) (BranchesStuck _ _ _ _ _ _ _))
                                  ((MkAtomNames a1 names an)
                                    (match many (mint-tele f ctx (Nil _) fs names) _
                                      ((MTStuck a2 b2 c2 d2) (BranchesStuck _ _ _ _ _ _ _))
                                      ((MTMinted a2 b2 c2 d2 ctxF fids mt)
                                        (let (many frefs) (erased rf) (refs fids))
                                        (let (many sub) (erased so) (somes frefs))
                                        (match many (subst f sub ret) _
                                          ((SubstStuck a3 b3) (BranchesStuck _ _ _ _ _ _ _))
                                          ((MkSubsted a3 b3 ret2 sb)
                                            (match many (type-of ctx s) _
                                              ((TypeOfStuck a4 b4) (BranchesStuck _ _ _ _ _ _ _))
                                              ((TypeIs a4 b4 sty ks st kq2)
                                                (match many (refine-dec f ctxF (Cons _ (MkEqn (Ref s) (App (Ref c) frefs)) (Cons _ (MkEqn sty ret2) (Nil _)))) _
                                                  ((RDStuck a5 b5) (BranchesStuck _ _ _ _ _ _ _))
                                                  ((RDContradicted a5 b5 cd)
                                                    (MkBranchesDec _ _ _ _ _ _ _ (BrErr (RRefutedBranch)) (EBRefuted ctx s tc ctors seen rt cs fnames items rest scope c cty fs ret names ctxF fids frefs sub ret2 sty sc n mc ns t cn an mt rf so sb st cd)))
                                                  ((RDRefined a5 b5 ctxR rf2)
                                                    (match many (elab-body f ctxR items) _
                                                      ((BodyStuck a6 b6) (BranchesStuck _ _ _ _ _ _ _))
                                                      ((MkBodyDec a6 b6 bout eb)
                                                        (match many bout _
                                                          ((EErr r) (MkBranchesDec _ _ _ _ _ _ _ (BrErr r) (EBBodyErr ctx s tc ctors seen rt cs fnames items rest scope c cty fs ret names ctxF fids frefs sub ret2 sty ctxR r sc n mc ns t cn an mt rf so sb st rf2 eb)))
                                                          ((EOk ctxB core ids)
                                                            (match many (check-rets f ctxB (Nil _) rt ids) _
                                                              ((RetsStuck a7 b7 c7 d7) (BranchesStuck _ _ _ _ _ _ _))
                                                              ((MkRetsDec a7 b7 c7 d7 rout cr)
                                                                (match many rout _
                                                                  ((RErr r) (MkBranchesDec _ _ _ _ _ _ _ (BrErr r) (EBRetsErr ctx s tc ctors seen rt cs fnames items rest scope c cty fs ret names ctxF fids frefs sub ret2 sty ctxR ctxB core ids r sc n mc ns t cn an mt rf so sb st rf2 eb cr)))
                                                                  ((ROk)
                                                                    (let (many ctx1) (erased lv) (leave ctxB ctx))
                                                                    (match many (elab-branches f ctx1 s tc ctors (Cons _ c seen) rt rest) _
                                                                      ((BranchesStuck a8 b8 c8 d8 e8 g8 h8) (BranchesStuck _ _ _ _ _ _ _))
                                                                      ((MkBranchesDec a8 b8 c8 d8 e8 g8 h8 bsout q)
                                                                        (match many bsout _
                                                                          ((BrErr r) (MkBranchesDec _ _ _ _ _ _ _ (BrErr r) (EBRestErr ctx s tc ctors seen rt cs fnames items rest scope c cty fs ret names ctxF fids frefs sub ret2 sty ctxR ctxB core ids ctx1 r sc n mc ns t cn an mt rf so sb st rf2 eb cr lv q)))
                                                                          ((BrOk out cbs seen2)
                                                                            (MkBranchesDec _ _ _ _ _ _ _ (BrOk out (Cons _ (MkBranch c fids core) cbs) seen2) (EBCons ctx s tc ctors seen rt cs fnames items rest scope c cty fs ret names ctxF fids frefs sub ret2 sty ctxR ctxB core ids ctx1 out cbs seen2 sc n mc ns t cn an mt rf so sb st rf2 eb cr lv q)))))))))))))))))))))))))
                              (else (BranchesStuck _ _ _ _ _ _ _))))))))))))))))
  (many covered : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Nat) s) (many (List (Nat)) ctors) (many (List (Nat)) seen) -> (many (CoveredDec ctx s ctors seen) r)
    (match many fuel _
      ((Zero) (CovStuck _ _ _ _))
      ((Succ f)
        (match many ctors _
          ((Nil a) (CovYes _ _ _ _ (CvNil ctx s seen)))
          ((Cons a c rest)
            (match many (mem-dec c seen) _
              ((MemYes b d m)
                (match many (covered f ctx s rest seen) _
                  ((CovStuck e g h k) (CovStuck _ _ _ _))
                  ((CovYes e g h k p) (CovYes _ _ _ _ (CvSeen ctx s c rest seen m p)))
                  ((CovNo e g h k p) (CovNo _ _ _ _ (UcThere ctx s c rest seen p)))))
              ((MemNo b d nm)
                (match many (refuted f ctx s c) _
                  ((RefStuck e g h) (CovStuck _ _ _ _))
                  ((RefNo e g h rc) (CovNo _ _ _ _ (UcHere ctx s c rest seen nm rc)))
                  ((RefYes e g h rf)
                    (match many (covered f ctx s rest seen) _
                      ((CovStuck e2 g2 h2 k2) (CovStuck _ _ _ _))
                      ((CovYes e2 g2 h2 k2 p) (CovYes _ _ _ _ (CvRefuted ctx s c rest seen nm rf p)))
                      ((CovNo e2 g2 h2 k2 p) (CovNo _ _ _ _ (UcThere ctx s c rest seen p)))))))))))))
  (many refuted : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Nat) s) (many (Nat) c) -> (many (RefutedDec ctx s c) r)
    (match many fuel _
      ((Zero) (RefStuck _ _ _))
      ((Succ f)
        (match many (type-of ctx c) _
          ((TypeOfStuck k l) (RefStuck _ _ _))
          ((TypeIs k l cty kc t kq)
            (match many (canonical f ctx cty) _
              ((CanonicalStuck m o) (RefStuck _ _ _))
              ((CanonicalIs m o cc cn)
                (match many cc _
                  ((ValCtor fs ret)
                    (let (many names) (erased nn) (nones fs))
                    (match many (mint-tele f ctx (Nil _) fs names) _
                      ((MTStuck a2 b2 c2 d2) (RefStuck _ _ _))
                      ((MTMinted a2 b2 c2 d2 ctxF fids mt)
                        (let (many frefs) (erased rf) (refs fids))
                        (let (many sub) (erased so) (somes frefs))
                        (match many (subst f sub ret) _
                          ((SubstStuck a3 b3) (RefStuck _ _ _))
                          ((MkSubsted a3 b3 ret2 sb)
                            (match many (type-of ctx s) _
                              ((TypeOfStuck a4 b4) (RefStuck _ _ _))
                              ((TypeIs a4 b4 sty ks st kq2)
                                (match many (refine-dec f ctxF (Cons _ (MkEqn (Ref s) (App (Ref c) frefs)) (Cons _ (MkEqn sty ret2) (Nil _)))) _
                                  ((RDStuck a5 b5) (RefStuck _ _ _))
                                  ((RDContradicted a5 b5 cd) (RefYes _ _ _ (RefutedBy ctx s c cty fs ret names ctxF fids frefs sub ret2 sty t cn nn mt rf so sb st cd)))
                                  ((RDRefined a5 b5 ctxR rf2) (RefNo _ _ _ (ReachableBy ctx s c cty fs ret names ctxF fids frefs sub ret2 sty ctxR t cn nn mt rf so sb st rf2)))))))))))
                  (else (RefStuck _ _ _))))))))))
  (many elab-body : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (List (Raw)) items) -> (many (BodyDec ctx items) r)
    (match many fuel _
      ((Zero) (BodyStuck _ _))
      ((Succ f)
        (match many items _
          ((Nil a) (BodyStuck _ _))
          ((Cons a first rest)
            (match many rest _
              ((Nil b)
                (match many (elab-expr f ctx first) _
                  ((ExprStuck c d) (BodyStuck _ _))
                  ((MkExprDec c d out p) (MkBodyDec _ _ out (BodyFinal ctx first out p)))))
              ((Cons b second more)
                (match many (elab-stmt f ctx first) _
                  ((StmtStuck c d) (BodyStuck _ _))
                  ((MkStmtDec c d sout p)
                    (match many sout _
                      ((SErr e) (MkBodyDec _ _ (EErr e) (BodyStmtErr ctx first second more e p)))
                      ((SOk ctx1 st)
                        (match many (elab-body f ctx1 (Cons _ second more)) _
                          ((BodyStuck c2 d2) (BodyStuck _ _))
                          ((MkBodyDec c2 d2 bout q)
                            (match many bout _
                              ((EErr e) (MkBodyDec _ _ (EErr e) (BodyRestErr ctx first second more ctx1 st e p q)))
                              ((EOk out core ids) (MkBodyDec _ _ (EOk out (CStmt st core) ids) (BodyStmt ctx first second more ctx1 st out core ids p q)))))))))))))))))
  (many elab-stmt : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Raw) raw) -> (many (StmtDec ctx raw) r)
    (match many fuel _
      ((Zero) (StmtStuck _ _))
      ((Succ f)
        (match many raw _
          ((RList items)
            (match many items _
              ((Cons a h rest)
                (match many h _
                  ((RKey k)
                    (match many k _
                      ((KLet)
                        (match many rest _
                          ((Cons b br body)
                            (match many br _
                              ((RList binders) (elab-let f ctx binders body))
                              (else (StmtStuck _ _))))
                          (else (StmtStuck _ _))))
                      ((KDefLvl)
                        (match many rest _
                          ((Cons b lr rest2)
                            (match many rest2 _
                              ((Nil c)
                                (match many lr _
                                  ((RAtom ls)
                                    (let (many x) (many out) (erased m) (mint ctx (Some _ ls) (App (Ref (Zero)) (Nil _)) (KLevel) (None _)))
                                    (MkStmtDec _ _ (SOk out (SDefLvl x)) (STDefLvl ctx ls x out m)))
                                  (else (StmtStuck _ _))))
                              (else (StmtStuck _ _))))
                          (else (StmtStuck _ _))))
                      ((KDefFns)
                        (match many rest _
                          ((Cons b lr defs) (elab-def-fns f ctx lr defs))
                          (else (StmtStuck _ _))))
                      ((KDefAdts) (elab-def-adts f ctx rest))
                      (else (StmtStuck _ _))))
                  (else (StmtStuck _ _))))
              (else (StmtStuck _ _))))
          (else (StmtStuck _ _))))))
  (many elab-let : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (List (Raw)) binders) (many (List (Raw)) items) -> (many (StmtDec ctx (RList (Cons (Raw) (RKey (KLet)) (Cons (Raw) (RList binders) items)))) r)
    (match many fuel _
      ((Zero) (StmtStuck _ _))
      ((Succ f)
        (match many (elab-body f ctx items) _
          ((BodyStuck a b) (StmtStuck _ _))
          ((MkBodyDec a b bout p)
            (match many bout _
              ((EErr r) (MkStmtDec _ _ (SErr r) (STLetErr ctx binders items r p)))
              ((EOk ctx1 core ids)
                (let (many scope) (erased sc) (ctx-scope ctx))
                (let (many ctxH) (erased h) (hide ctx1 scope))
                (match many (bind-let f ctxH binders ids) _
                  ((BindLetStuck c d e) (StmtStuck _ _))
                  ((MkBindLetDec c d e lout bl)
                    (match many lout _
                      ((AErr r) (MkStmtDec _ _ (SErr r) (STLetBindErr ctx binders items ctx1 core ids scope ctxH r p sc h bl)))
                      ((AOk out cores aids)
                        (match many cores _
                          ((Nil g) (MkStmtDec _ _ (SOk out (SLet aids core)) (STLet ctx binders items ctx1 core ids scope ctxH out aids p sc h bl)))
                          ((Cons g x y) (StmtStuck _ _))))))))))))))
  (many bind-let : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (List (Raw)) binders) (many (List (Nat)) ids) -> (many (BindLetDec ctx binders ids) r)
    (match many fuel _
      ((Zero) (BindLetStuck _ _ _))
      ((Succ f)
        (match many (len-dec _ _ binders ids) _
          ((LenDiff a b c d m) (MkBindLetDec _ _ _ (AErr (RSize)) (BLSize ctx binders ids m)))
          ((LenSame a b c d)
            (match many binders _
              ((Nil e) (match many ids _ ((Nil g) (MkBindLetDec _ _ _ (AOk ctx (Nil _) (Nil _)) (BLNil ctx))) ((Cons g x y) (BindLetStuck _ _ _))))
              ((Cons e b brest)
                (match many ids _
                  ((Nil g) (BindLetStuck _ _ _))
                  ((Cons g id irest)
                    (match many b _
                      ((RAtom x)
                        (match many (type-of ctx id) _
                          ((TypeOfStuck h k) (BindLetStuck _ _ _))
                          ((TypeIs h k ty kt t kq)
                            (let (many aid) (many ctx1) (erased m) (mint ctx (Some _ x) ty (KPlain) (Some _ (Ref id))))
                            (match many (bind-let f ctx1 brest irest) _
                              ((BindLetStuck h2 k2 l2) (BindLetStuck _ _ _))
                              ((MkBindLetDec h2 k2 l2 rout q)
                                (match many rout _
                                  ((AErr r) (MkBindLetDec _ _ _ (AErr r) (BLRestErr ctx (RAtom x) brest id irest x ty aid ctx1 r (BNAtom x) t m q)))
                                  ((AOk out cores aids)
                                    (match many cores _
                                      ((Nil h3) (MkBindLetDec _ _ _ (AOk out (Nil _) (Cons _ aid aids)) (BLName ctx x brest id irest ty aid ctx1 out aids t m q)))
                                      ((Cons h3 x2 y2) (BindLetStuck _ _ _))))))))))
                      (else
                        (match many (entry-dec b) _
                          ((EntryNot h) (BindLetStuck _ _ _))
                          ((EntryShape h s i tr x shape)
                            (match many s _
                              ((BTrue) (BindLetStuck _ _ _))
                              ((BFalse)
                                (match many (elab-term f ctx tr) _
                                  ((TermStuck k l) (BindLetStuck _ _ _))
                                  ((MkTermDec k l tout et)
                                    (match many tout _
                                      ((TErr r) (MkBindLetDec _ _ _ (AErr r) (BLTermErr ctx b i tr x brest id irest r shape et)))
                                      ((TOk t tty)
                                        (match many (type-of ctx id) _
                                          ((TypeOfStuck k2 l2) (BindLetStuck _ _ _))
                                          ((TypeIs k2 l2 ty kt ty1 kq)
                                            (match many i _
                                              ((BFalse)
                                                (match many (same-dec f ctx ty t) _
                                                  ((SDStuck k3 l3 m3) (BindLetStuck _ _ _))
                                                  ((SDDiffer k3 l3 m3 d2) (MkBindLetDec _ _ _ (AErr (RMismatch)) (BLTyMismatch ctx b tr x brest id irest t tty ty shape et ty1 d2)))
                                                  ((SDSame k3 l3 m3 sm)
                                                    (let (many aid) (many ctx1) (erased m) (mint ctx (Some _ x) ty (KPlain) (Some _ (Ref id))))
                                                    (match many (bind-let f ctx1 brest irest) _
                                                      ((BindLetStuck h2 k4 l4) (BindLetStuck _ _ _))
                                                      ((MkBindLetDec h2 k4 l4 rout q)
                                                        (match many rout _
                                                          ((AErr r) (MkBindLetDec _ _ _ (AErr r) (BLRestErr ctx b brest id irest x ty aid ctx1 r (BNEntry b (BFalse) tr x shape) ty1 m q)))
                                                          ((AOk out cores aids)
                                                            (match many cores _
                                                              ((Nil h3) (MkBindLetDec _ _ _ (AOk out (Nil _) (Cons _ aid aids)) (BLTy ctx b tr x brest id irest t tty ty aid ctx1 out aids shape et ty1 sm m q)))
                                                              ((Cons h3 x2 y2) (BindLetStuck _ _ _))))))))))
                                              ((BTrue)
                                                (match many (same-dec f ctx (Ref id) t) _
                                                  ((SDStuck k3 l3 m3) (BindLetStuck _ _ _))
                                                  ((SDDiffer k3 l3 m3 d2) (MkBindLetDec _ _ _ (AErr (RMismatch)) (BLIsMismatch ctx b tr x brest id irest t tty shape et d2)))
                                                  ((SDSame k3 l3 m3 sm)
                                                    (let (many aid) (many ctx1) (erased m) (mint ctx (Some _ x) ty (KPlain) (Some _ (Ref id))))
                                                    (match many (bind-let f ctx1 brest irest) _
                                                      ((BindLetStuck h2 k4 l4) (BindLetStuck _ _ _))
                                                      ((MkBindLetDec h2 k4 l4 rout q)
                                                        (match many rout _
                                                          ((AErr r) (MkBindLetDec _ _ _ (AErr r) (BLRestErr ctx b brest id irest x ty aid ctx1 r (BNEntry b (BTrue) tr x shape) ty1 m q)))
                                                          ((AOk out cores aids)
                                                            (match many cores _
                                                              ((Nil h3) (MkBindLetDec _ _ _ (AOk out (Nil _) (Cons _ aid aids)) (BLIs ctx b tr x brest id irest t tty ty aid ctx1 out aids shape et ty1 sm m q)))
                                                              ((Cons h3 x2 y2) (BindLetStuck _ _ _))))))))))))))))))))))))))))))))
  (many elab-def-fns : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Raw) lr) (many (List (Raw)) defs) -> (many (StmtDec ctx (RList (Cons (Raw) (RKey (KDefFns)) (Cons (Raw) lr defs)))) r)
    (match many fuel _
      ((Zero) (StmtStuck _ _))
      ((Succ f)
        (match many (elab-term f ctx lr) _
          ((TermStuck a b) (StmtStuck _ _))
          ((MkTermDec a b lout p)
            (match many lout _
              ((TErr r) (MkStmtDec _ _ (SErr r) (STDefFnsLevelErr ctx lr defs r p)))
              ((TOk l lty)
                (match many (same-dec f ctx lty (App (Ref (Zero)) (Nil _))) _
                  ((SDStuck c d e) (StmtStuck _ _))
                  ((SDDiffer c d e df) (MkStmtDec _ _ (SErr (RNotLevel)) (STDefFnsNotLevel ctx lr defs l lty p df)))
                  ((SDSame c d e sl)
                    (match many (mint-fns f ctx l defs) _
                      ((FnsStuck c2 d2 e2) (StmtStuck _ _))
                      ((MkFnsDec c2 d2 e2 fout mf)
                        (match many fout _
                          ((FErr r) (MkStmtDec _ _ (SErr r) (STDefFnsSigErr ctx lr defs l lty r p sl mf)))
                          ((FOk ctx1 sigs)
                            (match many (elab-bodies f ctx1 l sigs defs) _
                              ((BodiesStuck c3 d3 e3 g3) (StmtStuck _ _))
                              ((MkBodiesDec c3 d3 e3 g3 bout eb)
                                (match many bout _
                                  ((BsErr r) (MkStmtDec _ _ (SErr r) (STDefFnsBodyErr ctx lr defs l lty ctx1 sigs r p sl mf eb)))
                                  ((BsOk out fds) (MkStmtDec _ _ (SOk out (SDefFns fds)) (STDefFns ctx lr defs l lty ctx1 sigs out fds p sl mf eb)))))))))))))))))))
  (many mint-fns : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Term) l) (many (List (Raw)) defs) -> (many (FnsDec ctx l defs) r)
    (match many fuel _
      ((Zero) (FnsStuck _ _ _))
      ((Succ f)
        (match many defs _
          ((Nil a) (MkFnsDec _ _ _ (FOk ctx (Nil _)) (MFNil ctx l)))
          ((Cons a def rest)
            (match many def _
              ((RList ditems)
                (match many ditems _
                  ((Cons b fr d1)
                    (match many d1 _
                      ((Cons c pr d2)
                        (match many d2 _
                          ((Cons d rr items)
                            (match many fr _
                              ((RAtom fn)
                                (match many pr _
                                  ((RList ps)
                                    (match many rr _
                                      ((RList rs) (mint-fn f ctx l fn ps rs items rest))
                                      (else (FnsStuck _ _ _))))
                                  (else (FnsStuck _ _ _))))
                              (else (FnsStuck _ _ _))))
                          (else (FnsStuck _ _ _))))
                      (else (FnsStuck _ _ _))))
                  (else (FnsStuck _ _ _))))
              (else (FnsStuck _ _ _))))))))
  (many mint-fn : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Term) l) (many (String) fn) (many (List (Raw)) ps) (many (List (Raw)) rs) (many (List (Raw)) items) (many (List (Raw)) rest) ->
      (many (FnsDec ctx l (Cons (Raw) (RList (Cons (Raw) (RAtom fn) (Cons (Raw) (RList ps) (Cons (Raw) (RList rs) items)))) rest)) r)
    (match many fuel _
      ((Zero) (FnsStuck _ _ _))
      ((Succ f)
        (match many (elab-tele f ctx (Nil _) ps) _
          ((TeleStuck a b c) (FnsStuck _ _ _))
          ((MkTeleDec a b c pout ep)
            (match many pout _
              ((TeleErr r) (MkFnsDec _ _ _ (FErr r) (MFParamsErr ctx l fn ps rs items rest r ep)))
              ((TeleOk ctxP pt pids pn)
                (let (many acc) (erased bd) (binders pids))
                (match many (elab-tele f ctxP acc rs) _
                  ((TeleStuck a2 b2 c2) (FnsStuck _ _ _))
                  ((MkTeleDec a2 b2 c2 rout er)
                    (match many rout _
                      ((TeleErr r) (MkFnsDec _ _ _ (FErr r) (MFRetsErr ctx l fn ps rs items rest ctxP pt pids pn acc r ep bd er)))
                      ((TeleOk ctxR rt rids rn)
                        (let (many fid) (many ctx1) (erased m) (mint ctx (Some _ fn) (Fn l pt rt) (KPlain) (None _)))
                        (match many (mint-fns f ctx1 l rest) _
                          ((FnsStuck a3 b3 c3) (FnsStuck _ _ _))
                          ((MkFnsDec a3 b3 c3 fout q)
                            (match many fout _
                              ((FErr r) (MkFnsDec _ _ _ (FErr r) (MFRestErr ctx l fn ps rs items rest ctxP pt pids pn acc ctxR rt rids rn fid ctx1 r ep bd er m q)))
                              ((FOk out sigs) (MkFnsDec _ _ _ (FOk out (Cons _ (MkSig fid pt pn rt) sigs)) (MFCons ctx l fn ps rs items rest ctxP pt pids pn acc ctxR rt rids rn fid ctx1 out sigs ep bd er m q)))))))))))))))))
  (many elab-bodies : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Term) l) (many (List (Sig)) sigs) (many (List (Raw)) defs) -> (many (BodiesDec ctx l sigs defs) r)
    (match many fuel _
      ((Zero) (BodiesStuck _ _ _ _))
      ((Succ f)
        (match many sigs _
          ((Nil a) (match many defs _ ((Nil b) (MkBodiesDec _ _ _ _ (BsOk ctx (Nil _)) (BdNil ctx l))) ((Cons b x y) (BodiesStuck _ _ _ _))))
          ((Cons a sig srest)
            (match many defs _
              ((Nil b) (BodiesStuck _ _ _ _))
              ((Cons b def rest)
                (match many sig _
                  ((MkSig fid pt pn rt)
                    (match many def _
                      ((RList ditems)
                        (match many ditems _
                          ((Cons c fr d1)
                            (match many d1 _
                              ((Cons d pr d2)
                                (match many d2 _
                                  ((Cons e rr items)
                                    (match many fr _
                                      ((RAtom fn)
                                        (match many pr _
                                          ((RList ps)
                                            (match many rr _
                                              ((RList rs) (elab-fn-body f ctx l fid pt pn rt srest fn ps rs items rest))
                                              (else (BodiesStuck _ _ _ _))))
                                          (else (BodiesStuck _ _ _ _))))
                                      (else (BodiesStuck _ _ _ _))))
                                  (else (BodiesStuck _ _ _ _))))
                              (else (BodiesStuck _ _ _ _))))
                          (else (BodiesStuck _ _ _ _))))
                      (else (BodiesStuck _ _ _ _))))))))))))
  (many elab-fn-body : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Term) l) (many (Nat) fid) (many (List (Entry)) pt) (many (List (Maybe (String))) pn) (many (List (Entry)) rt) (many (List (Sig)) sigs)
      (many (String) fn) (many (List (Raw)) ps) (many (List (Raw)) rs) (many (List (Raw)) items) (many (List (Raw)) rest) ->
      (many (BodiesDec ctx l (Cons (Sig) (MkSig fid pt pn rt) sigs) (Cons (Raw) (RList (Cons (Raw) (RAtom fn) (Cons (Raw) (RList ps) (Cons (Raw) (RList rs) items)))) rest)) r)
    (match many fuel _
      ((Zero) (BodiesStuck _ _ _ _))
      ((Succ f)
        (match many (mint-tele f ctx (Nil _) pt pn) _
          ((MTStuck a b c d) (BodiesStuck _ _ _ _))
          ((MTMinted a b c d ctxP pids m)
            (match many (marked pt pids) _
              ((MarkedStuck e g) (BodiesStuck _ _ _ _))
              ((MkMarked e g subargs mk)
                (let (many ctxE) (erased en) (enter ctxP l subargs))
                (match many (elab-body f ctxE items) _
                  ((BodyStuck h k) (BodiesStuck _ _ _ _))
                  ((MkBodyDec h k bout eb)
                    (match many bout _
                      ((EErr r) (MkBodiesDec _ _ _ _ (BsErr r) (BdBodyErr ctx l fid pt pn rt sigs fn ps rs items rest ctxP pids subargs ctxE r m mk en eb)))
                      ((EOk ctxB core ids)
                        (let (many prefs) (erased rf) (refs pids))
                        (let (many sub) (erased so) (somes prefs))
                        (match many (check-rets f ctxB sub rt ids) _
                          ((RetsStuck a2 b2 c2 d2) (BodiesStuck _ _ _ _))
                          ((MkRetsDec a2 b2 c2 d2 rout cr)
                            (match many rout _
                              ((RErr r) (MkBodiesDec _ _ _ _ (BsErr r) (BdRetsErr ctx l fid pt pn rt sigs fn ps rs items rest ctxP pids subargs ctxE ctxB core ids prefs sub r m mk en eb rf so cr)))
                              ((ROk)
                                (let (many ctx1) (erased lv) (leave ctxB ctx))
                                (match many (elab-bodies f ctx1 l sigs rest) _
                                  ((BodiesStuck a3 b3 c3 d3) (BodiesStuck _ _ _ _))
                                  ((MkBodiesDec a3 b3 c3 d3 bsout q)
                                    (match many bsout _
                                      ((BsErr r) (MkBodiesDec _ _ _ _ (BsErr r) (BdRestErr ctx l fid pt pn rt sigs fn ps rs items rest ctxP pids subargs ctxE ctxB core ids prefs sub ctx1 r m mk en eb rf so cr lv q)))
                                      ((BsOk out fds) (MkBodiesDec _ _ _ _ (BsOk out (Cons _ (MkFnDef fid pids core) fds)) (BdCons ctx l fid pt pn rt sigs fn ps rs items rest ctxP pids subargs ctxE ctxB core ids prefs sub ctx1 out fds m mk en eb rf so cr lv q)))))))))))))))))))))
  (many elab-def-adts : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (List (Raw)) decls) -> (many (StmtDec ctx (RList (Cons (Raw) (RKey (KDefAdts)) decls))) r)
    (match many fuel _
      ((Zero) (StmtStuck _ _))
      ((Succ f)
        (let (many level) (erased lv) (ctx-level ctx))
        (match many level _
          ((Some a cur) (MkStmtDec _ _ (SErr (RTopLevelOnly)) (STDefAdtsNested ctx decls cur lv)))
          ((None a)
            (match many (mint-tycons f ctx decls) _
              ((TyconsStuck b c) (StmtStuck _ _))
              ((MkTyconsDec b c tout mt)
                (match many tout _
                  ((FErrT r) (MkStmtDec _ _ (SErr r) (STDefAdtsTyconErr ctx decls r lv mt)))
                  ((FOkT ctx1 tids)
                    (match many (mint-ctors f ctx1 decls tids) _
                      ((CtorsStuck d e g) (StmtStuck _ _))
                      ((MkCtorsDec d e g cout mc)
                        (match many cout _
                          ((FErrT r) (MkStmtDec _ _ (SErr r) (STDefAdtsCtorErr ctx decls ctx1 tids r lv mt mc)))
                          ((FOkT out ids) (MkStmtDec _ _ (SOk out (SDefAdts ids)) (STDefAdts ctx decls ctx1 tids out ids lv mt mc)))))))))))))))
  (many mint-tycons : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (List (Raw)) decls) -> (many (TyconsDec ctx decls) r)
    (match many fuel _
      ((Zero) (TyconsStuck _ _))
      ((Succ f)
        (match many decls _
          ((Nil a) (MkTyconsDec _ _ (FOkT ctx (Nil _)) (MTyNil ctx)))
          ((Cons a decl rest)
            (match many decl _
              ((RList ditems)
                (match many ditems _
                  ((Cons b tr d1)
                    (match many d1 _
                      ((Cons c pr ctors)
                        (match many tr _
                          ((RAtom tn)
                            (match many pr _
                              ((RList ps)
                                (match many (elab-tele f ctx (Nil _) ps) _
                                  ((TeleStuck d e g) (TyconsStuck _ _))
                                  ((MkTeleDec d e g pout ep)
                                    (match many pout _
                                      ((TeleErr r) (MkTyconsDec _ _ (FErrT r) (MTyErr ctx tn ps ctors rest r ep)))
                                      ((TeleOk ctxP pt pids pn)
                                        (let (many tid) (many ctx1) (erased m) (mint ctx (Some _ tn) (TyCtor pt) (KDecl) (None _)))
                                        (match many (mint-tycons f ctx1 rest) _
                                          ((TyconsStuck d2 e2) (TyconsStuck _ _))
                                          ((MkTyconsDec d2 e2 rout q)
                                            (match many rout _
                                              ((FErrT r) (MkTyconsDec _ _ (FErrT r) (MTyRestErr ctx tn ps ctors rest ctxP pt pids pn tid ctx1 r ep m q)))
                                              ((FOkT out tids) (MkTyconsDec _ _ (FOkT out (Cons _ tid tids)) (MTyCons ctx tn ps ctors rest ctxP pt pids pn tid ctx1 out tids ep m q)))))))))))
                              (else (TyconsStuck _ _))))
                          (else (TyconsStuck _ _))))
                      (else (TyconsStuck _ _))))
                  (else (TyconsStuck _ _))))
              (else (TyconsStuck _ _))))))))
  (many mint-ctors : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (List (Raw)) decls) (many (List (Nat)) tids) -> (many (CtorsDec ctx decls tids) r)
    (match many fuel _
      ((Zero) (CtorsStuck _ _ _))
      ((Succ f)
        (match many decls _
          ((Nil a) (match many tids _ ((Nil b) (MkCtorsDec _ _ _ (FOkT ctx (Nil _)) (MCNil ctx))) ((Cons b x y) (CtorsStuck _ _ _))))
          ((Cons a decl rest)
            (match many tids _
              ((Nil b) (CtorsStuck _ _ _))
              ((Cons b tid trest)
                (match many decl _
                  ((RList ditems)
                    (match many ditems _
                      ((Cons c tr d1)
                        (match many d1 _
                          ((Cons d pr ctors)
                            (match many tr _
                              ((RAtom tn)
                                (match many pr _
                                  ((RList ps)
                                    (match many (type-of ctx tid) _
                                      ((TypeOfStuck e g) (CtorsStuck _ _ _))
                                      ((TypeIs e g tty kt t kq)
                                        (match many (canonical f ctx tty) _
                                          ((CanonicalStuck h k) (CtorsStuck _ _ _))
                                          ((CanonicalIs h k tc cn)
                                            (match many tc _
                                              ((TyCtor pt)
                                                (let (many n) (erased ln) (list-len _ pt))
                                                (match many (mint-decl-ctors f ctx tid n ctors) _
                                                  ((DeclCtorsStuck a2 b2 c2 d2) (CtorsStuck _ _ _))
                                                  ((MkDeclCtorsDec a2 b2 c2 d2 dout mc)
                                                    (match many dout _
                                                      ((FErrT r) (MkCtorsDec _ _ _ (FErrT r) (MCErr ctx tn ps ctors rest tid trest tty pt n r t cn ln mc)))
                                                      ((FOkT ctx1 cids)
                                                        (let (many ctx2) (erased aa) (add-adt ctx1 (MkAdt tid cids)))
                                                        (match many (mint-ctors f ctx2 rest trest) _
                                                          ((CtorsStuck a3 b3 c3) (CtorsStuck _ _ _))
                                                          ((MkCtorsDec a3 b3 c3 rout q)
                                                            (match many rout _
                                                              ((FErrT r) (MkCtorsDec _ _ _ (FErrT r) (MCRestErr ctx tn ps ctors rest tid trest tty pt n ctx1 cids ctx2 r t cn ln mc aa q)))
                                                              ((FOkT out ids)
                                                                (let (many all) (erased ap) (append (Cons _ tid cids) ids))
                                                                (MkCtorsDec _ _ _ (FOkT out all) (MCCons ctx tn ps ctors rest tid trest tty pt n ctx1 cids ctx2 out ids all t cn ln mc aa q ap)))))))))))
                                              (else (CtorsStuck _ _ _))))))))
                                  (else (CtorsStuck _ _ _))))
                              (else (CtorsStuck _ _ _))))
                          (else (CtorsStuck _ _ _))))
                      (else (CtorsStuck _ _ _))))
                  (else (CtorsStuck _ _ _))))))))))
  (many mint-decl-ctors : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Nat) tid) (many (Nat) n) (many (List (Raw)) ctors) -> (many (DeclCtorsDec ctx tid n ctors) r)
    (match many fuel _
      ((Zero) (DeclCtorsStuck _ _ _ _))
      ((Succ f)
        (match many ctors _
          ((Nil a) (MkDeclCtorsDec _ _ _ _ (FOkT ctx (Nil _)) (MDNil ctx tid n)))
          ((Cons a ctor rest)
            (match many ctor _
              ((RList citems)
                (match many citems _
                  ((Cons b cr d1)
                    (match many d1 _
                      ((Cons c fr d2)
                        (match many d2 _
                          ((Cons d rr d3)
                            (match many d3 _
                              ((Nil e)
                                (match many cr _
                                  ((RAtom cn)
                                    (match many fr _
                                      ((RList fs) (mint-decl-ctor f ctx tid n cn fs rr rest))
                                      (else (DeclCtorsStuck _ _ _ _))))
                                  (else (DeclCtorsStuck _ _ _ _))))
                              (else (DeclCtorsStuck _ _ _ _))))
                          (else (DeclCtorsStuck _ _ _ _))))
                      (else (DeclCtorsStuck _ _ _ _))))
                  (else (DeclCtorsStuck _ _ _ _))))
              (else (DeclCtorsStuck _ _ _ _))))))))
  (many mint-decl-ctor : (subterm many (Nat) fuel) (many (Ctx) ctx) (many (Nat) tid) (many (Nat) n) (many (String) cn) (many (List (Raw)) fs) (many (Raw) rr) (many (List (Raw)) rest) ->
      (many (DeclCtorsDec ctx tid n (Cons (Raw) (RList (Cons (Raw) (RAtom cn) (Cons (Raw) (RList fs) (Cons (Raw) rr (Nil (Raw)))))) rest)) r)
    (match many fuel _
      ((Zero) (DeclCtorsStuck _ _ _ _))
      ((Succ f)
        (match many (elab-tele f ctx (Nil _) fs) _
          ((TeleStuck a b c) (DeclCtorsStuck _ _ _ _))
          ((MkTeleDec a b c fout ef)
            (match many fout _
              ((TeleErr r) (MkDeclCtorsDec _ _ _ _ (FErrT r) (MDFieldsErr ctx tid n cn fs rr rest r ef)))
              ((TeleOk ctxF ft fids fn)
                (match many (elab-term f ctxF rr) _
                  ((TermStuck d e) (DeclCtorsStuck _ _ _ _))
                  ((MkTermDec d e rout er)
                    (match many rout _
                      ((TErr r) (MkDeclCtorsDec _ _ _ _ (FErrT r) (MDRetErr ctx tid n cn fs rr rest ctxF ft fids fn r ef er)))
                      ((TOk ret rty)
                        (match many (canonical f ctxF ret) _
                          ((CanonicalStuck g h) (DeclCtorsStuck _ _ _ _))
                          ((CanonicalIs g h c cr)
                            (match many (ret-dec f ctxF tid n c) _
                              ((RetStuck a1 b1 c1 d1) (DeclCtorsStuck _ _ _ _))
                              ((RetNo a1 b1 c1 d1 br) (MkDeclCtorsDec _ _ _ _ (FErrT (RBadReturn)) (MDBadRet ctx tid n cn fs rr rest ctxF ft fids fn ret rty c ef er cr br)))
                              ((RetYes a1 b1 c1 args ln)
                                (let (many acc) (erased bd) (binders fids))
                                (match many (abstract f acc ret) _
                                  ((AbstractStuck a2 b2) (DeclCtorsStuck _ _ _ _))
                                  ((MkAbstracted a2 b2 ret2 ab)
                                    (let (many cid) (many ctx1) (erased m) (mint ctx (Some _ cn) (ValCtor ft ret2) (KDecl) (None _)))
                                    (match many (mint-decl-ctors f ctx1 tid n rest) _
                                      ((DeclCtorsStuck a3 b3 c3 d3) (DeclCtorsStuck _ _ _ _))
                                      ((MkDeclCtorsDec a3 b3 c3 d3 dout q)
                                        (match many dout _
                                          ((FErrT r) (MkDeclCtorsDec _ _ _ _ (FErrT r) (MDRestErr ctx tid n cn fs rr rest ctxF ft fids fn ret rty args acc ret2 cid ctx1 r ef er cr ln bd ab m q)))
                                          ((FOkT out cids) (MkDeclCtorsDec _ _ _ _ (FOkT out (Cons _ cid cids)) (MDCons ctx tid n cn fs rr rest ctxF ft fids fn ret rty args acc ret2 cid ctx1 out cids ef er cr ln bd ab m q))))))))))))))))))))))))

; ---- A program.
(def-adts
  (ProgramDec : ((List (Raw)) items) -> Type
    enum
    (many MkProgramDec : (erased (List (Raw)) items) (many (POut) out) (erased (ElabProgram items out) p) -> (ProgramDec items))
    (many ProgramStuck : (erased (List (Raw)) items) -> (ProgramDec items))))
(def-fns _ $ many elab-program : (many (Nat) fuel) (many (List (Raw)) items) -> (many (ProgramDec items) r)
  (match many (elab-body fuel init-ctx items) _
    ((BodyStuck a b) (ProgramStuck _))
    ((MkBodyDec a b out p)
      (match many out _
        ((EErr r) (MkProgramDec _ (PErr r) (ProgramErr items r p)))
        ((EOk ctx core ids)
          (match many (one-dec ids) _
            ((OneNo c n) (MkProgramDec _ (PErr (RSize)) (ProgramSize items ctx core ids p n)))
            ((OneYes x)
              (match many (type-of ctx x) _
                ((TypeOfStuck c d) (ProgramStuck _))
                ((TypeIs c d ty k t kq) (MkProgramDec _ (POk core ty) (ProgramOk items ctx core x ty p t)))))))))))

(MkUnit)
