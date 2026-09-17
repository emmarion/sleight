; mini/unify.sl -- forced unification (DESIGN.md section 18) for the minimal language: two canonical terms
; are walked together, identical atoms and binders are dropped, applications and formers are split into
; their parts, and a variable meets a term either by taking it as its rule ([Force], entering a branch) or
; by failing ([Check], comparing two types for identity, section 5). After a rule is minted the parts still
; to walk are canonicalized again ([Then]); otherwise they are walked as they are, which is what makes the
; functions structural: they recurse on a bound on the entries without a rule, which every mint lowers, and
; then on the term. The three contradictions are the [UFail] outcomes: an unassignable term (the occurs
; check and a telescope binder), two rigid atoms, and two shapes that differ. [UStuck] is the outcome on a
; table whose canonical forms are not head-free, which elaboration never builds. One session's proposal.

(def-adts $ Mode : -> Type
  enum
  (many Force : -> (Mode))
  (many Check : -> (Mode)))

(def-adts $ Eqn : -> Type
  enum
  (many MkEqn : (many (Term) l) (many (Term) r) -> (Eqn)))

(def-adts
  (UOut : -> Type
    enum
    (many UOk : (many (List (Rule)) rules) -> (UOut))
    (many UFail : -> (UOut))
    (many UStuck : -> (UOut)))
  (NotOk : ((UOut) o) -> Type
    enum
    (many NotOkFail : -> (NotOk (UFail)))
    (many NotOkStuck : -> (NotOk (UStuck)))))

; A term's shape as a code, so that two canonical terms of different shapes are told apart by one rule;
; and a term that is not a variable, decided.
(def-adts
  (ShapeOf : ((Term) t) ((Nat) s) -> Type
    enum
    (many ShRef : (erased (Nat) x) -> (ShapeOf (Ref x) (Zero)))
    (many ShBound : (erased (Nat) k) -> (ShapeOf (Bound k) (Succ (Zero))))
    (many ShApp : (erased (Term) h) (erased (List (Term)) as) -> (ShapeOf (App h as) (Succ (Succ (Zero)))))
    (many ShUniv : -> (ShapeOf (Univ) (Succ (Succ (Succ (Zero))))))
    (many ShFn : (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs) -> (ShapeOf (Fn l ps rs) (Succ (Succ (Succ (Succ (Zero)))))))
    (many ShTyCtor : (erased (List (Entry)) ps) -> (ShapeOf (TyCtor ps) (Succ (Succ (Succ (Succ (Succ (Zero))))))))
    (many ShValCtor : (erased (List (Entry)) ps) (erased (Term) r) -> (ShapeOf (ValCtor ps r) (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))))))
  (NonRef : ((Term) t) -> Type
    enum
    (many NRBound : (erased (Nat) k) -> (NonRef (Bound k)))
    (many NRApp : (erased (Term) h) (erased (List (Term)) as) -> (NonRef (App h as)))
    (many NRUniv : -> (NonRef (Univ)))
    (many NRFn : (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs) -> (NonRef (Fn l ps rs)))
    (many NRTyCtor : (erased (List (Entry)) ps) -> (NonRef (TyCtor ps)))
    (many NRValCtor : (erased (List (Entry)) ps) (erased (Term) r) -> (NonRef (ValCtor ps r))))
  (NonRefDec : ((Term) t) -> Type
    enum
    (many IsRef : (many (Nat) x) -> (NonRefDec (Ref x)))
    (many IsNonRef : (erased (Term) t) (erased (NonRef t) p) -> (NonRefDec t)))
  (NotDecl : ((Kind) k) -> Type
    enum
    (many NDPlain : -> (NotDecl (KPlain)))
    (many NDLevel : -> (NotDecl (KLevel)))))

(def-fns _ $ many shape-of : (many (Term) t) -> (many (Nat) s) (erased (ShapeOf t s) p)
  (match many t _
    ((Ref x) (values (Zero) (ShRef x)))
    ((Bound k) (values (Succ (Zero)) (ShBound k)))
    ((App h as) (values (Succ (Succ (Zero))) (ShApp h as)))
    ((Univ) (values (Succ (Succ (Succ (Zero)))) (ShUniv)))
    ((Fn l ps rs) (values (Succ (Succ (Succ (Succ (Zero))))) (ShFn l ps rs)))
    ((TyCtor ps) (values (Succ (Succ (Succ (Succ (Succ (Zero)))))) (ShTyCtor ps)))
    ((ValCtor ps r) (values (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))) (ShValCtor ps r)))))

(def-fns _ $ many nonref-dec : (many (Term) t) -> (many (NonRefDec t) r)
  (match many t _
    ((Ref x) (IsRef x))
    ((Bound k) (IsNonRef _ (NRBound k)))
    ((App h as) (IsNonRef _ (NRApp h as)))
    ((Univ) (IsNonRef _ (NRUniv)))
    ((Fn l ps rs) (IsNonRef _ (NRFn l ps rs)))
    ((TyCtor ps) (IsNonRef _ (NRTyCtor ps)))
    ((ValCtor ps r) (IsNonRef _ (NRValCtor ps r)))))

; Which side of an equation a variable sits on: [Sided s v t l r] reads the equation l = r as the variable
; v against the term t.
(def-adts
  (Side : -> Type
    enum
    (many SL : -> (Side))
    (many SR : -> (Side)))
  (Sided : ((Side) s) ((Term) v) ((Term) t) ((Term) l) ((Term) r) -> Type
    enum
    (many SidedL : (erased (Term) v) (erased (Term) t) -> (Sided (SL) v t v t))
    (many SidedR : (erased (Term) v) (erased (Term) t) -> (Sided (SR) v t t v))))

; ---- The bound unification decreases: at most [n] entries have no rule. Minting a rule for an entry that
; had none lowers it (assign-count), which is the measure the functions below recurse on first.
(def-adts
  (FreeCount : ((List (Ent)) ents) ((List (Rule)) rules) ((Nat) n) -> Type
    enum
    (many FCNil : (erased (List (Rule)) rules) -> (FreeCount (Nil (Ent)) rules (Zero)))
    (many FCBound : (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (List (Ent)) rest) (erased (List (Rule)) rules) (erased (Term) r) (erased (List (Rule)) after) (erased (Nat) n)
       (erased (RuleOf rules x r after) p) (erased (FreeCount rest rules n) q) -> (FreeCount (Cons (Ent) (MkEnt x ty k) rest) rules n))
    (many FCFree : (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (List (Ent)) rest) (erased (List (Rule)) rules) (erased (Nat) n)
       (erased (FreeCount rest rules n) q) -> (FreeCount (Cons (Ent) (MkEnt x ty k) rest) rules (Succ n)))))

(def-fns _ $ many free-count : (subterm many (List (Ent)) ents) (many (List (Rule)) rules) -> (many (Nat) n) (erased (FreeCount ents rules n) p)
  (match many ents _
    ((Nil a) (values (Zero) (FCNil rules)))
    ((Cons a e rest)
      (match many e _
        ((MkEnt x ty k)
          (let (many n) (erased q) (free-count rest rules))
          (match many (rule-dec rules x) _
            ((RuleHit l y r after p sb) (values n (FCBound x ty k rest rules r after n p q)))
            ((RuleMiss l y p) (values (Succ n) (FCFree x ty k rest rules n q)))))))))

(def-fns _ $ erased rule-of-no-rule : (erased (List (Rule)) rules) (erased (Nat) x) (erased (Term) r) (erased (List (Rule)) after) (subterm erased (RuleOf rules x r after) p) (erased (NoRule rules x) q) ->
    (erased (False) f)
  (match erased p _
    ((RuleHere y s rest) (match erased q _ ((NoRuleCons a b c d n e) (neq-irrefl x n))))
    ((RuleThere a y s t rest af n p2) (match erased q _ ((NoRuleCons a2 b2 c2 d2 n2 q2) (rule-of-no-rule rest x r after p2 q2))))))

(def-fns _ $ erased rule-of-snoc : (erased (List (Rule)) rules) (erased (Nat) x) (erased (Term) r) (erased (List (Rule)) after) (erased (Rule) q) (erased (List (Rule)) rules2)
    (subterm erased (RuleOf rules x r after) p) (erased (Snoc (Rule) rules q rules2) sn) -> (erased (List (Rule)) after2) (erased (RuleOf rules2 x r after2) p2)
  (match erased p _
    ((RuleHere y s rest) (match erased sn _ ((SnocCons a b c d out e) (values out (RuleHere x r out)))))
    ((RuleThere a y s t rest af n p1)
      (match erased sn _
        ((SnocCons a2 b2 c2 d2 out e)
          (let (erased af2) (erased p3) (rule-of-snoc rest x r af q out p1 e))
          (values af2 (RuleThere x y r t out af2 n p3)))))))

(def-fns _ $ erased fc-snoc : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) n) (erased (Rule) q) (erased (List (Rule)) rules2)
    (subterm erased (FreeCount ents rules n) fc) (erased (Snoc (Rule) rules q rules2) sn) -> (erased (FreeCount ents rules2 n) fc2)
  (match erased fc _
    ((FCNil a) (FCNil rules2))
    ((FCBound x ty k rest a r after m p c)
      (let (erased after2) (erased p2) (rule-of-snoc rules x r after q rules2 p sn))
      (FCBound x ty k rest rules2 r after2 m p2 (fc-snoc rest rules m q rules2 c sn)))
    ((FCFree x ty k rest a m c) (FCFree x ty k rest rules2 m (fc-snoc rest rules m q rules2 c sn)))))

(def-fns _ $ erased no-rule-snoc : (erased (List (Rule)) rules) (erased (Nat) x) (erased (Term) t) (erased (List (Rule)) rules2) (subterm erased (NoRule rules x) nr)
    (erased (Snoc (Rule) rules (MkRule x t) rules2) sn) -> (erased (RuleOf rules2 x t (Nil (Rule))) p)
  (match erased nr _
    ((NoRuleNil a) (match erased sn _ ((SnocNil b c) (RuleHere x t (Nil _)))))
    ((NoRuleCons a y s rest n p1) (match erased sn _ ((SnocCons b c d e out g) (RuleThere x y t s out (Nil _) n (no-rule-snoc rest x t out p1 g)))))))

(def-fns _ $ erased assign-count : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) n) (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (Term) t) (erased (List (Rule)) rules2)
    (erased (FreeCount ents rules n) fc) (subterm erased (EntOf ents x ty k) e) (erased (NoRule rules x) nr) (erased (Snoc (Rule) rules (MkRule x t) rules2) sn) ->
    (erased (Nat) m) (erased (Lt m n) lt) (erased (FreeCount ents rules2 m) fc2)
  (match erased e _
    ((EntHere a b c rest)
      (match erased fc _
        (absurd (FCBound x2 ty2 k2 rest2 a2 r after m p c2) (rule-of-no-rule rules x r after p nr))
        ((FCFree x2 ty2 k2 rest2 a2 m c2)
          (values m (lt-succ m) (FCBound x ty k rest rules2 t (Nil _) m (no-rule-snoc rules x t rules2 nr sn) (fc-snoc rest rules m (MkRule x t) rules2 c2 sn))))))
    ((EntThere a y b ty2 c k2 rest ne e2)
      (match erased fc _
        ((FCBound x2 ty3 k3 rest2 a2 r after m p c2)
          (let (erased m2) (erased lt) (erased fc3) (assign-count rest rules m x ty k t rules2 c2 e2 nr sn))
          (let (erased after2) (erased p2) (rule-of-snoc rules y r after (MkRule x t) rules2 p sn))
          (values m2 lt (FCBound y ty2 k2 rest rules2 r after2 m2 p2 fc3)))
        ((FCFree x2 ty3 k3 rest2 a2 m c2)
          (let (erased m2) (erased lt) (erased fc3) (assign-count rest rules m x ty k t rules2 c2 e2 nr sn))
          (values (Succ m2) (LtS m2 m lt) (FCFree y ty2 k2 rest rules2 m2 fc3)))))))

; ---- The relations.
(def-adts
  ; two terms, canonicalized and then walked
  (Unify : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((Term) l) ((Term) r) ((UOut) out) -> Type
    enum
    (many UBy : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (Term) l2) (erased (Term) r2) (erased (UOut) out)
       (erased (Canon rules l l2) cl) (erased (Canon rules r r2) cr) (erased (UnifyC m ents rules l2 r2 out) p) -> (Unify m ents rules l r out)))
  ; two canonical terms
  (UnifyC : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((Term) l) ((Term) r) ((UOut) out) -> Type
    enum
    ; identical atoms and binders, and the universe
    (many UCSame : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) -> (UnifyC m ents rules (Ref x) (Ref x) (UOk rules)))
    (many UCBound : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) k) -> (UnifyC m ents rules (Bound k) (Bound k) (UOk rules)))
    (many UCBoundNeq : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) j) (erased (Nat) k) (erased (Neq j k) n) -> (UnifyC m ents rules (Bound j) (Bound k) (UFail)))
    (many UCUniv : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) -> (UnifyC m ents rules (Univ) (Univ) (UOk rules)))
    ; applications and formers, part by part
    (many UCApp : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) h) (erased (Term) h2) (erased (List (Term)) as) (erased (List (Term)) as2) (erased (UOut) o1) (erased (UOut) out)
       (erased (UnifyC m ents rules h h2 o1) p) (erased (AfterList m ents rules o1 as as2 out) q) -> (UnifyC m ents rules (App h as) (App h2 as2) out))
    (many UCFn : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) lv) (erased (Term) lv2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2)
       (erased (List (Entry)) rs) (erased (List (Entry)) rs2) (erased (UOut) o1) (erased (UOut) o2) (erased (UOut) out)
       (erased (UnifyC m ents rules lv lv2 o1) p) (erased (AfterTele m ents rules o1 ps ps2 o2) q) (erased (AfterTele m ents rules o2 rs rs2 out) r) ->
       (UnifyC m ents rules (Fn lv ps rs) (Fn lv2 ps2 rs2) out))
    (many UCTyCtor : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (UOut) out)
       (erased (UnifyTeleC m ents rules ps ps2 out) p) -> (UnifyC m ents rules (TyCtor ps) (TyCtor ps2) out))
    (many UCValCtor : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (Term) ret) (erased (Term) ret2) (erased (UOut) o1) (erased (UOut) out)
       (erased (UnifyTeleC m ents rules ps ps2 o1) p) (erased (After m ents rules o1 ret ret2 out) q) -> (UnifyC m ents rules (ValCtor ps ret) (ValCtor ps2 ret2) out))
    ; two shapes that differ, neither a variable
    (many UCMismatch : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (Nat) a) (erased (Nat) b)
       (erased (NonRef l) nl) (erased (NonRef r) nr) (erased (ShapeOf l a) sa) (erased (ShapeOf r b) sb) (erased (Neq a b) n) -> (UnifyC m ents rules l r (UFail)))
    ; a variable against a term that is not one, on either side: in [Check] mode a failure; in [Force] mode a
    ; rule when the variable is neither rigid nor unknown and the term may be assigned to it
    (many UCCheckRef : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Side) s) (erased (Nat) x) (erased (Term) t) (erased (Term) l) (erased (Term) r)
       (erased (Sided s (Ref x) t l r) sd) (erased (NonRef t) nt) -> (UnifyC (Check) ents rules l r (UFail)))
    (many UCRigid : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Side) s) (erased (Nat) x) (erased (Term) t) (erased (Term) l) (erased (Term) r) (erased (Term) ty)
       (erased (Sided s (Ref x) t l r) sd) (erased (NonRef t) nt) (erased (EntOf ents x ty (KDecl)) e) -> (UnifyC (Force) ents rules l r (UFail)))
    (many UCUnknown : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Side) s) (erased (Nat) x) (erased (Term) t) (erased (Term) l) (erased (Term) r)
       (erased (Sided s (Ref x) t l r) sd) (erased (NonRef t) nt) (erased (NoEnt ents x) e) -> (UnifyC (Force) ents rules l r (UFail)))
    (many UCOccurs : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Side) s) (erased (Nat) x) (erased (Term) t) (erased (Term) l) (erased (Term) r)
       (erased (Sided s (Ref x) t l r) sd) (erased (NonRef t) nt) (erased (Unassignable (Zero) x t) u) -> (UnifyC (Force) ents rules l r (UFail)))
    (many UCBoundVar : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Side) s) (erased (Nat) x) (erased (Term) t) (erased (Term) l) (erased (Term) r) (erased (Term) rx) (erased (List (Rule)) rest)
       (erased (Sided s (Ref x) t l r) sd) (erased (NonRef t) nt) (erased (RuleOf rules x rx rest) p) -> (UnifyC (Force) ents rules l r (UStuck)))
    (many UCAssign : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Side) s) (erased (Nat) x) (erased (Term) t) (erased (Term) l) (erased (Term) r) (erased (Term) ty) (erased (Kind) k)
       (erased (List (Rule)) rules2)
       (erased (Sided s (Ref x) t l r) sd) (erased (NonRef t) nt) (erased (EntOf ents x ty k) e) (erased (NotDecl k) nd) (erased (NoRule rules x) nr) (erased (Assignable (Zero) x t) a)
       (erased (Snoc (Rule) rules (MkRule x t) rules2) sn) -> (UnifyC (Force) ents rules l r (UOk rules2)))
    ; two distinct variables: in [Force] mode the one that is not rigid, else the newer, becomes an alias of
    ; the other and their types are unified next (section 18's signature check); two rigid ones contradict
    (many UCCheckRefRef : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) (erased (Nat) y) (erased (Neq x y) n) -> (UnifyC (Check) ents rules (Ref x) (Ref y) (UFail)))
    (many UCRigidRigid : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) (erased (Nat) y) (erased (Term) tx) (erased (Term) ty)
       (erased (Neq x y) n) (erased (EntOf ents x tx (KDecl)) ex) (erased (EntOf ents y ty (KDecl)) ey) -> (UnifyC (Force) ents rules (Ref x) (Ref y) (UFail)))
    (many UCUnknownL : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) (erased (Nat) y) (erased (Neq x y) n) (erased (NoEnt ents x) e) -> (UnifyC (Force) ents rules (Ref x) (Ref y) (UFail)))
    (many UCUnknownR : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) (erased (Nat) y) (erased (Neq x y) n) (erased (NoEnt ents y) e) -> (UnifyC (Force) ents rules (Ref x) (Ref y) (UFail)))
    (many UCAliasBound : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) (erased (Nat) y) (erased (Term) tx) (erased (Kind) kx) (erased (Term) ty) (erased (Kind) ky)
       (erased (Nat) z) (erased (Term) tz) (erased (Nat) w) (erased (Term) tw) (erased (Term) rz) (erased (List (Rule)) rest)
       (erased (Neq x y) n) (erased (EntOf ents x tx kx) ex) (erased (EntOf ents y ty ky) ey) (erased (Orient x tx kx y ty ky z tz w tw) o) (erased (RuleOf rules z rz rest) p) ->
       (UnifyC (Force) ents rules (Ref x) (Ref y) (UStuck)))
    (many UCAlias : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) (erased (Nat) y) (erased (Term) tx) (erased (Kind) kx) (erased (Term) ty) (erased (Kind) ky)
       (erased (Nat) z) (erased (Term) tz) (erased (Nat) w) (erased (Term) tw) (erased (List (Rule)) rules1) (erased (UOut) out)
       (erased (Neq x y) n) (erased (EntOf ents x tx kx) ex) (erased (EntOf ents y ty ky) ey) (erased (Orient x tx kx y ty ky z tz w tw) o) (erased (NoRule rules z) nr)
       (erased (Snoc (Rule) rules (MkRule z (Ref w)) rules1) sn) (erased (Unify (Force) ents rules1 tz tw out) p) -> (UnifyC (Force) ents rules (Ref x) (Ref y) out)))
  (UnifyListC : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((List (Term)) as) ((List (Term)) bs) ((UOut) out) -> Type
    enum
    (many ULNil : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) -> (UnifyListC m ents rules (Nil (Term)) (Nil (Term)) (UOk rules)))
    (many ULArity : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Term)) as) (erased (List (Term)) bs) (erased (LenMismatch (Term) (Term) as bs) lm) ->
       (UnifyListC m ents rules as bs (UFail)))
    (many ULCons : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) a) (erased (Term) b) (erased (List (Term)) as) (erased (List (Term)) bs) (erased (UOut) o1) (erased (UOut) out)
       (erased (UnifyC m ents rules a b o1) p) (erased (AfterList m ents rules o1 as bs out) q) -> (UnifyListC m ents rules (Cons (Term) a as) (Cons (Term) b bs) out)))
  (UnifyTeleC : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((List (Entry)) es) ((List (Entry)) fs) ((UOut) out) -> Type
    enum
    (many UTNil : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) -> (UnifyTeleC m ents rules (Nil (Entry)) (Nil (Entry)) (UOk rules)))
    (many UTArity : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (LenMismatch (Entry) (Entry) es fs) lm) ->
       (UnifyTeleC m ents rules es fs (UFail)))
    (many UTSub : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Bool) s) (erased (Bool) s2) (erased (Bool) i) (erased (Bool) i2) (erased (Term) t) (erased (Term) u)
       (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (BoolNeq s s2) n) -> (UnifyTeleC m ents rules (Cons (Entry) (MkEntry s i t) es) (Cons (Entry) (MkEntry s2 i2 u) fs) (UFail)))
    (many UTIs : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Bool) s) (erased (Bool) i) (erased (Bool) i2) (erased (Term) t) (erased (Term) u)
       (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (BoolNeq i i2) n) -> (UnifyTeleC m ents rules (Cons (Entry) (MkEntry s i t) es) (Cons (Entry) (MkEntry s i2 u) fs) (UFail)))
    (many UTCons : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Bool) s) (erased (Bool) i) (erased (Term) t) (erased (Term) u) (erased (List (Entry)) es) (erased (List (Entry)) fs)
       (erased (UOut) o1) (erased (UOut) out)
       (erased (UnifyC m ents rules t u o1) p) (erased (AfterTele m ents rules o1 es fs out) q) -> (UnifyTeleC m ents rules (Cons (Entry) (MkEntry s i t) es) (Cons (Entry) (MkEntry s i u) fs) out)))
  ; What follows an outcome: nothing when it is not a table, else the next parts under that table, read
  ; again through it when it is not the table they were canonical under.
  (After : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((UOut) o1) ((Term) t) ((Term) u) ((UOut) out) -> Type
    enum
    (many AStop : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (UOut) o) (erased (Term) t) (erased (Term) u) (erased (NotOk o) n) -> (After m ents rules o t u o))
    (many AOk : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Rule)) rules1) (erased (Term) t) (erased (Term) u) (erased (Term) t2) (erased (Term) u2) (erased (UOut) out)
       (erased (Then rules rules1 t t2) p) (erased (Then rules rules1 u u2) q) (erased (UnifyC m ents rules1 t2 u2 out) r) -> (After m ents rules (UOk rules1) t u out)))
  (AfterList : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((UOut) o1) ((List (Term)) as) ((List (Term)) bs) ((UOut) out) -> Type
    enum
    (many ALStop : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (UOut) o) (erased (List (Term)) as) (erased (List (Term)) bs) (erased (NotOk o) n) -> (AfterList m ents rules o as bs o))
    (many ALOk : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Rule)) rules1) (erased (List (Term)) as) (erased (List (Term)) bs) (erased (List (Term)) as2) (erased (List (Term)) bs2) (erased (UOut) out)
       (erased (ThenList rules rules1 as as2) p) (erased (ThenList rules rules1 bs bs2) q) (erased (UnifyListC m ents rules1 as2 bs2 out) r) -> (AfterList m ents rules (UOk rules1) as bs out)))
  (AfterTele : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((UOut) o1) ((List (Entry)) es) ((List (Entry)) fs) ((UOut) out) -> Type
    enum
    (many ATStop : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (UOut) o) (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (NotOk o) n) -> (AfterTele m ents rules o es fs o))
    (many ATOk : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Rule)) rules1) (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (List (Entry)) es2) (erased (List (Entry)) fs2) (erased (UOut) out)
       (erased (ThenTele rules rules1 es es2) p) (erased (ThenTele rules rules1 fs fs2) q) (erased (UnifyTeleC m ents rules1 es2 fs2 out) r) -> (AfterTele m ents rules (UOk rules1) es fs out)))
  (Then : ((List (Rule)) rules0) ((List (Rule)) rules1) ((Term) t) ((Term) t2) -> Type
    enum
    (many ThenSame : (erased (List (Rule)) rules) (erased (Term) t) -> (Then rules rules t t))
    (many ThenCanon : (erased (List (Rule)) rules0) (erased (List (Rule)) rules1) (erased (Term) t) (erased (Term) t2) (erased (Canon rules1 t t2) p) -> (Then rules0 rules1 t t2)))
  (ThenList : ((List (Rule)) rules0) ((List (Rule)) rules1) ((List (Term)) ts) ((List (Term)) ts2) -> Type
    enum
    (many ThenListSame : (erased (List (Rule)) rules) (erased (List (Term)) ts) -> (ThenList rules rules ts ts))
    (many ThenListCanon : (erased (List (Rule)) rules0) (erased (List (Rule)) rules1) (erased (List (Term)) ts) (erased (List (Term)) ts2) (erased (CanonList rules1 ts ts2) p) -> (ThenList rules0 rules1 ts ts2)))
  (ThenTele : ((List (Rule)) rules0) ((List (Rule)) rules1) ((List (Entry)) es) ((List (Entry)) es2) -> Type
    enum
    (many ThenTeleSame : (erased (List (Rule)) rules) (erased (List (Entry)) es) -> (ThenTele rules rules es es))
    (many ThenTeleCanon : (erased (List (Rule)) rules0) (erased (List (Rule)) rules1) (erased (List (Entry)) es) (erased (List (Entry)) es2) (erased (CanonTele rules1 es es2) p) -> (ThenTele rules0 rules1 es es2)))
  ; A list of equations, each canonicalized under the table the ones before it left.
  (UnifyEqs : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((List (Eqn)) eqs) ((UOut) out) -> Type
    enum
    (many UENil : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) -> (UnifyEqs m ents rules (Nil (Eqn)) (UOk rules)))
    (many UECons : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (UOut) o1) (erased (UOut) out)
       (erased (Unify m ents rules l r o1) p) (erased (AfterEqs m ents rules o1 rest out) q) -> (UnifyEqs m ents rules (Cons (Eqn) (MkEqn l r) rest) out)))
  (AfterEqs : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((UOut) o1) ((List (Eqn)) rest) ((UOut) out) -> Type
    enum
    (many AEStop : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (UOut) o) (erased (List (Eqn)) rest) (erased (NotOk o) n) -> (AfterEqs m ents rules o rest o))
    (many AEOk : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Rule)) rules1) (erased (List (Eqn)) rest) (erased (UOut) out)
       (erased (UnifyEqs m ents rules1 rest out) p) -> (AfterEqs m ents rules (UOk rules1) rest out)))
  ; Which of two distinct variables takes the rule: [z] is aliased to [w].
  (Orient : ((Nat) x) ((Term) tx) ((Kind) kx) ((Nat) y) ((Term) ty) ((Kind) ky) ((Nat) z) ((Term) tz) ((Nat) w) ((Term) tw) -> Type
    enum
    (many OrRigidL : (erased (Nat) x) (erased (Term) tx) (erased (Nat) y) (erased (Term) ty) (erased (Kind) ky) (erased (NotDecl ky) n) -> (Orient x tx (KDecl) y ty ky y ty x tx))
    (many OrRigidR : (erased (Nat) x) (erased (Term) tx) (erased (Kind) kx) (erased (Nat) y) (erased (Term) ty) (erased (NotDecl kx) n) -> (Orient x tx kx y ty (KDecl) x tx y ty))
    (many OrNewerL : (erased (Nat) x) (erased (Term) tx) (erased (Kind) kx) (erased (Nat) y) (erased (Term) ty) (erased (Kind) ky) (erased (NotDecl kx) nx) (erased (NotDecl ky) ny) (erased (Lt y x) lt) ->
       (Orient x tx kx y ty ky x tx y ty))
    (many OrNewerR : (erased (Nat) x) (erased (Term) tx) (erased (Kind) kx) (erased (Nat) y) (erased (Term) ty) (erased (Kind) ky) (erased (NotDecl kx) nx) (erased (NotDecl ky) ny) (erased (Lt x y) lt) ->
       (Orient x tx kx y ty ky y ty x tx))))

(def-adts
  (Oriented : ((List (Ent)) ents) ((Nat) x) ((Term) tx) ((Kind) kx) ((Nat) y) ((Term) ty) ((Kind) ky) -> Type
    enum
    (many OrSome : (erased (List (Ent)) ents) (erased (Nat) x) (erased (Term) tx) (erased (Kind) kx) (erased (Nat) y) (erased (Term) ty) (erased (Kind) ky)
       (many (Nat) z) (many (Term) tz) (many (Nat) w) (many (Term) tw) (erased (Kind) kz) (erased (EntOf ents z tz kz) ez) (erased (Orient x tx kx y ty ky z tz w tw) o) -> (Oriented ents x tx kx y ty ky))
    (many OrNone : (erased (List (Ent)) ents) (erased (Nat) x) (erased (Term) tx) (erased (Nat) y) (erased (Term) ty) -> (Oriented ents x tx (KDecl) y ty (KDecl)))))

(def-fns _ $ many orient-age : (erased (List (Ent)) ents) (many (Nat) x) (many (Term) tx) (many (Kind) kx) (erased (NotDecl kx) nx) (erased (EntOf ents x tx kx) ex)
      (many (Nat) y) (many (Term) ty) (many (Kind) ky) (erased (NotDecl ky) ny) (erased (EntOf ents y ty ky) ey) (erased (Neq x y) n) -> (many (Oriented ents x tx kx y ty ky) r)
    (match many (nat-cmp x y) _
      ((CLt a b c d lt) (OrSome _ _ _ _ _ _ _ y ty x tx ky ey (OrNewerR x tx kx y ty ky nx ny lt)))
      (absurd (CEq a b c) (neq-irrefl x n))
      ((CGt a b c d lt) (OrSome _ _ _ _ _ _ _ x tx y ty kx ex (OrNewerL x tx kx y ty ky nx ny lt)))))

(def-fns _ $ many orient-plain : (erased (List (Ent)) ents) (many (Nat) x) (many (Term) tx) (many (Kind) kx) (erased (NotDecl kx) nx) (erased (EntOf ents x tx kx) ex)
      (many (Nat) y) (many (Term) ty) (many (Kind) ky) (erased (EntOf ents y ty ky) ey) (erased (Neq x y) n) -> (many (Oriented ents x tx kx y ty ky) r)
    (match many ky _
      ((KDecl) (OrSome _ _ _ _ _ _ _ x tx y ty kx ex (OrRigidR x tx kx y ty nx)))
      ((KPlain) (orient-age ents x tx kx nx ex y ty (KPlain) (NDPlain) ey n))
      ((KLevel) (orient-age ents x tx kx nx ex y ty (KLevel) (NDLevel) ey n))))

(def-fns _ $ many orient : (erased (List (Ent)) ents) (many (Nat) x) (many (Term) tx) (many (Kind) kx) (erased (EntOf ents x tx kx) ex) (many (Nat) y) (many (Term) ty) (many (Kind) ky) (erased (EntOf ents y ty ky) ey)
      (erased (Neq x y) n) -> (many (Oriented ents x tx kx y ty ky) r)
    (match many kx _
      ((KDecl)
        (match many ky _
          ((KDecl) (OrNone _ x tx y ty))
          ((KPlain) (OrSome _ _ _ _ _ _ _ y ty x tx (KPlain) ey (OrRigidL x tx y ty (KPlain) (NDPlain))))
          ((KLevel) (OrSome _ _ _ _ _ _ _ y ty x tx (KLevel) ey (OrRigidL x tx y ty (KLevel) (NDLevel))))))
      ((KPlain) (orient-plain ents x tx (KPlain) (NDPlain) ex y ty ky ey n))
      ((KLevel) (orient-plain ents x tx (KLevel) (NDLevel) ex y ty ky ey n))))

; ---- The functions. Each answers the outcome with its derivation and a [Step]: whether the table is
; unchanged, or a new table with the bound it lowered to, or no table.
(def-adts
  (Step : ((Nat) n) ((List (Ent)) ents) ((List (Rule)) rules) ((UOut) o) -> Type
    enum
    (many StSame : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) -> (Step n ents rules (UOk rules)))
    (many StMint : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (many (List (Rule)) rules1) (erased (Nat) n1) (erased (Lt n1 n) lt) (erased (FreeCount ents rules1 n1) fc) ->
       (Step n ents rules (UOk rules1)))
    (many StFail : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) -> (Step n ents rules (UFail)))
    (many StStuck : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) -> (Step n ents rules (UStuck))))
  ; The second of two subterm arguments in a group of mutually recursive functions can only decrease when
  ; the first stays: a phase is the third, so that a function may hand its own arguments to a helper.
  (Phase : -> Type
    enum
    (many PInner : -> (Phase))
    (many POuter : (many (Phase) inner) -> (Phase))))

; A step after a step, relative to the bound the first started from.
(def-fns _ $ many step-seq : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Rule)) rules1) (many (Step n ents rules (UOk rules1)) st1)
      (erased (Nat) n1) (erased (Lt n1 (Succ n)) le) (erased (UOut) o2) (many (Step n1 ents rules1 o2) st2) -> (many (Step n ents rules o2) st)
    (match many st2 _
      ((StSame a b c) st1)
      ((StMint a b c rules2 n2 lt2 fc2) (StMint _ _ _ rules2 n2 (lt-le-trans n2 n1 n lt2 le) fc2))
      ((StFail a b c) (StFail _ _ _))
      ((StStuck a b c) (StStuck _ _ _))))

; A variable against a term that is not one.
(def-fns _ $ many assign : (many (List (Ent)) ents) (many (List (Rule)) rules) (erased (Nat) n) (erased (FreeCount ents rules n) fc) (many (Side) s) (many (Nat) x) (many (Term) t) (erased (Term) l) (erased (Term) r)
      (erased (Term) ty) (erased (Kind) k) (erased (Sided s (Ref x) t l r) sd) (erased (NonRef t) nt) (erased (EntOf ents x ty k) e) (erased (NotDecl k) nd) ->
      (erased (UOut) o) (many (Step n ents rules o) st) (erased (UnifyC (Force) ents rules l r o) p)
    (match many (rule-dec rules x) _
      ((RuleHit a b rx rest p sb) (values (UStuck) (StStuck _ _ _) (UCBoundVar ents rules s x t l r rx rest sd nt p)))
      ((RuleMiss a b nr)
        (match many (assign-dec (Zero) x t) _
          ((ADNo a2 b2 c2 un) (values (UFail) (StFail _ _ _) (UCOccurs ents rules s x t l r sd nt un)))
          ((ADYes a2 b2 c2 ok)
            (let (many rules2) (erased sn) (snoc _ rules (MkRule x t)))
            (let (erased n1) (erased lt) (erased fc1) (assign-count ents rules n x ty k t rules2 fc e nr sn))
            (values (UOk rules2) (StMint _ _ _ rules2 n1 lt fc1) (UCAssign ents rules s x t l r ty k rules2 sd nt e nd nr ok sn)))))))

(def-fns _ $ many unify-ref : (many (Mode) m) (many (List (Ent)) ents) (many (List (Rule)) rules) (erased (Nat) n) (erased (FreeCount ents rules n) fc) (many (Side) s) (many (Nat) x) (many (Term) t)
      (erased (Term) l) (erased (Term) r) (erased (Sided s (Ref x) t l r) sd) (erased (NonRef t) nt) ->
      (erased (UOut) o) (many (Step n ents rules o) st) (erased (UnifyC m ents rules l r o) p)
    (match many m _
      ((Check) (values (UFail) (StFail _ _ _) (UCCheckRef ents rules s x t l r sd nt)))
      ((Force)
        (match many (ent-dec ents x) _
          ((EntMiss a b ne) (values (UFail) (StFail _ _ _) (UCUnknown ents rules s x t l r sd nt ne)))
          ((EntHit a b ty k e)
            (match many k _
              ((KDecl) (values (UFail) (StFail _ _ _) (UCRigid ents rules s x t l r ty sd nt e)))
              ((KPlain) (assign ents rules n fc s x t l r ty (KPlain) sd nt e (NDPlain)))
              ((KLevel) (assign ents rules n fc s x t l r ty (KLevel) sd nt e (NDLevel)))))))))

; Two distinct variables in [Force] mode, up to the alias: what remains is to unify the types.
(def-adts $ AliasStep : ((Nat) n) ((List (Ent)) ents) ((List (Rule)) rules) ((Nat) x) ((Nat) y) -> Type
  enum
  (many AliasStop : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) (erased (Nat) y) (erased (UOut) o) (many (Step n ents rules o) st)
     (erased (UnifyC (Force) ents rules (Ref x) (Ref y) o) p) -> (AliasStep n ents rules x y))
  (many AliasMint : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) (erased (Nat) y)
     (many (Nat) z) (many (Term) tz) (many (Nat) w) (many (Term) tw) (many (List (Rule)) rules1) (erased (Nat) n1) (erased (Lt n1 n) lt) (erased (FreeCount ents rules1 n1) fc)
     (erased (Term) tx) (erased (Kind) kx) (erased (Term) ty) (erased (Kind) ky) (erased (EntOf ents x tx kx) ex) (erased (EntOf ents y ty ky) ey) (erased (Orient x tx kx y ty ky z tz w tw) o)
     (erased (NoRule rules z) nr) (erased (Snoc (Rule) rules (MkRule z (Ref w)) rules1) sn) -> (AliasStep n ents rules x y)))

(def-fns _ $ many alias-step : (many (List (Ent)) ents) (many (List (Rule)) rules) (erased (Nat) n) (erased (FreeCount ents rules n) fc) (many (Nat) x) (many (Nat) y) (erased (Neq x y) nq) ->
      (many (AliasStep n ents rules x y) r)
    (match many (ent-dec ents x) _
      ((EntMiss a b ne) (AliasStop _ _ _ _ _ (UFail) (StFail _ _ _) (UCUnknownL ents rules x y nq ne)))
      ((EntHit a b tx kx ex)
        (match many (ent-dec ents y) _
          ((EntMiss a2 b2 ne) (AliasStop _ _ _ _ _ (UFail) (StFail _ _ _) (UCUnknownR ents rules x y nq ne)))
          ((EntHit a2 b2 ty ky ey)
            (match many (orient ents x tx kx ex y ty ky ey nq) _
              ((OrNone a3 b3 c3 d3 e3) (AliasStop _ _ _ _ _ (UFail) (StFail _ _ _) (UCRigidRigid ents rules x y tx ty nq ex ey)))
              ((OrSome a3 b3 c3 d3 e3 g3 h3 z tz w tw kz ez o)
                (match many (rule-dec rules z) _
                  ((RuleHit a4 b4 rz rest p sb) (AliasStop _ _ _ _ _ (UStuck) (StStuck _ _ _) (UCAliasBound ents rules x y tx kx ty ky z tz w tw rz rest nq ex ey o p)))
                  ((RuleMiss a4 b4 nr)
                    (let (many rules1) (erased sn) (snoc _ rules (MkRule z (Ref w))))
                    (let (erased n1) (erased lt) (erased fc1) (assign-count ents rules n z tz kz (Ref w) rules1 fc ez nr sn))
                    (AliasMint _ _ _ _ _ z tz w tw rules1 n1 lt fc1 tx kx ty ky ex ey o nr sn))))))))))

(def-fns _
  (many unify-canon : (many (Mode) m) (many (List (Ent)) ents) (many (List (Rule)) rules) (subterm erased (Nat) n) (erased (FreeCount ents rules n) fc) (subterm many (Term) l) (many (Term) r)
      (subterm many (POuter (PInner)) is phase) -> (erased (UOut) o) (many (Step n ents rules o) st) (erased (UnifyC m ents rules l r o) p)
    (match many (nonref-dec l) _
      ((IsRef x)
        (match many (nonref-dec r) _
          ((IsRef y)
            (match many (nat-dec x y) _
              ((NDSame z) (values (UOk rules) (StSame _ _ _) (UCSame m ents rules x)))
              ((NDDiff z w nq)
                (match many m _
                  ((Check) (values (UFail) (StFail _ _ _) (UCCheckRefRef ents rules x y nq)))
                  ((Force)
                    (match many (alias-step ents rules n fc x y nq) _
                      ((AliasStop a b c d e o st p) (values o st p))
                      ((AliasMint a b c d e z tz w tw rules1 n1 lt fc1 tx kx ty ky ex ey o nr sn)
                        (let (many tz2) (erased c1) (canon rules1 tz))
                        (let (many tw2) (erased c2) (canon rules1 tw))
                        (let (erased o2) (many st2) (erased q) (unify-canon m ents rules1 (subterm (lt-subterm n1 n lt)) n1 fc1 tz2 tw2 phase))
                        (values o2 (step-seq n ents rules rules1 (StMint _ _ _ rules1 n1 lt fc1) n1 (lt-weaken n1 n lt) o2 st2)
                          (UCAlias ents rules x y tx kx ty ky z tz w tw rules1 o2 nq ex ey o nr sn (UBy (Force) ents rules1 tz tw tz2 tw2 o2 c1 c2 q))))))))))
          ((IsNonRef tr0 nr) (unify-ref m ents rules n fc (SL) x r (Ref x) r (SidedL (Ref x) r) nr))))
      ((IsNonRef tl0 nl)
        (match many (nonref-dec r) _
          ((IsRef y) (unify-ref m ents rules n fc (SR) y l l (Ref y) (SidedR (Ref y) l) nl))
          ((IsNonRef tr0 nr)
            (let (many b) (erased sb) (shape-of r))
            (match many l _
              ((Ref x) (match erased nl _))
              ((Bound j)
                (match many (nat-dec (Succ (Zero)) b) _
                  ((NDDiff z w nq) (values (UFail) (StFail _ _ _) (UCMismatch m ents rules l r (Succ (Zero)) b nl nr (ShBound j) sb nq)))
                  ((NDSame z)
                    (match erased sb _
                      ((ShBound k0)
                        (match many r _
                          ((Bound k)
                            (match many (nat-dec j k) _
                              ((NDSame z2) (values (UOk rules) (StSame _ _ _) (UCBound m ents rules j)))
                              ((NDDiff z2 w2 nq) (values (UFail) (StFail _ _ _) (UCBoundNeq m ents rules j k nq)))))))))))
              ((App h as)
                (match many (nat-dec (Succ (Succ (Zero))) b) _
                  ((NDDiff z w nq) (values (UFail) (StFail _ _ _) (UCMismatch m ents rules l r (Succ (Succ (Zero))) b nl nr (ShApp h as) sb nq)))
                  ((NDSame z)
                    (match erased sb _
                      ((ShApp h0 as0)
                        (match many r _
                          ((App h2 as2)
                            (let (erased o1) (many st1) (erased p) (unify-canon m ents rules n fc h h2 phase))
                            (let (erased o2) (many st2) (erased q) (after-list m ents rules n fc _ l o1 st1 as as2 (prove-subterm as l) (PInner)))
                            (values o2 st2 (UCApp m ents rules h h2 as as2 o1 o2 p q)))))))))
              ((Univ)
                (match many (nat-dec (Succ (Succ (Succ (Zero)))) b) _
                  ((NDDiff z w nq) (values (UFail) (StFail _ _ _) (UCMismatch m ents rules l r (Succ (Succ (Succ (Zero)))) b nl nr (ShUniv) sb nq)))
                  ((NDSame z)
                    (match erased sb _
                      ((ShUniv) (match many r _ ((Univ) (values (UOk rules) (StSame _ _ _) (UCUniv m ents rules)))))))))
              ((Fn lv ps rs)
                (match many (nat-dec (Succ (Succ (Succ (Succ (Zero))))) b) _
                  ((NDDiff z w nq) (values (UFail) (StFail _ _ _) (UCMismatch m ents rules l r (Succ (Succ (Succ (Succ (Zero))))) b nl nr (ShFn lv ps rs) sb nq)))
                  ((NDSame z)
                    (match erased sb _
                      ((ShFn lv0 ps0 rs0)
                        (match many r _
                          ((Fn lv2 ps2 rs2)
                            (let (erased o1) (many st1) (erased p) (unify-canon m ents rules n fc lv lv2 phase))
                            (let (erased o2) (many st2) (erased q) (after-tele m ents rules n fc _ l o1 st1 ps ps2 (prove-subterm ps l) (PInner)))
                            (let (erased o3) (many st3) (erased q2) (after-tele m ents rules n fc _ l o2 st2 rs rs2 (prove-subterm rs l) (PInner)))
                            (values o3 st3 (UCFn m ents rules lv lv2 ps ps2 rs rs2 o1 o2 o3 p q q2)))))))))
              ((TyCtor ps)
                (match many (nat-dec (Succ (Succ (Succ (Succ (Succ (Zero)))))) b) _
                  ((NDDiff z w nq) (values (UFail) (StFail _ _ _) (UCMismatch m ents rules l r (Succ (Succ (Succ (Succ (Succ (Zero)))))) b nl nr (ShTyCtor ps) sb nq)))
                  ((NDSame z)
                    (match erased sb _
                      ((ShTyCtor ps0)
                        (match many r _
                          ((TyCtor ps2)
                            (let (erased o) (many st) (erased p) (unify-tele-canon m ents rules n fc ps ps2 phase))
                            (values o st (UCTyCtor m ents rules ps ps2 o p)))))))))
              ((ValCtor ps ret)
                (match many (nat-dec (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))) b) _
                  ((NDDiff z w nq) (values (UFail) (StFail _ _ _) (UCMismatch m ents rules l r (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))) b nl nr (ShValCtor ps ret) sb nq)))
                  ((NDSame z)
                    (match erased sb _
                      ((ShValCtor ps0 ret0)
                        (match many r _
                          ((ValCtor ps2 ret2)
                            (let (erased o1) (many st1) (erased p) (unify-tele-canon m ents rules n fc ps ps2 phase))
                            (let (erased o2) (many st2) (erased q) (after m ents rules n fc _ l o1 st1 ret ret2 (prove-subterm ret l) (PInner)))
                            (values o2 st2 (UCValCtor m ents rules ps ps2 ret ret2 o1 o2 p q)))))))))))))))
  (many unify-list-canon : (many (Mode) m) (many (List (Ent)) ents) (many (List (Rule)) rules) (subterm erased (Nat) n) (erased (FreeCount ents rules n) fc) (subterm many (List (Term)) as) (many (List (Term)) bs)
      (subterm many (POuter (PInner)) is phase) -> (erased (UOut) o) (many (Step n ents rules o) st) (erased (UnifyListC m ents rules as bs o) p)
    (match many as _
      ((Nil a)
        (match many bs _
          ((Nil b) (values (UOk rules) (StSame _ _ _) (ULNil m ents rules)))
          ((Cons b y ys) (values (UFail) (StFail _ _ _) (ULArity m ents rules as bs (LMNilCons _ _ y ys))))))
      ((Cons a x xs)
        (match many bs _
          ((Nil b) (values (UFail) (StFail _ _ _) (ULArity m ents rules as bs (LMConsNil _ _ x xs))))
          ((Cons b y ys)
            (let (erased o1) (many st1) (erased p) (unify-canon m ents rules n fc x y phase))
            (let (erased o2) (many st2) (erased q) (after-list m ents rules n fc _ as o1 st1 xs ys (prove-subterm xs as) (PInner)))
            (values o2 st2 (ULCons m ents rules x y xs ys o1 o2 p q)))))))
  (many unify-tele-canon : (many (Mode) m) (many (List (Ent)) ents) (many (List (Rule)) rules) (subterm erased (Nat) n) (erased (FreeCount ents rules n) fc) (subterm many (List (Entry)) es) (many (List (Entry)) fs)
      (subterm many (POuter (PInner)) is phase) -> (erased (UOut) o) (many (Step n ents rules o) st) (erased (UnifyTeleC m ents rules es fs o) p)
    (match many es _
      ((Nil a)
        (match many fs _
          ((Nil b) (values (UOk rules) (StSame _ _ _) (UTNil m ents rules)))
          ((Cons b f frest) (values (UFail) (StFail _ _ _) (UTArity m ents rules es fs (LMNilCons _ _ f frest))))))
      ((Cons a e rest)
        (match many fs _
          ((Nil b) (values (UFail) (StFail _ _ _) (UTArity m ents rules es fs (LMConsNil _ _ e rest))))
          ((Cons b f frest)
            (match many e _
              ((MkEntry s i t)
                (match many f _
                  ((MkEntry s2 i2 u)
                    (match many (bool-dec s s2) _
                      ((BDDiff c d nq) (values (UFail) (StFail _ _ _) (UTSub m ents rules s s2 i i2 t u rest frest nq)))
                      ((BDSame c)
                        (match many (bool-dec i i2) _
                          ((BDDiff d g nq) (values (UFail) (StFail _ _ _) (UTIs m ents rules s i i2 t u rest frest nq)))
                          ((BDSame d)
                            (let (erased o1) (many st1) (erased p) (unify-canon m ents rules n fc t u phase))
                            (let (erased o2) (many st2) (erased q) (after-tele m ents rules n fc _ es o1 st1 rest frest (prove-subterm rest es) (PInner)))
                            (values o2 st2 (UTCons m ents rules s i t u rest frest o1 o2 p q)))))))))))))))
  ; After a step: nothing when it left no table; the parts as they are when it left the table alone; the
  ; parts canonicalized again under the new table when it minted, the bound being lower then.
  (many after : (many (Mode) m) (many (List (Ent)) ents) (many (List (Rule)) rules) (subterm erased (Nat) n) (erased (FreeCount ents rules n) fc) (erased Type P) (subterm many P parent)
      (erased (UOut) o1) (many (Step n ents rules o1) st1) (many (Term) t) (many (Term) u) (erased (Subterm (Term) t P parent) sub) (subterm many (PInner) is phase) ->
      (erased (UOut) o) (many (Step n ents rules o) st) (erased (After m ents rules o1 t u o) p)
    (match many st1 _
      ((StFail a b c) (values (UFail) (StFail _ _ _) (AStop m ents rules (UFail) t u (NotOkFail))))
      ((StStuck a b c) (values (UStuck) (StStuck _ _ _) (AStop m ents rules (UStuck) t u (NotOkStuck))))
      ((StSame a b c)
        (let (erased o) (many st) (erased q) (unify-canon m ents rules n fc (subterm sub) t u (POuter (PInner))))
        (values o st (AOk m ents rules rules t u t u o (ThenSame rules t) (ThenSame rules u) q)))
      ((StMint a b c rules1 n1 lt fc1)
        (let (many t2) (erased c1) (canon rules1 t))
        (let (many u2) (erased c2) (canon rules1 u))
        (let (erased o) (many st2) (erased q) (unify-canon m ents rules1 (subterm (lt-subterm n1 n lt)) n1 fc1 t2 u2 (POuter (PInner))))
        (values o (step-seq n ents rules rules1 st1 n1 (lt-weaken n1 n lt) o st2) (AOk m ents rules rules1 t u t2 u2 o (ThenCanon rules rules1 t t2 c1) (ThenCanon rules rules1 u u2 c2) q)))))
  (many after-list : (many (Mode) m) (many (List (Ent)) ents) (many (List (Rule)) rules) (subterm erased (Nat) n) (erased (FreeCount ents rules n) fc) (erased Type P) (subterm many P parent)
      (erased (UOut) o1) (many (Step n ents rules o1) st1) (many (List (Term)) as) (many (List (Term)) bs) (erased (Subterm (List (Term)) as P parent) sub) (subterm many (PInner) is phase) ->
      (erased (UOut) o) (many (Step n ents rules o) st) (erased (AfterList m ents rules o1 as bs o) p)
    (match many st1 _
      ((StFail a b c) (values (UFail) (StFail _ _ _) (ALStop m ents rules (UFail) as bs (NotOkFail))))
      ((StStuck a b c) (values (UStuck) (StStuck _ _ _) (ALStop m ents rules (UStuck) as bs (NotOkStuck))))
      ((StSame a b c)
        (let (erased o) (many st) (erased q) (unify-list-canon m ents rules n fc (subterm sub) as bs (POuter (PInner))))
        (values o st (ALOk m ents rules rules as bs as bs o (ThenListSame rules as) (ThenListSame rules bs) q)))
      ((StMint a b c rules1 n1 lt fc1)
        (let (many as2) (erased c1) (canon-list rules1 as))
        (let (many bs2) (erased c2) (canon-list rules1 bs))
        (let (erased o) (many st2) (erased q) (unify-list-canon m ents rules1 (subterm (lt-subterm n1 n lt)) n1 fc1 as2 bs2 (POuter (PInner))))
        (values o (step-seq n ents rules rules1 st1 n1 (lt-weaken n1 n lt) o st2) (ALOk m ents rules rules1 as bs as2 bs2 o (ThenListCanon rules rules1 as as2 c1) (ThenListCanon rules rules1 bs bs2 c2) q)))))
  (many after-tele : (many (Mode) m) (many (List (Ent)) ents) (many (List (Rule)) rules) (subterm erased (Nat) n) (erased (FreeCount ents rules n) fc) (erased Type P) (subterm many P parent)
      (erased (UOut) o1) (many (Step n ents rules o1) st1) (many (List (Entry)) es) (many (List (Entry)) fs) (erased (Subterm (List (Entry)) es P parent) sub) (subterm many (PInner) is phase) ->
      (erased (UOut) o) (many (Step n ents rules o) st) (erased (AfterTele m ents rules o1 es fs o) p)
    (match many st1 _
      ((StFail a b c) (values (UFail) (StFail _ _ _) (ATStop m ents rules (UFail) es fs (NotOkFail))))
      ((StStuck a b c) (values (UStuck) (StStuck _ _ _) (ATStop m ents rules (UStuck) es fs (NotOkStuck))))
      ((StSame a b c)
        (let (erased o) (many st) (erased q) (unify-tele-canon m ents rules n fc (subterm sub) es fs (POuter (PInner))))
        (values o st (ATOk m ents rules rules es fs es fs o (ThenTeleSame rules es) (ThenTeleSame rules fs) q)))
      ((StMint a b c rules1 n1 lt fc1)
        (let (many es2) (erased c1) (canon-tele rules1 es))
        (let (many fs2) (erased c2) (canon-tele rules1 fs))
        (let (erased o) (many st2) (erased q) (unify-tele-canon m ents rules1 (subterm (lt-subterm n1 n lt)) n1 fc1 es2 fs2 (POuter (PInner))))
        (values o (step-seq n ents rules rules1 st1 n1 (lt-weaken n1 n lt) o st2) (ATOk m ents rules rules1 es fs es2 fs2 o (ThenTeleCanon rules rules1 es es2 c1) (ThenTeleCanon rules rules1 fs fs2 c2) q))))))

; Two terms as written, and a list of equations.
(def-fns _ $ many unify : (many (Mode) m) (many (List (Ent)) ents) (many (List (Rule)) rules) (erased (Nat) n) (erased (FreeCount ents rules n) fc) (many (Term) l) (many (Term) r) ->
    (erased (UOut) o) (many (Step n ents rules o) st) (erased (Unify m ents rules l r o) p)
  (let (many l2) (erased cl) (canon rules l))
  (let (many r2) (erased cr) (canon rules r))
  (let (erased o) (many st) (erased q) (unify-canon m ents rules n fc l2 r2 (POuter (PInner))))
  (values o st (UBy m ents rules l r l2 r2 o cl cr q)))

(def-fns _ $ many unify-eqs : (many (Mode) m) (many (List (Ent)) ents) (many (List (Rule)) rules) (erased (Nat) n) (erased (FreeCount ents rules n) fc) (subterm many (List (Eqn)) eqs) ->
    (many (UOut) o) (erased (UnifyEqs m ents rules eqs o) p)
  (match many eqs _
    ((Nil a) (values (UOk rules) (UENil m ents rules)))
    ((Cons a eqn rest)
      (match many eqn _
        ((MkEqn l r)
          (let (erased o1) (many st1) (erased p) (unify m ents rules n fc l r))
          (match many st1 _
            ((StFail b c d) (values (UFail) (UECons m ents rules l r rest (UFail) (UFail) p (AEStop m ents rules (UFail) rest (NotOkFail)))))
            ((StStuck b c d) (values (UStuck) (UECons m ents rules l r rest (UStuck) (UStuck) p (AEStop m ents rules (UStuck) rest (NotOkStuck)))))
            ((StSame b c d)
              (let (many o) (erased q) (unify-eqs m ents rules n fc rest))
              (values o (UECons m ents rules l r rest (UOk rules) o p (AEOk m ents rules rules rest o q))))
            ((StMint b c d rules1 n1 lt fc1)
              (let (many o) (erased q) (unify-eqs m ents rules1 n1 fc1 rest))
              (values o (UECons m ents rules l r rest (UOk rules1) o p (AEOk m ents rules rules1 rest o q))))))))))

(MkUnit)
