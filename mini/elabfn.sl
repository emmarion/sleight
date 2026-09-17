; mini/elabfn.sl -- the functions that derive mini/elab.sl's relations: for every judgment, a function that
; computes the outcome and its derivation, recursing on the raw syntax alone, or answers stuck. Beside the
; context they carry its well-formedness (mini/ctx.sl), which is what lets every context-level step conclude:
; a stuck answer is a malformed shape the relations have no rule for, with the one exception noted at
; [type-of-term]. Helpers first, in the order the relations were declared. One session's proposal.

(def-adts
  (WF : ((Ctx) ctx) -> Type
    enum
    (many MkWF : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
       (many (List (Nat)) ranks) (many (Nat) top) (erased (ValidFrom r ranks r ranks) v) (erased (AllLt ranks top) al)
       (erased (BoundedEnts n e) be) (erased (ScopedEnts e e) se) (erased (ScopedScope e s) ss) (erased (ScopedRules e r) sr) (erased (ScopedAdts e a) sa2) (erased (ScopedMaybe e l) sl)
       (erased (ScopedList e (Zero) sa) ssa) (erased (Builtins e) bi) (erased (RulesPlain e r) rp) -> (WF (MkCtx n s e r a l sa))))
  ; A rule minted with an entry goes only to one that is not rigid.
  (RuleOk : ((Kind) k) ((Maybe (Term)) rule) -> Type
    enum
    (many ROkNone : (erased (Kind) k) -> (RuleOk k (None (Term))))
    (many ROkSome : (erased (Kind) k) (erased (Term) t) (erased (NotDecl k) nd) -> (RuleOk k (Some (Term) t)))))

(def-fns _ $ erased rules-plain-weaken : (erased (Nat) n) (erased (List (Ent)) ents) (erased (Nat) y) (erased (Term) ty) (erased (Kind) k) (erased (List (Rule)) rules) (erased (BoundedEnts n ents) be) (erased (Lt n (Succ y)) le)
    (subterm erased (RulesPlain ents rules) b) -> (erased (RulesPlain (Cons (Ent) (MkEnt y ty k) ents) rules) c)
  (match erased b _
    ((RPNil a) (RPNil _))
    ((RPCons a x t rest ty2 k2 e nd q)
      (RPCons _ x t rest ty2 k2 (EntThere x y ty2 ty k2 k ents (lt-neq x y (lt-le x n y (has-ent-lt n ents x be (ent-of-has ents x ty2 k2 e)) le)) e) nd (rules-plain-weaken n ents y ty k rest be le q)))))
(def-fns _ $ erased decl-no-rule : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) (erased (Term) ty) (erased (EntOf ents x ty (KDecl)) e) (subterm erased (RulesPlain ents rules) b) -> (erased (NoRule rules x) nr)
  (match erased b _
    ((RPNil a) (NoRuleNil x))
    ((RPCons a y t rest ty2 k2 e2 nd q)
      (match many (nat-dec x y) _
        ((NDSame z) (match erased (ent-of-unique ents x ty (KDecl) ty2 k2 e e2) _ ((SameEntRefl c d) (match erased nd _))))
        ((NDDiff z w nq) (NoRuleCons x y t rest nq (decl-no-rule ents rest x ty e q)))))))

; ---- Helpers over the context and lists, each returning what it built with its derivation.

(def-fns _ $ many mint : (many (Ctx) ctx) (many (WF ctx) wf) (many (Maybe (String)) name) (many (Term) ty) (many (Kind) k) (many (Maybe (Term)) rule) (erased (Sc ctx (Zero) ty) sty) (erased (ScM ctx rule) srule) (erased (RuleOk k rule) rk) ->
    (many (Nat) id) (many (Ctx) out) (erased (Mint ctx name ty k rule id out) p) (many (WF out) wf2) (erased (Grew ctx out) g) (erased (EntIs out id ty k) h)
  (let-match many ctx (MkCtx n s e r a l sa))
  (let-match many wf (MkWF n0 s0 e0 r0 a0 l0 sa0 ranks top v al be se ss sr sa2 sl ssa bi rp))
  (let-match erased sty (MkSc q1 q2 q3 q4 q5 q6 q7 dq q8 st))
  (let-match erased srule (MkScM z1 z2 z3 z4 z5 z6 z7 z8 sm))
  (let (many s2) (erased an) (erased ss2)
    (match many name (((List (Name)) s2) ((AddName s name n s2) an) ((ScopedScope (Cons (Ent) (MkEnt n ty k) e) s2) ss2))
      ((None b) (values s (AddNameNone s n) (scoped-scope-weaken e (MkEnt n ty k) s ss)))
      ((Some b nm) (values (Cons _ (MkName nm n) s) (AddNameSome s nm n) (SSCons _ nm n s (HEHere n ty k e) (scoped-scope-weaken e (MkEnt n ty k) s ss))))))
  (let (erased rp1) (rules-plain-weaken n e n ty k r be (lt-succ n) rp))
  (let (many r2) (many ranks2) (many top2) (erased ar) (erased v2) (erased al2) (erased sr2) (erased rp2)
    (match many rule (((List (Rule)) r2) ((List (Nat)) ranks2) ((Nat) top2) ((AddRule r rule n r2) ar) ((ValidFrom r2 ranks2 r2 ranks2) v2) ((AllLt ranks2 top2) al2) ((ScopedRules (Cons (Ent) (MkEnt n ty k) e) r2) sr2)
        ((RulesPlain (Cons (Ent) (MkEnt n ty k) e) r2) rp2))
      ((None b) (values r ranks top (AddRuleNone r n) v al (scoped-rules-weaken e (MkEnt n ty k) r sr) rp1))
      ((Some b t)
        (match erased sm _
          ((SMSome b2 t2 st2)
            (match erased rk _
              ((ROkSome k0 t0 nd)
                (values (Cons _ (MkRule n t) r) (Cons _ top ranks) (Succ top) (AddRuleSome r t n)
                  (VFCons _ _ n t top r ranks (below-cons n e r ranks t top t top be (Zero) st2 (below-all r ranks top v al t)) (valid-cons n e r ranks r ranks t top be sr v))
                  (ALCons top ranks (Succ top) (lt-succ top) (all-lt-weaken top (Succ top) ranks (lt-weaken top (Succ top) (lt-succ top)) al))
                  (SRCons _ n t r (scoped-weaken e (MkEnt n ty k) (Zero) t st2) (scoped-rules-weaken e (MkEnt n ty k) r sr))
                  (RPCons _ n t r ty k (EntHere n ty k e) nd rp1)))))))))
  (values n (MkCtx (Succ n) s2 (Cons _ (MkEnt n ty k) e) r2 a l sa) (MintTo n s e r a l sa name ty k rule s2 r2 an ar)
    (MkWF _ _ _ _ _ _ _ ranks2 top2 v2 al2 (BECons (Succ n) n ty k e (lt-succ n) (bounded-ents-weaken n (Succ n) e (lt-weaken n (Succ n) (lt-succ n)) be))
      (SECons _ n ty k e (scoped-weaken e (MkEnt n ty k) (Zero) ty st) (scoped-ents-weaken e (MkEnt n ty k) e se)) ss2 sr2 (scoped-adts-weaken n e n ty k a be (lt-succ n) sa2)
      (scoped-maybe-weaken e (MkEnt n ty k) l sl) (scoped-weaken-list e (MkEnt n ty k) (Zero) sa ssa) (builtins-weaken e (MkEnt n ty k) bi) rp2)
    (GrewBy n s e r a l sa (Succ n) s2 (Cons _ (MkEnt n ty k) e) r2 a l sa (lt-weaken n (Succ n) (lt-succ n)) (ExtCons n e e n ty k (lt-succ n) (ExtRefl n e)))
    (MkEntIs _ _ _ _ _ _ _ n ty k (EntHere n ty k e))))

(def-fns _ $ many ctx-ents : (many (Ctx) ctx) -> (many (List (Ent)) ents) (erased (Ents ctx ents) p)
  (match many ctx _ ((MkCtx n s e r a l sa) (values e (EntsOf n s e r a l sa)))))
(def-fns _ $ many ctx-rules : (many (Ctx) ctx) -> (many (List (Rule)) rules) (erased (Rules ctx rules) p)
  (match many ctx _ ((MkCtx n s e r a l sa) (values r (RulesOf n s e r a l sa)))))
(def-fns _ $ many ctx-scope : (many (Ctx) ctx) -> (many (List (Name)) scope) (erased (Scope ctx scope) p)
  (match many ctx _ ((MkCtx n s e r a l sa) (values s (ScopeOf n s e r a l sa)))))
(def-fns _ $ many ctx-adts : (many (Ctx) ctx) -> (many (List (Adt)) adts) (erased (Adts ctx adts) p)
  (match many ctx _ ((MkCtx n s e r a l sa) (values a (AdtsOf n s e r a l sa)))))
(def-fns _ $ many ctx-level : (many (Ctx) ctx) (many (WF ctx) wf) -> (many (Maybe (Term)) level) (erased (Level ctx level) p) (erased (ScM ctx level) sc)
  (let-match many ctx (MkCtx n s e r a l sa))
  (let-match many wf (MkWF n0 s0 e0 r0 a0 l0 sa0 ranks top v al be se ss sr sa2 sl ssa bi rp))
  (values l (LevelOf n s e r a l sa) (MkScM _ _ _ _ _ _ _ l sl)))
(def-fns _ $ many ctx-subargs : (many (Ctx) ctx) (many (WF ctx) wf) -> (many (List (Term)) subargs) (erased (SubArgs ctx subargs) p) (erased (ScL ctx (Zero) subargs) sc)
  (let-match many ctx (MkCtx n s e r a l sa))
  (let-match many wf (MkWF n0 s0 e0 r0 a0 l0 sa0 ranks top v al be se ss sr sa2 sl ssa bi rp))
  (values sa (SubArgsOf n s e r a l sa) (MkScL _ _ _ _ _ _ _ _ sa ssa)))
; Leaving keeps the inner id supply and the outer everything else.
(def-fns _ $ many leave : (many (Ctx) inner) (many (Ctx) outer) (many (WF outer) wf) (erased (Grew outer inner) g) -> (many (Ctx) out) (erased (Leave inner outer out) p) (many (WF out) wf2) (erased (Grew outer out) g2)
  (let-match many inner (MkCtx n s e r a l sa))
  (let-match many outer (MkCtx n0 s0 e0 r0 a0 l0 sa0))
  (let-match many wf (MkWF m1 m2 m3 m4 m5 m6 m7 ranks top v al be se ss sr sa2 sl ssa bi rp))
  (let-match erased g (GrewBy k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 le ext))
  (values (MkCtx n s0 e0 r0 a0 l0 sa0) (LeaveTo n s e r a l sa n0 s0 e0 r0 a0 l0 sa0)
    (MkWF _ _ _ _ _ _ _ ranks top v al (bounded-ents-weaken n0 n e0 le be) se ss sr sa2 sl ssa bi rp)
    (GrewBy n0 s0 e0 r0 a0 l0 sa0 n s0 e0 r0 a0 l0 sa0 le (ExtRefl n0 e0))))
(def-fns _ $ many hide : (many (Ctx) inner) (many (WF inner) wf) (many (Ctx) outer) (many (WF outer) wf0) (erased (Grew outer inner) g) ->
    (many (List (Name)) s0) (erased (Scope outer s0) sc) (many (Ctx) out) (erased (Hide inner s0 out) p) (many (WF out) wf2) (erased (Grew outer out) g2) (erased (Grew inner out) gi)
  (let-match many inner (MkCtx n s e r a l sa))
  (let-match many outer (MkCtx n0 s0 e0 r0 a0 l0 sa0))
  (let-match many wf (MkWF m1 m2 m3 m4 m5 m6 m7 ranks top v al be se ss sr sa2 sl ssa bi rp))
  (let-match many wf0 (MkWF j1 j2 j3 j4 j5 j6 j7 ranks0 top0 v0 al0 be0 se0 ss0 sr0 sa20 sl0 ssa0 bi0 rp0))
  (let-match erased g (GrewBy k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 le ext))
  (values s0 (ScopeOf n0 s0 e0 r0 a0 l0 sa0) (MkCtx n s0 e r a l sa) (HideTo n s e r a l sa s0)
    (MkWF _ _ _ _ _ _ _ ranks top v al be se (scoped-scope-ext n0 e0 e s0 ss0 ext) sr sa2 sl ssa bi rp)
    (GrewBy n0 s0 e0 r0 a0 l0 sa0 n s0 e r a l sa le ext) (GrewBy n s e r a l sa n s0 e r a l sa (lt-succ n) (ExtRefl n e))))
(def-fns _ $ many enter : (many (Ctx) ctx) (many (WF ctx) wf) (many (Term) l2) (many (List (Term)) sa2) (erased (Sc ctx (Zero) l2) sl2) (erased (ScL ctx (Zero) sa2) ssa2) ->
    (many (Ctx) out) (erased (Enter ctx l2 sa2 out) p) (many (WF out) wf2) (erased (Grew ctx out) g)
  (let-match many ctx (MkCtx n s e r a l sa))
  (let-match many wf (MkWF m1 m2 m3 m4 m5 m6 m7 ranks top v al be se ss sr sad sl ssa bi rp))
  (let-match erased sl2 (MkSc q1 q2 q3 q4 q5 q6 q7 dq q8 st))
  (let-match erased ssa2 (MkScL z1 z2 z3 z4 z5 z6 z7 dq z8 sts))
  (values (MkCtx n s e r a (Some _ l2) sa2) (EnterTo n s e r a l sa l2 sa2)
    (MkWF _ _ _ _ _ _ _ ranks top v al be se ss sr sad (SMSome _ l2 st) sts bi rp)
    (GrewBy n s e r a l sa n s e r a (Some _ l2) sa2 (lt-succ n) (ExtRefl n e))))
(def-fns _ $ many add-adt : (many (Ctx) ctx) (many (WF ctx) wf) (many (Nat) tid) (many (List (Nat)) cids) (erased (Has ctx tid) ht) (erased (Ctors ctx cids) hc) ->
    (many (Ctx) out) (erased (AddAdt ctx (MkAdt tid cids) out) p) (many (WF out) wf2) (erased (Grew ctx out) g)
  (let-match many ctx (MkCtx n s e r a l sa))
  (let-match many wf (MkWF m1 m2 m3 m4 m5 m6 m7 ranks top v al be se ss sr sa2 sl ssa bi rp))
  (let-match erased ht (MkHas q1 q2 q3 q4 q5 q6 q7 q8 h))
  (let-match erased hc (MkCtors z1 z2 z3 z4 z5 z6 z7 z8 cs))
  (values (MkCtx n s e r (Cons _ (MkAdt tid cids) a) l sa) (AddAdtTo n s e r a l sa (MkAdt tid cids))
    (MkWF _ _ _ _ _ _ _ ranks top v al be se ss sr (SACons _ tid cids a h cs sa2) sl ssa bi rp)
    (GrewBy n s e r a l sa n s e r (Cons _ (MkAdt tid cids) a) l sa (lt-succ n) (ExtRefl n e))))

; Evidence carried from one context to one grown from it.
(def-fns _ $ erased sc-grew : (erased (Ctx) c1) (erased (Ctx) c2) (erased (Nat) d) (erased (Term) t) (erased (Grew c1 c2) g) (erased (Sc c1 d t) p) -> (erased (Sc c2 d t) q)
  (let-match erased g (GrewBy n0 s0 e0 r0 a0 l0 sa0 n1 s1 e1 r1 a1 l1 sa1 le ext))
  (let-match erased p (MkSc q1 q2 q3 q4 q5 q6 q7 q8 q9 st))
  (MkSc _ _ _ _ _ _ _ _ t (scoped-ext n0 e0 e1 d t st ext)))
(def-fns _ $ erased scl-grew : (erased (Ctx) c1) (erased (Ctx) c2) (erased (Nat) d) (erased (List (Term)) ts) (erased (Grew c1 c2) g) (erased (ScL c1 d ts) p) -> (erased (ScL c2 d ts) q)
  (let-match erased g (GrewBy n0 s0 e0 r0 a0 l0 sa0 n1 s1 e1 r1 a1 l1 sa1 le ext))
  (let-match erased p (MkScL q1 q2 q3 q4 q5 q6 q7 q8 q9 st))
  (MkScL _ _ _ _ _ _ _ _ ts (scoped-ext-list n0 e0 e1 d ts st ext)))
(def-fns _ $ erased sct-grew : (erased (Ctx) c1) (erased (Ctx) c2) (erased (Nat) d) (erased (List (Entry)) es) (erased (Nat) out) (erased (Grew c1 c2) g) (erased (ScT c1 d es out) p) -> (erased (ScT c2 d es out) q)
  (let-match erased g (GrewBy n0 s0 e0 r0 a0 l0 sa0 n1 s1 e1 r1 a1 l1 sa1 le ext))
  (let-match erased p (MkScT q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 st))
  (MkScT _ _ _ _ _ _ _ _ _ es (scoped-ext-tele n0 e0 e1 d es out st ext)))
(def-fns _ $ erased scs-grew : (erased (Ctx) c1) (erased (Ctx) c2) (erased (List (Maybe (Term))) sub) (erased (Nat) m) (erased (Grew c1 c2) g) (erased (ScS c1 sub m) p) -> (erased (ScS c2 sub m) q)
  (let-match erased g (GrewBy n0 s0 e0 r0 a0 l0 sa0 n1 s1 e1 r1 a1 l1 sa1 le ext))
  (let-match erased p (MkScS q1 q2 q3 q4 q5 q6 q7 q8 q9 st ly))
  (MkScS _ _ _ _ _ _ _ sub _ (scoped-ext-sub n0 e0 e1 sub st ext) ly))
(def-fns _ $ erased has-grew : (erased (Ctx) c1) (erased (Ctx) c2) (erased (Nat) x) (erased (Grew c1 c2) g) (erased (Has c1 x) p) -> (erased (Has c2 x) q)
  (let-match erased g (GrewBy n0 s0 e0 r0 a0 l0 sa0 n1 s1 e1 r1 a1 l1 sa1 le ext))
  (let-match erased p (MkHas q1 q2 q3 q4 q5 q6 q7 q8 h))
  (MkHas _ _ _ _ _ _ _ x (has-ent-ext n0 e0 e1 x h ext)))
(def-fns _ $ erased has-all-grew : (erased (Ctx) c1) (erased (Ctx) c2) (erased (List (Nat)) ids) (erased (Grew c1 c2) g) (erased (HasAll c1 ids) p) -> (erased (HasAll c2 ids) q)
  (let-match erased g (GrewBy n0 s0 e0 r0 a0 l0 sa0 n1 s1 e1 r1 a1 l1 sa1 le ext))
  (let-match erased p (MkHasAll q1 q2 q3 q4 q5 q6 q7 q8 h))
  (MkHasAll _ _ _ _ _ _ _ ids (all-has-ext n0 e0 e1 ids h ext)))
(def-fns _ $ erased ctors-grew : (erased (Ctx) c1) (erased (Ctx) c2) (erased (List (Nat)) ids) (many (WF c1) wf) (erased (Grew c1 c2) g) (erased (Ctors c1 ids) p) -> (erased (Ctors c2 ids) q)
  (let-match erased g (GrewBy n0 s0 e0 r0 a0 l0 sa0 n1 s1 e1 r1 a1 l1 sa1 le ext))
  (let-match erased p (MkCtors q1 q2 q3 q4 q5 q6 q7 q8 cs))
  (let-match many wf (MkWF m1 m2 m3 m4 m5 m6 m7 ranks top v al be se ss sr sa2 sl ssa bi rp))
  (MkCtors _ _ _ _ _ _ _ ids (all-ctor-ext n0 e0 e1 ids be cs ext)))
(def-fns _ $ erased cov-grew : (erased (Ctx) c0) (erased (List (Maybe (Nat))) acc) (erased (Ctx) c1) (erased (Nat) m) (erased (Cov c0 acc c1 m) c) -> (erased (Grew c0 c1) g)
  (let-match erased c (MkCov n0 s0 e0 r0 a0 l0 sa0 n1 s1 e1 r1 a1 l1 sa1 acc2 mm le cv ly))
  (GrewBy n0 s0 e0 r0 a0 l0 sa0 n1 s1 e1 r1 a1 l1 sa1 le (covers-ext n0 e0 acc e1 cv)))
(def-fns _ $ erased cov-mint : (erased (Ctx) c0) (erased (List (Maybe (Nat))) acc) (erased (Ctx) ctx) (erased (Maybe (String)) name) (erased (Term) ty) (erased (Kind) k) (erased (Maybe (Term)) rule) (erased (Nat) id) (erased (Ctx) out)
    (erased (Nat) m) (erased (Cov c0 acc ctx m) c) (erased (Mint ctx name ty k rule id out) mt) -> (erased (Cov c0 (Cons (Maybe (Nat)) (Some (Nat) id) acc) out (Succ m)) c2)
  (let-match erased c (MkCov n0 s0 e0 r0 a0 l0 sa0 n1 s1 e1 r1 a1 l1 sa1 acc2 mm le cv ly))
  (let-match erased mt (MintTo n s e r a l sa name2 ty2 k2 rule2 s2 r2 an ar))
  (MkCov _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (le-trans n0 n1 (Succ n1) le (lt-weaken n1 (Succ n1) (lt-succ n1)))
    (CovSome n0 e0 acc e1 id ty k le cv) (LaySome _ id acc m ly)))
(def-fns _ $ erased cov-refl : (erased (Ctx) ctx) -> (erased (Cov ctx (Nil (Maybe (Nat))) ctx (Zero)) c)
  (let-match erased ctx (MkCtx n s e r a l sa))
  (MkCov _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (lt-succ n) (CovNil n e) (LayNil _)))
; The wrappers' pieces, where a term's parts are wanted on their own.
(def-fns _ $ erased sc-ref : (erased (Ctx) ctx) (erased (Nat) x) (erased (Has ctx x) h) -> (erased (Sc ctx (Zero) (Ref x)) p)
  (let-match erased h (MkHas q1 q2 q3 q4 q5 q6 q7 q8 he))
  (MkSc _ _ _ _ _ _ _ _ (Ref x) (ScRef _ _ x he)))
(def-fns _ $ erased sc-tyapp : (erased (Ctx) ctx) (erased (Term) h) (erased (List (Entry)) ps) (erased (List (Term)) as) (erased (Nat) pd) (erased (Sc ctx (Zero) h) p) (erased (ScT ctx (Zero) ps pd) t)
    (erased (ScL ctx (Zero) as) q) (erased (LenEq (Term) (Entry) as ps) n) -> (erased (Sc ctx (Zero) (TyApp h ps as)) r)
  (let-match erased p (MkSc q1 q2 q3 q4 q5 q6 q7 dq q8 sh))
  (let-match erased t (MkScT y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 sps))
  (let-match erased q (MkScL z1 z2 z3 z4 z5 z6 z7 dq z8 sas))
  (MkSc _ _ _ _ _ _ _ _ (TyApp h ps as) (ScTyApp _ _ h ps as _ sh sps sas n)))
(def-fns _ $ erased sc-valapp : (erased (Ctx) ctx) (erased (Term) h) (erased (List (Entry)) ps) (erased (Term) r) (erased (List (Term)) as) (erased (Nat) pd) (erased (Sc ctx (Zero) h) p) (erased (ScT ctx (Zero) ps pd) t)
    (erased (Sc ctx pd r) pr) (erased (ScL ctx (Zero) as) q) (erased (LenEq (Term) (Entry) as ps) n) -> (erased (Sc ctx (Zero) (ValApp h ps r as)) s)
  (let-match erased p (MkSc q1 q2 q3 q4 q5 q6 q7 dq q8 sh))
  (let-match erased t (MkScT y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 sps))
  (let-match erased pr (MkSc x1 x2 x3 x4 x5 x6 x7 x8 x9 sr))
  (let-match erased q (MkScL z1 z2 z3 z4 z5 z6 z7 dq z8 sas))
  (MkSc _ _ _ _ _ _ _ _ (ValApp h ps r as) (ScValApp _ _ h ps r as _ sh sps sr sas n)))
(def-fns _ $ erased sc-univ : (erased (Ctx) ctx) -> (erased (Sc ctx (Zero) (Univ)) p)
  (let-match erased ctx (MkCtx n s e r a l sa))
  (MkSc _ _ _ _ _ _ _ _ (Univ) (ScUniv _ _)))
(def-fns _ $ erased sc-level-ty : (erased (Ctx) ctx) (many (WF ctx) wf) -> (erased (Sc ctx (Zero) level-ty) p)
  (let-match many wf (MkWF n s e r a l sa ranks top v al be se ss sr sa2 sl ssa bi rp))
  (let-match erased bi (MkBuiltins z h0 h1 h2))
  (MkSc _ _ _ _ _ _ _ _ _ (ScTyApp _ _ _ _ _ _ (ScRef _ _ _ h0) (ScTNil _ _) (ScNil _ _) (LENil _ _))))
(def-fns _ $ erased sc-predates : (erased (Ctx) ctx) (many (WF ctx) wf) (erased (Term) ty) (erased (Term) av) (erased (Term) lv) (erased (Sc ctx (Zero) ty) pty) (erased (Sc ctx (Zero) av) pav) (erased (Sc ctx (Zero) lv) plv) ->
    (erased (Sc ctx (Zero) (TyApp (Ref (Succ (Zero))) predates-ps (Cons (Term) ty (Cons (Term) av (Cons (Term) lv (Nil (Term))))))) p)
  (let-match many wf (MkWF n s e r a l sa ranks top v al be se ss sr sa2 sl ssa bi rp))
  (let-match erased bi (MkBuiltins z h0 h1 h2))
  (let-match erased pty (MkSc q1 q2 q3 q4 q5 q6 q7 q8 q9 sty))
  (let-match erased pav (MkSc y1 y2 y3 y4 y5 y6 y7 y8 y9 sav))
  (let-match erased plv (MkSc z1 z2 z3 z4 z5 z6 z7 z8 z9 slv))
  (MkSc _ _ _ _ _ _ _ _ _ (ScTyApp _ _ _ _ _ _ (ScRef _ _ _ h1)
    (ScTCons _ _ _ _ _ _ _ (ScUniv _ _) (ScTCons _ _ _ _ _ _ _ (ScBound _ _ _ (LtZ _)) (ScTCons _ _ _ _ _ _ _ (ScTyApp _ _ _ _ _ _ (ScRef _ _ _ h0) (ScTNil _ _) (ScNil _ _) (LENil _ _)) (ScTNil _ _))))
    (ScCons _ _ _ _ sty (ScCons _ _ _ _ sav (ScCons _ _ _ _ slv (ScNil _ _)))) (LECons _ _ _ _ _ _ (LECons _ _ _ _ _ _ (LECons _ _ _ _ _ _ (LENil _ _)))))))
(def-fns _ $ erased sc-subterm : (erased (Ctx) ctx) (many (WF ctx) wf) (erased (Term) ta) (erased (Term) av) (erased (Term) tb) (erased (Term) bv) (erased (Sc ctx (Zero) ta) pta) (erased (Sc ctx (Zero) av) pav)
    (erased (Sc ctx (Zero) tb) ptb) (erased (Sc ctx (Zero) bv) pbv) ->
    (erased (Sc ctx (Zero) (TyApp (Ref (Succ (Succ (Zero)))) subterm-ps (Cons (Term) ta (Cons (Term) av (Cons (Term) tb (Cons (Term) bv (Nil (Term)))))))) p)
  (let-match many wf (MkWF n s e r a l sa ranks top v al be se ss sr sa2 sl ssa bi rp))
  (let-match erased bi (MkBuiltins z h0 h1 h2))
  (let-match erased pta (MkSc q1 q2 q3 q4 q5 q6 q7 q8 q9 sta))
  (let-match erased pav (MkSc y1 y2 y3 y4 y5 y6 y7 y8 y9 sav))
  (let-match erased ptb (MkSc z1 z2 z3 z4 z5 z6 z7 z8 z9 stb))
  (let-match erased pbv (MkSc x1 x2 x3 x4 x5 x6 x7 x8 x9 sbv))
  (MkSc _ _ _ _ _ _ _ _ _ (ScTyApp _ _ _ _ _ _ (ScRef _ _ _ h2)
    (ScTCons _ _ _ _ _ _ _ (ScUniv _ _) (ScTCons _ _ _ _ _ _ _ (ScBound _ _ _ (LtZ _)) (ScTCons _ _ _ _ _ _ _ (ScUniv _ _) (ScTCons _ _ _ _ _ _ _ (ScBound _ _ _ (LtZ _)) (ScTNil _ _)))))
    (ScCons _ _ _ _ sta (ScCons _ _ _ _ sav (ScCons _ _ _ _ stb (ScCons _ _ _ _ sbv (ScNil _ _))))) (LECons _ _ _ _ _ _ (LECons _ _ _ _ _ _ (LECons _ _ _ _ _ _ (LECons _ _ _ _ _ _ (LENil _ _))))))))
(def-fns _ $ erased sc-builtin : (erased (Ctx) ctx) (many (WF ctx) wf) -> (erased (Has ctx (Succ (Zero))) h1) (erased (Has ctx (Succ (Succ (Zero)))) h2)
  (let-match many wf (MkWF n s e r a l sa ranks top v al be se ss sr sa2 sl ssa bi rp))
  (let-match erased bi (MkBuiltins z h0 hh1 hh2))
  (values (MkHas _ _ _ _ _ _ _ _ hh1) (MkHas _ _ _ _ _ _ _ _ hh2)))
(def-fns _ $ erased sc-fn : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs) (erased (Nat) d1) (erased (Nat) d2) (erased (Sc ctx (Zero) l) p) (erased (ScT ctx (Zero) ps d1) q)
    (erased (ScT ctx d1 rs d2) r) -> (erased (Sc ctx (Zero) (Fn l ps rs)) s)
  (let-match erased p (MkSc q1 q2 q3 q4 q5 q6 q7 q8 q9 sl))
  (let-match erased q (MkScT z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 sps))
  (let-match erased r (MkScT y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 srs))
  (MkSc _ _ _ _ _ _ _ _ (Fn l ps rs) (ScFn _ _ l ps rs _ _ sl sps srs)))
(def-fns _ $ erased sc-tyctor : (erased (Ctx) ctx) (erased (List (Entry)) ps) (erased (Nat) d1) (erased (ScT ctx (Zero) ps d1) q) -> (erased (Sc ctx (Zero) (TyCtor ps)) s)
  (let-match erased q (MkScT z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 sps))
  (MkSc _ _ _ _ _ _ _ _ (TyCtor ps) (ScTyCtor _ _ ps _ sps)))
(def-fns _ $ erased sc-valctor : (erased (Ctx) ctx) (erased (List (Entry)) ps) (erased (Term) r) (erased (Nat) d1) (erased (ScT ctx (Zero) ps d1) q) (erased (Sc ctx d1 r) p) -> (erased (Sc ctx (Zero) (ValCtor ps r)) s)
  (let-match erased q (MkScT z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 sps))
  (let-match erased p (MkSc q1 q2 q3 q4 q5 q6 q7 q8 q9 sr))
  (MkSc _ _ _ _ _ _ _ _ (ValCtor ps r) (ScValCtor _ _ ps r _ sps sr)))
(def-fns _ $ erased sc-fn-parts : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs) (erased (Sc ctx (Zero) (Fn l ps rs)) s) ->
    (erased (Nat) d1) (erased (Nat) d2) (erased (Sc ctx (Zero) l) p) (erased (ScT ctx (Zero) ps d1) q) (erased (ScT ctx d1 rs d2) r)
  (let-match erased s (MkSc q1 q2 q3 q4 q5 q6 q7 q8 q9 sf))
  (match erased sf _ ((ScFn a dq l0 ps0 rs0 e1 e2 sl sps srs) (values e1 e2 (MkSc _ _ _ _ _ _ _ _ l sl) (MkScT _ _ _ _ _ _ _ _ _ ps sps) (MkScT _ _ _ _ _ _ _ _ _ rs srs)))))
(def-fns _ $ erased sc-tyctor-parts : (erased (Ctx) ctx) (erased (List (Entry)) ps) (erased (Sc ctx (Zero) (TyCtor ps)) s) -> (erased (Nat) d1) (erased (ScT ctx (Zero) ps d1) q)
  (let-match erased s (MkSc q1 q2 q3 q4 q5 q6 q7 q8 q9 sf))
  (match erased sf _ ((ScTyCtor a dq ps0 e1 sps) (values e1 (MkScT _ _ _ _ _ _ _ _ _ ps sps)))))
(def-fns _ $ erased sc-valctor-parts : (erased (Ctx) ctx) (erased (List (Entry)) ps) (erased (Term) r) (erased (Sc ctx (Zero) (ValCtor ps r)) s) -> (erased (Nat) d1) (erased (ScT ctx (Zero) ps d1) q) (erased (Sc ctx d1 r) p)
  (let-match erased s (MkSc q1 q2 q3 q4 q5 q6 q7 q8 q9 sf))
  (match erased sf _ ((ScValCtor a dq ps0 r0 e1 sps sr) (values e1 (MkScT _ _ _ _ _ _ _ _ _ ps sps) (MkSc _ _ _ _ _ _ _ _ r sr)))))
(def-fns _ $ erased sc-app-parts : (erased (Ctx) ctx) (erased (Term) b) (erased (Term) h) (erased (List (Term)) as) (erased (AppParts b h as) ap) (erased (Sc ctx (Zero) b) s) -> (erased (Sc ctx (Zero) h) p) (erased (ScL ctx (Zero) as) q)
  (let-match erased s (MkSc q1 q2 q3 q4 q5 q6 q7 dq q8 sf))
  (match erased ap _
    ((APTy h0 ps as0) (match erased sf _ ((ScTyApp a dq h1 ps1 as1 o1 sh st sas n) (values (MkSc _ _ _ _ _ _ _ _ h sh) (MkScL _ _ _ _ _ _ _ _ as sas)))))
    ((APVal h0 ps r as0) (match erased sf _ ((ScValApp a dq h1 ps1 r1 as1 o1 sh st sr sas n) (values (MkSc _ _ _ _ _ _ _ _ h sh) (MkScL _ _ _ _ _ _ _ _ as sas)))))))
(def-fns _ $ erased scl-parts : (erased (Ctx) ctx) (erased (Term) t) (erased (List (Term)) ts) (erased (ScL ctx (Zero) (Cons (Term) t ts)) s) -> (erased (Sc ctx (Zero) t) p) (erased (ScL ctx (Zero) ts) q)
  (let-match erased s (MkScL q1 q2 q3 q4 q5 q6 q7 dq q8 sf))
  (match erased sf _ ((ScCons a dq t0 ts0 st sts) (values (MkSc _ _ _ _ _ _ _ _ t st) (MkScL _ _ _ _ _ _ _ _ ts sts)))))
(def-fns _ $ erased scl-cons : (erased (Ctx) ctx) (erased (Term) t) (erased (List (Term)) ts) (erased (Sc ctx (Zero) t) p) (erased (ScL ctx (Zero) ts) q) -> (erased (ScL ctx (Zero) (Cons (Term) t ts)) s)
  (let-match erased p (MkSc q1 q2 q3 q4 q5 q6 q7 dq q8 st))
  (let-match erased q (MkScL z1 z2 z3 z4 z5 z6 z7 dq z8 sts))
  (MkScL _ _ _ _ _ _ _ _ (Cons _ t ts) (ScCons _ _ t ts st sts)))
(def-fns _ $ erased scl-nil : (erased (Ctx) ctx) -> (erased (ScL ctx (Zero) (Nil (Term))) s)
  (let-match erased ctx (MkCtx n s e r a l sa))
  (MkScL _ _ _ _ _ _ _ _ (Nil _) (ScNil _ _)))
(def-fns _ $ erased sct-parts : (erased (Ctx) ctx) (erased (Nat) d) (erased (Nat) out) (erased (Bool) s) (erased (Bool) i) (erased (Term) t) (erased (List (Entry)) es) (erased (ScT ctx d (Cons (Entry) (MkEntry s i t) es) out) st) ->
    (erased (Sc ctx d t) p) (erased (ScT ctx (Succ d) es out) q)
  (let-match erased st (MkScT q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 sf))
  (match erased sf _ ((ScTCons a dq s0 i0 t0 es0 oq st0 sts) (values (MkSc _ _ _ _ _ _ _ _ t st0) (MkScT _ _ _ _ _ _ _ _ _ es sts)))))
(def-fns _ $ erased scs-nil : (erased (Ctx) ctx) -> (erased (ScS ctx (Nil (Maybe (Term))) (Zero)) s)
  (let-match erased ctx (MkCtx n s e r a l sa))
  (MkScS _ _ _ _ _ _ _ (Nil _) _ (ScSNil _) (LayNil _)))
(def-fns _ $ erased scs-cons : (erased (Ctx) ctx) (erased (Term) t) (erased (List (Maybe (Term))) sub) (erased (Nat) m) (erased (Sc ctx (Zero) t) p) (erased (ScS ctx sub m) q) ->
    (erased (ScS ctx (Cons (Maybe (Term)) (Some (Term) t) sub) (Succ m)) s)
  (let-match erased p (MkSc q1 q2 q3 q4 q5 q6 q7 q8 q9 st))
  (let-match erased q (MkScS z1 z2 z3 z4 z5 z6 z7 z8 z9 sts ly))
  (MkScS _ _ _ _ _ _ _ _ _ (ScSSome _ t sub st sts) (LaySome _ t sub m ly)))
(def-fns _ $ erased scm-none : (erased (Ctx) ctx) -> (erased (ScM ctx (None (Term))) s)
  (let-match erased ctx (MkCtx n s e r a l sa))
  (MkScM _ _ _ _ _ _ _ (None _) (SMNone _)))
(def-fns _ $ erased scm-some : (erased (Ctx) ctx) (erased (Term) t) (erased (Sc ctx (Zero) t) p) -> (erased (ScM ctx (Some (Term) t)) s)
  (let-match erased p (MkSc q1 q2 q3 q4 q5 q6 q7 dq q8 st))
  (MkScM _ _ _ _ _ _ _ (Some _ t) (SMSome _ t st)))
(def-fns _ $ erased entis-has : (erased (Ctx) ctx) (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (EntIs ctx x ty k) p) -> (erased (Has ctx x) h)
  (let-match erased p (MkEntIs q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 eo))
  (MkHas _ _ _ _ _ _ _ x (ent-of-has _ x ty k eo)))
(def-fns _ $ erased ctor-of-entis : (erased (Ctx) ctx) (erased (Nat) c) (erased (List (Entry)) fs) (erased (Term) r) (erased (EntIs ctx c (ValCtor fs r) (KDecl)) p) -> (erased (Ctor ctx c) h)
  (let-match erased p (MkEntIs q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 eo))
  (MkCtor _ _ _ _ _ _ _ c fs r eo))
(def-fns _ $ erased tycon-of-entis : (erased (Ctx) ctx) (erased (Nat) t) (erased (List (Entry)) ps) (erased (EntIs ctx t (TyCtor ps) (KDecl)) p) -> (erased (Tycon ctx t) h)
  (let-match erased p (MkEntIs q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 eo))
  (MkTycon _ _ _ _ _ _ _ t ps eo))
(def-fns _ $ erased ctor-has : (erased (Ctx) ctx) (erased (Nat) c) (erased (Ctor ctx c) p) -> (erased (Has ctx c) h)
  (let-match erased p (MkCtor q1 q2 q3 q4 q5 q6 q7 q8 fs r eo))
  (MkHas _ _ _ _ _ _ _ c (ent-of-has _ c _ _ eo)))
(def-fns _ $ erased tycon-has : (erased (Ctx) ctx) (erased (Nat) t) (erased (Tycon ctx t) p) -> (erased (Has ctx t) h)
  (let-match erased p (MkTycon q1 q2 q3 q4 q5 q6 q7 q8 ps eo))
  (MkHas _ _ _ _ _ _ _ t (ent-of-has _ t _ _ eo)))
(def-fns _ $ erased scm-some-parts : (erased (Ctx) ctx) (erased (Term) t) (erased (ScM ctx (Some (Term) t)) p) -> (erased (Sc ctx (Zero) t) s)
  (let-match erased p (MkScM q1 q2 q3 q4 q5 q6 q7 q8 sm))
  (match erased sm _ ((SMSome a t0 st) (MkSc _ _ _ _ _ _ _ _ t st))))
(def-fns _ $ erased ctors-nil : (erased (Ctx) ctx) -> (erased (Ctors ctx (Nil (Nat))) h)
  (let-match erased ctx (MkCtx n s e r a l sa))
  (MkCtors _ _ _ _ _ _ _ (Nil _) (ACNil _)))
(def-fns _ $ erased ctors-cons : (erased (Ctx) ctx) (erased (Nat) c) (erased (List (Nat)) ids) (erased (Ctor ctx c) p) (erased (Ctors ctx ids) q) -> (erased (Ctors ctx (Cons (Nat) c ids)) h)
  (let-match erased p (MkCtor q1 q2 q3 q4 q5 q6 q7 q8 fs r eo))
  (let-match erased q (MkCtors z1 z2 z3 z4 z5 z6 z7 z8 cs))
  (MkCtors _ _ _ _ _ _ _ _ (ACCons _ c ids fs r eo cs)))
(def-fns _ $ erased has-all-parts : (erased (Ctx) ctx) (erased (Nat) x) (erased (List (Nat)) ids) (erased (HasAll ctx (Cons (Nat) x ids)) h) -> (erased (Has ctx x) p) (erased (HasAll ctx ids) q)
  (let-match erased h (MkHasAll q1 q2 q3 q4 q5 q6 q7 q8 ah))
  (match erased ah _ ((AHCons a x0 ids0 hx hids) (values (MkHas _ _ _ _ _ _ _ x hx) (MkHasAll _ _ _ _ _ _ _ ids hids)))))
(def-fns _ $ erased has-all-cons : (erased (Ctx) ctx) (erased (Nat) x) (erased (List (Nat)) ids) (erased (Has ctx x) p) (erased (HasAll ctx ids) q) -> (erased (HasAll ctx (Cons (Nat) x ids)) h)
  (let-match erased p (MkHas q1 q2 q3 q4 q5 q6 q7 q8 hx))
  (let-match erased q (MkHasAll z1 z2 z3 z4 z5 z6 z7 z8 hids))
  (MkHasAll _ _ _ _ _ _ _ _ (AHCons _ x ids hx hids)))
(def-fns _ $ erased has-all-nil : (erased (Ctx) ctx) -> (erased (HasAll ctx (Nil (Nat))) h)
  (let-match erased ctx (MkCtx n s e r a l sa))
  (MkHasAll _ _ _ _ _ _ _ (Nil _) (AHNil _)))
(def-fns _ $ erased ctors-parts : (erased (Ctx) ctx) (erased (Nat) c) (erased (List (Nat)) ids) (erased (Ctors ctx (Cons (Nat) c ids)) h) -> (erased (Ctors ctx ids) q)
  (let-match erased h (MkCtors q1 q2 q3 q4 q5 q6 q7 q8 ah))
  (match erased ah _ ((ACCons a c0 ids0 fs r e hids) (MkCtors _ _ _ _ _ _ _ ids hids))))
(def-fns _ $ erased ctors-head : (erased (Ctx) ctx) (erased (Nat) c) (erased (List (Nat)) ids) (erased (Ctors ctx (Cons (Nat) c ids)) h) -> (erased (Ctor ctx c) q)
  (let-match erased h (MkCtors q1 q2 q3 q4 q5 q6 q7 q8 ah))
  (match erased ah _ ((ACCons a c0 ids0 fs r e hids) (MkCtor _ _ _ _ _ _ _ c fs r e))))
(def-fns _ $ erased ctors-mem : (erased (Ctx) ctx) (erased (Nat) c) (erased (List (Nat)) ids) (erased (Ctors ctx ids) h) (subterm erased (Mem c ids) m) -> (erased (Ctor ctx c) q)
  (match erased m _
    ((MemHere x xs) (ctors-head ctx c xs h))
    ((MemThere x y xs p) (ctors-mem ctx c xs (ctors-parts ctx y xs h) p))))
(def-fns _ $ erased nth-has : (erased (Ctx) ctx) (erased (List (Nat)) ids) (erased (Nat) i) (erased (Nat) x) (erased (HasAll ctx ids) h) (subterm erased (Nth (Nat) ids i x) p) -> (erased (Has ctx x) q)
  (match erased p _
    ((NthHere a x0 rest) (let (erased hx) (erased hrest) (has-all-parts ctx x rest h)) hx)
    ((NthThere a y rest i2 x0 p2) (let (erased hy) (erased hrest) (has-all-parts ctx y rest h)) (nth-has ctx rest i2 x hrest p2))))
(def-fns _ $ erased ctor-grew : (erased (Ctx) c1) (erased (Ctx) c2) (erased (Nat) c) (many (WF c1) wf) (erased (Grew c1 c2) g) (erased (Ctor c1 c) p) -> (erased (Ctor c2 c) q)
  (let-match erased g (GrewBy n0 s0 e0 r0 a0 l0 sa0 n1 s1 e1 r1 a1 l1 sa1 le ext))
  (let-match erased p (MkCtor q1 q2 q3 q4 q5 q6 q7 q8 fs r eo))
  (let-match many wf (MkWF m1 m2 m3 m4 m5 m6 m7 ranks top v al be se ss sr sa2 sl ssa bi rp))
  (MkCtor _ _ _ _ _ _ _ c fs r (ent-of-ext n0 e0 e1 c (ValCtor fs r) (KDecl) be eo ext)))

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
(def-fns _ $ many nones : (subterm many (List (Entry)) es) -> (many (List (Maybe (String))) names) (erased (Nones es names) p) (erased (LenEq (Entry) (Maybe (String)) es names) l)
  (match many es _
    ((Nil a) (values (Nil _) (NonesNil) (LENil _ _)))
    ((Cons a e rest) (let (many names) (erased p) (erased l) (nones rest)) (values (Cons _ (None _) names) (NonesCons e rest names p) (LECons _ _ e (None _) rest names l)))))
(def-fns _ $ many append : (subterm many (List (Nat)) xs) (many (List (Nat)) ys) -> (many (List (Nat)) out) (erased (Append xs ys out) p)
  (match many xs _
    ((Nil a) (values ys (AppendNil ys)))
    ((Cons a x rest) (let (many out) (erased p) (append rest ys)) (values (Cons _ x out) (AppendCons x rest ys out p)))))
(def-fns _ $ many marked : (subterm many (List (Entry)) tele) (many (List (Nat)) ids) (erased (LenEq (Entry) (Nat) tele ids) le) -> (many (List (Term)) out) (erased (Marked tele ids out) p)
  (match many tele _
    ((Nil a) (match many ids _ ((Nil b) (values (Nil _) (MarkedNil))) ((Cons b x rest) (match erased le _))))
    ((Cons a e es)
      (match many ids _
        ((Nil b) (match erased le _))
        ((Cons b x rest)
          (match many e _
            ((MkEntry s i t)
              (match erased le _
                ((LECons c d g h k m le2)
                  (let (many out) (erased p) (marked es rest le2))
                  (match many s _
                    ((BTrue) (values (Cons _ (Ref x) out) (MarkedYes i t es x rest out p)))
                    ((BFalse) (values out (MarkedNo i t es x rest out p)))))))))))))

; Field names of a branch pattern: atoms, or a malformed shape.
(def-adts
  (AtomNamesDec : ((List (Raw)) raws) -> Type
    enum
    (many MkAtomNames : (erased (List (Raw)) raws) (many (List (Maybe (String))) names) (erased (AtomNames raws names) p) (erased (LenEq (Raw) (Maybe (String)) raws names) l) -> (AtomNamesDec raws))
    (many AtomNamesStuck : (erased (List (Raw)) raws) -> (AtomNamesDec raws))))
(def-fns _ $ many atom-names : (subterm many (List (Raw)) raws) -> (many (AtomNamesDec raws) r)
  (match many raws _
    ((Nil a) (MkAtomNames _ (Nil _) (ANNil) (LENil _ _)))
    ((Cons a r rest)
      (match many r _
        ((RAtom x)
          (match many (atom-names rest) _
            ((AtomNamesStuck b) (AtomNamesStuck _))
            ((MkAtomNames b names p l) (MkAtomNames _ (Cons _ (Some _ x) names) (ANCons x rest names p) (LECons _ _ r (Some _ x) rest names l)))))
        (else (AtomNamesStuck _))))))

(def-adts
  (MemDec : ((Nat) x) ((List (Nat)) xs) -> Type
    enum
    (many MemYes : (erased (Nat) x) (erased (List (Nat)) xs) (erased (Mem x xs) p) -> (MemDec x xs))
    (many MemNo : (erased (Nat) x) (erased (List (Nat)) xs) (erased (NotMem x xs) p) -> (MemDec x xs)))
  (OneDec : ((List (Nat)) ids) -> Type
    enum
    (many OneYes : (many (Nat) x) -> (OneDec (Cons (Nat) x (Nil (Nat)))))
    (many OneNo : (erased (List (Nat)) ids) (erased (NotOne ids) p) -> (OneDec ids)))
  (NotLenDec : ((Nat) n) ((List (Term)) as) -> Type
    enum
    (many LenIs : (erased (Nat) n) (erased (List (Term)) as) (erased (Length (Term) as n) p) -> (NotLenDec n as))
    (many LenIsNot : (erased (Nat) n) (erased (List (Term)) as) (erased (NotLen n as) p) -> (NotLenDec n as))))
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
(def-fns _ $ many one-dec : (many (List (Nat)) ids) -> (many (OneDec ids) r)
  (match many ids _
    ((Nil a) (OneNo _ (NotOneNil)))
    ((Cons a x rest)
      (match many rest _
        ((Nil b) (OneYes x))
        ((Cons b y more) (OneNo _ (NotOneMore x y more)))))))
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
(def-fns _ $ erased len-eq-trans : (erased Type A) (erased Type B) (erased Type C) (erased (List A) xs) (erased (List B) ys) (erased (List C) zs) (subterm erased (LenEq A B xs ys) p) (erased (LenEq B C ys zs) q) ->
    (erased (LenEq A C xs zs) r)
  (match erased p _
    ((LENil a b) (match erased q _ ((LENil c d) (LENil _ _))))
    ((LECons a b x y xs2 ys2 p2) (match erased q _ ((LECons c d y2 z ys3 zs2 q2) (LECons _ _ x z xs2 zs2 (len-eq-trans _ _ _ xs2 ys2 zs2 p2 q2)))))))
(def-fns _ $ erased len-eq-sym : (erased Type A) (erased Type B) (erased (List A) xs) (erased (List B) ys) (subterm erased (LenEq A B xs ys) p) -> (erased (LenEq B A ys xs) q)
  (match erased p _
    ((LENil a b) (LENil _ _))
    ((LECons a b x y xs2 ys2 p2) (LECons _ _ y x ys2 xs2 (len-eq-sym _ _ xs2 ys2 p2)))))
; A marked position of a telescope has an id in a list of the telescope's length.
(def-fns _ $ erased nth-marked : (erased (List (Entry)) ps) (erased (List (Nat)) ids) (erased (Nat) i) (erased (Nat) j) (subterm erased (MarkedIndex ps i j) mi) (erased (LenEq (Entry) (Nat) ps ids) le) (erased (NoNth (Nat) ids i) nn) ->
    (erased (False) f)
  (match erased mi _
    ((MIHere is t es) (match erased le _ ((LECons a b x y xs ys p) (match erased nn _))))
    ((MIYes is t es i2 j2 p) (match erased le _ ((LECons a b x y xs ys q) (match erased nn _ ((NoNthCons c d rest i3 nn2) (nth-marked es ys i2 j2 p q nn2))))))
    ((MINo is t es i2 j2 p) (match erased le _ ((LECons a b x y xs ys q) (match erased nn _ ((NoNthCons c d rest i3 nn2) (nth-marked es ys i2 j2 p q nn2))))))))

; Scope of what the helpers build.
(def-fns _ $ erased sc-somes : (erased (Ctx) ctx) (erased (List (Term)) as) (erased (List (Maybe (Term))) sub) (erased (Nat) m) (erased (Length (Term) as m) ln) (erased (ScL ctx (Zero) as) p) (erased (Somes as sub) so) ->
    (erased (ScS ctx sub m) q)
  (let-match erased p (MkScL q1 q2 q3 q4 q5 q6 q7 q8 q9 sas))
  (MkScS _ _ _ _ _ _ _ _ _ (somes-scoped _ as sub sas so) (somes-layout as sub m so ln)))
(def-fns _ $ erased refs-scoped : (erased (Ctx) ctx) (erased (List (Nat)) ids) (erased (List (Term)) ts) (erased (HasAll ctx ids) h) (subterm erased (Refs ids ts) rf) -> (erased (ScL ctx (Zero) ts) q)
  (match erased rf _
    ((RefsNil) (scl-nil ctx))
    ((RefsCons x rest ts2 p)
      (let (erased hx) (erased hrest) (has-all-parts ctx x rest h))
      (scl-cons ctx (Ref x) ts2 (sc-ref ctx x hx) (refs-scoped ctx rest ts2 hrest p)))))
(def-fns _ $ erased marked-scoped : (erased (Ctx) ctx) (erased (List (Entry)) tele) (erased (List (Nat)) ids) (erased (List (Term)) out) (erased (HasAll ctx ids) h) (subterm erased (Marked tele ids out) mk) -> (erased (ScL ctx (Zero) out) q)
  (match erased mk _
    ((MarkedNil) (scl-nil ctx))
    ((MarkedYes i t es x rest out2 p)
      (let (erased hx) (erased hrest) (has-all-parts ctx x rest h))
      (scl-cons ctx (Ref x) out2 (sc-ref ctx x hx) (marked-scoped ctx es rest out2 hrest p)))
    ((MarkedNo i t es x rest out2 p)
      (let (erased hx) (erased hrest) (has-all-parts ctx x rest h))
      (marked-scoped ctx es rest out2 hrest p))))
(def-fns _ $ erased sc-subst : (erased (Ctx) ctx) (erased (List (Maybe (Term))) sub) (erased (Nat) m) (erased (Term) t) (erased (Term) u) (erased (ScS ctx sub m) ss) (erased (Sc ctx m t) st) (erased (Subst sub t u) sb) ->
    (erased (Sc ctx (Zero) u) su)
  (let-match erased ss (MkScS q1 q2 q3 q4 q5 q6 q7 q8 q9 ssub ly))
  (let-match erased st (MkSc z1 z2 z3 z4 z5 z6 z7 z8 z9 sct))
  (MkSc _ _ _ _ _ _ _ _ u (subst-scoped _ sub (Zero) m t u ssub ly sct sb)))
(def-fns _ $ erased scs-length : (erased (Ctx) ctx) (erased (List (Maybe (Term))) sub) (erased (Nat) m) (erased (ScS ctx sub m) ss) -> (erased (Length (Maybe (Term)) sub m) ln)
  (let-match erased ss (MkScS q1 q2 q3 q4 q5 q6 q7 q8 q9 ssub ly))
  (layout-length _ sub (Zero) m ly))
(def-fns _ $ erased sc-closed : (erased (Ctx) ctx) (erased (Nat) d) (erased (Term) t) (erased (Sc ctx d t) st) -> (erased (Closed d t) c)
  (let-match erased st (MkSc q1 q2 q3 q4 q5 q6 q7 q8 q9 sct))
  (scoped-closed _ d t sct))
(def-fns _ $ erased sc-abstract : (erased (Ctx) ctx0) (erased (List (Maybe (Nat))) acc) (erased (Ctx) ctx) (erased (Nat) m) (erased (Term) t) (erased (Term) u) (erased (Cov ctx0 acc ctx m) c) (erased (Sc ctx (Zero) t) st)
    (erased (Abstract acc t u) ab) -> (erased (Sc ctx0 m u) su)
  (let-match erased c (MkCov n0 s0 e0 r0 a0 l0 sa0 n1 s1 e1 r1 a1 l1 sa1 acc2 mm le cv ly))
  (let-match erased st (MkSc z1 z2 z3 z4 z5 z6 z7 z8 z9 sct))
  (MkSc _ _ _ _ _ _ _ _ u (abstract-covers n0 e0 acc e1 (Zero) m t u cv ly sct ab)))

; The binders a telescope's ids become cover the same entries as the accumulated ids do, innermost first.
(def-adts
  (CoversRev : ((Nat) n0) ((List (Ent)) e0) ((List (Maybe (Nat))) acc) ((List (Nat)) ids) ((List (Ent)) e1) -> Type
    enum
    (many CvRNil : (erased (Nat) n0) (erased (List (Ent)) e0) (erased (List (Maybe (Nat))) acc) (erased (List (Ent)) e1) (erased (Covers n0 e0 acc e1) c) -> (CoversRev n0 e0 acc (Nil (Nat)) e1))
    (many CvRCons : (erased (Nat) n0) (erased (List (Ent)) e0) (erased (List (Maybe (Nat))) acc) (erased (Nat) x) (erased (List (Nat)) ids) (erased (List (Ent)) e1)
       (erased (CoversRev n0 e0 (Cons (Maybe (Nat)) (Some (Nat) x) acc) ids e1) c) -> (CoversRev n0 e0 acc (Cons (Nat) x ids) e1)))
  (CovRev : ((Ctx) ctx0) ((List (Maybe (Nat))) acc) ((List (Nat)) ids) ((Ctx) ctx1) -> Type
    enum
    (many MkCovRev : (erased (Nat) n0) (erased (List (Name)) s0) (erased (List (Ent)) e0) (erased (List (Rule)) r0) (erased (List (Adt)) a0) (erased (Maybe (Term)) l0) (erased (List (Term)) sa0)
       (erased (Nat) n1) (erased (List (Name)) s1) (erased (List (Ent)) e1) (erased (List (Rule)) r1) (erased (List (Adt)) a1) (erased (Maybe (Term)) l1) (erased (List (Term)) sa1)
       (erased (List (Maybe (Nat))) acc) (erased (List (Nat)) ids) (erased (Lt n0 (Succ n1)) le) (erased (CoversRev n0 e0 acc ids e1) c) -> (CovRev (MkCtx n0 s0 e0 r0 a0 l0 sa0) acc ids (MkCtx n1 s1 e1 r1 a1 l1 sa1))))
  (Cat : ((List (Maybe (Nat))) xs) ((List (Maybe (Nat))) ys) ((List (Maybe (Nat))) out) -> Type
    enum
    (many CatNil : (erased (List (Maybe (Nat))) ys) -> (Cat (Nil (Maybe (Nat))) ys ys))
    (many CatCons : (erased (Maybe (Nat)) x) (erased (List (Maybe (Nat))) xs) (erased (List (Maybe (Nat))) ys) (erased (List (Maybe (Nat))) out) (erased (Cat xs ys out) p) ->
       (Cat (Cons (Maybe (Nat)) x xs) ys (Cons (Maybe (Nat)) x out)))))
(def-fns _ $ erased cat-nil : (subterm erased (List (Maybe (Nat))) xs) -> (erased (Cat xs (Nil (Maybe (Nat))) xs) p)
  (match erased xs _
    ((Nil a) (CatNil (Nil _)))
    ((Cons a x rest) (CatCons x rest (Nil _) rest (cat-nil rest)))))
(def-fns _ $ erased snoc-cat : (erased (List (Maybe (Nat))) b2) (erased (Maybe (Nat)) y) (erased (List (Maybe (Nat))) b) (erased (List (Maybe (Nat))) acc) (erased (List (Maybe (Nat))) out) (subterm erased (SnocId b2 y b) sn)
    (erased (Cat b acc out) ct) -> (erased (Cat b2 (Cons (Maybe (Nat)) y acc) out) r)
  (match erased sn _
    ((SnocIdNil x) (match erased ct _ ((CatCons x2 xs ys out2 q) (match erased q _ ((CatNil ys2) (CatNil (Cons _ y acc)))))))
    ((SnocIdCons z zs x b3 p) (match erased ct _ ((CatCons x2 xs ys out2 q) (CatCons z zs (Cons _ y acc) out2 (snoc-cat zs y b3 acc out2 p q)))))))
(def-fns _ $ erased covers-rev-binders : (erased (Nat) n0) (erased (List (Ent)) e0) (erased (List (Maybe (Nat))) acc) (erased (List (Nat)) ids) (erased (List (Ent)) e1) (erased (List (Maybe (Nat))) b) (erased (List (Maybe (Nat))) out)
    (subterm erased (CoversRev n0 e0 acc ids e1) cr) (erased (Binders ids b) bd) (erased (Cat b acc out) ct) -> (erased (Covers n0 e0 out e1) c)
  (match erased cr _
    ((CvRNil a d g h c2) (match erased bd _ ((BindersNil) (match erased ct _ ((CatNil ys) c2)))))
    ((CvRCons a d g x ids2 h cr2)
      (match erased bd _
        ((BindersCons x2 ids3 b2 out2 bd2 sn) (covers-rev-binders n0 e0 (Cons _ (Some _ x) acc) ids2 e1 b2 out cr2 bd2 (snoc-cat b2 (Some _ x) b acc out sn ct)))))))
(def-fns _ $ erased len-eq-length-r : (erased Type A) (erased Type B) (erased (List A) xs) (erased (List B) ys) (erased (Nat) m) (subterm erased (LenEq A B xs ys) le) (erased (Length A xs m) ln) -> (erased (Length B ys m) q)
  (match erased le _
    ((LENil a b) (match erased ln _ ((LenNil c) (LenNil _))))
    ((LECons a b x y xs2 ys2 p) (match erased ln _ ((LenCons c x0 xs0 m2 l2) (LenCons _ y ys2 m2 (len-eq-length-r _ _ xs2 ys2 m2 p l2)))))))
(def-fns _ $ erased snocid-layout : (erased (List (Maybe (Nat))) xs) (erased (Nat) x) (erased (List (Maybe (Nat))) out) (erased (Nat) m) (subterm erased (SnocId xs (Some (Nat) x) out) sn) (erased (Layout (Nat) xs (Zero) m) ly) ->
    (erased (Layout (Nat) out (Zero) (Succ m)) q)
  (match erased sn _
    ((SnocIdNil y) (match erased ly _ ((LayNil b) (LaySome _ x (Nil _) (Zero) (LayNil _)))))
    ((SnocIdCons y ys z out2 p) (match erased ly _ ((LaySome b y0 ys0 m2 l2) (LaySome _ y0 out2 (Succ m2) (snocid-layout ys x out2 m2 p l2)))))))
(def-fns _ $ erased binders-layout : (erased (List (Nat)) ids) (erased (List (Maybe (Nat))) b) (erased (Nat) m) (subterm erased (Binders ids b) bd) (erased (Length (Nat) ids m) ln) -> (erased (Layout (Nat) b (Zero) m) q)
  (match erased bd _
    ((BindersNil) (match erased ln _ ((LenNil a) (LayNil _))))
    ((BindersCons x ids2 acc out p sn) (match erased ln _ ((LenCons a x0 ids0 m2 l2) (snocid-layout acc x out m2 sn (binders-layout ids2 acc m2 p l2)))))))
(def-fns _ $ erased tele-ids-length : (erased (Ctx) ctx) (erased (List (Entry)) pt) (erased (List (Nat)) ids) (erased (Nat) m) (erased (ScT ctx (Zero) pt m) spt) (erased (LenEq (Entry) (Nat) pt ids) li) -> (erased (Length (Nat) ids m) ln)
  (let-match erased spt (MkScT q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 sps))
  (let (erased m2) (erased lp) (list-len _ pt))
  (match erased (stele-plus _ (Zero) pt m m2 sps lp) _ ((PlusZ b) (len-eq-length-r _ _ pt ids m2 li lp))))
(def-fns _ $ erased refs-length : (erased (List (Nat)) ids) (erased (List (Term)) ts) (erased (Nat) m) (subterm erased (Refs ids ts) rf) (erased (Length (Nat) ids m) ln) -> (erased (Length (Term) ts m) q)
  (match erased rf _
    ((RefsNil) (match erased ln _ ((LenNil a) (LenNil _))))
    ((RefsCons x ids2 ts2 p) (match erased ln _ ((LenCons a x0 ids0 m2 l2) (LenCons _ (Ref x) ts2 m2 (refs-length ids2 ts2 m2 p l2)))))))
(def-fns _ $ erased refs-len-eq : (erased (List (Entry)) ps) (erased (List (Nat)) ids) (erased (List (Term)) ts) (erased (LenEq (Entry) (Nat) ps ids) le) (subterm erased (Refs ids ts) rf) -> (erased (LenEq (Term) (Entry) ts ps) q)
  (match erased rf _
    ((RefsNil) (match erased le _ ((LENil a b) (LENil _ _))))
    ((RefsCons x ids2 ts2 p) (match erased le _ ((LECons a b e y ps2 ids0 le2) (LECons _ _ (Ref x) e ts2 ps2 (refs-len-eq ps2 ids2 ts2 le2 p)))))))
(def-fns _ $ erased args-len-eq : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (List (Entry)) tele) (erased (List (Raw)) args) (erased (List (Term)) ts) (subterm erased (ElabTermArgs ctx acc tele args (ArgsOk ts)) p) ->
    (erased (LenEq (Term) (Entry) ts tele) le)
  (match erased p _
    ((ETANil a b) (LENil _ _))
    ((ETATy a b s t es ar rest at aty t2 ts2 q sb sm q2) (LECons _ _ at (MkEntry s (BFalse) t) ts2 es (args-len-eq ctx (Cons _ (Some _ at) acc) es rest ts2 q2)))
    ((ETAIs a b s t es ar rest at aty t2 ts2 q sb sm q2) (LECons _ _ at (MkEntry s (BTrue) t) ts2 es (args-len-eq ctx (Cons _ (Some _ at) acc) es rest ts2 q2)))))
(def-fns _ $ many inst-ret-sc : (many (Ctx) ctx) (erased (Nat) out) (many (List (Entry)) ps) (many (Term) ret) (many (List (Term)) as) (erased (ScT ctx (Zero) ps out) sps) (erased (Sc ctx out ret) sret) (erased (ScL ctx (Zero) as) sas)
    (erased (LenEq (Term) (Entry) as ps) le) -> (many (List (Maybe (Term))) sub) (erased (Somes as sub) so) (many (Term) ty) (erased (Subst sub ret ty) q) (erased (Sc ctx (Zero) ty) sty)
  (let-match many ctx (MkCtx n s e r a l sa))
  (let-match erased sps (MkScT q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 tps))
  (let-match erased sret (MkSc z1 z2 z3 z4 z5 z6 z7 z8 z9 tret))
  (let-match erased sas (MkScL y1 y2 y3 y4 y5 y6 y7 y8 y9 tas))
  (let (many sub) (erased so) (many ty) (erased q) (erased sty) (inst-ret e out ps ret as tps tret tas le))
  (values sub so ty q (MkSc _ _ _ _ _ _ _ _ ty sty)))
(def-fns _ $ erased cov-binders : (erased (Ctx) ctx0) (erased (List (Nat)) ids) (erased (Ctx) ctx1) (erased (List (Maybe (Nat))) b) (erased (Nat) m) (erased (List (Entry)) pt) (erased (CovRev ctx0 (Nil (Maybe (Nat))) ids ctx1) cr)
    (erased (Binders ids b) bd) (erased (ScT ctx0 (Zero) pt m) spt) (erased (LenEq (Entry) (Nat) pt ids) li) -> (erased (Cov ctx0 b ctx1 m) c)
  (let-match erased cr (MkCovRev n0 s0 e0 r0 a0 l0 sa0 n1 s1 e1 r1 a1 l1 sa1 acc ids2 le c2))
  (MkCov _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ le (covers-rev-binders n0 e0 (Nil _) ids e1 b b c2 bd (cat-nil b)) (binders-layout ids b m bd (tele-ids-length ctx0 pt ids m spt li))))
(def-fns _ $ erased covers-rev-ext : (erased (Nat) n0) (erased (List (Ent)) e0) (erased (List (Maybe (Nat))) acc) (erased (List (Nat)) ids) (erased (List (Ent)) e1) (subterm erased (CoversRev n0 e0 acc ids e1) cr) -> (erased (Ext n0 e0 e1) x)
  (match erased cr _
    ((CvRNil a d g h c2) (covers-ext n0 e0 acc e1 c2))
    ((CvRCons a d g y ids2 h cr2) (covers-rev-ext n0 e0 (Cons _ (Some _ y) acc) ids2 e1 cr2))))
(def-fns _ $ erased covrev-grew : (erased (Ctx) ctx0) (erased (List (Maybe (Nat))) acc) (erased (List (Nat)) ids) (erased (Ctx) ctx1) (erased (CovRev ctx0 acc ids ctx1) cr) -> (erased (Grew ctx0 ctx1) g)
  (let-match erased cr (MkCovRev n0 s0 e0 r0 a0 l0 sa0 n1 s1 e1 r1 a1 l1 sa1 acc2 ids2 le c2))
  (GrewBy n0 s0 e0 r0 a0 l0 sa0 n1 s1 e1 r1 a1 l1 sa1 le (covers-rev-ext n0 e0 acc ids e1 c2)))

; A canonical former is a former of the same kind.
(def-adts
  (IsValCtor : ((Term) t) -> Type
    enum
    (many IVC : (erased (List (Entry)) ps) (erased (Term) r) -> (IsValCtor (ValCtor ps r))))
  (IsTyCtor : ((Term) t) -> Type
    enum
    (many ITC : (erased (List (Entry)) ps) -> (IsTyCtor (TyCtor ps)))))
(def-fns _ $ erased canon-valctor : (erased (List (Rule)) rules) (erased (List (Entry)) ps) (erased (Term) r) (erased (Term) u) (erased (Canon rules (ValCtor ps r) u) c) -> (erased (IsValCtor u) p)
  (match erased c _ ((CanValCtor a ps0 ps2 r0 r2 q p2) (IVC ps2 r2))))
(def-fns _ $ erased canon-tyctor : (erased (List (Rule)) rules) (erased (List (Entry)) ps) (erased (Term) u) (erased (Canon rules (TyCtor ps) u) c) -> (erased (IsTyCtor u) p)
  (match erased c _ ((CanTyCtor a ps0 ps2 q) (ITC ps2))))

; ---- Context-level decisions: the type and kind of an entry, canonical forms, identity, refinement.

(def-fns _ $ many type-of : (many (Ctx) ctx) (many (WF ctx) wf) (many (Nat) x) (erased (Has ctx x) h) ->
    (many (Term) ty) (many (Kind) k) (erased (TypeOf ctx x ty) p) (erased (KindOf ctx x k) q) (erased (Sc ctx (Zero) ty) sc) (erased (List (Ent)) e2) (erased (Ents ctx e2) ee) (erased (EntOf e2 x ty k) eo)
  (let-match many ctx (MkCtx n s e r a l sa))
  (let-match many wf (MkWF m1 m2 m3 m4 m5 m6 m7 ranks top v al be se ss sr sa2 sl ssa bi rp))
  (let-match erased h (MkHas q1 q2 q3 q4 q5 q6 q7 q8 he))
  (match many (ent-dec e x) _
    (absurd (EntMiss b c m) (has-ent-no-ent e x he m))
    ((EntHit b c ty k p) (values ty k (TypeOfBy ctx x ty k e (EntsOf n s e r a l sa) p) (KindOfBy ctx x ty k e (EntsOf n s e r a l sa) p) (MkSc _ _ _ _ _ _ _ _ ty (ent-of-scoped e e x ty k se p)) e (EntsOf n s e r a l sa) p))))

(def-fns _ $ many canonical : (many (Ctx) ctx) (many (WF ctx) wf) (many (Term) t) (erased (Sc ctx (Zero) t) st) -> (many (Term) u) (erased (Canonical ctx t u) p) (erased (Sc ctx (Zero) u) su)
  (let-match many ctx (MkCtx n s e r a l sa))
  (let-match many wf (MkWF m1 m2 m3 m4 m5 m6 m7 ranks top v al be se ss sr sa2 sl ssa bi rp))
  (let-match erased st (MkSc q1 q2 q3 q4 q5 q6 q7 dq q8 sct))
  (let (many u) (erased c) (canon-tb e r (MkTable _ _ ranks top v al sr rp) t))
  (values u (CanonicalBy ctx t u r (RulesOf n s e r a l sa) c) (MkSc _ _ _ _ _ _ _ _ u (canon-scoped e r (Zero) t u sr sct c))))

(def-adts
  (SameDec : ((Ctx) ctx) ((Term) t) ((Term) u) -> Type
    enum
    (many SDSame : (erased (Ctx) ctx) (erased (Term) t) (erased (Term) u) (erased (Same ctx t u) p) -> (SameDec ctx t u))
    (many SDDiffer : (erased (Ctx) ctx) (erased (Term) t) (erased (Term) u) (erased (Differ ctx t u) p) -> (SameDec ctx t u)))
  (RefineDec : ((Ctx) ctx) ((Term) t) ((Term) u) -> Type
    enum
    (many RDRefined : (erased (Ctx) ctx) (erased (Term) t) (erased (Term) u) (many (Ctx) out) (many (WF out) wf) (erased (Grew ctx out) g) (erased (Refine ctx t u out) p) -> (RefineDec ctx t u))
    (many RDContradicted : (erased (Ctx) ctx) (erased (Term) t) (erased (Term) u) (erased (Contradict ctx t u) p) -> (RefineDec ctx t u))))
(def-fns _ $ many same-dec : (many (Ctx) ctx) (many (WF ctx) wf) (many (Term) t) (many (Term) u) (erased (Sc ctx (Zero) t) st) (erased (Sc ctx (Zero) u) su) -> (many (SameDec ctx t u) r)
  (let-match many ctx (MkCtx n s e r a l sa))
  (let-match many wf (MkWF m1 m2 m3 m4 m5 m6 m7 ranks top v al be se ss sr sa2 sl ssa bi rp))
  (let-match erased st (MkSc q1 q2 q3 q4 q5 q6 q7 dq q8 sct))
  (let-match erased su (MkSc z1 z2 z3 z4 z5 z6 z7 dq z8 scu))
  (let (many cnt) (erased fc) (free-count e r))
  (match many (unify-eqs (Check) e se r (MkTable _ _ ranks top v al sr rp) cnt fc (Cons _ (MkEqn t u) (Nil _)) (SqCons _ _ _ _ sct scu (SqNil _))) _
    ((MkEqs y0 y1 y2 y3 o ot p)
      (match many o _
        ((UFail) (SDDiffer _ _ _ (DifferBy ctx t u e r (EntsOf n s e r a l sa) (RulesOf n s e r a l sa) p)))
        ((UOk rules2) (SDSame _ _ _ (SameBy ctx t u e r rules2 (EntsOf n s e r a l sa) (RulesOf n s e r a l sa) p)))))))
(def-fns _ $ many refine : (many (Ctx) ctx) (many (WF ctx) wf) (many (Term) t) (many (Term) u) (erased (Sc ctx (Zero) t) st) (erased (Sc ctx (Zero) u) su) -> (many (RefineDec ctx t u) d)
  (let-match many ctx (MkCtx n s e r a l sa))
  (let-match many wf (MkWF m1 m2 m3 m4 m5 m6 m7 ranks top v al be se ss sr sa2 sl ssa bi rp))
  (let-match erased st (MkSc q1 q2 q3 q4 q5 q6 q7 dq q8 sct))
  (let-match erased su (MkSc z1 z2 z3 z4 z5 z6 z7 dq z8 scu))
  (let (many cnt) (erased fc) (free-count e r))
  (match many (unify-eqs (Force) e se r (MkTable _ _ ranks top v al sr rp) cnt fc (Cons _ (MkEqn t u) (Nil _)) (SqCons _ _ _ _ sct scu (SqNil _))) _
    ((MkEqs y0 y1 y2 y3 o ot p)
      (match many o _
        ((UFail) (RDContradicted _ _ _ (ContradictBy ctx t u e r (EntsOf n s e r a l sa) (RulesOf n s e r a l sa) p)))
        ((UOk rules2)
          (match many ot _
            ((OTOk b rules3 tb)
              (match many tb _
                ((MkTable c d ranks2 top2 v2 al2 sr2 rp2)
                  (RDRefined _ _ _ (MkCtx n s e rules2 a l sa) (MkWF _ _ _ _ _ _ _ ranks2 top2 v2 al2 be se ss sr2 sa2 sl ssa bi rp2)
                    (GrewBy n s e r a l sa n s e rules2 a l sa (lt-succ n) (ExtRefl n e))
                    (RefineBy ctx t u (MkCtx n s e rules2 a l sa) e r rules2 (EntsOf n s e r a l sa) (RulesOf n s e r a l sa) p (WithRulesTo n s e r a l sa rules2))))))))))))

; The type of a closed term of the grammar, through the context.
(def-adts $ TypedDec : ((Ctx) ctx) ((Term) t) -> Type
  enum
  (many TypedIs : (erased (Ctx) ctx) (erased (Term) t) (many (Term) ty) (erased (Typed ctx t ty) p) (erased (Sc ctx (Zero) ty) sc) -> (TypedDec ctx t)))
(def-fns _ $ many typed-dec : (many (Ctx) ctx) (many (WF ctx) wf) (many (Term) t) (erased (Sc ctx (Zero) t) st) -> (many (TypedDec ctx t) r)
  (let-match many ctx (MkCtx n s e r a l sa))
  (let-match many wf (MkWF m1 m2 m3 m4 m5 m6 m7 ranks top v al be se ss sr sa2 sl ssa bi rp))
  (let-match erased st (MkSc q1 q2 q3 q4 q5 q6 q7 dq q8 sct))
  (match many (type-of-term e se r (MkTable _ _ ranks top v al sr rp) t sct) _
    ((TotIs w1 w2 w3 ty p sc) (TypedIs _ _ ty (TypedBy ctx t ty e r (EntsOf n s e r a l sa) (RulesOf n s e r a l sa) p) (MkSc _ _ _ _ _ _ _ _ ty sc)))))

; Minting a telescope's entries with the names given.
(def-adts
  (MintTeleDec : ((Ctx) ctx) ((List (Maybe (Term))) acc) ((List (Entry)) tele) ((List (Maybe (String))) names) -> Type
    enum
    (many MTMinted : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (List (Entry)) tele) (erased (List (Maybe (String))) names) (many (Ctx) out) (many (List (Nat)) ids)
       (many (WF out) wf) (erased (Grew ctx out) g) (erased (HasAll out ids) h) (erased (LenEq (Entry) (Nat) tele ids) le) (erased (MintTele ctx acc tele names out ids) p) -> (MintTeleDec ctx acc tele names))))
(def-fns _ $ many mint-tele : (many (Ctx) ctx) (many (WF ctx) wf) (many (List (Maybe (Term))) acc) (erased (Nat) m) (erased (ScS ctx acc m) sacc) (subterm many (List (Entry)) tele) (erased (Nat) out) (erased (ScT ctx m tele out) stele)
    (many (List (Maybe (String))) names) (erased (LenEq (Entry) (Maybe (String)) tele names) len) -> (many (MintTeleDec ctx acc tele names) r)
  (match many tele _
    ((Nil a)
      (match many names _
        ((Nil b) (MTMinted _ _ _ _ ctx (Nil _) wf (grew-refl ctx) (has-all-nil ctx) (LENil _ _) (MTNil ctx acc)))
        ((Cons b nm ns) (match erased len _))))
    ((Cons a e es)
      (match many names _
        ((Nil b) (match erased len _))
        ((Cons b name ns)
          (match many e _
            ((MkEntry s i t)
              (match erased len _
                ((LECons c d g h k m len2)
                  (let (erased st) (erased ses) (sct-parts ctx _ _ s i t es stele))
                  (let (many t2) (erased sb) (subst acc _ (scs-length ctx acc _ sacc) t (sc-closed ctx _ t st)))
                  (let (erased st2) (sc-subst ctx acc _ t t2 sacc st sb))
                  (match many i _
                    ((BFalse)
                      (let (many x) (many ctx1) (erased mnt) (many wf1) (erased g1) (erased hx) (mint ctx wf name t2 (KPlain) (None _) st2 (scm-none ctx) (ROkNone _)))
                      (match many (mint-tele ctx1 wf1 (Cons _ (Some _ (Ref x)) acc) _ (scs-cons ctx1 (Ref x) acc _ (sc-ref ctx1 x (entis-has ctx1 x _ _ hx)) (scs-grew ctx ctx1 acc _ g1 sacc)) es _ (sct-grew ctx ctx1 _ es _ g1 ses) ns len2) _
                        ((MTMinted g2 h2 k2 l2 out ids wf2 g3 hids le p)
                          (MTMinted _ _ _ _ out (Cons _ x ids) wf2 (grew-trans ctx ctx1 out g1 g3) (has-all-cons out x ids (has-grew ctx1 out x g3 (entis-has ctx1 x _ _ hx)) hids) (LECons _ _ e x es ids le)
                            (MTTy ctx acc s t es name ns t2 x ctx1 out ids sb mnt p)))))
                    ((BTrue)
                      (match many (typed-dec ctx wf t2 st2) _
                        ((TypedIs g2 h2 ty tt sty)
                          (let (many x) (many ctx1) (erased mnt) (many wf1) (erased g1) (erased hx) (mint ctx wf name ty (KPlain) (Some _ t2) sty (scm-some ctx t2 st2) (ROkSome _ _ (NDPlain))))
                          (match many (mint-tele ctx1 wf1 (Cons _ (Some _ (Ref x)) acc) _ (scs-cons ctx1 (Ref x) acc _ (sc-ref ctx1 x (entis-has ctx1 x _ _ hx)) (scs-grew ctx ctx1 acc _ g1 sacc)) es _ (sct-grew ctx ctx1 _ es _ g1 ses) ns len2) _
                            ((MTMinted g3 h3 k3 l3 out ids wf2 g4 hids le p)
                              (MTMinted _ _ _ _ out (Cons _ x ids) wf2 (grew-trans ctx ctx1 out g1 g4) (has-all-cons out x ids (has-grew ctx1 out x g4 (entis-has ctx1 x _ _ hx)) hids) (LECons _ _ e x es ids le)
                                (MTIs ctx acc s t es name ns t2 ty x ctx1 out ids sb tt mnt p)))))))))))))))))

; A strict subterm, decided on canonical terms.
(def-adts
  (SubDec : ((Ctx) ctx) ((Term) a) ((Term) b) -> Type
    enum
    (many SubYes : (erased (Ctx) ctx) (erased (Term) a) (erased (Term) b) (erased (StrictSub ctx a b) p) -> (SubDec ctx a b))
    (many SubNo : (erased (Ctx) ctx) (erased (Term) a) (erased (Term) b) (erased (NotSub ctx a b) p) -> (SubDec ctx a b)))
  (SubListDec : ((Ctx) ctx) ((Term) a) ((List (Term)) as) -> Type
    enum
    (many SubLYes : (erased (Ctx) ctx) (erased (Term) a) (erased (List (Term)) as) (erased (SubOfList ctx a as) p) -> (SubListDec ctx a as))
    (many SubLNo : (erased (Ctx) ctx) (erased (Term) a) (erased (List (Term)) as) (erased (NotSubList ctx a as) p) -> (SubListDec ctx a as))))
(def-fns _ $ many sub-parts : (many (Ctx) ctx) (many (WF ctx) wf) (many (Term) a) (erased (Term) b) (many (Term) h) (erased (List (Term)) as) (erased (AppParts b h as) ap) (erased (Sc ctx (Zero) a) sa) (erased (Sc ctx (Zero) h) sh)
    (many (SubListDec ctx a as) sl) -> (many (SubDec ctx a b) r)
  (match many (same-dec ctx wf a h sa sh) _
    ((SDSame c d e s) (SubYes _ _ _ (SSHead ctx a b h as ap s)))
    ((SDDiffer c d e df)
      (match many sl _
        ((SubLYes c2 d2 e2 p) (SubYes _ _ _ (SSArg ctx a b h as ap p)))
        ((SubLNo c2 d2 e2 p) (SubNo _ _ _ (NSApp ctx a b h as ap df p)))))))
(def-fns _
  (many sub-dec : (many (Ctx) ctx) (many (WF ctx) wf) (many (Term) a) (erased (Sc ctx (Zero) a) sa) (subterm many (Term) b) (erased (Sc ctx (Zero) b) sb) -> (many (SubDec ctx a b) r)
    (match many b _
      ((TyApp h ps as)
        (let (erased sh) (erased sas) (sc-app-parts ctx _ h as (APTy h ps as) sb))
        (sub-parts ctx wf a _ h as (APTy h ps as) sa sh (sub-list-dec ctx wf a sa as sas)))
      ((ValApp h ps rt as)
        (let (erased sh) (erased sas) (sc-app-parts ctx _ h as (APVal h ps rt as) sb))
        (sub-parts ctx wf a _ h as (APVal h ps rt as) sa sh (sub-list-dec ctx wf a sa as sas)))
      ((Ref x) (SubNo _ _ _ (NSNotApp ctx a (Ref x) (NotAppRef x))))
      ((Bound k) (SubNo _ _ _ (NSNotApp ctx a (Bound k) (NotAppBound k))))
      ((Univ) (SubNo _ _ _ (NSNotApp ctx a (Univ) (NotAppUniv))))
      ((Fn l ps rs) (SubNo _ _ _ (NSNotApp ctx a (Fn l ps rs) (NotAppFn l ps rs))))
      ((TyCtor ps) (SubNo _ _ _ (NSNotApp ctx a (TyCtor ps) (NotAppTyCtor ps))))
      ((ValCtor ps ret) (SubNo _ _ _ (NSNotApp ctx a (ValCtor ps ret) (NotAppValCtor ps ret))))))
  (many sub-list-dec : (many (Ctx) ctx) (many (WF ctx) wf) (many (Term) a) (erased (Sc ctx (Zero) a) sa) (subterm many (List (Term)) as) (erased (ScL ctx (Zero) as) sas) -> (many (SubListDec ctx a as) r)
    (match many as _
      ((Nil c) (SubLNo _ _ _ (NSLNil ctx a)))
      ((Cons c b rest)
        (let (erased sb) (erased srest) (scl-parts ctx b rest sas))
        (match many (same-dec ctx wf a b sa sb) _
          ((SDSame c1 d1 e1 s) (SubLYes _ _ _ (SLSame ctx a b rest s)))
          ((SDDiffer c1 d1 e1 df)
            (match many (sub-dec ctx wf a sa b sb) _
              ((SubYes c2 d2 e2 p) (SubLYes _ _ _ (SLDeep ctx a b rest p)))
              ((SubNo c2 d2 e2 n)
                (match many (sub-list-dec ctx wf a sa rest srest) _
                  ((SubLYes c3 d3 e3 p) (SubLYes _ _ _ (SLThere ctx a b rest p)))
                  ((SubLNo c3 d3 e3 p) (SubLNo _ _ _ (NSLCons ctx a b rest df n p))))))))))))

; ---- Terms of the grammar, telescopes, and their arguments. Beside each outcome, what it built is scoped;
; a telescope's entries, abstracted over its binders, are scoped in the context it was entered from.

(def-adts
  (EntryDec : ((Raw) raw) -> Type
    enum
    (many EntryShape : (erased (Raw) raw) (many (Bool) s) (many (Bool) i) (many (Raw) tr) (many (String) x) (erased (EntryRaw raw s i tr x) p) (erased (Subterm (Raw) tr (Raw) raw) sub) -> (EntryDec raw))
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
                    ((RAtom x) (EntryShape _ (BFalse) (BFalse) r1 x (EntryTy r1 x) (prove-subterm r1 raw)))
                    (else (EntryNot _))))
                ((Cons c r3 rest3)
                  (match many rest3 _
                    ((Nil d)
                      (match many r3 _
                        ((RAtom x)
                          (match many r1 _
                            ((RKey k)
                              (match many k _
                                ((KSubterm) (EntryShape _ (BTrue) (BFalse) r2 x (EntrySub r2 x) (prove-subterm r2 raw)))
                                (else (EntryNot _))))
                            (else
                              (match many r2 _
                                ((RKey k2)
                                  (match many k2 _
                                    ((KIs) (EntryShape _ (BFalse) (BTrue) r1 x (EntryIs r1 x) (prove-subterm r1 raw)))
                                    (else (EntryNot _))))
                                (else (EntryNot _))))))
                        (else (EntryNot _))))
                    (else (EntryNot _))))))
            (else (EntryNot _))))
        (else (EntryNot _))))
    (else (EntryNot _))))

(def-adts
  (TSc : ((Ctx) ctx) ((TOut) out) -> Type
    enum
    (many TSOk : (erased (Ctx) ctx) (erased (Term) t) (erased (Term) ty) (erased (Sc ctx (Zero) t) st) (erased (Sc ctx (Zero) ty) sty) -> (TSc ctx (TOk t ty)))
    (many TSErr : (erased (Ctx) ctx) (erased (Reason) r) -> (TSc ctx (TErr r))))
  (ASc : ((Ctx) ctx) ((ArgsOut) out) -> Type
    enum
    (many ASOk : (erased (Ctx) ctx) (erased (List (Term)) ts) (erased (ScL ctx (Zero) ts) sts) -> (ASc ctx (ArgsOk ts)))
    (many ASErr : (erased (Ctx) ctx) (erased (Reason) r) -> (ASc ctx (ArgsErr r))))
  (TeleSc : ((Ctx) ctx0) ((List (Maybe (Nat))) acc) ((Nat) m) ((Ctx) ctx) ((TeleOut) out) -> Type
    enum
    (many TLOk : (erased (Ctx) ctx0) (erased (List (Maybe (Nat))) acc) (erased (Ctx) ctx) (erased (Ctx) out) (erased (List (Entry)) tele) (erased (List (Nat)) ids) (erased (List (Maybe (String))) names)
       (erased (Nat) m) (erased (Nat) mout) (many (WF out) wf) (erased (CovRev ctx0 acc ids out) cr) (erased (ScT ctx0 m tele mout) st) (erased (LenEq (Entry) (Nat) tele ids) li) (erased (LenEq (Entry) (Maybe (String)) tele names) ln) ->
       (TeleSc ctx0 acc m ctx (TeleOk out tele ids names)))
    (many TLErr : (erased (Ctx) ctx0) (erased (List (Maybe (Nat))) acc) (erased (Nat) m) (erased (Ctx) ctx) (erased (Reason) r) -> (TeleSc ctx0 acc m ctx (TeleErr r))))
  (TermDec : ((Ctx) ctx) ((Raw) raw) -> Type
    enum
    (many MkTermDec : (erased (Ctx) ctx) (erased (Raw) raw) (many (TOut) out) (erased (ElabTerm ctx raw out) p) (erased (TSc ctx out) sc) -> (TermDec ctx raw))
    (many TermStuck : (erased (Ctx) ctx) (erased (Raw) raw) -> (TermDec ctx raw)))
  (ArgsDec : ((Ctx) ctx) ((List (Maybe (Term))) acc) ((List (Entry)) tele) ((List (Raw)) args) -> Type
    enum
    (many MkArgsDec : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (List (Entry)) tele) (erased (List (Raw)) args) (many (ArgsOut) out) (erased (ElabTermArgs ctx acc tele args out) p) (erased (ASc ctx out) sc) ->
       (ArgsDec ctx acc tele args))
    (many ArgsStuck : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (List (Entry)) tele) (erased (List (Raw)) args) -> (ArgsDec ctx acc tele args)))
  (TeleDec : ((Ctx) ctx0) ((List (Maybe (Nat))) acc) ((Nat) m) ((Ctx) ctx) ((List (Raw)) raws) -> Type
    enum
    (many MkTeleDec : (erased (Ctx) ctx0) (erased (List (Maybe (Nat))) acc) (erased (Nat) m) (erased (Ctx) ctx) (erased (List (Raw)) raws) (many (TeleOut) out) (erased (ElabTele ctx acc raws out) p) (many (TeleSc ctx0 acc m ctx out) sc) ->
       (TeleDec ctx0 acc m ctx raws))
    (many TeleStuck : (erased (Ctx) ctx0) (erased (List (Maybe (Nat))) acc) (erased (Nat) m) (erased (Ctx) ctx) (erased (List (Raw)) raws) -> (TeleDec ctx0 acc m ctx raws))))

(def-fns _ $ erased scope-has-ctx : (erased (Ctx) ctx) (many (WF ctx) wf) (erased (List (Name)) scope) (erased (String) s) (erased (Nat) x) (erased (Scope ctx scope) sc) (erased (NameOf scope s x) n) -> (erased (Has ctx x) h)
  (let-match many wf (MkWF n0 s0 e r a l sa ranks top v al be se ss sr sa2 sl ssa bi rp))
  (let-match erased sc (ScopeOf z1 z2 z3 z4 z5 z6 z7))
  (MkHas _ _ _ _ _ _ _ x (scope-has e scope s x ss n)))
(def-fns _ $ erased sct-nil : (erased (Ctx) ctx) (erased (Nat) d) -> (erased (ScT ctx d (Nil (Entry)) d) s)
  (let-match erased ctx (MkCtx n s e r a l sa))
  (MkScT _ _ _ _ _ _ _ _ _ (Nil _) (ScTNil _ _)))
(def-fns _ $ erased sct-cons : (erased (Ctx) ctx) (erased (Nat) d) (erased (Nat) out) (erased (Bool) s) (erased (Bool) i) (erased (Term) t) (erased (List (Entry)) es) (erased (Sc ctx d t) p) (erased (ScT ctx (Succ d) es out) q) ->
    (erased (ScT ctx d (Cons (Entry) (MkEntry s i t) es) out) st)
  (let-match erased p (MkSc q1 q2 q3 q4 q5 q6 q7 q8 q9 sct))
  (let-match erased q (MkScT z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 sts))
  (MkScT _ _ _ _ _ _ _ _ _ _ (ScTCons _ _ s i t es _ sct sts)))
(def-fns _ $ erased covrev-nil : (erased (Ctx) ctx0) (erased (List (Maybe (Nat))) acc) (erased (Ctx) ctx) (erased (Nat) m) (erased (Cov ctx0 acc ctx m) c) -> (erased (CovRev ctx0 acc (Nil (Nat)) ctx) cr)
  (let-match erased c (MkCov n0 s0 e0 r0 a0 l0 sa0 n1 s1 e1 r1 a1 l1 sa1 acc2 mm le cv ly))
  (MkCovRev _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ le (CvRNil n0 e0 acc e1 cv)))
(def-fns _ $ erased covrev-cons : (erased (Ctx) ctx0) (erased (List (Maybe (Nat))) acc) (erased (Nat) x) (erased (List (Nat)) ids) (erased (Ctx) out) (erased (CovRev ctx0 (Cons (Maybe (Nat)) (Some (Nat) x) acc) ids out) c) ->
    (erased (CovRev ctx0 acc (Cons (Nat) x ids) out) cr)
  (let-match erased c (MkCovRev n0 s0 e0 r0 a0 l0 sa0 n1 s1 e1 r1 a1 l1 sa1 acc2 ids2 le cv))
  (MkCovRev _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ le (CvRCons n0 e0 acc x ids e1 cv)))

; A ValCtor former's return (ASSUMPTIONS 80): the four ways the canonical return is not an application of a
; type constructor other than the former's own binders.
(def-adts
  (TyAppDec : ((Term) c) -> Type
    enum
    (many IsTyApp : (many (Term) h) (many (List (Entry)) ps) (many (List (Term)) as) -> (TyAppDec (TyApp h ps as)))
    (many IsNotTyApp : (erased (Term) c) (erased (NotTyApp c) p) -> (TyAppDec c)))
  (TyCtorDec : ((Term) u) -> Type
    enum
    (many TDIs : (many (List (Entry)) ps) -> (TyCtorDec (TyCtor ps)))
    (many TDNot : (erased (Term) u) (erased (NotTyCtor u) p) -> (TyCtorDec u)))
  (FormerRetDec : ((Ctx) ctx) ((List (Nat)) pids) ((Term) c) -> Type
    enum
    (many FROk : (erased (Ctx) ctx) (erased (List (Nat)) pids) (many (Nat) t) (many (List (Entry)) aps) (many (List (Term)) args) (many (Term) tty) (many (List (Entry)) tps)
       (erased (NotMem t pids) nm) (erased (TypeOf ctx t tty) tt) (erased (Canonical ctx tty (TyCtor tps)) ct) -> (FormerRetDec ctx pids (TyApp (Ref t) aps args)))
    (many FRBad : (erased (Ctx) ctx) (erased (List (Nat)) pids) (erased (Term) c) (erased (BadFormerRet ctx pids c) br) -> (FormerRetDec ctx pids c))))
(def-fns _ $ many tyapp-dec : (many (Term) c) -> (many (TyAppDec c) r)
  (match many c _
    ((TyApp h ps as) (IsTyApp h ps as))
    ((ValApp h ps r as) (IsNotTyApp _ (NTAValApp h ps r as)))
    ((Ref x) (IsNotTyApp _ (NTAOther _ (NotAppRef x))))
    ((Bound k) (IsNotTyApp _ (NTAOther _ (NotAppBound k))))
    ((Univ) (IsNotTyApp _ (NTAOther _ (NotAppUniv))))
    ((Fn l ps rs) (IsNotTyApp _ (NTAOther _ (NotAppFn l ps rs))))
    ((TyCtor ps) (IsNotTyApp _ (NTAOther _ (NotAppTyCtor ps))))
    ((ValCtor ps r) (IsNotTyApp _ (NTAOther _ (NotAppValCtor ps r))))))
(def-fns _ $ many tyctor-dec : (many (Term) u) -> (many (TyCtorDec u) r)
  (match many u _
    ((TyCtor ps) (TDIs ps))
    ((Ref x) (TDNot _ (NTCRef x)))
    ((Bound k) (TDNot _ (NTCBound k)))
    ((TyApp h ps as) (TDNot _ (NTCTyApp h ps as)))
    ((ValApp h ps r as) (TDNot _ (NTCValApp h ps r as)))
    ((Univ) (TDNot _ (NTCUniv)))
    ((Fn l ps rs) (TDNot _ (NTCFn l ps rs)))
    ((ValCtor ps r) (TDNot _ (NTCValCtor ps r)))))
(def-fns _ $ erased sc-ref-has : (erased (Ctx) ctx) (erased (Nat) x) (erased (Sc ctx (Zero) (Ref x)) s) -> (erased (Has ctx x) h)
  (match erased s _ ((MkSc q1 q2 q3 q4 q5 q6 q7 dq q8 sc) (match erased sc _ ((ScRef a dq x0 hx) (MkHas _ _ _ _ _ _ _ x hx))))))
(def-fns _ $ many former-ret-dec : (many (Ctx) ctx) (many (WF ctx) wf) (many (List (Nat)) pids) (many (Term) c) (erased (Sc ctx (Zero) c) sc) -> (many (FormerRetDec ctx pids c) r)
  (match many (tyapp-dec c) _
    ((IsNotTyApp a na) (FRBad _ _ _ (BFNotApp ctx pids c na)))
    ((IsTyApp h hps args)
      (match many (nonref-dec h) _
        ((IsNonRef a nr) (FRBad _ _ _ (BFHead ctx pids h hps args nr)))
        ((IsRef t)
          (match many (mem-dec t pids) _
            ((MemYes a b m) (FRBad _ _ _ (BFOwn ctx pids t hps args m)))
            ((MemNo a b nm)
              (let (erased sh) (erased sargs) (sc-app-parts ctx _ (Ref t) args (APTy (Ref t) hps args) sc))
              (let (many tty) (many kk) (erased tt) (erased kq) (erased stty) (erased e2) (erased ee) (erased eo) (type-of ctx wf t (sc-ref-has ctx t sh)))
              (let (many u) (erased cu) (erased su) (canonical ctx wf tty stty))
              (match many (tyctor-dec u) _
                ((TDIs tps) (FROk _ _ t hps args tty tps nm tt cu))
                ((TDNot a nt) (FRBad _ _ _ (BFNotTycon ctx pids t hps args tty u tt cu nt)))))))))))

(def-fns _
  (many elab-term : (many (Ctx) ctx) (many (WF ctx) wf) (subterm many (Raw) raw) (subterm many (POuter (PInner)) is ph) -> (many (TermDec ctx raw) r)
    (match many raw _
      ((RAtom s)
        (let (many scope) (erased sc) (ctx-scope ctx))
        (match many (name-dec scope s) _
          ((NameMiss a b n) (MkTermDec _ _ (TErr (RUnbound)) (ETUnbound ctx s scope sc n) (TSErr _ _)))
          ((NameHit a b x n)
            (let (erased hx) (scope-has-ctx ctx wf scope s x sc n))
            (let (many ty) (many k) (erased p) (erased q) (erased sty) (erased e2) (erased ee) (erased eo) (type-of ctx wf x hx))
            (MkTermDec _ _ (TOk (Ref x) ty) (ETName ctx s x ty scope sc n p) (TSOk _ _ _ (sc-ref ctx x hx) sty)))))
      ((RKey k) (TermStuck _ _))
      ((RList items)
        (match many items _
          ((Nil a) (TermStuck _ _))
          ((Cons a h args)
            (match many h _
              ((RKey k) (elab-former ctx wf k args (POuter (PInner))))
              ((RAtom s) (elab-term-app ctx wf h args items (POuter (PInner)) (HeadAtom s)))
              ((RList inner) (elab-term-app ctx wf h args items (POuter (PInner)) (HeadList inner)))))))))
  ; (h args...) with a name or a list at the head
  (many elab-term-app : (many (Ctx) ctx) (many (WF ctx) wf) (many (Raw) h) (many (List (Raw)) args) (subterm many (Cons (Raw) h args) is items) (subterm many (POuter (PInner)) is ph) (erased (HeadRaw h) hr) ->
      (many (TermDec ctx (RList items)) r)
    (match many (elab-term ctx wf h (POuter (PInner))) _
      ((TermStuck a b) (TermStuck _ _))
      ((MkTermDec a b hout p sc)
        (match many hout _
          ((TErr r) (MkTermDec _ _ (TErr r) (ETAppHeadErr ctx h args r p) (TSErr _ _)))
          ((TOk ht hty)
            (match erased sc _
              ((TSOk a2 b2 c2 sht shty)
                (let (many hc) (erased cn) (erased shc) (canonical ctx wf hty shty))
                (match many hc _
                  ((TyCtor ps)
                    (let (erased pd) (erased sps) (sc-tyctor-parts ctx ps shc))
                    (match many (elab-term-args ctx wf (Nil _) _ (scs-nil ctx) ps _ sps args (POuter (PInner))) _
                      ((ArgsStuck e g k l) (TermStuck _ _))
                      ((MkArgsDec e g k l aout ap asc)
                        (match many aout _
                          ((ArgsErr r) (MkTermDec _ _ (TErr r) (ETAppArgsErr ctx h args ht hty ps r p (HeadTy ctx hty ps cn) ap) (TSErr _ _)))
                          ((ArgsOk ts)
                            (match erased asc _
                              ((ASOk e2 g2 sts) (MkTermDec _ _ (TOk (TyApp ht ps ts) (Univ)) (ETTyApp ctx h args ht hty ps ts p cn ap) (TSOk _ _ _ (sc-tyapp ctx ht ps ts _ sht sps sts (args-len-eq ctx (Nil _) ps args ts ap)) (sc-univ ctx))))))))))
                  ((ValCtor ps ret)
                    (let (erased pd) (erased sps) (erased sret) (sc-valctor-parts ctx ps ret shc))
                    (match many (elab-term-args ctx wf (Nil _) _ (scs-nil ctx) ps _ sps args (POuter (PInner))) _
                      ((ArgsStuck e g k l) (TermStuck _ _))
                      ((MkArgsDec e g k l aout ap asc)
                        (match many aout _
                          ((ArgsErr r) (MkTermDec _ _ (TErr r) (ETAppArgsErr ctx h args ht hty ps r p (HeadVal ctx hty ps ret cn) ap) (TSErr _ _)))
                          ((ArgsOk ts)
                            (match erased asc _
                              ((ASOk e2 g2 sts)
                                (let (many sub) (erased so) (many ty) (erased sb) (erased sty) (inst-ret-sc ctx pd ps ret ts sps sret sts (args-len-eq ctx (Nil _) ps args ts ap)))
                                (MkTermDec _ _ (TOk (ValApp ht ps ret ts) ty) (ETValApp ctx h args ht hty ps ret ts sub ty p cn ap so sb)
                                  (TSOk _ _ _ (sc-valapp ctx ht ps ret ts _ sht sps sret sts (args-len-eq ctx (Nil _) ps args ts ap)) sty)))))))))
                  ((Ref x) (MkTermDec _ _ (TErr (RNotApplicable)) (ETNotApplicable ctx h args ht hty (Ref x) p cn (NoTeleRef x)) (TSErr _ _)))
                  ((Bound k) (MkTermDec _ _ (TErr (RNotApplicable)) (ETNotApplicable ctx h args ht hty (Bound k) p cn (NoTeleBound k)) (TSErr _ _)))
                  ((TyApp h2 ps2 as2) (MkTermDec _ _ (TErr (RNotApplicable)) (ETNotApplicable ctx h args ht hty (TyApp h2 ps2 as2) p cn (NoTeleTyApp h2 ps2 as2)) (TSErr _ _)))
                  ((ValApp h2 ps2 r2 as2) (MkTermDec _ _ (TErr (RNotApplicable)) (ETNotApplicable ctx h args ht hty (ValApp h2 ps2 r2 as2) p cn (NoTeleValApp h2 ps2 r2 as2)) (TSErr _ _)))
                  ((Univ) (MkTermDec _ _ (TErr (RNotApplicable)) (ETNotApplicable ctx h args ht hty (Univ) p cn (NoTeleUniv)) (TSErr _ _)))
                  ((Fn l ps rs) (MkTermDec _ _ (TErr (RNotApplicable)) (ETNotApplicable ctx h args ht hty (Fn l ps rs) p cn (NoTeleFn l ps rs)) (TSErr _ _)))))))))))
  ; the formers: (Fn L (params) (rets)), (TyCtor (params)), (ValCtor (params) ret)
  (many elab-former : (many (Ctx) ctx) (many (WF ctx) wf) (many (Key) k) (subterm many (List (Raw)) items) (subterm many (POuter (PInner)) is ph) -> (many (TermDec ctx (RList (Cons (Raw) (RKey k) items))) r)
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
                              ((RList rs) (elab-fn ctx wf lr ps rs items (PInner)))
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
                    (match many (elab-tele ctx ctx wf (Nil _) _ (cov-refl ctx) ps (POuter (PInner))) _
                      ((TeleStuck c d e g mq) (TermStuck _ _))
                      ((MkTeleDec c d e g mq tout ep tsc)
                        (match many tout _
                          ((TeleErr r) (MkTermDec _ _ (TErr r) (ETTyCtorErr ctx ps r ep) (TSErr _ _)))
                          ((TeleOk ctx1 pt pids pn)
                            (match many tsc _
                              ((TLOk z1 z2 z3 z4 z5 z6 z7 mq oq wf1 cr spt li ln) (MkTermDec _ _ (TOk (TyCtor pt) (Univ)) (ETTyCtor ctx ps ctx1 pt pids pn ep) (TSOk _ _ _ (sc-tyctor ctx pt _ spt) (sc-univ ctx))))))))))
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
                      ((RList ps) (elab-valctor ctx wf ps rr items (PInner)))
                      (else (TermStuck _ _))))
                  (else (TermStuck _ _))))
              (else (TermStuck _ _))))
          (else (TermStuck _ _))))
      (else (TermStuck _ _))))
  (many elab-fn : (many (Ctx) ctx) (many (WF ctx) wf) (many (Raw) lr) (many (List (Raw)) ps) (many (List (Raw)) rs)
      (subterm many (Cons (Raw) lr (Cons (Raw) (RList ps) (Cons (Raw) (RList rs) (Nil (Raw))))) is items) (subterm many (PInner) is ph) ->
      (many (TermDec ctx (RList (Cons (Raw) (RKey (KFn)) items))) r)
    (match many (elab-term ctx wf lr (POuter (PInner))) _
      ((TermStuck a b) (TermStuck _ _))
      ((MkTermDec a b lout p sc)
        (match many lout _
          ((TErr r) (MkTermDec _ _ (TErr r) (ETFnLevelErr ctx lr ps rs r p) (TSErr _ _)))
          ((TOk l lty)
            (match erased sc _
              ((TSOk a2 b2 c2 sl slty)
                (match many (same-dec ctx wf lty level-ty slty (sc-level-ty ctx wf)) _
                  ((SDDiffer c d e df) (MkTermDec _ _ (TErr (RNotLevel)) (ETFnNotLevel ctx lr ps rs l lty p df) (TSErr _ _)))
                  ((SDSame c d e sm)
                    (match many (elab-tele ctx ctx wf (Nil _) _ (cov-refl ctx) ps (POuter (PInner))) _
                      ((TeleStuck c2 d2 e2 g2 mq) (TermStuck _ _))
                      ((MkTeleDec c2 d2 e2 g2 mq pout ep psc)
                        (match many pout _
                          ((TeleErr r) (MkTermDec _ _ (TErr r) (ETFnParamsErr ctx lr ps rs l lty r p sm ep) (TSErr _ _)))
                          ((TeleOk ctx1 pt pids pn)
                            (match many psc _
                              ((TLOk z1 z2 z3 z4 z5 z6 z7 mq oq wf1 cr spt li ln)
                                (let (many acc) (erased bd) (binders pids))
                                (match many (elab-tele ctx ctx1 wf1 acc _ (cov-binders ctx pids ctx1 acc _ pt cr bd spt li) rs (POuter (PInner))) _
                                  ((TeleStuck c3 d3 e3 g3 mq) (TermStuck _ _))
                                  ((MkTeleDec c3 d3 e3 g3 mq rout er rsc)
                                    (match many rout _
                                      ((TeleErr r) (MkTermDec _ _ (TErr r) (ETFnRetsErr ctx lr ps rs l lty ctx1 pt pids pn acc r p sm ep bd er) (TSErr _ _)))
                                      ((TeleOk ctx2 rt rids rn)
                                        (match many rsc _
                                          ((TLOk y1 y2 y3 y4 y5 y6 y7 mq oq wf2 cr2 srt li2 ln2)
                                            (MkTermDec _ _ (TOk (Fn l pt rt) (Univ)) (ETFn ctx lr ps rs l lty ctx1 pt pids pn acc ctx2 rt rids rn p sm ep bd er)
                                              (TSOk _ _ _ (sc-fn ctx l pt rt _ _ sl spt srt) (sc-univ ctx))))))))))))))))))))))))
  (many elab-valctor : (many (Ctx) ctx) (many (WF ctx) wf) (many (List (Raw)) ps) (many (Raw) rr) (subterm many (Cons (Raw) (RList ps) (Cons (Raw) rr (Nil (Raw)))) is items) (subterm many (PInner) is ph) ->
      (many (TermDec ctx (RList (Cons (Raw) (RKey (KValCtor)) items))) r)
    (match many (elab-tele ctx ctx wf (Nil _) _ (cov-refl ctx) ps (POuter (PInner))) _
      ((TeleStuck c2 d2 e2 g2 mq) (TermStuck _ _))
      ((MkTeleDec c2 d2 e2 g2 mq pout ep psc)
        (match many pout _
          ((TeleErr r) (MkTermDec _ _ (TErr r) (ETValCtorParamsErr ctx ps rr r ep) (TSErr _ _)))
          ((TeleOk ctx1 pt pids pn)
            (match many psc _
              ((TLOk z1 z2 z3 z4 z5 z6 z7 mq oq wf1 cr spt li ln)
                (match many (elab-term ctx1 wf1 rr (POuter (PInner))) _
                  ((TermStuck a b) (TermStuck _ _))
                  ((MkTermDec a b rout er sc)
                    (match many rout _
                      ((TErr r) (MkTermDec _ _ (TErr r) (ETValCtorRetErr ctx ps rr ctx1 pt pids pn r ep er) (TSErr _ _)))
                      ((TOk ret rty)
                        (match erased sc _
                          ((TSOk a2 b2 c2 sret srty)
                            (let (many c) (erased cn) (erased scn) (canonical ctx1 wf1 ret sret))
                            (match many (former-ret-dec ctx1 wf1 pids c scn) _
                              ((FRBad d1 d2 d3 br) (MkTermDec _ _ (TErr (RBadReturn)) (ETValCtorBadRet ctx ps rr ctx1 pt pids pn ret rty c ep er cn br) (TSErr _ _)))
                              ((FROk d1 d2 t aps args tty tps nm tt ct)
                                (let (many acc) (erased bd) (binders pids))
                                (let (many ret2) (erased ab) (abstract acc ret))
                                (MkTermDec _ _ (TOk (ValCtor pt ret2) (Univ)) (ETValCtor ctx ps rr ctx1 pt pids pn acc ret rty t aps args tty tps ret2 ep er cn nm tt ct bd ab)
                                  (TSOk _ _ _ (sc-valctor ctx pt ret2 _ spt (sc-abstract ctx acc ctx1 _ ret ret2 (cov-binders ctx pids ctx1 acc _ pt cr bd spt li) sret ab)) (sc-univ ctx))))))))))))))))))
  (many elab-term-args : (many (Ctx) ctx) (many (WF ctx) wf) (many (List (Maybe (Term))) acc) (erased (Nat) m) (erased (ScS ctx acc m) sacc) (many (List (Entry)) tele) (erased (Nat) out) (erased (ScT ctx m tele out) stele) (subterm many (List (Raw)) args)
      (subterm many (POuter (PInner)) is ph) -> (many (ArgsDec ctx acc tele args) r)
    (match many (len-dec _ _ tele args) _
      ((LenDiff a b c d m) (MkArgsDec _ _ _ _ (ArgsErr (RArity)) (ETAArity ctx acc tele args m) (ASErr _ _)))
      ((LenSame a b c d le)
        (match many tele _
          ((Nil e) (match many args _ ((Nil g) (MkArgsDec _ _ _ _ (ArgsOk (Nil _)) (ETANil ctx acc) (ASOk _ _ (scl-nil ctx)))) ((Cons g x y) (match erased le _))))
          ((Cons e entry es)
            (match many args _
              ((Nil g) (match erased le _))
              ((Cons g ar rest)
                (match many entry _
                  ((MkEntry s i t)
                    (let (erased st) (erased ses) (sct-parts ctx _ _ s i t es stele))
                    (match many (elab-term ctx wf ar (POuter (PInner))) _
                      ((TermStuck h k) (ArgsStuck _ _ _ _))
                      ((MkTermDec h k aout p sc)
                        (match many aout _
                          ((TErr r) (MkArgsDec _ _ _ _ (ArgsErr r) (ETAErr ctx acc (MkEntry s i t) es ar rest r p) (ASErr _ _)))
                          ((TOk at aty)
                            (match erased sc _
                              ((TSOk h2 k2 l2 sat saty)
                                (let (many t2) (erased sb) (subst acc _ (scs-length ctx acc _ sacc) t (sc-closed ctx _ t st)))
                                (let (erased st2) (sc-subst ctx acc _ t t2 sacc st sb))
                                (match many i _
                                  ((BFalse)
                                    (match many (same-dec ctx wf aty t2 saty st2) _
                                      ((SDDiffer h3 k3 l3 d) (MkArgsDec _ _ _ _ (ArgsErr (RMismatch)) (ETATyMismatch ctx acc s t es ar rest at aty t2 p sb d) (ASErr _ _)))
                                      ((SDSame h3 k3 l3 sm)
                                        (match many (elab-term-args ctx wf (Cons _ (Some _ at) acc) _ (scs-cons ctx at acc _ sat sacc) es _ ses rest (POuter (PInner))) _
                                          ((ArgsStuck h4 k4 l4 m4) (ArgsStuck _ _ _ _))
                                          ((MkArgsDec h4 k4 l4 m4 rout q rsc)
                                            (match many rout _
                                              ((ArgsErr r) (MkArgsDec _ _ _ _ (ArgsErr r) (ETARestErr ctx acc s (BFalse) t es ar rest at aty r p q) (ASErr _ _)))
                                              ((ArgsOk ts)
                                                (match erased rsc _
                                                  ((ASOk h5 k5 sts) (MkArgsDec _ _ _ _ (ArgsOk (Cons _ at ts)) (ETATy ctx acc s t es ar rest at aty t2 ts p sb sm q) (ASOk _ _ (scl-cons ctx at ts sat sts))))))))))))
                                  ((BTrue)
                                    (match many (same-dec ctx wf at t2 sat st2) _
                                      ((SDDiffer h3 k3 l3 d) (MkArgsDec _ _ _ _ (ArgsErr (RMismatch)) (ETAIsMismatch ctx acc s t es ar rest at aty t2 p sb d) (ASErr _ _)))
                                      ((SDSame h3 k3 l3 sm)
                                        (match many (elab-term-args ctx wf (Cons _ (Some _ at) acc) _ (scs-cons ctx at acc _ sat sacc) es _ ses rest (POuter (PInner))) _
                                          ((ArgsStuck h4 k4 l4 m4) (ArgsStuck _ _ _ _))
                                          ((MkArgsDec h4 k4 l4 m4 rout q rsc)
                                            (match many rout _
                                              ((ArgsErr r) (MkArgsDec _ _ _ _ (ArgsErr r) (ETARestErr ctx acc s (BTrue) t es ar rest at aty r p q) (ASErr _ _)))
                                              ((ArgsOk ts)
                                                (match erased rsc _
                                                  ((ASOk h5 k5 sts) (MkArgsDec _ _ _ _ (ArgsOk (Cons _ at ts)) (ETAIs ctx acc s t es ar rest at aty t2 ts p sb sm q) (ASOk _ _ (scl-cons ctx at ts sat sts))))))))))))))))))))))))))))
  (many elab-tele : (erased (Ctx) ctx0) (many (Ctx) ctx) (many (WF ctx) wf) (many (List (Maybe (Nat))) acc) (erased (Nat) m) (erased (Cov ctx0 acc ctx m) cov) (subterm many (List (Raw)) raws) (subterm many (POuter (PInner)) is ph) ->
      (many (TeleDec ctx0 acc m ctx raws) r)
    (match many raws _
      ((Nil a) (MkTeleDec _ _ _ _ _ (TeleOk ctx (Nil _) (Nil _) (Nil _)) (ELNil ctx acc) (TLOk _ _ _ _ _ _ _ _ _ wf (covrev-nil ctx0 acc ctx _ cov) (sct-nil ctx0 _) (LENil _ _) (LENil _ _))))
      ((Cons a e rest)
        (match many (entry-dec e) _
          ((EntryNot b) (TeleStuck _ _ _ _ _))
          ((EntryShape b s i tr x shape sub)
            (match many (elab-term ctx wf (subterm (subterm-trans sub (prove-subterm e raws))) tr (POuter (PInner))) _
              ((TermStuck c d) (TeleStuck _ _ _ _ _))
              ((MkTermDec c d tout p sc)
                (match many tout _
                  ((TErr r) (MkTeleDec _ _ _ _ _ (TeleErr r) (ELTermErr ctx acc e s i tr x rest r shape p) (TLErr _ _ _ _ _)))
                  ((TOk t tty)
                    (match erased sc _
                      ((TSOk c2 d2 e2 st stty)
                        (match many i _
                          ((BFalse)
                            (match many (same-dec ctx wf tty (Univ) stty (sc-univ ctx)) _
                              ((SDDiffer g h k d) (MkTeleDec _ _ _ _ _ (TeleErr (RMismatch)) (ELNotType ctx acc e s tr x rest t tty shape p d) (TLErr _ _ _ _ _)))
                              ((SDSame g h k su)
                                (let (many id) (many ctx1) (erased m) (many wf1) (erased g1) (erased hid) (mint ctx wf (Some _ x) t (KPlain) (None _) st (scm-none ctx) (ROkNone _)))
                                (let (many t2) (erased ab) (abstract acc t))
                                (match many (elab-tele ctx0 ctx1 wf1 (Cons _ (Some _ id) acc) _ (cov-mint ctx0 acc ctx (Some _ x) t (KPlain) (None _) id ctx1 _ cov m) rest (POuter (PInner))) _
                                  ((TeleStuck g3 h3 k3 l3 mq) (TeleStuck _ _ _ _ _))
                                  ((MkTeleDec g3 h3 k3 l3 mq rout q rsc)
                                    (match many rout _
                                      ((TeleErr r) (MkTeleDec _ _ _ _ _ (TeleErr r) (ELRestErr ctx acc e s (BFalse) tr x rest t tty id ctx1 t (None _) r shape p (EMTy t tty) m q) (TLErr _ _ _ _ _)))
                                      ((TeleOk out es ids names)
                                        (match many rsc _
                                          ((TLOk y1 y2 y3 y4 y5 y6 y7 mq oq wf2 cr sct li ln)
                                            (MkTeleDec _ _ _ _ _ (TeleOk out (Cons _ (MkEntry s (BFalse) t2) es) (Cons _ id ids) (Cons _ (Some _ x) names))
                                              (ELTy ctx acc e s tr x rest t tty id ctx1 t2 out es ids names shape p su m ab q)
                                              (TLOk _ _ _ _ _ _ _ _ _ wf2 (covrev-cons ctx0 acc id ids out cr) (sct-cons ctx0 _ _ s (BFalse) t2 es (sc-abstract ctx0 acc ctx _ t t2 cov st ab) sct)
                                                (LECons _ _ _ id es ids li) (LECons _ _ _ (Some _ x) es names ln))))))))))))
                          ((BTrue)
                            (let (many id) (many ctx1) (erased m) (many wf1) (erased g1) (erased hid) (mint ctx wf (Some _ x) tty (KPlain) (Some _ t) stty (scm-some ctx t st) (ROkSome _ _ (NDPlain))))
                            (let (many t2) (erased ab) (abstract acc t))
                            (match many (elab-tele ctx0 ctx1 wf1 (Cons _ (Some _ id) acc) _ (cov-mint ctx0 acc ctx (Some _ x) tty (KPlain) (Some _ t) id ctx1 _ cov m) rest (POuter (PInner))) _
                              ((TeleStuck g3 h3 k3 l3 mq) (TeleStuck _ _ _ _ _))
                              ((MkTeleDec g3 h3 k3 l3 mq rout q rsc)
                                (match many rout _
                                  ((TeleErr r) (MkTeleDec _ _ _ _ _ (TeleErr r) (ELRestErr ctx acc e s (BTrue) tr x rest t tty id ctx1 tty (Some _ t) r shape p (EMIs t tty) m q) (TLErr _ _ _ _ _)))
                                  ((TeleOk out es ids names)
                                    (match many rsc _
                                      ((TLOk y1 y2 y3 y4 y5 y6 y7 mq oq wf2 cr sct li ln)
                                        (MkTeleDec _ _ _ _ _ (TeleOk out (Cons _ (MkEntry s (BTrue) t2) es) (Cons _ id ids) (Cons _ (Some _ x) names))
                                          (ELIs ctx acc e s tr x rest t tty id ctx1 t2 out es ids names shape p m ab q)
                                          (TLOk _ _ _ _ _ _ _ _ _ wf2 (covrev-cons ctx0 acc id ids out cr) (sct-cons ctx0 _ _ s (BTrue) t2 es (sc-abstract ctx0 acc ctx _ t t2 cov st ab) sct)
                                            (LECons _ _ _ id es ids li) (LECons _ _ _ (Some _ x) es names ln)))))))))))))))))))))))

; ---- Decisions for calls: the annotation among the arguments, the marked positions, the prefix check, and
; the shapes a proof's type must have. What a call's items yield is a subterm of the items, for the walk.

(def-adts
  (Elems : ((List (Raw)) parent) ((List (Raw)) args) -> Type
    enum
    (many ElNil : (erased (List (Raw)) parent) -> (Elems parent (Nil (Raw))))
    (many ElCons : (erased (List (Raw)) parent) (erased (Raw) a) (erased (List (Raw)) rest) (erased (Subterm (Raw) a (List (Raw)) parent) p) (erased (Elems parent rest) q) -> (Elems parent (Cons (Raw) a rest))))
  (AnnIn : ((List (Raw)) parent) ((Ann) ann) -> Type
    enum
    (many InNone : (erased (List (Raw)) parent) -> (AnnIn parent (ANone)))
    (many InPredates : (erased (List (Raw)) parent) (erased (Raw) p) (erased (Subterm (Raw) p (List (Raw)) parent) s) -> (AnnIn parent (APredates p)))
    (many InSubterm : (erased (List (Raw)) parent) (erased (Nat) i) (erased (Raw) p) (erased (Subterm (Raw) p (List (Raw)) parent) s) -> (AnnIn parent (ASubterm i p))))
  (PlainDec : ((List (Raw)) args) -> Type
    enum
    (many PlainYes : (erased (List (Raw)) args) (erased (Plain args) p) -> (PlainDec args))
    (many PlainNo : (erased (List (Raw)) args) -> (PlainDec args)))
  (AnnKeyDec : ((Key) k) -> Type
    enum
    (many AKNot : (erased (Key) k) (erased (NotAnnKey k) p) -> (AnnKeyDec k))
    (many AKPredates : -> (AnnKeyDec (KPredates)))
    (many AKSubterm : -> (AnnKeyDec (KSubterm)))
    (many AKOther : (erased (Key) k) -> (AnnKeyDec k)))
  (AnnItem : ((Raw) item) -> Type
    enum
    (many AIPredates : (many (Raw) p) -> (AnnItem (RList (Cons (Raw) (RKey (KPredates)) (Cons (Raw) p (Nil (Raw)))))))
    (many AISubterm : (many (Raw) p) -> (AnnItem (RList (Cons (Raw) (RKey (KSubterm)) (Cons (Raw) p (Nil (Raw)))))))
    (many AINone : (erased (Raw) item) -> (AnnItem item)))
  (SubAtDec : ((List (Raw)) items) -> Type
    enum
    (many SubAtYes : (erased (List (Raw)) items) (many (Nat) i) (many (Raw) p) (many (List (Raw)) args) (erased (SubtermAt items i p args) q) (erased (Subterm (Raw) p (List (Raw)) items) s) (erased (Elems items args) el) ->
       (SubAtDec items))
    (many SubAtNo : (erased (List (Raw)) items) -> (SubAtDec items)))
  (CallRawDec : ((List (Raw)) items) -> Type
    enum
    (many MkCallRaw : (erased (List (Raw)) items) (many (Ann) ann) (many (List (Raw)) args) (erased (CallRaw items ann args) p) (erased (AnnIn items ann) ai) (erased (Elems items args) el) -> (CallRawDec items))
    (many CallRawStuck : (erased (List (Raw)) items) -> (CallRawDec items))))

(def-fns _ $ erased elems-weaken : (erased (List (Raw)) inner) (erased (List (Raw)) outer) (erased (List (Raw)) args) (erased (Subterm (List (Raw)) inner (List (Raw)) outer) s) (subterm erased (Elems inner args) el) ->
    (erased (Elems outer args) el2)
  (match erased el _
    ((ElNil a) (ElNil outer))
    ((ElCons a x rest p q) (ElCons outer x rest (subterm-trans p s) (elems-weaken inner outer rest s q)))))
(def-fns _ $ erased elems-refl : (subterm erased (List (Raw)) args) -> (erased (Elems args args) el)
  (match erased args _
    ((Nil a) (ElNil _))
    ((Cons a x rest) (ElCons args x rest (prove-subterm x args) (elems-weaken rest args rest (prove-subterm rest args) (elems-refl rest))))))

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
(def-fns _ $ many subterm-at-dec : (subterm many (List (Raw)) items) -> (many (SubAtDec items) r)
  (match many items _
    ((Nil a) (SubAtNo _))
    ((Cons a x rest)
      (match many (ann-item x) _
        ((AISubterm p)
          (match many rest _
            ((Nil b) (SubAtNo _))
            ((Cons b arg args)
              (match many (plain-dec rest) _
                ((PlainYes c pl) (SubAtYes _ (Zero) p rest (SAHere p arg args pl) (prove-subterm p items) (elems-weaken rest items rest (prove-subterm rest items) (elems-refl rest))))
                ((PlainNo c) (SubAtNo _))))))
        (else
          (match many (plain-dec (Cons _ x (Nil _))) _
            ((PlainNo c) (SubAtNo _))
            ((PlainYes c pl)
              (match many (subterm-at-dec rest) _
                ((SubAtNo d) (SubAtNo _))
                ((SubAtYes d i p args q s el)
                  (SubAtYes _ (Succ i) p (Cons _ x args) (SAThere x rest i p args pl q) (subterm-trans s (prove-subterm rest items))
                    (ElCons items x args (prove-subterm x items) (elems-weaken rest items args (prove-subterm rest items) el))))))))))))
(def-fns _ $ many call-raw-dec : (many (List (Raw)) items) -> (many (CallRawDec items) r)
  (match many items _
    ((Nil a) (MkCallRaw _ (ANone) (Nil _) (CRPlain (Nil _) (PlainNil)) (InNone _) (ElNil _)))
    ((Cons a x rest)
      (match many (ann-item x) _
        ((AIPredates p)
          (match many (plain-dec rest) _
            ((PlainYes b pl) (MkCallRaw _ (APredates p) rest (CRPredates p rest pl) (InPredates _ p (prove-subterm p items)) (elems-weaken rest items rest (prove-subterm rest items) (elems-refl rest))))
            ((PlainNo b) (CallRawStuck _))))
        (else
          (match many (plain-dec items) _
            ((PlainYes b pl) (MkCallRaw _ (ANone) items (CRPlain items pl) (InNone _) (elems-refl items)))
            ((PlainNo b)
              (match many (subterm-at-dec items) _
                ((SubAtNo c) (CallRawStuck _))
                ((SubAtYes c i p args q s el) (MkCallRaw _ (ASubterm i p) args (CRSubterm items i p args q) (InSubterm _ i p s) el))))))))))

(def-adts
  (MarkedIndexDec : ((List (Entry)) ps) ((Nat) i) -> Type
    enum
    (many MIYesAt : (erased (List (Entry)) ps) (erased (Nat) i) (many (Nat) j) (erased (MarkedIndex ps i j) p) -> (MarkedIndexDec ps i))
    (many MINoAt : (erased (List (Entry)) ps) (erased (Nat) i) (erased (Unmarked ps i) p) -> (MarkedIndexDec ps i)))
  (PrefixDec : ((Ctx) ctx) ((Nat) j) ((List (Term)) as) ((List (Term)) bs) -> Type
    enum
    (many PrefixYes : (erased (Ctx) ctx) (erased (Nat) j) (erased (List (Term)) as) (erased (List (Term)) bs) (many (Term) b) (erased (SamePrefix ctx j as bs b) p) (erased (Sc ctx (Zero) b) sb) -> (PrefixDec ctx j as bs))
    (many PrefixNo : (erased (Ctx) ctx) (erased (Nat) j) (erased (List (Term)) as) (erased (List (Term)) bs) (erased (DifferPrefix ctx j as bs) p) -> (PrefixDec ctx j as bs)))
  ; A list of three or four terms, from its length.
  (As3 : ((List (Term)) as) -> Type
    enum
    (many MkAs3 : (erased (Term) a) (erased (Term) b) (erased (Term) c) -> (As3 (Cons (Term) a (Cons (Term) b (Cons (Term) c (Nil (Term))))))))
  (As4 : ((List (Term)) as) -> Type
    enum
    (many MkAs4 : (erased (Term) a) (erased (Term) b) (erased (Term) c) (erased (Term) d) -> (As4 (Cons (Term) a (Cons (Term) b (Cons (Term) c (Cons (Term) d (Nil (Term))))))))))
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
(def-fns _ $ many prefix-dec : (many (Ctx) ctx) (many (WF ctx) wf) (subterm many (Nat) j) (many (List (Term)) as) (many (List (Term)) bs) (erased (ScL ctx (Zero) as) sas) (erased (ScL ctx (Zero) bs) sbs) -> (many (PrefixDec ctx j as bs) r)
  (match many j _
    ((Zero)
      (match many bs _
        ((Nil a) (PrefixNo _ _ _ _ (DPNilB ctx (Zero) as)))
        ((Cons a b rest) (let (erased sb) (erased srest) (scl-parts ctx b rest sbs)) (PrefixYes _ _ _ _ b (SPZero ctx as b rest) sb))))
    ((Succ j2)
      (match many as _
        ((Nil a) (PrefixNo _ _ _ _ (DPNilA ctx (Succ j2) bs)))
        ((Cons a x xs)
          (match many bs _
            ((Nil b) (PrefixNo _ _ _ _ (DPNilB ctx (Succ j2) (Cons _ x xs))))
            ((Cons b y ys)
              (let (erased sx) (erased sxs) (scl-parts ctx x xs sas))
              (let (erased sy) (erased sys) (scl-parts ctx y ys sbs))
              (match many (same-dec ctx wf x y sx sy) _
                ((SDDiffer c d e df) (PrefixNo _ _ _ _ (DPHere ctx j2 x xs y ys df)))
                ((SDSame c d e sm)
                  (match many (prefix-dec ctx wf j2 xs ys sxs sys) _
                    ((PrefixNo c2 d2 e2 g2 p) (PrefixNo _ _ _ _ (DPThere ctx j2 x xs y ys sm p)))
                    ((PrefixYes c2 d2 e2 g2 bb p sb) (PrefixYes _ _ _ _ bb (SPSucc ctx j2 x xs y ys bb sm p) sb))))))))))))
(def-fns _ $ erased len3 : (erased (List (Term)) as) (erased (Length (Term) as (Succ (Succ (Succ (Zero))))) ln) -> (erased (As3 as) p)
  (match erased ln _ ((LenCons a x rest n l1) (match erased l1 _ ((LenCons b y rest2 n2 l2) (match erased l2 _ ((LenCons c z rest3 n3 l3) (match erased l3 _ ((LenNil d) (MkAs3 x y z))))))))))
(def-fns _ $ erased len4 : (erased (List (Term)) as) (erased (Length (Term) as (Succ (Succ (Succ (Succ (Zero)))))) ln) -> (erased (As4 as) p)
  (match erased ln _
    ((LenCons a x rest n l1)
      (match erased l1 _ ((LenCons b y rest2 n2 l2) (match erased l2 _ ((LenCons c z rest3 n3 l3) (match erased l3 _ ((LenCons d w rest4 n4 l4) (match erased l4 _ ((LenNil e) (MkAs4 x y z w))))))))))))

; A proof's canonical type as (Predates ty a lv), with each part the same as required, or why not.
(def-adts
  (PredatesDec : ((Ctx) ctx) ((Term) c) ((Term) l) ((Term) cur) -> Type
    enum
    (many PDYes : (erased (Ctx) ctx) (erased (Term) c) (erased (Term) l) (erased (Term) cur) (many (Term) h) (many (List (Entry)) hps) (many (Term) ty) (many (Term) a) (many (Term) lv)
       (erased (Same ctx h (Ref (Succ (Zero)))) sh) (erased (Same ctx ty level-ty) sty) (erased (Same ctx a l) sa) (erased (Same ctx lv cur) sc) ->
       (PredatesDec ctx (TyApp h hps (Cons (Term) ty (Cons (Term) a (Cons (Term) lv (Nil (Term)))))) l cur))
    (many PDNo : (erased (Ctx) ctx) (erased (Term) c) (erased (Term) l) (erased (Term) cur) (erased (NotPredates ctx c l cur) p) -> (PredatesDec ctx c l cur)))
  (SubtermDec : ((Ctx) ctx) ((Term) c) ((Term) a) ((Term) b) -> Type
    enum
    (many STYes : (erased (Ctx) ctx) (erased (Term) c) (erased (Term) a) (erased (Term) b) (many (Term) h) (many (List (Entry)) hps) (many (Term) ta) (many (Term) a0) (many (Term) tb) (many (Term) b0)
       (erased (Same ctx h (Ref (Succ (Succ (Zero))))) sh) (erased (Same ctx a0 a) sa) (erased (Same ctx b0 b) sb) ->
       (SubtermDec ctx (TyApp h hps (Cons (Term) ta (Cons (Term) a0 (Cons (Term) tb (Cons (Term) b0 (Nil (Term))))))) a b))
    (many STNo : (erased (Ctx) ctx) (erased (Term) c) (erased (Term) a) (erased (Term) b) (erased (NotSubtermOf ctx c a b) p) -> (SubtermDec ctx c a b))))
(def-fns _ $ many predates-dec : (many (Ctx) ctx) (many (WF ctx) wf) (many (Term) c) (many (Term) l) (many (Term) cur) (erased (Sc ctx (Zero) c) scc) (erased (Sc ctx (Zero) l) sl) (erased (Sc ctx (Zero) cur) scur) -> (many (PredatesDec ctx c l cur) r)
  (let (erased h1) (erased h2) (sc-builtin ctx wf))
  (match many (tyapp-dec c) _
    ((IsNotTyApp a na) (PDNo _ _ _ _ (NPNotApp ctx c l cur na)))
    ((IsTyApp h hps as)
      (let (erased sh) (erased sas) (sc-app-parts ctx _ h as (APTy h hps as) scc))
      (match many (not-len-dec (Succ (Succ (Succ (Zero)))) as) _
        ((LenIsNot b d nl) (PDNo _ _ _ _ (NPArity ctx h hps as l cur nl)))
        ((LenIs b d ln)
          (match erased (len3 as ln) _
            ((MkAs3 x1 x2 x3)
              (match many as _
                ((Cons e ty rest1)
                  (match many rest1 _
                    ((Cons g a rest2)
                      (match many rest2 _
                        ((Cons k lv rest3)
                          (let (erased sty) (erased srest1) (scl-parts ctx ty rest1 sas))
                          (let (erased sa) (erased srest2) (scl-parts ctx a rest2 srest1))
                          (let (erased slv) (erased srest3) (scl-parts ctx lv rest3 srest2))
                          (match many (same-dec ctx wf h (Ref (Succ (Zero))) sh (sc-ref ctx _ h1)) _
                            ((SDDiffer a1 b1 c1 df) (PDNo _ _ _ _ (NPHead ctx h hps as l cur df)))
                            ((SDSame a1 b1 c1 ssh)
                              (match many (same-dec ctx wf ty level-ty sty (sc-level-ty ctx wf)) _
                                ((SDDiffer a2 b2 c2 df) (PDNo _ _ _ _ (NPType ctx h hps ty a lv l cur df)))
                                ((SDSame a2 b2 c2 ssty)
                                  (match many (same-dec ctx wf a l sa sl) _
                                    ((SDDiffer a3 b3 c3 df) (PDNo _ _ _ _ (NPLevel ctx h hps ty a lv l cur df)))
                                    ((SDSame a3 b3 c3 ssa)
                                      (match many (same-dec ctx wf lv cur slv scur) _
                                        ((SDDiffer a4 b4 c4 df) (PDNo _ _ _ _ (NPCur ctx h hps ty a lv l cur df)))
                                        ((SDSame a4 b4 c4 ssc) (PDYes ctx c l cur h hps ty a lv ssh ssty ssa ssc))))))))))))))))))))))
(def-fns _ $ many subterm-dec : (many (Ctx) ctx) (many (WF ctx) wf) (many (Term) c) (many (Term) a) (many (Term) b) (erased (Sc ctx (Zero) c) scc) (erased (Sc ctx (Zero) a) sa) (erased (Sc ctx (Zero) b) sb) -> (many (SubtermDec ctx c a b) r)
  (let (erased h1) (erased h2) (sc-builtin ctx wf))
  (match many (tyapp-dec c) _
    ((IsNotTyApp x na) (STNo _ _ _ _ (NTNotApp ctx c a b na)))
    ((IsTyApp h hps as)
      (let (erased sh) (erased sas) (sc-app-parts ctx _ h as (APTy h hps as) scc))
      (match many (not-len-dec (Succ (Succ (Succ (Succ (Zero))))) as) _
        ((LenIsNot x d nl) (STNo _ _ _ _ (NTArity ctx h hps as a b nl)))
        ((LenIs x d ln)
          (match erased (len4 as ln) _
            ((MkAs4 x1 x2 x3 x4)
              (match many as _
                ((Cons e ta rest1)
                  (match many rest1 _
                    ((Cons g a0 rest2)
                      (match many rest2 _
                        ((Cons k tb rest3)
                          (match many rest3 _
                            ((Cons m b0 rest4)
                              (let (erased sta) (erased srest1) (scl-parts ctx ta rest1 sas))
                              (let (erased sa0) (erased srest2) (scl-parts ctx a0 rest2 srest1))
                              (let (erased stb) (erased srest3) (scl-parts ctx tb rest3 srest2))
                              (let (erased sb0) (erased srest4) (scl-parts ctx b0 rest4 srest3))
                              (match many (same-dec ctx wf h (Ref (Succ (Succ (Zero)))) sh (sc-ref ctx _ h2)) _
                                ((SDDiffer a1 b1 c1 df) (STNo _ _ _ _ (NTHead ctx h hps as a b df)))
                                ((SDSame a1 b1 c1 ssh)
                                  (match many (same-dec ctx wf a0 a sa0 sa) _
                                    ((SDDiffer a3 b3 c3 df) (STNo _ _ _ _ (NTSmall ctx h hps ta a0 tb b0 a b df)))
                                    ((SDSame a3 b3 c3 ssa)
                                      (match many (same-dec ctx wf b0 b sb0 sb) _
                                        ((SDDiffer a4 b4 c4 df) (STNo _ _ _ _ (NTBig ctx h hps ta a0 tb b0 a b df)))
                                        ((SDSame a4 b4 c4 ssb) (STYes ctx c a b h hps ta a0 tb b0 ssh ssa ssb))))))))))))))))))))))

; A declared type constructor and a declared constructor, read through the entry each was minted with.
(def-fns _ $ erased tycon-grew : (erased (Ctx) c1) (erased (Ctx) c2) (erased (Nat) tid) (many (WF c1) wf) (erased (Grew c1 c2) g) (erased (Tycon c1 tid) p) -> (erased (Tycon c2 tid) q)
  (let-match erased g (GrewBy n0 s0 e0 r0 a0 l0 sa0 n1 s1 e1 r1 a1 l1 sa1 le ext))
  (let-match erased p (MkTycon q1 q2 q3 q4 q5 q6 q7 q8 pt eo))
  (let-match many wf (MkWF m1 m2 m3 m4 m5 m6 m7 ranks top v al be se ss sr sa2 sl ssa bi rp))
  (MkTycon _ _ _ _ _ _ _ tid pt (ent-of-ext n0 e0 e1 tid (TyCtor pt) (KDecl) be eo ext)))
(def-fns _ $ erased tycons-grew : (erased (Ctx) c1) (erased (Ctx) c2) (erased (List (Nat)) tids) (many (WF c1) wf) (erased (Grew c1 c2) g) (subterm erased (Tycons c1 tids) p) -> (erased (Tycons c2 tids) q)
  (match erased p _
    ((TyNil a) (TyNil _))
    ((TyCons a tid rest t q2) (TyCons _ tid rest (tycon-grew c1 c2 tid wf g t) (tycons-grew c1 c2 rest wf g q2)))))
(def-fns _ $ many tycon-of : (many (Ctx) ctx) (many (WF ctx) wf) (many (Nat) tid) (erased (Tycon ctx tid) tc) ->
    (many (List (Entry)) pt) (many (Term) tty) (erased (TypeOf ctx tid tty) t) (erased (Canonical ctx tty (TyCtor pt)) c) (erased (Nat) pout) (erased (ScT ctx (Zero) pt pout) spt)
  (let-match erased tc (MkTycon q1 q2 q3 q4 q5 q6 q7 q8 pt0 eo))
  (let (many tty) (many k) (erased p) (erased q) (erased sty) (erased e2) (erased ee) (erased eo2) (type-of ctx wf tid (MkHas _ _ _ _ _ _ _ tid (ent-of-has _ tid _ _ eo))))
  (let-match erased ee (EntsOf z1 z2 z3 z4 z5 z6 z7))
  (match erased (ent-of-unique _ tid tty k (TyCtor pt0) (KDecl) eo2 eo) _
    ((SameEntRefl y1 y2)
      (let (many u) (erased cn) (erased su) (canonical ctx wf tty sty))
      (let-match erased cn (CanonicalBy x1 x2 x3 r0 rr can))
      (match erased (canon-tyctor r0 pt0 u can) _
        ((ITC pt2)
          (match many u _
            ((TyCtor pt) (let (erased pd) (erased spt) (sc-tyctor-parts ctx pt su)) (values pt tty p cn pd spt))))))))
(def-fns _ $ many ctor-of : (many (Ctx) ctx) (many (WF ctx) wf) (many (Nat) c) (erased (Ctor ctx c) cc) ->
    (many (List (Entry)) fs) (many (Term) ret) (many (Term) cty) (erased (TypeOf ctx c cty) t) (erased (Canonical ctx cty (ValCtor fs ret)) cn) (erased (Nat) fout) (erased (ScT ctx (Zero) fs fout) sfs) (erased (Sc ctx fout ret) sret)
  (let-match erased cc (MkCtor q1 q2 q3 q4 q5 q6 q7 q8 fs0 r0 eo))
  (let (many cty) (many k) (erased p) (erased q) (erased sty) (erased e2) (erased ee) (erased eo2) (type-of ctx wf c (MkHas _ _ _ _ _ _ _ c (ent-of-has _ c _ _ eo))))
  (let-match erased ee (EntsOf z1 z2 z3 z4 z5 z6 z7))
  (match erased (ent-of-unique _ c cty k (ValCtor fs0 r0) (KDecl) eo2 eo) _
    ((SameEntRefl y1 y2)
      (let (many u) (erased cn) (erased su) (canonical ctx wf cty sty))
      (let-match erased cn (CanonicalBy x1 x2 x3 rl rr can))
      (match erased (canon-valctor rl fs0 r0 u can) _
        ((IVC fs2 r2)
          (match many u _
            ((ValCtor fs ret)
              (let (erased fd) (erased sfs) (erased sret) (sc-valctor-parts ctx fs ret su))
              (values fs ret cty p cn fd sfs sret))))))))

; A constructor's canonical return against its own type constructor and arity: a head that is not that
; type constructor differs from it outright, both being free of rules.
(def-adts
  (RetDec : ((Ctx) ctx) ((Nat) tid) ((Nat) n) ((Term) c) -> Type
    enum
    (many RetYes : (erased (Ctx) ctx) (erased (Nat) tid) (erased (Nat) n) (many (List (Entry)) tps) (many (List (Term)) args) (erased (Length (Term) args n) ln) -> (RetDec ctx tid n (TyApp (Ref tid) tps args)))
    (many RetNo : (erased (Ctx) ctx) (erased (Nat) tid) (erased (Nat) n) (erased (Term) c) (erased (BadRet ctx tid n c) p) -> (RetDec ctx tid n c))))
(def-fns _ $ erased head-differ : (erased (Ctx) ctx) (erased (Term) h) (erased (Nat) tid) (erased (List (Ent)) e) (erased (Ents ctx e) ee) (erased (List (Rule)) r) (erased (Rules ctx r) rr) (erased (Canon r h h) chh)
    (erased (NonRef h) nr) (erased (NoRule r tid) nt) -> (erased (Differ ctx h (Ref tid)) d)
  (DifferBy ctx h (Ref tid) e r ee rr (UCheckRef e r h (Ref tid) (Nil _) (SR) tid h h (Ref tid) chh (CanFree r tid nt) (SidedR (Ref tid) h) nr)))
(def-fns _ $ many ret-dec : (many (Ctx) ctx) (many (WF ctx) wf) (many (Nat) tid) (erased (Tycon ctx tid) tc) (many (Nat) n) (erased (Term) ret) (many (Term) c) (erased (Canonical ctx ret c) cn) -> (many (RetDec ctx tid n c) r)
  (let-match many ctx (MkCtx nx s e r a l sa))
  (let-match many wf (MkWF m1 m2 m3 m4 m5 m6 m7 ranks top v al be se ss sr sa2 sl ssa bi rp))
  (let-match erased tc (MkTycon q1 q2 q3 q4 q5 q6 q7 q8 pt eo))
  (let-match erased cn (CanonicalBy z1 z2 z3 r0 rr can))
  (let-match erased rr (RulesOf y1 y2 y3 y4 y5 y6 y7))
  (let (erased cc) (canon-canonical r ret c can))
  (let (erased nt) (decl-no-rule e r tid (TyCtor pt) eo rp))
  (let (erased ee) (EntsOf nx s e r a l sa))
  (match many (tyapp-dec c) _
    ((IsNotTyApp x na) (RetNo _ _ _ _ (BRNotApp ctx tid n c na)))
    ((IsTyApp h hps as)
      (match erased cc _
        ((CnTyApp b h0 ps0 as0 ch cas)
          (match many h _
            ((Ref y)
              (match many (nat-dec y tid) _
                ((NDSame z)
                  (match many (not-len-dec n as) _
                    ((LenIsNot b2 d nl) (RetNo _ _ _ _ (BRArity ctx tid n (Ref y) hps as nl)))
                    ((LenIs b2 d ln) (RetYes _ _ _ hps as ln))))
                ((NDDiff z w nq)
                  (match erased ch _
                    ((CnRef b2 y0 ny)
                      (RetNo _ _ _ _ (BRHead ctx tid n (Ref y) hps as (DifferBy ctx (Ref y) (Ref tid) e r ee (RulesOf nx s e r a l sa) (UCheckRefRef e r (Ref y) (Ref tid) (Nil _) y tid (CanFree r y ny) (CanFree r tid nt) nq)))))))))
            ((Bound k) (RetNo _ _ _ _ (BRHead ctx tid n h hps as (head-differ ctx h tid e ee r (RulesOf nx s e r a l sa) (canonical-fix r h ch) (NRBound k) nt))))
            ((TyApp h2 ps2 as2) (RetNo _ _ _ _ (BRHead ctx tid n h hps as (head-differ ctx h tid e ee r (RulesOf nx s e r a l sa) (canonical-fix r h ch) (NRTyApp h2 ps2 as2) nt))))
            ((ValApp h2 ps2 r2 as2) (RetNo _ _ _ _ (BRHead ctx tid n h hps as (head-differ ctx h tid e ee r (RulesOf nx s e r a l sa) (canonical-fix r h ch) (NRValApp h2 ps2 r2 as2) nt))))
            ((Univ) (RetNo _ _ _ _ (BRHead ctx tid n h hps as (head-differ ctx h tid e ee r (RulesOf nx s e r a l sa) (canonical-fix r h ch) (NRUniv) nt))))
            ((Fn lv ps rs) (RetNo _ _ _ _ (BRHead ctx tid n h hps as (head-differ ctx h tid e ee r (RulesOf nx s e r a l sa) (canonical-fix r h ch) (NRFn lv ps rs) nt))))
            ((TyCtor ps) (RetNo _ _ _ _ (BRHead ctx tid n h hps as (head-differ ctx h tid e ee r (RulesOf nx s e r a l sa) (canonical-fix r h ch) (NRTyCtor ps) nt))))
            ((ValCtor ps rt) (RetNo _ _ _ _ (BRHead ctx tid n h hps as (head-differ ctx h tid e ee r (RulesOf nx s e r a l sa) (canonical-fix r h ch) (NRValCtor ps rt) nt))))))))))

; Why a canonical scrutinee type cannot be matched, or the declared type constructor at its head.
(def-adts
  (MatchableDec : ((Ctx) ctx) ((Term) c) -> Type
    enum
    (many MatchableYes : (erased (Ctx) ctx) (many (Nat) tc) (many (List (Entry)) tps) (many (List (Term)) targs) (many (List (Adt)) adts) (many (List (Nat)) ctors) (erased (Adts ctx adts) ad) (erased (AdtOf adts tc ctors) ao)
       (erased (Ctors ctx ctors) cs) -> (MatchableDec ctx (TyApp (Ref tc) tps targs)))
    (many MatchableNo : (erased (Ctx) ctx) (erased (Term) c) (erased (Unmatchable ctx c) p) -> (MatchableDec ctx c))))
(def-fns _ $ many matchable-dec : (many (Ctx) ctx) (many (WF ctx) wf) (many (Term) c) -> (many (MatchableDec ctx c) r)
  (let-match many ctx (MkCtx nx s e r a l sa))
  (let-match many wf (MkWF m1 m2 m3 m4 m5 m6 m7 ranks top v al be se ss sr sa2 sl ssa bi rp))
  (match many (tyapp-dec c) _
    ((IsNotTyApp x na) (MatchableNo _ _ (UmNotApp ctx c na)))
    ((IsTyApp h hps as)
      (match many h _
        ((Ref tc)
          (match many (adt-dec a tc) _
            ((AdtMiss b d n) (MatchableNo _ _ (UmNoAdt ctx tc hps as a (AdtsOf nx s e r a l sa) n)))
            ((AdtHit b d ctors ao)
              (let (erased ht) (erased acs) (adt-of-scoped e a tc ctors sa2 ao))
              (MatchableYes _ tc hps as a ctors (AdtsOf nx s e r a l sa) ao (MkCtors _ _ _ _ _ _ _ ctors acs)))))
        ((Bound k) (MatchableNo _ _ (UmHeadVar ctx (Bound k) hps as (NRBound k))))
        ((TyApp h2 ps2 as2) (MatchableNo _ _ (UmHeadVar ctx (TyApp h2 ps2 as2) hps as (NRTyApp h2 ps2 as2))))
        ((ValApp h2 ps2 r2 as2) (MatchableNo _ _ (UmHeadVar ctx (ValApp h2 ps2 r2 as2) hps as (NRValApp h2 ps2 r2 as2))))
        ((Univ) (MatchableNo _ _ (UmHeadVar ctx (Univ) hps as (NRUniv))))
        ((Fn lv ps rs) (MatchableNo _ _ (UmHeadVar ctx (Fn lv ps rs) hps as (NRFn lv ps rs))))
        ((TyCtor ps) (MatchableNo _ _ (UmHeadVar ctx (TyCtor ps) hps as (NRTyCtor ps))))
        ((ValCtor ps rt) (MatchableNo _ _ (UmHeadVar ctx (ValCtor ps rt) hps as (NRValCtor ps rt))))))))

; A canonical proof type as a Predates or Subterm application, or why not.
(def-adts
  (PShapeDec : ((Ctx) ctx) ((Term) c) -> Type
    enum
    (many PSYes : (erased (Ctx) ctx) (erased (Term) c) (many (Term) ty) (many (Term) a) (many (Term) lv) (erased (PredatesShape ctx c ty a lv) p) (erased (Sc ctx (Zero) ty) sty) (erased (Sc ctx (Zero) a) sa) (erased (Sc ctx (Zero) lv) slv) ->
       (PShapeDec ctx c))
    (many PSNo : (erased (Ctx) ctx) (erased (Term) c) (erased (NotPredatesShape ctx c) p) -> (PShapeDec ctx c)))
  (SShapeDec : ((Ctx) ctx) ((Term) c) -> Type
    enum
    (many SSYes : (erased (Ctx) ctx) (erased (Term) c) (many (Term) ta) (many (Term) a) (many (Term) tb) (many (Term) b) (erased (SubtermShape ctx c ta a tb b) p)
       (erased (Sc ctx (Zero) ta) sta) (erased (Sc ctx (Zero) a) sa) (erased (Sc ctx (Zero) tb) stb) (erased (Sc ctx (Zero) b) sb) -> (SShapeDec ctx c))
    (many SSNo : (erased (Ctx) ctx) (erased (Term) c) (erased (NotSubtermShape ctx c) p) -> (SShapeDec ctx c))))
(def-fns _ $ many predates-shape : (many (Ctx) ctx) (many (WF ctx) wf) (many (Term) c) (erased (Sc ctx (Zero) c) scc) -> (many (PShapeDec ctx c) r)
  (let (erased h1) (erased h2) (sc-builtin ctx wf))
  (match many (tyapp-dec c) _
    ((IsNotTyApp x na) (PSNo _ _ (NPSNotApp ctx c na)))
    ((IsTyApp h hps as)
      (let (erased sh) (erased sas) (sc-app-parts ctx _ h as (APTy h hps as) scc))
      (match many (not-len-dec (Succ (Succ (Succ (Zero)))) as) _
        ((LenIsNot b d nl) (PSNo _ _ (NPSArity ctx h hps as nl)))
        ((LenIs b d ln)
          (match many (same-dec ctx wf h (Ref (Succ (Zero))) sh (sc-ref ctx _ h1)) _
            ((SDDiffer a1 b1 c1 df) (PSNo _ _ (NPSHead ctx h hps as df)))
            ((SDSame a1 b1 c1 ssh)
              (match erased (len3 as ln) _
                ((MkAs3 x1 x2 x3)
                  (match many as _
                    ((Cons e ty rest1)
                      (match many rest1 _
                        ((Cons g a rest2)
                          (match many rest2 _
                            ((Cons k2 lv rest3)
                              (let (erased sty) (erased srest1) (scl-parts ctx ty rest1 sas))
                              (let (erased sa) (erased srest2) (scl-parts ctx a rest2 srest1))
                              (let (erased slv) (erased srest3) (scl-parts ctx lv rest3 srest2))
                              (PSYes ctx c ty a lv (PSBy ctx h hps ty a lv ssh) sty sa slv))))))))))))))))
(def-fns _ $ many subterm-shape : (many (Ctx) ctx) (many (WF ctx) wf) (many (Term) c) (erased (Sc ctx (Zero) c) scc) -> (many (SShapeDec ctx c) r)
  (let (erased h1) (erased h2) (sc-builtin ctx wf))
  (match many (tyapp-dec c) _
    ((IsNotTyApp x na) (SSNo _ _ (NSSNotApp ctx c na)))
    ((IsTyApp h hps as)
      (let (erased sh) (erased sas) (sc-app-parts ctx _ h as (APTy h hps as) scc))
      (match many (not-len-dec (Succ (Succ (Succ (Succ (Zero))))) as) _
        ((LenIsNot b d nl) (SSNo _ _ (NSSArity ctx h hps as nl)))
        ((LenIs b d ln)
          (match many (same-dec ctx wf h (Ref (Succ (Succ (Zero)))) sh (sc-ref ctx _ h2)) _
            ((SDDiffer a1 b1 c1 df) (SSNo _ _ (NSSHead ctx h hps as df)))
            ((SDSame a1 b1 c1 ssh)
              (match erased (len4 as ln) _
                ((MkAs4 x1 x2 x3 x4)
                  (match many as _
                    ((Cons e ta rest1)
                      (match many rest1 _
                        ((Cons g a rest2)
                          (match many rest2 _
                            ((Cons k2 tb rest3)
                              (match many rest3 _
                                ((Cons m b rest4)
                                  (let (erased sta) (erased srest1) (scl-parts ctx ta rest1 sas))
                                  (let (erased sa) (erased srest2) (scl-parts ctx a rest2 srest1))
                                  (let (erased stb) (erased srest3) (scl-parts ctx tb rest3 srest2))
                                  (let (erased sb) (erased srest4) (scl-parts ctx b rest4 srest3))
                                  (SSYes ctx c ta a tb b (SSBy ctx h hps ta a tb b ssh) sta sa stb sb))))))))))))))))))

; What each axiom concludes from two canonical proof types, with the evidence its rule wants; the
; derivation itself is assembled by [axiom-derivation], one case per axiom.
(def-adts
  (AxiomOk : ((Key) k) ((Ctx) ctx1) ((Term) cp) ((Ctx) ctx2) ((Term) cq) ((Term) concl) -> Type
    enum
    (many AOPredatesTrans : (erased (Ctx) ctx1) (erased (Term) cp) (erased (Ctx) ctx2) (erased (Term) cq) (erased (Term) ty) (erased (Term) a) (erased (Term) l1) (erased (Term) ty2) (erased (Term) l1b) (erased (Term) l2)
       (erased (PredatesShape ctx1 cp ty a l1) s1) (erased (PredatesShape ctx2 cq ty2 l1b l2) s2) (erased (Same ctx2 ty2 level-ty) st) (erased (Same ctx2 l1b l1) sl) ->
       (AxiomOk (KPredatesTrans) ctx1 cp ctx2 cq (TyApp (Ref (Succ (Zero))) predates-ps (Cons (Term) ty (Cons (Term) a (Cons (Term) l2 (Nil (Term))))))))
    (many AOSubtermTrans : (erased (Ctx) ctx1) (erased (Term) cp) (erased (Ctx) ctx2) (erased (Term) cq) (erased (Term) ta) (erased (Term) a) (erased (Term) tb) (erased (Term) b) (erased (Term) tb2) (erased (Term) b2) (erased (Term) tc) (erased (Term) c)
       (erased (SubtermShape ctx1 cp ta a tb b) s1) (erased (SubtermShape ctx2 cq tb2 b2 tc c) s2) (erased (Same ctx2 tb2 tb) st) (erased (Same ctx2 b2 b) sb) ->
       (AxiomOk (KSubtermTrans) ctx1 cp ctx2 cq (TyApp (Ref (Succ (Succ (Zero)))) subterm-ps (Cons (Term) ta (Cons (Term) a (Cons (Term) tc (Cons (Term) c (Nil (Term)))))))))
    (many AOPredatesSubterm : (erased (Ctx) ctx1) (erased (Term) cp) (erased (Ctx) ctx2) (erased (Term) cq) (erased (Term) ty) (erased (Term) a) (erased (Term) l) (erased (Term) tb) (erased (Term) b) (erased (Term) ty2) (erased (Term) a2)
       (erased (PredatesShape ctx1 cp ty a l) s1) (erased (SubtermShape ctx2 cq tb b ty2 a2) s2) (erased (Same ctx2 ty2 ty) st) (erased (Same ctx2 a2 a) sa) ->
       (AxiomOk (KPredatesSubterm) ctx1 cp ctx2 cq (TyApp (Ref (Succ (Zero))) predates-ps (Cons (Term) tb (Cons (Term) b (Cons (Term) l (Nil (Term)))))))))
  (AxiomDec : ((Key) k) ((Ctx) ctx1) ((Term) cp) ((Ctx) ctx2) ((Term) cq) -> Type
    enum
    (many AxOk : (erased (Key) k) (erased (Ctx) ctx1) (erased (Term) cp) (erased (Ctx) ctx2) (erased (Term) cq) (many (Term) concl) (erased (AxiomOk k ctx1 cp ctx2 cq concl) p) (erased (Sc ctx2 (Zero) concl) sc) ->
       (AxiomDec k ctx1 cp ctx2 cq))
    (many AxBad : (erased (Key) k) (erased (Ctx) ctx1) (erased (Term) cp) (erased (Ctx) ctx2) (erased (Term) cq) (erased (AxiomBad k ctx1 cp ctx2 cq) p) -> (AxiomDec k ctx1 cp ctx2 cq))))
(def-fns _ $ many axiom-check : (many (Key) k) (many (Ctx) ctx1) (many (WF ctx1) wf1) (many (Term) cp) (erased (Sc ctx1 (Zero) cp) scp) (many (Ctx) ctx2) (many (WF ctx2) wf2) (erased (Grew ctx1 ctx2) g) (many (Term) cq) (erased (Sc ctx2 (Zero) cq) scq)
    (erased (AxiomKey k) ak) -> (many (AxiomDec k ctx1 cp ctx2 cq) r)
  (let (erased h1) (erased h2) (sc-builtin ctx2 wf2))
  (match many k _
    ((KPredatesTrans)
      (match many (predates-shape ctx1 wf1 cp scp) _
        ((PSNo a b n) (AxBad _ _ _ _ _ (ABPredatesTransP ctx1 cp ctx2 cq n)))
        ((PSYes a b ty a1 l1 s1 sty sa1 sl1)
          (match many (predates-shape ctx2 wf2 cq scq) _
            ((PSNo c d n) (AxBad _ _ _ _ _ (ABPredatesTransQ ctx1 cp ctx2 cq n)))
            ((PSYes c d ty2 l1b l2 s2 sty2 sl1b sl2)
              (match many (same-dec ctx2 wf2 ty2 level-ty sty2 (sc-level-ty ctx2 wf2)) _
                ((SDDiffer e g2 h df) (AxBad _ _ _ _ _ (ABPredatesTransType ctx1 cp ctx2 cq ty2 l1b l2 s2 df)))
                ((SDSame e g2 h st)
                  (match many (same-dec ctx2 wf2 l1b l1 sl1b (sc-grew ctx1 ctx2 _ l1 g sl1)) _
                    ((SDDiffer e2 g3 h3 df) (AxBad _ _ _ _ _ (ABPredatesTransLink ctx1 cp ctx2 cq ty a1 l1 ty2 l1b l2 s1 s2 df)))
                    ((SDSame e2 g3 h3 sl)
                      (AxOk _ _ _ _ _ (TyApp (Ref (Succ (Zero))) predates-ps (Cons _ ty (Cons _ a1 (Cons _ l2 (Nil _))))) (AOPredatesTrans ctx1 cp ctx2 cq ty a1 l1 ty2 l1b l2 s1 s2 st sl)
                        (sc-predates ctx2 wf2 _ _ _ (sc-grew ctx1 ctx2 _ ty g sty) (sc-grew ctx1 ctx2 _ a1 g sa1) sl2)))))))))))
    ((KSubtermTrans)
      (match many (subterm-shape ctx1 wf1 cp scp) _
        ((SSNo a b n) (AxBad _ _ _ _ _ (ABSubtermTransP ctx1 cp ctx2 cq n)))
        ((SSYes a b ta a1 tb b1 s1 sta sa1 stb sb1)
          (match many (subterm-shape ctx2 wf2 cq scq) _
            ((SSNo c d n) (AxBad _ _ _ _ _ (ABSubtermTransQ ctx1 cp ctx2 cq n)))
            ((SSYes c d tb2 b2 tc c1 s2 stb2 sb2 stc sc1)
              (match many (same-dec ctx2 wf2 tb2 tb stb2 (sc-grew ctx1 ctx2 _ tb g stb)) _
                ((SDDiffer e g2 h df) (AxBad _ _ _ _ _ (ABSubtermTransType ctx1 cp ctx2 cq ta a1 tb b1 tb2 b2 tc c1 s1 s2 df)))
                ((SDSame e g2 h st)
                  (match many (same-dec ctx2 wf2 b2 b1 sb2 (sc-grew ctx1 ctx2 _ b1 g sb1)) _
                    ((SDDiffer e2 g3 h3 df) (AxBad _ _ _ _ _ (ABSubtermTransLink ctx1 cp ctx2 cq ta a1 tb b1 tb2 b2 tc c1 s1 s2 df)))
                    ((SDSame e2 g3 h3 sb)
                      (AxOk _ _ _ _ _ (TyApp (Ref (Succ (Succ (Zero)))) subterm-ps (Cons _ ta (Cons _ a1 (Cons _ tc (Cons _ c1 (Nil _)))))) (AOSubtermTrans ctx1 cp ctx2 cq ta a1 tb b1 tb2 b2 tc c1 s1 s2 st sb)
                        (sc-subterm ctx2 wf2 _ _ _ _ (sc-grew ctx1 ctx2 _ ta g sta) (sc-grew ctx1 ctx2 _ a1 g sa1) stc sc1)))))))))))
    ((KPredatesSubterm)
      (match many (predates-shape ctx1 wf1 cp scp) _
        ((PSNo a b n) (AxBad _ _ _ _ _ (ABPredatesSubtermP ctx1 cp ctx2 cq n)))
        ((PSYes a b ty a1 l s1 sty sa1 sl)
          (match many (subterm-shape ctx2 wf2 cq scq) _
            ((SSNo c d n) (AxBad _ _ _ _ _ (ABPredatesSubtermQ ctx1 cp ctx2 cq n)))
            ((SSYes c d tb b1 ty2 a2 s2 stb sb1 sty2 sa2)
              (match many (same-dec ctx2 wf2 ty2 ty sty2 (sc-grew ctx1 ctx2 _ ty g sty)) _
                ((SDDiffer e g2 h df) (AxBad _ _ _ _ _ (ABPredatesSubtermType ctx1 cp ctx2 cq ty a1 l tb b1 ty2 a2 s1 s2 df)))
                ((SDSame e g2 h st)
                  (match many (same-dec ctx2 wf2 a2 a1 sa2 (sc-grew ctx1 ctx2 _ a1 g sa1)) _
                    ((SDDiffer e2 g3 h3 df) (AxBad _ _ _ _ _ (ABPredatesSubtermLink ctx1 cp ctx2 cq ty a1 l tb b1 ty2 a2 s1 s2 df)))
                    ((SDSame e2 g3 h3 sa)
                      (AxOk _ _ _ _ _ (TyApp (Ref (Succ (Zero))) predates-ps (Cons _ tb (Cons _ b1 (Cons _ l (Nil _))))) (AOPredatesSubterm ctx1 cp ctx2 cq ty a1 l tb b1 ty2 a2 s1 s2 st sa)
                        (sc-predates ctx2 wf2 _ _ _ stb sb1 (sc-grew ctx1 ctx2 _ l g sl))))))))))))
    ((KFn) (match erased ak _)) ((KTyCtor) (match erased ak _)) ((KValCtor) (match erased ak _)) ((KIs) (match erased ak _)) ((KSubterm) (match erased ak _)) ((KPredates) (match erased ak _)) ((KLet) (match erased ak _)) ((KDefLvl) (match erased ak _)) ((KDefFns) (match erased ak _)) ((KDefAdts) (match erased ak _)) ((KMatch) (match erased ak _)) ((KValues) (match erased ak _)) ((KProveSubterm) (match erased ak _)) ((KProvePredates) (match erased ak _))))

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

; ---- Expressions, statements, bodies and declarations: one function per judgment. Beside each outcome
; that carries a context out, its well-formedness and growth, and that the ids it names are entries.

(def-adts
  (ESc : ((Ctx) ctx) ((EOut) out) -> Type
    enum
    (many ESOk : (erased (Ctx) ctx) (erased (Ctx) out) (erased (Core) core) (erased (List (Nat)) ids) (many (WF out) wf) (erased (Grew ctx out) g) (erased (HasAll out ids) h) -> (ESc ctx (EOk out core ids)))
    (many ESErr : (erased (Ctx) ctx) (erased (Reason) r) -> (ESc ctx (EErr r))))
  (AOSc : ((Ctx) ctx) ((AOut) out) -> Type
    enum
    (many AOOk : (erased (Ctx) ctx) (erased (Ctx) out) (erased (List (Core)) cores) (erased (List (Nat)) ids) (many (WF out) wf) (erased (Grew ctx out) g) (erased (HasAll out ids) h) -> (AOSc ctx (AOk out cores ids)))
    (many AOErr : (erased (Ctx) ctx) (erased (Reason) r) -> (AOSc ctx (AErr r))))
  (ArgsLen : ((List (Entry)) tele) ((AOut) out) -> Type
    enum
    (many ArgLenOk : (erased (List (Entry)) tele) (erased (Ctx) out) (erased (List (Core)) cores) (erased (List (Nat)) ids) (erased (LenEq (Entry) (Nat) tele ids) le) -> (ArgsLen tele (AOk out cores ids)))
    (many ArgLenErr : (erased (List (Entry)) tele) (erased (Reason) r) -> (ArgsLen tele (AErr r))))
  (NilCores : ((AOut) out) -> Type
    enum
    (many NCOk : (erased (Ctx) out) (erased (List (Nat)) ids) -> (NilCores (AOk out (Nil (Core)) ids)))
    (many NCErr : (erased (Reason) r) -> (NilCores (AErr r))))
  (SSc : ((Ctx) ctx) ((SOut) out) -> Type
    enum
    (many SSOk : (erased (Ctx) ctx) (erased (Ctx) out) (erased (Stmt) st) (many (WF out) wf) (erased (Grew ctx out) g) -> (SSc ctx (SOk out st)))
    (many SSErr : (erased (Ctx) ctx) (erased (Reason) r) -> (SSc ctx (SErr r))))
  (DSc : ((Ctx) ctx) ((DOut) out) -> Type
    enum
    (many DSOk : (erased (Ctx) ctx) (erased (Ctx) out) (many (WF out) wf) (erased (Grew ctx out) g) -> (DSc ctx (DOk out)))
    (many DSErr : (erased (Ctx) ctx) (erased (Reason) r) -> (DSc ctx (DErr r))))
  (BrSc : ((Ctx) ctx) ((BrOut) out) -> Type
    enum
    (many BrSOk : (erased (Ctx) ctx) (erased (Ctx) out) (erased (List (Branch)) bs) (erased (List (Nat)) seen) (many (WF out) wf) (erased (Grew ctx out) g) -> (BrSc ctx (BrOk out bs seen)))
    (many BrSErr : (erased (Ctx) ctx) (erased (Reason) r) -> (BrSc ctx (BrErr r))))
  (SigsSc : ((Ctx) ctx) ((List (Sig)) sigs) -> Type
    enum
    (many SigsNil : (erased (Ctx) ctx) -> (SigsSc ctx (Nil (Sig))))
    (many SigsCons : (erased (Ctx) ctx) (erased (Nat) fid) (erased (List (Entry)) pt) (erased (List (Maybe (String))) pn) (erased (List (Entry)) rt) (erased (List (Sig)) sigs)
       (erased (Nat) d1) (erased (Nat) d2) (erased (ScT ctx (Zero) pt d1) spt) (erased (ScT ctx d1 rt d2) srt) (erased (LenEq (Entry) (Maybe (String)) pt pn) lpn) (erased (SigsSc ctx sigs) q) -> (SigsSc ctx (Cons (Sig) (MkSig fid pt pn rt) sigs))))
  (FSc : ((Ctx) ctx) ((FOut) out) -> Type
    enum
    (many FSOk : (erased (Ctx) ctx) (erased (Ctx) out) (erased (List (Sig)) sigs) (many (WF out) wf) (erased (Grew ctx out) g) (erased (SigsSc out sigs) ss) -> (FSc ctx (FOk out sigs)))
    (many FSErr : (erased (Ctx) ctx) (erased (Reason) r) -> (FSc ctx (FErr r))))
  (FnsLen : ((List (Raw)) defs) ((FOut) out) -> Type
    enum
    (many FLOk : (erased (List (Raw)) defs) (erased (Ctx) out) (erased (List (Sig)) sigs) (erased (LenEq (Raw) (Sig) defs sigs) le) -> (FnsLen defs (FOk out sigs)))
    (many FLErr : (erased (List (Raw)) defs) (erased (Reason) r) -> (FnsLen defs (FErr r))))
  (BsSc : ((Ctx) ctx) ((BsOut) out) -> Type
    enum
    (many BsSOk : (erased (Ctx) ctx) (erased (Ctx) out) (erased (List (FnDef)) fds) (many (WF out) wf) (erased (Grew ctx out) g) -> (BsSc ctx (BsOk out fds)))
    (many BsSErr : (erased (Ctx) ctx) (erased (Reason) r) -> (BsSc ctx (BsErr r))))
  (TySc : ((Ctx) ctx) ((List (Raw)) decls) ((FOutT) out) -> Type
    enum
    (many TySOk : (erased (Ctx) ctx) (erased (List (Raw)) decls) (erased (Ctx) out) (erased (List (Nat)) tids) (many (WF out) wf) (erased (Grew ctx out) g) (erased (Tycons out tids) ty) (erased (LenEq (Raw) (Nat) decls tids) le) ->
       (TySc ctx decls (FOkT out tids)))
    (many TySErr : (erased (Ctx) ctx) (erased (List (Raw)) decls) (erased (Reason) r) -> (TySc ctx decls (FErrT r))))
  (CSc : ((Ctx) ctx) ((FOutT) out) -> Type
    enum
    (many CSOk : (erased (Ctx) ctx) (erased (Ctx) out) (erased (List (Nat)) ids) (many (WF out) wf) (erased (Grew ctx out) g) -> (CSc ctx (FOkT out ids)))
    (many CSErr : (erased (Ctx) ctx) (erased (Reason) r) -> (CSc ctx (FErrT r))))
  (DCSc : ((Ctx) ctx) ((FOutT) out) -> Type
    enum
    (many DCOk : (erased (Ctx) ctx) (erased (Ctx) out) (erased (List (Nat)) cids) (many (WF out) wf) (erased (Grew ctx out) g) (erased (Ctors out cids) cs) -> (DCSc ctx (FOkT out cids)))
    (many DCErr : (erased (Ctx) ctx) (erased (Reason) r) -> (DCSc ctx (FErrT r)))))

(def-adts
  (ExprDec : ((Ctx) ctx) ((Raw) raw) -> Type
    enum
    (many MkExprDec : (erased (Ctx) ctx) (erased (Raw) raw) (many (EOut) out) (erased (ElabExpr ctx raw out) p) (many (ESc ctx out) sc) -> (ExprDec ctx raw))
    (many ExprStuck : (erased (Ctx) ctx) (erased (Raw) raw) -> (ExprDec ctx raw)))
  (ItemsDec : ((Ctx) ctx) ((List (Raw)) raws) -> Type
    enum
    (many MkItemsDec : (erased (Ctx) ctx) (erased (List (Raw)) raws) (many (AOut) out) (erased (ElabItems ctx raws out) p) (many (AOSc ctx out) sc) -> (ItemsDec ctx raws))
    (many ItemsStuck : (erased (Ctx) ctx) (erased (List (Raw)) raws) -> (ItemsDec ctx raws)))
  (ExprArgsDec : ((Ctx) ctx) ((List (Maybe (Term))) acc) ((List (Entry)) tele) ((List (Raw)) args) -> Type
    enum
    (many MkExprArgsDec : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (List (Entry)) tele) (erased (List (Raw)) args) (many (AOut) out) (erased (ElabExprArgs ctx acc tele args out) p)
       (many (AOSc ctx out) sc) (erased (ArgsLen tele out) al) -> (ExprArgsDec ctx acc tele args))
    (many ExprArgsStuck : (erased (Ctx) ctx) (erased (List (Maybe (Term))) acc) (erased (List (Entry)) tele) (erased (List (Raw)) args) -> (ExprArgsDec ctx acc tele args)))
  (DecreaseDec : ((Ctx) ctx) ((Term) l) ((List (Entry)) ps) ((List (Nat)) ids) ((Ann) ann) -> Type
    enum
    (many MkDecreaseDec : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Nat)) ids) (erased (Ann) ann) (many (DOut) out) (erased (Decrease ctx l ps ids ann out) p) (many (DSc ctx out) sc) ->
       (DecreaseDec ctx l ps ids ann))
    (many DecreaseStuck : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Nat)) ids) (erased (Ann) ann) -> (DecreaseDec ctx l ps ids ann)))
  (BranchesDec : ((Ctx) ctx) ((Nat) s) ((Nat) tc) ((List (Nat)) ctors) ((List (Nat)) seen) ((List (Entry)) rt) ((List (Raw)) brs) -> Type
    enum
    (many MkBranchesDec : (erased (Ctx) ctx) (erased (Nat) s) (erased (Nat) tc) (erased (List (Nat)) ctors) (erased (List (Nat)) seen) (erased (List (Entry)) rt) (erased (List (Raw)) brs) (many (BrOut) out)
       (erased (ElabBranches ctx s tc ctors seen rt brs out) p) (many (BrSc ctx out) sc) -> (BranchesDec ctx s tc ctors seen rt brs))
    (many BranchesStuck : (erased (Ctx) ctx) (erased (Nat) s) (erased (Nat) tc) (erased (List (Nat)) ctors) (erased (List (Nat)) seen) (erased (List (Entry)) rt) (erased (List (Raw)) brs) -> (BranchesDec ctx s tc ctors seen rt brs)))
  (CoveredDec : ((Ctx) ctx) ((Nat) s) ((List (Nat)) ctors) ((List (Nat)) seen) -> Type
    enum
    (many CovYes : (erased (Ctx) ctx) (erased (Nat) s) (erased (List (Nat)) ctors) (erased (List (Nat)) seen) (erased (Covered ctx s ctors seen) p) -> (CoveredDec ctx s ctors seen))
    (many CovNo : (erased (Ctx) ctx) (erased (Nat) s) (erased (List (Nat)) ctors) (erased (List (Nat)) seen) (erased (Uncovered ctx s ctors seen) p) -> (CoveredDec ctx s ctors seen)))
  (RefutedDec : ((Ctx) ctx) ((Nat) s) ((Nat) c) -> Type
    enum
    (many RefYes : (erased (Ctx) ctx) (erased (Nat) s) (erased (Nat) c) (erased (Refuted ctx s c) p) -> (RefutedDec ctx s c))
    (many RefNo : (erased (Ctx) ctx) (erased (Nat) s) (erased (Nat) c) (erased (Reachable ctx s c) p) -> (RefutedDec ctx s c)))
  (BodyDec : ((Ctx) ctx) ((List (Raw)) items) -> Type
    enum
    (many MkBodyDec : (erased (Ctx) ctx) (erased (List (Raw)) items) (many (EOut) out) (erased (ElabBody ctx items out) p) (many (ESc ctx out) sc) -> (BodyDec ctx items))
    (many BodyStuck : (erased (Ctx) ctx) (erased (List (Raw)) items) -> (BodyDec ctx items)))
  (StmtDec : ((Ctx) ctx) ((Raw) raw) -> Type
    enum
    (many MkStmtDec : (erased (Ctx) ctx) (erased (Raw) raw) (many (SOut) out) (erased (ElabStmt ctx raw out) p) (many (SSc ctx out) sc) -> (StmtDec ctx raw))
    (many StmtStuck : (erased (Ctx) ctx) (erased (Raw) raw) -> (StmtDec ctx raw)))
  (BindLetDec : ((Ctx) ctx) ((List (Raw)) binders) ((List (Nat)) ids) -> Type
    enum
    (many MkBindLetDec : (erased (Ctx) ctx) (erased (List (Raw)) binders) (erased (List (Nat)) ids) (many (AOut) out) (erased (BindLet ctx binders ids out) p) (many (AOSc ctx out) sc) (erased (NilCores out) nc) ->
       (BindLetDec ctx binders ids))
    (many BindLetStuck : (erased (Ctx) ctx) (erased (List (Raw)) binders) (erased (List (Nat)) ids) -> (BindLetDec ctx binders ids)))
  (FnsDec : ((Ctx) ctx) ((Term) l) ((List (Raw)) defs) -> Type
    enum
    (many MkFnsDec : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Raw)) defs) (many (FOut) out) (erased (MintFns ctx l defs out) p) (many (FSc ctx out) sc) (erased (FnsLen defs out) fl) -> (FnsDec ctx l defs))
    (many FnsStuck : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Raw)) defs) -> (FnsDec ctx l defs)))
  (BodiesDec : ((Ctx) ctx) ((Term) l) ((List (Sig)) sigs) ((List (Raw)) defs) -> Type
    enum
    (many MkBodiesDec : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Sig)) sigs) (erased (List (Raw)) defs) (many (BsOut) out) (erased (ElabBodies ctx l sigs defs out) p) (many (BsSc ctx out) sc) -> (BodiesDec ctx l sigs defs))
    (many BodiesStuck : (erased (Ctx) ctx) (erased (Term) l) (erased (List (Sig)) sigs) (erased (List (Raw)) defs) -> (BodiesDec ctx l sigs defs)))
  (TyconsDec : ((Ctx) ctx) ((List (Raw)) decls) -> Type
    enum
    (many MkTyconsDec : (erased (Ctx) ctx) (erased (List (Raw)) decls) (many (FOutT) out) (erased (MintTycons ctx decls out) p) (many (TySc ctx decls out) sc) -> (TyconsDec ctx decls))
    (many TyconsStuck : (erased (Ctx) ctx) (erased (List (Raw)) decls) -> (TyconsDec ctx decls)))
  (CtorsDec : ((Ctx) ctx) ((List (Raw)) decls) ((List (Nat)) tids) -> Type
    enum
    (many MkCtorsDec : (erased (Ctx) ctx) (erased (List (Raw)) decls) (erased (List (Nat)) tids) (many (FOutT) out) (erased (MintCtors ctx decls tids out) p) (many (CSc ctx out) sc) -> (CtorsDec ctx decls tids))
    (many CtorsStuck : (erased (Ctx) ctx) (erased (List (Raw)) decls) (erased (List (Nat)) tids) -> (CtorsDec ctx decls tids)))
  (DeclCtorsDec : ((Ctx) ctx) ((Nat) tid) ((Nat) n) ((List (Raw)) ctors) -> Type
    enum
    (many MkDeclCtorsDec : (erased (Ctx) ctx) (erased (Nat) tid) (erased (Nat) n) (erased (List (Raw)) ctors) (many (FOutT) out) (erased (MintDeclCtors ctx tid n ctors out) p) (many (DCSc ctx out) sc) -> (DeclCtorsDec ctx tid n ctors))
    (many DeclCtorsStuck : (erased (Ctx) ctx) (erased (Nat) tid) (erased (Nat) n) (erased (List (Raw)) ctors) -> (DeclCtorsDec ctx tid n ctors))))

(def-fns _ $ erased sigs-grew : (erased (Ctx) c1) (erased (Ctx) c2) (erased (List (Sig)) sigs) (erased (Grew c1 c2) g) (subterm erased (SigsSc c1 sigs) p) -> (erased (SigsSc c2 sigs) q)
  (match erased p _
    ((SigsNil a) (SigsNil _))
    ((SigsCons a fid pt pn rt rest d1 d2 spt srt lpn q2) (SigsCons _ fid pt pn rt rest _ _ (sct-grew c1 c2 _ pt _ g spt) (sct-grew c1 c2 _ rt _ g srt) lpn (sigs-grew c1 c2 rest g q2)))))

; The results of a body against a return telescope.
(def-fns _ $ erased arglen-ok : (erased (List (Entry)) tele) (erased (Ctx) out) (erased (List (Core)) cores) (erased (List (Nat)) ids) (erased (ArgsLen tele (AOk out cores ids)) al) -> (erased (LenEq (Entry) (Nat) tele ids) le)
  (match erased al _ ((ArgLenOk a b c d le) le)))
(def-fns _ $ many check-rets : (many (Ctx) ctx) (many (WF ctx) wf) (many (List (Maybe (Term))) acc) (erased (Nat) m) (erased (ScS ctx acc m) sacc) (subterm many (List (Entry)) rets) (erased (Nat) out) (erased (ScT ctx m rets out) srets) (many (List (Nat)) ids)
    (erased (HasAll ctx ids) hids) -> (many (ROut) out) (erased (CheckRets ctx acc rets ids out) p)
  (match many (len-dec _ _ rets ids) _
    ((LenDiff a b c d m) (values (RErr (RSize)) (CRSize ctx acc rets ids m)))
    ((LenSame a b c d le)
      (match many rets _
        ((Nil e) (match many ids _ ((Nil g) (values (ROk) (CRNil ctx acc))) ((Cons g x y) (match erased le _))))
        ((Cons e entry es)
          (match many ids _
            ((Nil g) (match erased le _))
            ((Cons g x rest)
              (match many entry _
                ((MkEntry s i t)
                  (let (erased st) (erased ses) (sct-parts ctx _ _ s i t es srets))
                  (let (erased hx) (erased hrest) (has-all-parts ctx x rest hids))
                  (let (many t2) (erased sb) (subst acc _ (scs-length ctx acc _ sacc) t (sc-closed ctx _ t st)))
                  (let (erased st2) (sc-subst ctx acc _ t t2 sacc st sb))
                  (let (erased sacc2) (scs-cons ctx (Ref x) acc _ (sc-ref ctx x hx) sacc))
                  (match many i _
                    ((BFalse)
                      (let (many xty) (many kx) (erased ty) (erased kq) (erased sxty) (erased e2) (erased ee) (erased eo) (type-of ctx wf x hx))
                      (match many (same-dec ctx wf xty t2 sxty st2) _
                        ((SDDiffer h3 k3 l3 d2) (values (RErr (RMismatch)) (CRTyMismatch ctx acc s t es x rest xty t2 ty sb d2)))
                        ((SDSame h3 k3 l3 sm)
                          (let (many out) (erased q) (check-rets ctx wf (Cons _ (Some _ (Ref x)) acc) _ sacc2 es _ ses rest hrest))
                          (values out (CRTy ctx acc s t es x rest xty t2 out ty sb sm q)))))
                    ((BTrue)
                      (match many (same-dec ctx wf (Ref x) t2 (sc-ref ctx x hx) st2) _
                        ((SDDiffer h3 k3 l3 d2) (values (RErr (RMismatch)) (CRIsMismatch ctx acc s t es x rest t2 sb d2)))
                        ((SDSame h3 k3 l3 sm)
                          (let (many out) (erased q) (check-rets ctx wf (Cons _ (Some _ (Ref x)) acc) _ sacc2 es _ ses rest hrest))
                          (values out (CRIs ctx acc s t es x rest t2 out sb sm q)))))))))))))))

; The binders of a let, each aliasing one value.
(def-fns _ $ many bind-let : (many (Ctx) ctx) (many (WF ctx) wf) (subterm many (List (Raw)) binders) (many (List (Nat)) ids) (erased (HasAll ctx ids) hids) -> (many (BindLetDec ctx binders ids) r)
  (match many (len-dec _ _ binders ids) _
    ((LenDiff a b c d m) (MkBindLetDec _ _ _ (AErr (RSize)) (BLSize ctx binders ids m) (AOErr _ _) (NCErr _)))
    ((LenSame a b c d le)
      (match many binders _
        ((Nil e) (match many ids _ ((Nil g) (MkBindLetDec _ _ _ (AOk ctx (Nil _) (Nil _)) (BLNil ctx) (AOOk _ _ _ _ wf (grew-refl ctx) (has-all-nil ctx)) (NCOk _ _))) ((Cons g x y) (match erased le _))))
        ((Cons e b brest)
          (match many ids _
            ((Nil g) (match erased le _))
            ((Cons g id irest)
              (let (erased hid) (erased hirest) (has-all-parts ctx id irest hids))
              (let (many ty) (many kt) (erased t) (erased kq) (erased sty) (erased e2) (erased ee) (erased eo) (type-of ctx wf id hid))
              (match many b _
                ((RAtom x)
                  (let (many aid) (many ctx1) (erased m) (many wf1) (erased g1) (erased eis) (mint ctx wf (Some _ x) ty (KPlain) (Some _ (Ref id)) sty (scm-some ctx (Ref id) (sc-ref ctx id hid)) (ROkSome _ _ (NDPlain))))
                  (match many (bind-let ctx1 wf1 brest irest (has-all-grew ctx ctx1 irest g1 hirest)) _
                    ((BindLetStuck h2 k2 l2) (BindLetStuck _ _ _))
                    ((MkBindLetDec h2 k2 l2 rout q rsc nc)
                      (match many rout _
                        ((AErr r) (MkBindLetDec _ _ _ (AErr r) (BLRestErr ctx (RAtom x) brest id irest x ty aid ctx1 r (BNAtom x) t m q) (AOErr _ _) (NCErr _)))
                        ((AOk out cores aids)
                          (match erased nc _
                            ((NCOk z1 z2)
                              (match many rsc _
                                ((AOOk y1 y2 y3 y4 wf2 g2 h2)
                                  (MkBindLetDec _ _ _ (AOk out (Nil _) (Cons _ aid aids)) (BLName ctx x brest id irest ty aid ctx1 out aids t m q)
                                    (AOOk _ _ _ _ wf2 (grew-trans ctx ctx1 out g1 g2) (has-all-cons out aid aids (has-grew ctx1 out aid g2 (entis-has ctx1 aid _ _ eis)) h2)) (NCOk _ _)))))))))))
                (else
                  (match many (entry-dec b) _
                    ((EntryNot h) (BindLetStuck _ _ _))
                    ((EntryShape h s i tr x shape sub)
                      (match many s _
                        ((BTrue) (BindLetStuck _ _ _))
                        ((BFalse)
                          (match many (elab-term ctx wf tr (POuter (PInner))) _
                            ((TermStuck k l) (BindLetStuck _ _ _))
                            ((MkTermDec k l tout et tsc)
                              (match many tout _
                                ((TErr r) (MkBindLetDec _ _ _ (AErr r) (BLTermErr ctx b i tr x brest id irest r shape et) (AOErr _ _) (NCErr _)))
                                ((TOk t0 tty)
                                  (match erased tsc _
                                    ((TSOk k2 l2 m2 st0 stty)
                                      (match many i _
                                        ((BFalse)
                                          (match many (same-dec ctx wf ty t0 sty st0) _
                                            ((SDDiffer k3 l3 m3 d2) (MkBindLetDec _ _ _ (AErr (RMismatch)) (BLTyMismatch ctx b tr x brest id irest t0 tty ty shape et t d2) (AOErr _ _) (NCErr _)))
                                            ((SDSame k3 l3 m3 sm)
                                              (let (many aid) (many ctx1) (erased m) (many wf1) (erased g1) (erased eis) (mint ctx wf (Some _ x) ty (KPlain) (Some _ (Ref id)) sty (scm-some ctx (Ref id) (sc-ref ctx id hid)) (ROkSome _ _ (NDPlain))))
                                              (match many (bind-let ctx1 wf1 brest irest (has-all-grew ctx ctx1 irest g1 hirest)) _
                                                ((BindLetStuck h2 k4 l4) (BindLetStuck _ _ _))
                                                ((MkBindLetDec h2 k4 l4 rout q rsc nc)
                                                  (match many rout _
                                                    ((AErr r) (MkBindLetDec _ _ _ (AErr r) (BLRestErr ctx b brest id irest x ty aid ctx1 r (BNEntry b (BFalse) tr x shape) t m q) (AOErr _ _) (NCErr _)))
                                                    ((AOk out cores aids)
                                                      (match erased nc _
                                                        ((NCOk z1 z2)
                                                          (match many rsc _
                                                            ((AOOk y1 y2 y3 y4 wf2 g2 h2)
                                                              (MkBindLetDec _ _ _ (AOk out (Nil _) (Cons _ aid aids)) (BLTy ctx b tr x brest id irest t0 tty ty aid ctx1 out aids shape et t sm m q)
                                                                (AOOk _ _ _ _ wf2 (grew-trans ctx ctx1 out g1 g2) (has-all-cons out aid aids (has-grew ctx1 out aid g2 (entis-has ctx1 aid _ _ eis)) h2)) (NCOk _ _)))))))))))))
                                        ((BTrue)
                                          (match many (same-dec ctx wf (Ref id) t0 (sc-ref ctx id hid) st0) _
                                            ((SDDiffer k3 l3 m3 d2) (MkBindLetDec _ _ _ (AErr (RMismatch)) (BLIsMismatch ctx b tr x brest id irest t0 tty shape et d2) (AOErr _ _) (NCErr _)))
                                            ((SDSame k3 l3 m3 sm)
                                              (let (many aid) (many ctx1) (erased m) (many wf1) (erased g1) (erased eis) (mint ctx wf (Some _ x) ty (KPlain) (Some _ (Ref id)) sty (scm-some ctx (Ref id) (sc-ref ctx id hid)) (ROkSome _ _ (NDPlain))))
                                              (match many (bind-let ctx1 wf1 brest irest (has-all-grew ctx ctx1 irest g1 hirest)) _
                                                ((BindLetStuck h2 k4 l4) (BindLetStuck _ _ _))
                                                ((MkBindLetDec h2 k4 l4 rout q rsc nc)
                                                  (match many rout _
                                                    ((AErr r) (MkBindLetDec _ _ _ (AErr r) (BLRestErr ctx b brest id irest x ty aid ctx1 r (BNEntry b (BTrue) tr x shape) t m q) (AOErr _ _) (NCErr _)))
                                                    ((AOk out cores aids)
                                                      (match erased nc _
                                                        ((NCOk z1 z2)
                                                          (match many rsc _
                                                            ((AOOk y1 y2 y3 y4 wf2 g2 h2)
                                                              (MkBindLetDec _ _ _ (AOk out (Nil _) (Cons _ aid aids)) (BLIs ctx b tr x brest id irest t0 tty ty aid ctx1 out aids shape et t sm m q)
                                                                (AOOk _ _ _ _ wf2 (grew-trans ctx ctx1 out g1 g2) (has-all-cons out aid aids (has-grew ctx1 out aid g2 (entis-has ctx1 aid _ _ eis)) h2)) (NCOk _ _)))))))))))))))))))))))))))))))))

; A constructor refuted by the facts, or reachable; every constructor covered.
(def-fns _ $ many refuted : (many (Ctx) ctx) (many (WF ctx) wf) (many (Nat) s) (erased (Has ctx s) hs) (many (Nat) c) (erased (Ctor ctx c) cc) -> (many (RefutedDec ctx s c) r)
  (let (many fs) (many ret) (many cty) (erased t) (erased cn) (erased fd) (erased sfs) (erased sret) (ctor-of ctx wf c cc))
  (let (many names) (erased nn) (erased ln) (nones fs))
  (match many (mint-tele ctx wf (Nil _) _ (scs-nil ctx) fs _ sfs names ln) _
    ((MTMinted a2 b2 c2 d2 ctxF fids wfF gF hfids le mt)
      (let (many frefs) (erased rf) (refs fids))
      (let (erased sfrefs) (refs-scoped ctxF fids frefs hfids rf))
      (match many (refine ctxF wfF (Ref s) (ValApp (Ref c) fs ret frefs) (sc-ref ctxF s (has-grew ctx ctxF s gF hs)) (sc-valapp ctxF (Ref c) fs ret frefs _ (sc-ref ctxF c (has-grew ctx ctxF c gF (ctor-has ctx c cc))) (sct-grew ctx ctxF _ fs _ gF sfs) (sc-grew ctx ctxF _ ret gF sret) sfrefs (refs-len-eq fs fids frefs le rf))) _
        ((RDContradicted a5 b5 c5 cd) (RefYes _ _ _ (RefutedBy ctx s c cty fs ret names ctxF fids frefs t cn nn mt rf cd)))
        ((RDRefined a5 b5 c5 ctxR wfR gR rf2) (RefNo _ _ _ (ReachableBy ctx s c cty fs ret names ctxF fids frefs ctxR t cn nn mt rf rf2)))))))
(def-fns _ $ many covered : (many (Ctx) ctx) (many (WF ctx) wf) (many (Nat) s) (erased (Has ctx s) hs) (subterm many (List (Nat)) ctors) (erased (Ctors ctx ctors) cs) (many (List (Nat)) seen) -> (many (CoveredDec ctx s ctors seen) r)
  (match many ctors _
    ((Nil a) (CovYes _ _ _ _ (CvNil ctx s seen)))
    ((Cons a c rest)
      (match many (mem-dec c seen) _
        ((MemYes b d m)
          (match many (covered ctx wf s hs rest (ctors-parts ctx c rest cs) seen) _
            ((CovYes e g h k p) (CovYes _ _ _ _ (CvSeen ctx s c rest seen m p)))
            ((CovNo e g h k p) (CovNo _ _ _ _ (UcThere ctx s c rest seen p)))))
        ((MemNo b d nm)
          (match many (refuted ctx wf s hs c (ctors-head ctx c rest cs)) _
            ((RefNo e g h rc) (CovNo _ _ _ _ (UcHere ctx s c rest seen nm rc)))
            ((RefYes e g h rf)
              (match many (covered ctx wf s hs rest (ctors-parts ctx c rest cs) seen) _
                ((CovYes e2 g2 h2 k2 p) (CovYes _ _ _ _ (CvRefuted ctx s c rest seen nm rf p)))
                ((CovNo e2 g2 h2 k2 p) (CovNo _ _ _ _ (UcThere ctx s c rest seen p)))))))))))

; A def-fns's signatures.
(def-fns _
  (many mint-fns : (many (Ctx) ctx) (many (WF ctx) wf) (many (Term) l) (erased (Sc ctx (Zero) l) sl) (subterm many (List (Raw)) defs) (subterm many (POuter (PInner)) is ph) -> (many (FnsDec ctx l defs) r)
    (match many defs _
      ((Nil a) (MkFnsDec _ _ _ (FOk ctx (Nil _)) (MFNil ctx l) (FSOk _ _ _ wf (grew-refl ctx) (SigsNil _)) (FLOk _ _ _ (LENil _ _))))
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
                                  ((RList rs) (mint-fn ctx wf l sl fn ps rs items rest defs (PInner)))
                                  (else (FnsStuck _ _ _))))
                              (else (FnsStuck _ _ _))))
                          (else (FnsStuck _ _ _))))
                      (else (FnsStuck _ _ _))))
                  (else (FnsStuck _ _ _))))
              (else (FnsStuck _ _ _))))
          (else (FnsStuck _ _ _))))))
  (many mint-fn : (many (Ctx) ctx) (many (WF ctx) wf) (many (Term) l) (erased (Sc ctx (Zero) l) sl) (many (String) fn) (many (List (Raw)) ps) (many (List (Raw)) rs) (many (List (Raw)) items) (many (List (Raw)) rest)
      (subterm many (Cons (Raw) (RList (Cons (Raw) (RAtom fn) (Cons (Raw) (RList ps) (Cons (Raw) (RList rs) items)))) rest) is defs) (subterm many (PInner) is ph) -> (many (FnsDec ctx l defs) r)
    (match many (elab-tele ctx ctx wf (Nil _) _ (cov-refl ctx) ps (POuter (PInner))) _
      ((TeleStuck a b c d mq) (FnsStuck _ _ _))
      ((MkTeleDec a b c d mq pout ep psc)
        (match many pout _
          ((TeleErr r) (MkFnsDec _ _ _ (FErr r) (MFParamsErr ctx l fn ps rs items rest r ep) (FSErr _ _) (FLErr _ _)))
          ((TeleOk ctxP pt pids pn)
            (match many psc _
              ((TLOk z1 z2 z3 z4 z5 z6 z7 mq oq wfP cr spt li ln)
                (let (many acc) (erased bd) (binders pids))
                (match many (elab-tele ctx ctxP wfP acc _ (cov-binders ctx pids ctxP acc _ pt cr bd spt li) rs (POuter (PInner))) _
                  ((TeleStuck a2 b2 c2 d2 mq) (FnsStuck _ _ _))
                  ((MkTeleDec a2 b2 c2 d2 mq rout er rsc)
                    (match many rout _
                      ((TeleErr r) (MkFnsDec _ _ _ (FErr r) (MFRetsErr ctx l fn ps rs items rest ctxP pt pids pn acc r ep bd er) (FSErr _ _) (FLErr _ _)))
                      ((TeleOk ctxR rt rids rn)
                        (match many rsc _
                          ((TLOk y1 y2 y3 y4 y5 y6 y7 mq oq wfR cr2 srt li2 ln2)
                            (let (many fid) (many ctx1) (erased m) (many wf1) (erased g1) (erased eis) (mint ctx wf (Some _ fn) (Fn l pt rt) (KPlain) (None _) (sc-fn ctx l pt rt _ _ sl spt srt) (scm-none ctx) (ROkNone _)))
                            (match many (mint-fns ctx1 wf1 l (sc-grew ctx ctx1 _ l g1 sl) rest (POuter (PInner))) _
                              ((FnsStuck a3 b3 c3) (FnsStuck _ _ _))
                              ((MkFnsDec a3 b3 c3 fout q fsc fl)
                                (match many fout _
                                  ((FErr r) (MkFnsDec _ _ _ (FErr r) (MFRestErr ctx l fn ps rs items rest ctxP pt pids pn acc ctxR rt rids rn fid ctx1 r ep bd er m q) (FSErr _ _) (FLErr _ _)))
                                  ((FOk out sigs)
                                    (match many fsc _
                                      ((FSOk x1 x2 x3 wf2 g2 ssigs)
                                        (match erased fl _
                                          ((FLOk w1 w2 w3 le)
                                            (let (erased g) (grew-trans ctx ctx1 out g1 g2))
                                            (MkFnsDec _ _ _ (FOk out (Cons _ (MkSig fid pt pn rt) sigs)) (MFCons ctx l fn ps rs items rest ctxP pt pids pn acc ctxR rt rids rn fid ctx1 out sigs ep bd er m q)
                                              (FSOk _ _ _ wf2 g (SigsCons _ fid pt pn rt sigs _ _ (sct-grew ctx out _ pt _ g spt) (sct-grew ctx out _ rt _ g srt) ln ssigs))
                                              (FLOk _ _ _ (LECons _ _ (RList (Cons _ (RAtom fn) (Cons _ (RList ps) (Cons _ (RList rs) items)))) (MkSig fid pt pn rt) rest sigs le)))))))))))))))))))))))))

; def-adts: the type constructors, then the constructors, each declaration adding its ADT.
(def-fns _
  (many mint-decl-ctors : (many (Ctx) ctx) (many (WF ctx) wf) (many (Nat) tid) (erased (Tycon ctx tid) tc) (many (Nat) n) (subterm many (List (Raw)) ctors) (subterm many (POuter (PInner)) is ph) -> (many (DeclCtorsDec ctx tid n ctors) r)
    (match many ctors _
      ((Nil a) (MkDeclCtorsDec _ _ _ _ (FOkT ctx (Nil _)) (MDNil ctx tid n) (DCOk _ _ _ wf (grew-refl ctx) (ctors-nil ctx))))
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
                                  ((RList fs) (mint-decl-ctor ctx wf tid tc n cn fs rr rest ctors (PInner)))
                                  (else (DeclCtorsStuck _ _ _ _))))
                              (else (DeclCtorsStuck _ _ _ _))))
                          (else (DeclCtorsStuck _ _ _ _))))
                      (else (DeclCtorsStuck _ _ _ _))))
                  (else (DeclCtorsStuck _ _ _ _))))
              (else (DeclCtorsStuck _ _ _ _))))
          (else (DeclCtorsStuck _ _ _ _))))))
  (many mint-decl-ctor : (many (Ctx) ctx) (many (WF ctx) wf) (many (Nat) tid) (erased (Tycon ctx tid) tc) (many (Nat) n) (many (String) cn) (many (List (Raw)) fs) (many (Raw) rr) (many (List (Raw)) rest)
      (subterm many (Cons (Raw) (RList (Cons (Raw) (RAtom cn) (Cons (Raw) (RList fs) (Cons (Raw) rr (Nil (Raw)))))) rest) is ctors) (subterm many (PInner) is ph) -> (many (DeclCtorsDec ctx tid n ctors) r)
    (match many (elab-tele ctx ctx wf (Nil _) _ (cov-refl ctx) fs (POuter (PInner))) _
      ((TeleStuck a b c d mq) (DeclCtorsStuck _ _ _ _))
      ((MkTeleDec a b c d mq fout ef fsc)
        (match many fout _
          ((TeleErr r) (MkDeclCtorsDec _ _ _ _ (FErrT r) (MDFieldsErr ctx tid n cn fs rr rest r ef) (DCErr _ _)))
          ((TeleOk ctxF ft fids fn)
            (match many fsc _
              ((TLOk z1 z2 z3 z4 z5 z6 z7 mq oq wfF cr sft li ln)
                (let (erased gF) (covrev-grew ctx (Nil _) fids ctxF cr))
                (match many (elab-term ctxF wfF rr (POuter (PInner))) _
                  ((TermStuck d2 e2) (DeclCtorsStuck _ _ _ _))
                  ((MkTermDec d2 e2 rout er tsc)
                    (match many rout _
                      ((TErr r) (MkDeclCtorsDec _ _ _ _ (FErrT r) (MDRetErr ctx tid n cn fs rr rest ctxF ft fids fn r ef er) (DCErr _ _)))
                      ((TOk ret rty)
                        (match erased tsc _
                          ((TSOk y1 y2 y3 sret srty)
                            (let (many c) (erased crn) (erased scc) (canonical ctxF wfF ret sret))
                            (match many (ret-dec ctxF wfF tid (tycon-grew ctx ctxF tid wf gF tc) n ret c crn) _
                              ((RetNo a1 b1 c1 d1 br) (MkDeclCtorsDec _ _ _ _ (FErrT (RBadReturn)) (MDBadRet ctx tid n cn fs rr rest ctxF ft fids fn ret rty c ef er crn br) (DCErr _ _)))
                              ((RetYes a1 b1 c1 tps args lnn)
                                (let (many acc) (erased bd) (binders fids))
                                (let (many ret2) (erased ab) (abstract acc ret))
                                (let (erased sret2) (sc-abstract ctx acc ctxF _ ret ret2 (cov-binders ctx fids ctxF acc _ ft cr bd sft li) sret ab))
                                (let (many cid) (many ctx1) (erased m) (many wf1) (erased g1) (erased eis) (mint ctx wf (Some _ cn) (ValCtor ft ret2) (KDecl) (None _) (sc-valctor ctx ft ret2 _ sft sret2) (scm-none ctx) (ROkNone _)))
                                (match many (mint-decl-ctors ctx1 wf1 tid (tycon-grew ctx ctx1 tid wf g1 tc) n rest (POuter (PInner))) _
                                  ((DeclCtorsStuck a3 b3 c3 d3) (DeclCtorsStuck _ _ _ _))
                                  ((MkDeclCtorsDec a3 b3 c3 d3 dout q dsc)
                                    (match many dout _
                                      ((FErrT r) (MkDeclCtorsDec _ _ _ _ (FErrT r) (MDRestErr ctx tid n cn fs rr rest ctxF ft fids fn ret rty tps args acc ret2 cid ctx1 r ef er crn lnn bd ab m q) (DCErr _ _)))
                                      ((FOkT out cids)
                                        (match many dsc _
                                          ((DCOk x1 x2 x3 wf2 g2 ccids)
                                            (MkDeclCtorsDec _ _ _ _ (FOkT out (Cons _ cid cids)) (MDCons ctx tid n cn fs rr rest ctxF ft fids fn ret rty tps args acc ret2 cid ctx1 out cids ef er crn lnn bd ab m q)
                                              (DCOk _ _ _ wf2 (grew-trans ctx ctx1 out g1 g2) (ctors-cons out cid cids (ctor-grew ctx1 out cid wf1 g2 (ctor-of-entis ctx1 cid ft ret2 eis)) ccids)))))))))))))))))))))))))
(def-fns _ $ many mint-tycons : (many (Ctx) ctx) (many (WF ctx) wf) (subterm many (List (Raw)) decls) -> (many (TyconsDec ctx decls) r)
  (match many decls _
    ((Nil a) (MkTyconsDec _ _ (FOkT ctx (Nil _)) (MTyNil ctx) (TySOk _ _ _ _ wf (grew-refl ctx) (TyNil _) (LENil _ _))))
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
                          (match many (elab-tele ctx ctx wf (Nil _) _ (cov-refl ctx) ps (POuter (PInner))) _
                            ((TeleStuck d e g h mq) (TyconsStuck _ _))
                            ((MkTeleDec d e g h mq pout ep psc)
                              (match many pout _
                                ((TeleErr r) (MkTyconsDec _ _ (FErrT r) (MTyErr ctx tn ps ctors rest r ep) (TySErr _ _ _)))
                                ((TeleOk ctxP pt pids pn)
                                  (match many psc _
                                    ((TLOk z1 z2 z3 z4 z5 z6 z7 mq oq wfP cr spt li ln)
                                      (let (many tid) (many ctx1) (erased m) (many wf1) (erased g1) (erased eis) (mint ctx wf (Some _ tn) (TyCtor pt) (KDecl) (None _) (sc-tyctor ctx pt _ spt) (scm-none ctx) (ROkNone _)))
                                      (match many (mint-tycons ctx1 wf1 rest) _
                                        ((TyconsStuck d2 e2) (TyconsStuck _ _))
                                        ((MkTyconsDec d2 e2 rout q rsc)
                                          (match many rout _
                                            ((FErrT r) (MkTyconsDec _ _ (FErrT r) (MTyRestErr ctx tn ps ctors rest ctxP pt pids pn tid ctx1 r ep m q) (TySErr _ _ _)))
                                            ((FOkT out tids)
                                              (match many rsc _
                                                ((TySOk y1 y2 y3 y4 wf2 g2 tys le)
                                                  (MkTyconsDec _ _ (FOkT out (Cons _ tid tids)) (MTyCons ctx tn ps ctors rest ctxP pt pids pn tid ctx1 out tids ep m q)
                                                    (TySOk _ _ _ _ wf2 (grew-trans ctx ctx1 out g1 g2) (TyCons _ tid tids (tycon-grew ctx1 out tid wf1 g2 (tycon-of-entis ctx1 tid pt eis)) tys) (LECons _ _ decl tid rest tids le))))))))))))))))
                        (else (TyconsStuck _ _))))
                    (else (TyconsStuck _ _))))
                (else (TyconsStuck _ _))))
            (else (TyconsStuck _ _))))
        (else (TyconsStuck _ _))))))
(def-fns _ $ many mint-ctors : (many (Ctx) ctx) (many (WF ctx) wf) (subterm many (List (Raw)) decls) (many (List (Nat)) tids) (erased (Tycons ctx tids) tys) (erased (LenEq (Raw) (Nat) decls tids) le) -> (many (CtorsDec ctx decls tids) r)
  (match many decls _
    ((Nil a) (match many tids _ ((Nil b) (MkCtorsDec _ _ _ (FOkT ctx (Nil _)) (MCNil ctx) (CSOk _ _ _ wf (grew-refl ctx)))) ((Cons b x y) (match erased le _))))
    ((Cons a decl rest)
      (match many tids _
        ((Nil b) (match erased le _))
        ((Cons b tid trest)
          (match erased le _
            ((LECons c1 c2 c3 c4 c5 c6 le2)
              (match erased tys _
                ((TyCons c7 c8 c9 tc tys2)
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
                                      (let (many pt) (many tty) (erased t) (erased cn) (erased pd) (erased spt) (tycon-of ctx wf tid tc))
                                      (let (many n) (erased ln) (list-len _ pt))
                                      (match many (mint-decl-ctors ctx wf tid tc n ctors (POuter (PInner))) _
                                        ((DeclCtorsStuck a2 b2 c2 d2) (CtorsStuck _ _ _))
                                        ((MkDeclCtorsDec a2 b2 c2 d2 dout mc dsc)
                                          (match many dout _
                                            ((FErrT r) (MkCtorsDec _ _ _ (FErrT r) (MCErr ctx tn ps ctors rest tid trest tty pt n r t cn ln mc) (CSErr _ _)))
                                            ((FOkT ctx1 cids)
                                              (match many dsc _
                                                ((DCOk x1 x2 x3 wf1 g1 ccids)
                                                  (let (many ctx2) (erased aa) (many wf2) (erased g2) (add-adt ctx1 wf1 tid cids (has-grew ctx ctx1 tid g1 (tycon-has ctx tid tc)) ccids))
                                                  (let (erased g12) (grew-trans ctx ctx1 ctx2 g1 g2))
                                                  (match many (mint-ctors ctx2 wf2 rest trest (tycons-grew ctx ctx2 trest wf g12 tys2) le2) _
                                                    ((CtorsStuck a3 b3 c3) (CtorsStuck _ _ _))
                                                    ((MkCtorsDec a3 b3 c3 rout q csc)
                                                      (match many rout _
                                                        ((FErrT r) (MkCtorsDec _ _ _ (FErrT r) (MCRestErr ctx tn ps ctors rest tid trest tty pt n ctx1 cids ctx2 r t cn ln mc aa q) (CSErr _ _)))
                                                        ((FOkT out ids)
                                                          (match many csc _
                                                            ((CSOk y1 y2 y3 wf3 g3)
                                                              (let (many all) (erased ap) (append (Cons _ tid cids) ids))
                                                              (MkCtorsDec _ _ _ (FOkT out all) (MCCons ctx tn ps ctors rest tid trest tty pt n ctx1 cids ctx2 out ids all t cn ln mc aa q ap)
                                                                (CSOk _ _ _ wf3 (grew-trans ctx ctx2 out g12 g3))))))))))))))))
                                    (else (CtorsStuck _ _ _))))
                                (else (CtorsStuck _ _ _))))
                            (else (CtorsStuck _ _ _))))
                        (else (CtorsStuck _ _ _))))
                    (else (CtorsStuck _ _ _))))))))))))
(def-fns _ $ many elab-def-adts : (many (Ctx) ctx) (many (WF ctx) wf) (many (List (Raw)) decls) -> (many (StmtDec ctx (RList (Cons (Raw) (RKey (KDefAdts)) decls))) r)
  (let (many level) (erased lv) (erased slv) (ctx-level ctx wf))
  (match many level _
    ((Some a cur) (MkStmtDec _ _ (SErr (RTopLevelOnly)) (STDefAdtsNested ctx decls cur lv) (SSErr _ _)))
    ((None a)
      (match many (mint-tycons ctx wf decls) _
        ((TyconsStuck b c) (StmtStuck _ _))
        ((MkTyconsDec b c tout mt tsc)
          (match many tout _
            ((FErrT r) (MkStmtDec _ _ (SErr r) (STDefAdtsTyconErr ctx decls r lv mt) (SSErr _ _)))
            ((FOkT ctx1 tids)
              (match many tsc _
                ((TySOk z1 z2 z3 z4 wf1 g1 tys le)
                  (match many (mint-ctors ctx1 wf1 decls tids tys le) _
                    ((CtorsStuck d e g) (StmtStuck _ _))
                    ((MkCtorsDec d e g cout mc csc)
                      (match many cout _
                        ((FErrT r) (MkStmtDec _ _ (SErr r) (STDefAdtsCtorErr ctx decls ctx1 tids r lv mt mc) (SSErr _ _)))
                        ((FOkT out ids)
                          (match many csc _
                            ((CSOk y1 y2 y3 wf2 g2) (MkStmtDec _ _ (SOk out (SDefAdts ids)) (STDefAdts ctx decls ctx1 tids out ids lv mt mc) (SSOk _ _ _ wf2 (grew-trans ctx ctx1 out g1 g2))))))))))))))))))

; The proof forms: (prove-subterm a b), (prove-predates x L), and a former as a value.
(def-fns _ $ many elab-prove-subterm : (many (Ctx) ctx) (many (WF ctx) wf) (many (Raw) ar) (many (Raw) br) ->
    (many (ExprDec ctx (RList (Cons (Raw) (RKey (KProveSubterm)) (Cons (Raw) ar (Cons (Raw) br (Nil (Raw))))))) r)
  (let (erased h1) (erased h2) (sc-builtin ctx wf))
  (match many (elab-term ctx wf ar (POuter (PInner))) _
    ((TermStuck a b) (ExprStuck _ _))
    ((MkTermDec a b aout p asc)
      (match many aout _
        ((TErr r) (MkExprDec _ _ (EErr r) (EXProveSubtermErrA ctx ar br r p) (ESErr _ _)))
        ((TOk at aty)
          (match erased asc _
            ((TSOk a2 b2 c2 sat saty)
              (match many (elab-term ctx wf br (POuter (PInner))) _
                ((TermStuck c d) (ExprStuck _ _))
                ((MkTermDec c d bout q bsc)
                  (match many bout _
                    ((TErr r) (MkExprDec _ _ (EErr r) (EXProveSubtermErrB ctx ar br at aty r p q) (ESErr _ _)))
                    ((TOk bt bty)
                      (match erased bsc _
                        ((TSOk c3 d3 e3 sbt sbty)
                          (let (many ca) (erased c1) (erased sca) (canonical ctx wf at sat))
                          (let (many cb) (erased c2) (erased scb) (canonical ctx wf bt sbt))
                          (match many (sub-dec ctx wf ca sca cb scb) _
                            ((SubNo a1 b1 c4 ns) (MkExprDec _ _ (EErr (RBadProof)) (EXProveSubtermNot ctx ar br at aty bt bty ca cb p q c1 c2 ns) (ESErr _ _)))
                            ((SubYes a1 b1 c4 ss)
                              (let (many e3) (many out) (erased m) (many wf2) (erased g2) (erased eis)
                                (mint ctx wf (None _) (TyApp (Ref (Succ (Succ (Zero)))) subterm-ps (Cons _ aty (Cons _ at (Cons _ bty (Cons _ bt (Nil _)))))) (KPlain) (None _)
                                  (sc-subterm ctx wf _ _ _ _ saty sat sbty sbt) (scm-none ctx) (ROkNone _)))
                              (MkExprDec _ _ (EOk out (CToken) (Cons _ e3 (Nil _))) (EXProveSubterm ctx ar br at aty bt bty ca cb e3 out p q c1 c2 ss m)
                                (ESOk _ _ _ _ wf2 g2 (has-all-cons out e3 (Nil _) (entis-has out e3 _ _ eis) (has-all-nil out)))))))))))))))))))
(def-fns _ $ many elab-prove-predates : (many (Ctx) ctx) (many (WF ctx) wf) (many (String) xs) (many (String) ls) ->
    (many (ExprDec ctx (RList (Cons (Raw) (RKey (KProvePredates)) (Cons (Raw) (RAtom xs) (Cons (Raw) (RAtom ls) (Nil (Raw))))))) r)
  (let (erased h1) (erased h2) (sc-builtin ctx wf))
  (let (many scope) (erased sc) (ctx-scope ctx))
  (match many (name-dec scope xs) _
    ((NameMiss a b n) (MkExprDec _ _ (EErr (RUnbound)) (EXProvePredatesUnboundX ctx xs ls scope sc n) (ESErr _ _)))
    ((NameHit a b x nx)
      (match many (name-dec scope ls) _
        ((NameMiss c d n) (MkExprDec _ _ (EErr (RUnbound)) (EXProvePredatesUnboundL ctx xs ls scope x sc nx n) (ESErr _ _)))
        ((NameHit c d l nl)
          (let (erased hx) (scope-has-ctx ctx wf scope xs x sc nx))
          (let (erased hl) (scope-has-ctx ctx wf scope ls l sc nl))
          (let (many tx) (many kx) (erased t) (erased kq) (erased stx) (erased e2) (erased ee) (erased eo) (type-of ctx wf x hx))
          (let (many tl) (many kl) (erased t2) (erased kd) (erased stl) (erased e3) (erased ee2) (erased eo2) (type-of ctx wf l hl))
          (match many kl _
            ((KPlain) (MkExprDec _ _ (EErr (RNotLevel)) (EXProvePredatesNotLevel ctx xs ls scope x l (KPlain) sc nx nl kd (NLKPlain)) (ESErr _ _)))
            ((KDecl) (MkExprDec _ _ (EErr (RNotLevel)) (EXProvePredatesNotLevel ctx xs ls scope x l (KDecl) sc nx nl kd (NLKDecl)) (ESErr _ _)))
            ((KLevel)
              (match many (nat-cmp x l) _
                ((CLt a1 b1 c1 d1 lt)
                  (let (many e4) (many out) (erased m) (many wf2) (erased g2) (erased eis)
                    (mint ctx wf (None _) (TyApp (Ref (Succ (Zero))) predates-ps (Cons _ tx (Cons _ (Ref x) (Cons _ (Ref l) (Nil _))))) (KPlain) (None _)
                      (sc-predates ctx wf _ _ _ stx (sc-ref ctx x hx) (sc-ref ctx l hl)) (scm-none ctx) (ROkNone _)))
                  (MkExprDec _ _ (EOk out (CToken) (Cons _ e4 (Nil _))) (EXProvePredates ctx xs ls scope x l tx e4 out sc nx nl t kd lt m)
                    (ESOk _ _ _ _ wf2 g2 (has-all-cons out e4 (Nil _) (entis-has out e4 _ _ eis) (has-all-nil out)))))
                ((CEq a1 b1 c1) (MkExprDec _ _ (EErr (RBadProof)) (EXProvePredatesAfter ctx xs ls scope x l sc nx nl kd (lt-succ x)) (ESErr _ _)))
                ((CGt a1 b1 c1 d1 gt) (MkExprDec _ _ (EErr (RBadProof)) (EXProvePredatesAfter ctx xs ls scope x l sc nx nl kd (lt-weaken l x gt)) (ESErr _ _)))))))))))
(def-fns _ $ many elab-former-expr : (many (Ctx) ctx) (many (WF ctx) wf) (many (Key) k) (many (List (Raw)) items) (erased (FormerKey k) fk) -> (many (ExprDec ctx (RList (Cons (Raw) (RKey k) items))) r)
  (match many (elab-term ctx wf (RList (Cons _ (RKey k) items)) (POuter (PInner))) _
    ((TermStuck a b) (ExprStuck _ _))
    ((MkTermDec a b out p tsc)
      (match many out _
        ((TErr r) (MkExprDec _ _ (EErr r) (EXFormerErr ctx k items r fk p) (ESErr _ _)))
        ((TOk t ty)
          (match erased tsc _
            ((TSOk a2 b2 c2 st sty)
              (let (many x) (many out2) (erased m) (many wf2) (erased g2) (erased eis) (mint ctx wf (None _) ty (KPlain) (Some _ t) sty (scm-some ctx t st) (ROkSome _ _ (NDPlain))))
              (MkExprDec _ _ (EOk out2 (CFormer t) (Cons _ x (Nil _))) (EXFormer ctx k items t ty x out2 fk p m) (ESOk _ _ _ _ wf2 g2 (has-all-cons out2 x (Nil _) (entis-has out2 x _ _ eis) (has-all-nil out2)))))))))))

; The group proper. Each function decreases on the raw syntax it walks, then on a phase for a call that
; walks the same syntax, then on the list of arguments still to be walked.
(def-fns _
  (many elab-expr : (many (Ctx) ctx) (many (WF ctx) wf) (subterm many (Raw) raw) (subterm many (POuter (PInner)) is ph) (subterm many (Nil (Raw)) is tl) -> (many (ExprDec ctx raw) r)
    (match many raw _
      ((RAtom s)
        (let (many scope) (erased sc) (ctx-scope ctx))
        (match many (name-dec scope s) _
          ((NameMiss a b n) (MkExprDec _ _ (EErr (RUnbound)) (EXUnbound ctx s scope sc n) (ESErr _ _)))
          ((NameHit a b x n)
            (MkExprDec _ _ (EOk ctx (CVar x) (Cons _ x (Nil _))) (EXName ctx s x scope sc n) (ESOk _ _ _ _ wf (grew-refl ctx) (has-all-cons ctx x (Nil _) (scope-has-ctx ctx wf scope s x sc n) (has-all-nil ctx)))))))
      ((RKey k) (ExprStuck _ _))
      ((RList items)
        (match many items _
          ((Nil a) (ExprStuck _ _))
          ((Cons a h rest)
            (match many h _
              ((RAtom s) (elab-app ctx wf h rest items (POuter (PInner)) (Nil _) (HeadAtom s)))
              ((RList inner) (elab-app ctx wf h rest items (POuter (PInner)) (Nil _) (HeadList inner)))
              ((RKey k)
                (match many k _
                  ((KValues)
                    (match many (elab-items ctx wf rest (POuter (PInner)) (Nil _)) _
                      ((ItemsStuck b c) (ExprStuck _ _))
                      ((MkItemsDec b c out p isc)
                        (match many out _
                          ((AErr r) (MkExprDec _ _ (EErr r) (EXValuesErr ctx rest r p) (ESErr _ _)))
                          ((AOk out2 cores ids)
                            (match many isc _
                              ((AOOk z1 z2 z3 z4 wf2 g2 h2) (MkExprDec _ _ (EOk out2 (CValues cores) ids) (EXValues ctx rest out2 cores ids p) (ESOk _ _ _ _ wf2 g2 h2)))))))))
                  ((KFn) (elab-former-expr ctx wf (KFn) rest (FKFn)))
                  ((KTyCtor) (elab-former-expr ctx wf (KTyCtor) rest (FKTyCtor)))
                  ((KValCtor) (elab-former-expr ctx wf (KValCtor) rest (FKValCtor)))
                  ((KMatch)
                    (match many rest _
                      ((Cons b sr rest2)
                        (match many rest2 _
                          ((Cons c annr brs)
                            (match many annr _
                              ((RList ann) (elab-match ctx wf sr ann brs rest (POuter (PInner)) (Nil _)))
                              (else (ExprStuck _ _))))
                          (else (ExprStuck _ _))))
                      (else (ExprStuck _ _))))
                  ((KProveSubterm)
                    (match many rest _
                      ((Cons b ar rest2)
                        (match many rest2 _
                          ((Cons c br rest3)
                            (match many rest3 _
                              ((Nil d) (elab-prove-subterm ctx wf ar br))
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
                                      ((RAtom ls) (elab-prove-predates ctx wf xs ls))
                                      (else (ExprStuck _ _))))
                                  (else (ExprStuck _ _))))
                              (else (ExprStuck _ _))))
                          (else (ExprStuck _ _))))
                      (else (ExprStuck _ _))))
                  ((KPredatesTrans) (elab-axiom-args ctx wf (KPredatesTrans) rest (POuter (PInner)) (Nil _) (AKPredatesTrans)))
                  ((KSubtermTrans) (elab-axiom-args ctx wf (KSubtermTrans) rest (POuter (PInner)) (Nil _) (AKSubtermTrans)))
                  ((KPredatesSubterm) (elab-axiom-args ctx wf (KPredatesSubterm) rest (POuter (PInner)) (Nil _) (AKPredatesSubterm)))
                  (else (ExprStuck _ _))))))))))
  ; an axiom's two items
  (many elab-axiom-args : (many (Ctx) ctx) (many (WF ctx) wf) (many (Key) k) (subterm many (List (Raw)) items) (subterm many (POuter (PInner)) is ph) (subterm many (Nil (Raw)) is tl) (erased (AxiomKey k) ak) ->
      (many (ExprDec ctx (RList (Cons (Raw) (RKey k) items))) r)
    (match many items _
      ((Cons a pr rest1)
        (match many rest1 _
          ((Cons b qr rest2)
            (match many rest2 _
              ((Nil c) (elab-axiom ctx wf k pr qr items (PInner) (Nil _) ak))
              (else (ExprStuck _ _))))
          (else (ExprStuck _ _))))
      (else (ExprStuck _ _))))
  ; (axiom p q): both proofs elaborated, their canonical types read, and the axiom's own check applied
  (many elab-axiom : (many (Ctx) ctx) (many (WF ctx) wf) (many (Key) k) (many (Raw) pr) (many (Raw) qr) (subterm many (Cons (Raw) pr (Cons (Raw) qr (Nil (Raw)))) is items) (subterm many (PInner) is ph)
      (subterm many (Nil (Raw)) is tl) (erased (AxiomKey k) ak) -> (many (ExprDec ctx (RList (Cons (Raw) (RKey k) items))) r)
    (match many (elab-expr ctx wf pr (POuter (PInner)) (Nil _)) _
      ((ExprStuck a b) (ExprStuck _ _))
      ((MkExprDec a b pout ep psc)
        (match many pout _
          ((EErr r) (MkExprDec _ _ (EErr r) (EXAxiomErrP ctx k pr qr r ak ep) (ESErr _ _)))
          ((EOk ctx1 pc pids)
            (match many psc _
              ((ESOk a1 b1 c1 d1 wf1 g1 hp)
                (match many (one-dec pids) _
                  ((OneNo c n) (MkExprDec _ _ (EErr (RSize)) (EXAxiomSizeP ctx k pr qr ctx1 pc pids ak ep n) (ESErr _ _)))
                  ((OneYes p)
                    (match many (elab-expr ctx1 wf1 qr (POuter (PInner)) (Nil _)) _
                      ((ExprStuck c d) (ExprStuck _ _))
                      ((MkExprDec c d qout eq qsc)
                        (match many qout _
                          ((EErr r) (MkExprDec _ _ (EErr r) (EXAxiomErrQ ctx k pr qr ctx1 pc p r ak ep eq) (ESErr _ _)))
                          ((EOk ctx2 qc qids)
                            (match many qsc _
                              ((ESOk a2 b2 c2 d2 wf2 g2 hq)
                                (match many (one-dec qids) _
                                  ((OneNo e n) (MkExprDec _ _ (EErr (RSize)) (EXAxiomSizeQ ctx k pr qr ctx1 pc p ctx2 qc qids ak ep eq n) (ESErr _ _)))
                                  ((OneYes q)
                                    (let (erased hpp) (erased hp0) (has-all-parts ctx1 p (Nil _) hp))
                                    (let (erased hqq) (erased hq0) (has-all-parts ctx2 q (Nil _) hq))
                                    (let (many pty) (many kp) (erased tp) (erased kq1) (erased spty) (erased e1) (erased ee1) (erased eo1) (type-of ctx1 wf1 p hpp))
                                    (let (many cp) (erased c1) (erased scp) (canonical ctx1 wf1 pty spty))
                                    (let (many qty) (many kq2) (erased tq) (erased kq3) (erased sqty) (erased e2) (erased ee2) (erased eo2) (type-of ctx2 wf2 q hqq))
                                    (let (many cq) (erased c2) (erased scq) (canonical ctx2 wf2 qty sqty))
                                    (match many (axiom-check k ctx1 wf1 cp scp ctx2 wf2 g2 cq scq ak) _
                                      ((AxBad a3 b3 c3 d3 e3 bad) (MkExprDec _ _ (EErr (RBadProof)) (EXAxiomBad ctx k pr qr ctx1 pc p pty cp ctx2 qc q qty cq ep tp c1 eq tq c2 bad) (ESErr _ _)))
                                      ((AxOk a3 b3 c3 d3 e3 concl ok sconcl)
                                        (let (many e3) (many out) (erased m) (many wf3) (erased g3) (erased eis) (mint ctx2 wf2 (None _) concl (KPlain) (None _) sconcl (scm-none ctx2) (ROkNone _)))
                                        (MkExprDec _ _ (EOk out (CToken) (Cons _ e3 (Nil _))) (axiom-derivation ctx k pr qr ctx1 pc p pty cp ctx2 qc q qty cq e3 out concl ep tp c1 eq tq c2 ok m)
                                          (ESOk _ _ _ _ wf3 (grew-trans ctx ctx2 out (grew-trans ctx ctx1 ctx2 g1 g2) g3) (has-all-cons out e3 (Nil _) (entis-has out e3 _ _ eis) (has-all-nil out)))))))))))))))))))))))
  ; (h items...): a constructor or type-constructor application, or a call
  (many elab-app : (many (Ctx) ctx) (many (WF ctx) wf) (many (Raw) h) (many (List (Raw)) items) (subterm many (Cons (Raw) h items) is hitems) (subterm many (POuter (PInner)) is ph) (subterm many (Nil (Raw)) is tl)
      (erased (HeadRaw h) hr) -> (many (ExprDec ctx (RList hitems)) r)
    (match many (elab-expr ctx wf h (POuter (PInner)) (Nil _)) _
      ((ExprStuck a b) (ExprStuck _ _))
      ((MkExprDec a b hout p hsc)
        (match many hout _
          ((EErr r) (MkExprDec _ _ (EErr r) (EXHeadErr ctx h items r hr p) (ESErr _ _)))
          ((EOk ctx1 hc hids)
            (match many hsc _
              ((ESOk a1 b1 c1 d1 wf1 g1 hh)
                (match many (one-dec hids) _
                  ((OneNo c n) (MkExprDec _ _ (EErr (RSize)) (EXHeadSize ctx h items ctx1 hc hids hr p n) (ESErr _ _)))
                  ((OneYes x)
                    (let (erased hx) (erased hx0) (has-all-parts ctx1 x (Nil _) hh))
                    (let (many hty) (many kx) (erased t) (erased kq) (erased shty) (erased e1) (erased ee1) (erased eo1) (type-of ctx1 wf1 x hx))
                    (let (many hc2) (erased cn) (erased shc) (canonical ctx1 wf1 hty shty))
                    (match many hc2 _
                      ((TyCtor ps)
                        (let (erased pd) (erased sps) (sc-tyctor-parts ctx1 ps shc))
                        (match many (elab-expr-args ctx1 wf1 (Nil _) _ (scs-nil ctx1) ps _ sps items (PInner) items (elems-refl items)) _
                          ((ExprArgsStuck a2 b2 c2 d2) (ExprStuck _ _))
                          ((MkExprArgsDec a2 b2 c2 d2 aout ap asc al)
                            (match many aout _
                              ((AErr r) (MkExprDec _ _ (EErr r) (EXAppArgsErr ctx h items ctx1 hc x hty ps r hr p t (HeadTy ctx1 hty ps cn) ap) (ESErr _ _)))
                              ((AOk ctx2 cores ids)
                                (match many asc _
                                  ((AOOk a3 b3 c3 d3 wf2 g2 hids2)
                                    (let (many ts) (erased rf) (refs ids))
                                    (let (many e3) (many out) (erased m) (many wf3) (erased g3) (erased eis)
                                      (mint ctx2 wf2 (None _) (Univ) (KPlain) (Some _ (TyApp (Ref x) ps ts)) (sc-univ ctx2)
                                        (scm-some ctx2 _ (sc-tyapp ctx2 (Ref x) ps ts _ (sc-ref ctx2 x (has-grew ctx1 ctx2 x g2 hx)) (sct-grew ctx1 ctx2 _ ps _ g2 sps) (refs-scoped ctx2 ids ts hids2 rf) (refs-len-eq ps ids ts (arglen-ok ps ctx2 cores ids al) rf))) (ROkSome _ _ (NDPlain))))
                                    (MkExprDec _ _ (EOk out (CApp hc cores) (Cons _ e3 (Nil _))) (EXTyApp ctx h items ctx1 hc x hty ps ctx2 cores ids ts e3 out hr p t cn ap rf m)
                                      (ESOk _ _ _ _ wf3 (grew-trans ctx ctx2 out (grew-trans ctx ctx1 ctx2 g1 g2) g3) (has-all-cons out e3 (Nil _) (entis-has out e3 _ _ eis) (has-all-nil out)))))))))))
                      ((ValCtor ps ret)
                        (let (erased pd) (erased sps) (erased sret) (sc-valctor-parts ctx1 ps ret shc))
                        (match many (elab-expr-args ctx1 wf1 (Nil _) _ (scs-nil ctx1) ps _ sps items (PInner) items (elems-refl items)) _
                          ((ExprArgsStuck a2 b2 c2 d2) (ExprStuck _ _))
                          ((MkExprArgsDec a2 b2 c2 d2 aout ap asc al)
                            (match many aout _
                              ((AErr r) (MkExprDec _ _ (EErr r) (EXAppArgsErr ctx h items ctx1 hc x hty ps r hr p t (HeadVal ctx1 hty ps ret cn) ap) (ESErr _ _)))
                              ((AOk ctx2 cores ids)
                                (match many asc _
                                  ((AOOk a3 b3 c3 d3 wf2 g2 hids2)
                                    (let (many ts) (erased rf) (refs ids))
                                    (let (erased sts) (refs-scoped ctx2 ids ts hids2 rf))
                                    (let (erased le) (arglen-ok ps ctx2 cores ids al))
                                    (let (many sub) (erased so) (many ty) (erased sb) (erased sty) (inst-ret-sc ctx2 pd ps ret ts (sct-grew ctx1 ctx2 _ ps _ g2 sps) (sc-grew ctx1 ctx2 _ ret g2 sret) sts (refs-len-eq ps ids ts le rf)))
                                    (let (many e3) (many out) (erased m) (many wf3) (erased g3) (erased eis)
                                      (mint ctx2 wf2 (None _) ty (KPlain) (Some _ (ValApp (Ref x) ps ret ts)) sty
                                        (scm-some ctx2 _ (sc-valapp ctx2 (Ref x) ps ret ts _ (sc-ref ctx2 x (has-grew ctx1 ctx2 x g2 hx)) (sct-grew ctx1 ctx2 _ ps _ g2 sps) (sc-grew ctx1 ctx2 _ ret g2 sret) sts (refs-len-eq ps ids ts le rf))) (ROkSome _ _ (NDPlain))))
                                    (MkExprDec _ _ (EOk out (CApp hc cores) (Cons _ e3 (Nil _))) (EXValApp ctx h items ctx1 hc x hty ps ret ctx2 cores ids ts sub ty e3 out hr p t cn ap rf so sb m)
                                      (ESOk _ _ _ _ wf3 (grew-trans ctx ctx2 out (grew-trans ctx ctx1 ctx2 g1 g2) g3) (has-all-cons out e3 (Nil _) (entis-has out e3 _ _ eis) (has-all-nil out)))))))))))
                      ((Fn l ps rs)
                        (match many (call-raw-dec items) _
                          ((CallRawStuck a1) (ExprStuck _ _))
                          ((MkCallRaw a1 ann args cr ai el)
                            (let (erased pd) (erased pd2) (erased sl) (erased sps) (erased srs) (sc-fn-parts ctx1 l ps rs shc))
                            (match many (elab-expr-args ctx1 wf1 (Nil _) _ (scs-nil ctx1) ps _ sps items (PInner) args el) _
                              ((ExprArgsStuck a2 b2 c2 d2) (ExprStuck _ _))
                              ((MkExprArgsDec a2 b2 c2 d2 aout ap asc al)
                                (match many aout _
                                  ((AErr r) (MkExprDec _ _ (EErr r) (EXCallArgsErr ctx h items ctx1 hc x hty l ps rs ann args r hr p t cn cr ap) (ESErr _ _)))
                                  ((AOk ctx2 cores ids)
                                    (match many asc _
                                      ((AOOk a3 b3 c3 d3 wf2 g2 hids2)
                                        (match erased al _
                                          ((ArgLenOk a4 b4 c4 d4 le)
                                            (match many (decrease ctx2 wf2 l (sc-grew ctx1 ctx2 _ l g2 sl) ps ids hids2 le ann items (PInner) (Nil _) ai) _
                                              ((DecreaseStuck a5 b5 c5 d5 e5) (ExprStuck _ _))
                                              ((MkDecreaseDec a5 b5 c5 d5 e5 dout dp dsc)
                                                (match many dout _
                                                  ((DErr r) (MkExprDec _ _ (EErr r) (EXCallDecreaseErr ctx h items ctx1 hc x hty l ps rs ann args ctx2 cores ids r hr p t cn cr ap dp) (ESErr _ _)))
                                                  ((DOk ctx3)
                                                    (match many dsc _
                                                      ((DSOk a6 b6 wf3 g3)
                                                        (let (many ts) (erased rf) (refs ids))
                                                        (let (many sub) (erased so) (somes ts))
                                                        (let (many names) (erased nn) (erased ln) (nones rs))
                                                        (let (erased g13) (grew-trans ctx1 ctx2 ctx3 g2 g3))
                                                        (let (erased sts) (refs-scoped ctx3 ids ts (has-all-grew ctx2 ctx3 ids g3 hids2) rf))
                                                        (match many (mint-tele ctx3 wf3 sub _ (sc-somes ctx3 ts sub _ (refs-length ids ts _ rf (tele-ids-length ctx1 ps ids _ sps le)) sts so) rs _ (sct-grew ctx1 ctx3 _ rs _ g13 srs) names ln) _
                                                          ((MTMinted a7 b7 c7 d7 out rids wf4 g4 hrids le2 m)
                                                            (MkExprDec _ _ (EOk out (CCall hc cores) rids) (EXCall ctx h items ctx1 hc x hty l ps rs ann args ctx2 cores ids ctx3 ts sub names out rids hr p t cn cr ap dp rf so nn m)
                                                              (ESOk _ _ _ _ wf4 (grew-trans ctx ctx3 out (grew-trans ctx ctx1 ctx3 g1 g13) g4) hrids)))))))))))))))))))))
                      ((Ref y) (MkExprDec _ _ (EErr (RNotApplicable)) (EXNotApplicable ctx h items ctx1 hc x hty (Ref y) hr p t cn (NTNRef y)) (ESErr _ _)))
                      ((Bound kk) (MkExprDec _ _ (EErr (RNotApplicable)) (EXNotApplicable ctx h items ctx1 hc x hty (Bound kk) hr p t cn (NTNBound kk)) (ESErr _ _)))
                      ((TyApp h2 ps2 as2) (MkExprDec _ _ (EErr (RNotApplicable)) (EXNotApplicable ctx h items ctx1 hc x hty (TyApp h2 ps2 as2) hr p t cn (NTNTyApp h2 ps2 as2)) (ESErr _ _)))
                      ((ValApp h2 ps2 r2 as2) (MkExprDec _ _ (EErr (RNotApplicable)) (EXNotApplicable ctx h items ctx1 hc x hty (ValApp h2 ps2 r2 as2) hr p t cn (NTNValApp h2 ps2 r2 as2)) (ESErr _ _)))
                      ((Univ) (MkExprDec _ _ (EErr (RNotApplicable)) (EXNotApplicable ctx h items ctx1 hc x hty (Univ) hr p t cn (NTNUniv)) (ESErr _ _)))))))))))))
  ; Arguments, expressions of size one, against a telescope, each a part of the call's items.
  (many elab-expr-args : (many (Ctx) ctx) (many (WF ctx) wf) (many (List (Maybe (Term))) acc) (erased (Nat) m) (erased (ScS ctx acc m) sacc) (many (List (Entry)) tele) (erased (Nat) out) (erased (ScT ctx m tele out) stele)
      (subterm many (List (Raw)) parent) (subterm many (PInner) is ph) (subterm many (List (Raw)) args) (erased (Elems parent args) el) -> (many (ExprArgsDec ctx acc tele args) r)
    (match many (len-dec _ _ tele args) _
      ((LenDiff a b c d m) (MkExprArgsDec _ _ _ _ (AErr (RArity)) (EAArity ctx acc tele args m) (AOErr _ _) (ArgLenErr _ _)))
      ((LenSame a b c d le)
        (match many tele _
          ((Nil e) (match many args _ ((Nil g) (MkExprArgsDec _ _ _ _ (AOk ctx (Nil _) (Nil _)) (EANil ctx acc) (AOOk _ _ _ _ wf (grew-refl ctx) (has-all-nil ctx)) (ArgLenOk _ _ _ _ (LENil _ _)))) ((Cons g x y) (match erased le _))))
          ((Cons e entry es)
            (match many args _
              ((Nil g) (match erased le _))
              ((Cons g ar rest)
                (match many entry _
                  ((MkEntry s i t)
                    (match erased el _
                      ((ElCons g1 g2 g3 sub el2)
                        (let (erased st) (erased ses) (sct-parts ctx _ _ s i t es stele))
                        (match many (elab-expr ctx wf (subterm sub) ar (POuter (PInner)) (Nil _)) _
                          ((ExprStuck h k) (ExprArgsStuck _ _ _ _))
                          ((MkExprDec h k aout p esc)
                            (match many aout _
                              ((EErr r) (MkExprArgsDec _ _ _ _ (AErr r) (EAErr ctx acc (MkEntry s i t) es ar rest r p) (AOErr _ _) (ArgLenErr _ _)))
                              ((EOk ctx1 core ids)
                                (match many esc _
                                  ((ESOk h1 k1 l1 m1 wf1 g1 h2)
                                    (match many (one-dec ids) _
                                      ((OneNo h3 n) (MkExprArgsDec _ _ _ _ (AErr (RSize)) (EASize ctx acc (MkEntry s i t) es ar rest ctx1 core ids p n) (AOErr _ _) (ArgLenErr _ _)))
                                      ((OneYes x)
                                        (let (erased hx) (erased hx0) (has-all-parts ctx1 x (Nil _) h2))
                                        (let (many t2) (erased sb) (subst acc _ (scs-length ctx acc _ sacc) t (sc-closed ctx _ t st)))
                                        (let (erased sacc1) (scs-grew ctx ctx1 acc _ g1 sacc))
                                        (let (erased st2) (sc-subst ctx1 acc _ t t2 sacc1 (sc-grew ctx ctx1 _ t g1 st) sb))
                                        (let (erased sacc2) (scs-cons ctx1 (Ref x) acc _ (sc-ref ctx1 x hx) sacc1))
                                        (let (erased ses1) (sct-grew ctx ctx1 _ es _ g1 ses))
                                        (match many i _
                                          ((BFalse)
                                            (let (many xty) (many kx) (erased ty) (erased kq) (erased sxty) (erased e1) (erased ee1) (erased eo1) (type-of ctx1 wf1 x hx))
                                            (match many (same-dec ctx1 wf1 xty t2 sxty st2) _
                                              ((SDDiffer h4 k4 l4 d2) (MkExprArgsDec _ _ _ _ (AErr (RMismatch)) (EATyMismatch ctx acc s t es ar rest ctx1 core x xty t2 p ty sb d2) (AOErr _ _) (ArgLenErr _ _)))
                                              ((SDSame h4 k4 l4 sm)
                                                (match many (elab-expr-args ctx1 wf1 (Cons _ (Some _ (Ref x)) acc) _ sacc2 es _ ses1 parent (PInner) rest el2) _
                                                  ((ExprArgsStuck h5 k5 l5 m5) (ExprArgsStuck _ _ _ _))
                                                  ((MkExprArgsDec h5 k5 l5 m5 rout q rsc al)
                                                    (match many rout _
                                                      ((AErr r) (MkExprArgsDec _ _ _ _ (AErr r) (EARestErr ctx acc s (BFalse) t es ar rest ctx1 core x r p q) (AOErr _ _) (ArgLenErr _ _)))
                                                      ((AOk out cores ids2)
                                                        (match many rsc _
                                                          ((AOOk y1 y2 y3 y4 wf2 g2 hids2)
                                                            (match erased al _
                                                              ((ArgLenOk w1 w2 w3 w4 le2)
                                                                (MkExprArgsDec _ _ _ _ (AOk out (Cons _ core cores) (Cons _ x ids2)) (EATy ctx acc s t es ar rest ctx1 core x xty t2 out cores ids2 p ty sb sm q)
                                                                  (AOOk _ _ _ _ wf2 (grew-trans ctx ctx1 out g1 g2) (has-all-cons out x ids2 (has-grew ctx1 out x g2 hx) hids2)) (ArgLenOk _ _ _ _ (LECons _ _ entry x es ids2 le2))))))))))))))
                                          ((BTrue)
                                            (match many (same-dec ctx1 wf1 (Ref x) t2 (sc-ref ctx1 x hx) st2) _
                                              ((SDDiffer h4 k4 l4 d2) (MkExprArgsDec _ _ _ _ (AErr (RMismatch)) (EAIsMismatch ctx acc s t es ar rest ctx1 core x t2 p sb d2) (AOErr _ _) (ArgLenErr _ _)))
                                              ((SDSame h4 k4 l4 sm)
                                                (match many (elab-expr-args ctx1 wf1 (Cons _ (Some _ (Ref x)) acc) _ sacc2 es _ ses1 parent (PInner) rest el2) _
                                                  ((ExprArgsStuck h5 k5 l5 m5) (ExprArgsStuck _ _ _ _))
                                                  ((MkExprArgsDec h5 k5 l5 m5 rout q rsc al)
                                                    (match many rout _
                                                      ((AErr r) (MkExprArgsDec _ _ _ _ (AErr r) (EARestErr ctx acc s (BTrue) t es ar rest ctx1 core x r p q) (AOErr _ _) (ArgLenErr _ _)))
                                                      ((AOk out cores ids2)
                                                        (match many rsc _
                                                          ((AOOk y1 y2 y3 y4 wf2 g2 hids2)
                                                            (match erased al _
                                                              ((ArgLenOk w1 w2 w3 w4 le2)
                                                                (MkExprArgsDec _ _ _ _ (AOk out (Cons _ core cores) (Cons _ x ids2)) (EAIs ctx acc s t es ar rest ctx1 core x t2 out cores ids2 p sb sm q)
                                                                  (AOOk _ _ _ _ wf2 (grew-trans ctx ctx1 out g1 g2) (has-all-cons out x ids2 (has-grew ctx1 out x g2 hx) hids2)) (ArgLenOk _ _ _ _ (LECons _ _ entry x es ids2 le2))))))))))))))))))))))))))))))))))
  ; The call-site proof.
  (many decrease : (many (Ctx) ctx) (many (WF ctx) wf) (many (Term) l) (erased (Sc ctx (Zero) l) sl) (many (List (Entry)) ps) (many (List (Nat)) ids) (erased (HasAll ctx ids) hids) (erased (LenEq (Entry) (Nat) ps ids) le) (many (Ann) ann)
      (subterm many (List (Raw)) parent) (subterm many (PInner) is ph) (subterm many (Nil (Raw)) is tl) (erased (AnnIn parent ann) ai) -> (many (DecreaseDec ctx l ps ids ann) r)
    (let (many level) (erased lv) (erased slv) (ctx-level ctx wf))
    (match many level _
      ((None a)
        (match many ann _
          ((ANone) (MkDecreaseDec _ _ _ _ _ (DOk ctx) (DTop ctx l ps ids lv) (DSOk _ _ wf (grew-refl ctx))))
          ((APredates pr) (MkDecreaseDec _ _ _ _ _ (DErr (RBadProof)) (DTopPredates ctx l ps ids pr lv) (DSErr _ _)))
          ((ASubterm i pr) (MkDecreaseDec _ _ _ _ _ (DErr (RBadProof)) (DTopSubterm ctx l ps ids i pr lv) (DSErr _ _)))))
      ((Some a cur)
        (let (erased scur) (scm-some-parts ctx cur slv))
        (match many ann _
          ((ANone) (MkDecreaseDec _ _ _ _ _ (DErr (RNoProof)) (DNone ctx l ps ids cur lv) (DSErr _ _)))
          ((APredates pr)
            (match erased ai _
              ((InPredates a2 p2 sub)
                (match many (elab-expr ctx wf (subterm sub) pr (POuter (PInner)) (Nil _)) _
                  ((ExprStuck b c) (DecreaseStuck _ _ _ _ _))
                  ((MkExprDec b c pout ep esc)
                    (match many pout _
                      ((EErr r) (MkDecreaseDec _ _ _ _ _ (DErr r) (DPredatesErr ctx l ps ids pr cur r lv ep) (DSErr _ _)))
                      ((EOk ctx1 pc pids)
                        (match many esc _
                          ((ESOk b1 c1 d1 e1 wf1 g1 hp)
                            (match many (one-dec pids) _
                              ((OneNo d n) (MkDecreaseDec _ _ _ _ _ (DErr (RSize)) (DPredatesSize ctx l ps ids pr cur ctx1 pc pids lv ep n) (DSErr _ _)))
                              ((OneYes p)
                                (let (erased hpp) (erased hp0) (has-all-parts ctx1 p (Nil _) hp))
                                (let (many pty) (many kp) (erased t) (erased kq) (erased spty) (erased e2) (erased ee2) (erased eo2) (type-of ctx1 wf1 p hpp))
                                (let (many c) (erased cn) (erased scc) (canonical ctx1 wf1 pty spty))
                                (match many (predates-dec ctx1 wf1 c l cur scc (sc-grew ctx ctx1 _ l g1 sl) (sc-grew ctx ctx1 _ cur g1 scur)) _
                                  ((PDNo a1 b2 c2 d2 np) (MkDecreaseDec _ _ _ _ _ (DErr (RBadProof)) (DPredatesBad ctx l ps ids pr cur ctx1 pc p pty c lv ep t cn np) (DSErr _ _)))
                                  ((PDYes a1 b2 c2 d2 hh hps ty aa lv2 sh sty sa scc2)
                                    (MkDecreaseDec _ _ _ _ _ (DOk ctx1) (DPredates ctx l ps ids pr cur ctx1 pc p pty hh hps ty aa lv2 lv ep t cn sh sty sa scc2) (DSOk _ _ wf1 g1)))))))))))))))
          ((ASubterm i pr)
            (match many (same-dec ctx wf l cur sl scur) _
              ((SDDiffer b c d df) (MkDecreaseDec _ _ _ _ _ (DErr (RBadProof)) (DSubtermLevel ctx l ps ids i pr cur lv df) (DSErr _ _)))
              ((SDSame b c d sl2)
                (match many (marked-index-dec ps i) _
                  ((MINoAt e g um) (MkDecreaseDec _ _ _ _ _ (DErr (RBadProof)) (DSubtermUnmarked ctx l ps ids i pr cur lv sl2 um) (DSErr _ _)))
                  ((MIYesAt e g j mi)
                    (match many (nth-dec _ ids i) _
                      (absurd (NthMiss a1 b1 c1 nn) (nth-marked ps ids i j mi le nn))
                      ((NthHit a1 b1 c1 xi ni)
                        (let (many cargs) (erased mk) (marked ps ids le))
                        (let (many subargs) (erased sa) (erased ssa) (ctx-subargs ctx wf))
                        (match many (prefix-dec ctx wf j cargs subargs (marked-scoped ctx ps ids cargs hids mk) ssa) _
                          ((PrefixNo a3 b3 c3 d3 dp) (MkDecreaseDec _ _ _ _ _ (DErr (RBadProof)) (DSubtermPrefix ctx l ps ids i pr cur j cargs subargs lv sl2 mi mk sa dp) (DSErr _ _)))
                          ((PrefixYes a3 b3 c3 d3 bb sp sbb)
                            (match erased ai _
                              ((InSubterm a4 i4 p4 sub)
                                (match many (elab-expr ctx wf (subterm sub) pr (POuter (PInner)) (Nil _)) _
                                  ((ExprStuck a5 b5) (DecreaseStuck _ _ _ _ _))
                                  ((MkExprDec a5 b5 pout ep esc)
                                    (match many pout _
                                      ((EErr r) (MkDecreaseDec _ _ _ _ _ (DErr r) (DSubtermErr ctx l ps ids i pr cur r lv sl2 ep) (DSErr _ _)))
                                      ((EOk ctx1 pc pids)
                                        (match many esc _
                                          ((ESOk b1 c1 d1 e1 wf1 g1 hp)
                                            (match many (one-dec pids) _
                                              ((OneNo a6 n) (MkDecreaseDec _ _ _ _ _ (DErr (RSize)) (DSubtermSize ctx l ps ids i pr cur ctx1 pc pids lv sl2 ep n) (DSErr _ _)))
                                              ((OneYes p)
                                                (let (erased hpp) (erased hp0) (has-all-parts ctx1 p (Nil _) hp))
                                                (let (many pty) (many kp) (erased t) (erased kq) (erased spty) (erased e2) (erased ee2) (erased eo2) (type-of ctx1 wf1 p hpp))
                                                (let (many c) (erased cn) (erased scc) (canonical ctx1 wf1 pty spty))
                                                (match many (subterm-dec ctx1 wf1 c (Ref xi) bb scc (sc-ref ctx1 xi (has-grew ctx ctx1 xi g1 (nth-has ctx ids i xi hids ni))) (sc-grew ctx ctx1 _ bb g1 sbb)) _
                                                  ((STNo a7 b7 c7 d7 ns) (MkDecreaseDec _ _ _ _ _ (DErr (RBadProof)) (DSubtermBad ctx l ps ids i pr cur j xi cargs subargs bb ctx1 pc p pty c lv sl2 mi ni mk sa sp ep t cn ns) (DSErr _ _)))
                                                  ((STYes a7 b7 c7 d7 hh hps ta a0 tb b0 sh sa0 sb0)
                                                    (MkDecreaseDec _ _ _ _ _ (DOk ctx1) (DSubterm ctx l ps ids i pr cur j xi cargs subargs bb ctx1 pc p pty hh hps ta a0 tb b0 lv sl2 mi ni mk sa sp ep t cn sh sa0 sb0) (DSOk _ _ wf1 g1)))))))))))))))))))))))))))
  ; (match s (rets) branches...)
  (many elab-match : (many (Ctx) ctx) (many (WF ctx) wf) (many (Raw) sr) (many (List (Raw)) ann) (many (List (Raw)) brs) (subterm many (Cons (Raw) sr (Cons (Raw) (RList ann) brs)) is rest)
      (subterm many (POuter (PInner)) is ph) (subterm many (Nil (Raw)) is tl) -> (many (ExprDec ctx (RList (Cons (Raw) (RKey (KMatch)) rest))) r)
    (match many (elab-expr ctx wf sr (POuter (PInner)) (Nil _)) _
      ((ExprStuck a b) (ExprStuck _ _))
      ((MkExprDec a b sout p ssc)
        (match many sout _
          ((EErr r) (MkExprDec _ _ (EErr r) (EXMatchScrutErr ctx sr ann brs r p) (ESErr _ _)))
          ((EOk ctx1 sc sids)
            (match many ssc _
              ((ESOk a1 b1 c1 d1 wf1 g1 hs)
                (match many (one-dec sids) _
                  ((OneNo c n) (MkExprDec _ _ (EErr (RSize)) (EXMatchScrutSize ctx sr ann brs ctx1 sc sids p n) (ESErr _ _)))
                  ((OneYes s)
                    (let (erased hss) (erased hs0) (has-all-parts ctx1 s (Nil _) hs))
                    (let (many sty) (many ks) (erased t) (erased kq) (erased ssty) (erased e2) (erased ee2) (erased eo2) (type-of ctx1 wf1 s hss))
                    (let (many cs) (erased cn) (erased scs) (canonical ctx1 wf1 sty ssty))
                    (match many (matchable-dec ctx1 wf1 cs) _
                      ((MatchableNo a2 b2 um) (MkExprDec _ _ (EErr (RNotMatchable)) (EXNotMatchable ctx sr ann brs ctx1 sc s sty cs p t cn um) (ESErr _ _)))
                      ((MatchableYes a2 tc tps targs adts ctors ad ao cctors)
                        (match many (elab-tele ctx1 ctx1 wf1 (Nil _) _ (cov-refl ctx1) ann (POuter (PInner))) _
                          ((TeleStuck a3 b3 c3 d3 mq) (ExprStuck _ _))
                          ((MkTeleDec a3 b3 c3 d3 mq tout et tsc)
                            (match many tout _
                              ((TeleErr r) (MkExprDec _ _ (EErr r) (EXMatchAnnErr ctx sr ann brs ctx1 sc s r p et) (ESErr _ _)))
                              ((TeleOk ctxA rt rids rn)
                                (match many tsc _
                                  ((TLOk z1 z2 z3 z4 z5 z6 z7 mq oq wfA cr srt li ln)
                                    (let (many ctx2) (erased lv) (many wf2) (erased g12) (leave ctxA ctx1 wf1 (covrev-grew ctx1 (Nil _) rids ctxA cr)))
                                    (match many (elab-branches ctx2 wf2 s (has-grew ctx1 ctx2 s g12 hss) tc ctors (ctors-grew ctx1 ctx2 ctors wf1 g12 cctors) (Nil _) rt _ (sct-grew ctx1 ctx2 _ rt _ g12 srt) brs (POuter (PInner)) (Nil _)) _
                                      ((BranchesStuck a4 b4 c4 d4 e4 g4 h4) (ExprStuck _ _))
                                      ((MkBranchesDec a4 b4 c4 d4 e4 g4 h4 bout eb bsc)
                                        (match many bout _
                                          ((BrErr r) (MkExprDec _ _ (EErr r) (EXMatchBranchesErr ctx sr ann brs ctx1 sc s sty tc tps targs adts ctors ctxA rt rids rn ctx2 r p t cn ad ao et lv eb) (ESErr _ _)))
                                          ((BrOk ctx3 cbs seen)
                                            (match many bsc _
                                              ((BrSOk a5 b5 c5 d5 wf3 g23)
                                                (let (erased g13) (grew-trans ctx1 ctx2 ctx3 g12 g23))
                                                (match many (covered ctx3 wf3 s (has-grew ctx1 ctx3 s g13 hss) ctors (ctors-grew ctx1 ctx3 ctors wf1 g13 cctors) seen) _
                                                  ((CovNo a6 b6 c6 d6 uc) (MkExprDec _ _ (EErr (RMissingBranch)) (EXMatchUncovered ctx sr ann brs ctx1 sc s sty tc tps targs adts ctors ctxA rt rids rn ctx2 ctx3 cbs seen p t cn ad ao et lv eb uc) (ESErr _ _)))
                                                  ((CovYes a6 b6 c6 d6 cv)
                                                    (let (many names) (erased nn) (erased ln2) (nones rt))
                                                    (match many (mint-tele ctx3 wf3 (Nil _) _ (scs-nil ctx3) rt _ (sct-grew ctx1 ctx3 _ rt _ g13 srt) names ln2) _
                                                      ((MTMinted a7 b7 c7 d7 out ids wf4 g34 hids le m)
                                                        (MkExprDec _ _ (EOk out (CMatch sc cbs) ids) (EXMatch ctx sr ann brs ctx1 sc s sty tc tps targs adts ctors ctxA rt rids rn ctx2 ctx3 cbs seen names out ids p t cn ad ao et lv eb cv nn m)
                                                          (ESOk _ _ _ _ wf4 (grew-trans ctx ctx3 out (grew-trans ctx ctx1 ctx3 g1 g13) g34) hids)))))))))))))))))))))))))))))
  (many elab-branches : (many (Ctx) ctx) (many (WF ctx) wf) (many (Nat) s) (erased (Has ctx s) hs) (many (Nat) tc) (many (List (Nat)) ctors) (erased (Ctors ctx ctors) cctors) (many (List (Nat)) seen) (many (List (Entry)) rt)
      (erased (Nat) rout) (erased (ScT ctx (Zero) rt rout) srt) (subterm many (List (Raw)) brs) (subterm many (POuter (PInner)) is ph) (subterm many (Nil (Raw)) is tl) -> (many (BranchesDec ctx s tc ctors seen rt brs) r)
    (match many brs _
      ((Nil a) (MkBranchesDec _ _ _ _ _ _ _ (BrOk ctx (Nil _) seen) (EBNil ctx s tc ctors seen rt) (BrSOk _ _ _ _ wf (grew-refl ctx))))
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
                          ((RAtom cs) (elab-branch ctx wf s hs tc ctors cctors seen rt _ srt cs fnames items rest brs (PInner) (Nil _)))
                          (else (BranchesStuck _ _ _ _ _ _ _))))
                      (else (BranchesStuck _ _ _ _ _ _ _))))
                  (else (BranchesStuck _ _ _ _ _ _ _))))
              (else (BranchesStuck _ _ _ _ _ _ _))))
          (else (BranchesStuck _ _ _ _ _ _ _))))))
  (many elab-branch : (many (Ctx) ctx) (many (WF ctx) wf) (many (Nat) s) (erased (Has ctx s) hs) (many (Nat) tc) (many (List (Nat)) ctors) (erased (Ctors ctx ctors) cctors) (many (List (Nat)) seen) (many (List (Entry)) rt)
      (erased (Nat) rout) (erased (ScT ctx (Zero) rt rout) srt) (many (String) cs) (many (List (Raw)) fnames) (many (List (Raw)) items) (many (List (Raw)) rest)
      (subterm many (Cons (Raw) (RList (Cons (Raw) (RList (Cons (Raw) (RAtom cs) fnames)) items)) rest) is brs) (subterm many (PInner) is ph) (subterm many (Nil (Raw)) is tl) ->
      (many (BranchesDec ctx s tc ctors seen rt brs) r)
    (let (many scope) (erased sc) (ctx-scope ctx))
    (match many (name-dec scope cs) _
      ((NameMiss a b n) (MkBranchesDec _ _ _ _ _ _ _ (BrErr (RUnbound)) (EBUnbound ctx s tc ctors seen rt cs fnames items rest scope sc n) (BrSErr _ _)))
      ((NameHit a b c n)
        (match many (mem-dec c ctors) _
          ((MemNo d e nm) (MkBranchesDec _ _ _ _ _ _ _ (BrErr (RNotCtor)) (EBNotCtor ctx s tc ctors seen rt cs fnames items rest scope c sc n nm) (BrSErr _ _)))
          ((MemYes d e mc)
            (match many (mem-dec c seen) _
              ((MemYes g h ms) (MkBranchesDec _ _ _ _ _ _ _ (BrErr (RDuplicateBranch)) (EBDuplicate ctx s tc ctors seen rt cs fnames items rest scope c sc n mc ms) (BrSErr _ _)))
              ((MemNo g h ns)
                (let (erased cc) (ctors-mem ctx c ctors cctors mc))
                (let (many fs) (many ret) (many cty) (erased t) (erased cn) (erased fd) (erased sfs) (erased sret) (ctor-of ctx wf c cc))
                (match many (atom-names fnames) _
                  ((AtomNamesStuck a1) (BranchesStuck _ _ _ _ _ _ _))
                  ((MkAtomNames a1 names an lfn)
                    (match many (len-dec _ _ fs fnames) _
                      ((LenDiff x1 x2 x3 x4 lm) (BranchesStuck _ _ _ _ _ _ _))
                      ((LenSame x1 x2 x3 x4 lfs)
                        (match many (mint-tele ctx wf (Nil _) _ (scs-nil ctx) fs _ sfs names (len-eq-trans _ _ _ fs fnames names lfs lfn)) _
                          ((MTMinted a2 b2 c2 d2 ctxF fids wfF gF hfids le mt)
                            (let (many frefs) (erased rf) (refs fids))
                            (let (erased sfrefs) (refs-scoped ctxF fids frefs hfids rf))
                            (match many (refine ctxF wfF (Ref s) (ValApp (Ref c) fs ret frefs) (sc-ref ctxF s (has-grew ctx ctxF s gF hs)) (sc-valapp ctxF (Ref c) fs ret frefs _ (sc-ref ctxF c (has-grew ctx ctxF c gF (ctor-has ctx c cc))) (sct-grew ctx ctxF _ fs _ gF sfs) (sc-grew ctx ctxF _ ret gF sret) sfrefs (refs-len-eq fs fids frefs le rf))) _
                              ((RDContradicted a5 b5 c5 cd)
                                (MkBranchesDec _ _ _ _ _ _ _ (BrErr (RRefutedBranch)) (EBRefuted ctx s tc ctors seen rt cs fnames items rest scope c cty fs ret names ctxF fids frefs sc n mc ns t cn an mt rf cd) (BrSErr _ _)))
                              ((RDRefined a5 b5 c5 ctxR wfR gR rf2)
                                (let (erased gFR) (grew-trans ctx ctxF ctxR gF gR))
                                (match many (elab-body ctxR wfR items (POuter (PInner)) (Nil _)) _
                                  ((BodyStuck a6 b6) (BranchesStuck _ _ _ _ _ _ _))
                                  ((MkBodyDec a6 b6 bout eb bsc)
                                    (match many bout _
                                      ((EErr r) (MkBranchesDec _ _ _ _ _ _ _ (BrErr r) (EBBodyErr ctx s tc ctors seen rt cs fnames items rest scope c cty fs ret names ctxF fids frefs ctxR r sc n mc ns t cn an mt rf rf2 eb) (BrSErr _ _)))
                                      ((EOk ctxB core ids)
                                        (match many bsc _
                                          ((ESOk a7 b7 c7 d7 wfB gB hids)
                                            (let (erased gB0) (grew-trans ctx ctxR ctxB gFR gB))
                                            (let (many rout) (erased crr) (check-rets ctxB wfB (Nil _) _ (scs-nil ctxB) rt _ (sct-grew ctx ctxB _ rt _ gB0 srt) ids hids))
                                            (match many rout _
                                              ((RErr r) (MkBranchesDec _ _ _ _ _ _ _ (BrErr r) (EBRetsErr ctx s tc ctors seen rt cs fnames items rest scope c cty fs ret names ctxF fids frefs ctxR ctxB core ids r sc n mc ns t cn an mt rf rf2 eb crr) (BrSErr _ _)))
                                              ((ROk)
                                                (let (many ctx1) (erased lv) (many wf1) (erased g1) (leave ctxB ctx wf gB0))
                                                (match many (elab-branches ctx1 wf1 s (has-grew ctx ctx1 s g1 hs) tc ctors (ctors-grew ctx ctx1 ctors wf g1 cctors) (Cons _ c seen) rt _ (sct-grew ctx ctx1 _ rt _ g1 srt) rest (POuter (PInner)) (Nil _)) _
                                                  ((BranchesStuck a8 b8 c8 d8 e8 g8 h8) (BranchesStuck _ _ _ _ _ _ _))
                                                  ((MkBranchesDec a8 b8 c8 d8 e8 g8 h8 bsout q bsc2)
                                                    (match many bsout _
                                                      ((BrErr r) (MkBranchesDec _ _ _ _ _ _ _ (BrErr r) (EBRestErr ctx s tc ctors seen rt cs fnames items rest scope c cty fs ret names ctxF fids frefs ctxR ctxB core ids ctx1 r sc n mc ns t cn an mt rf rf2 eb crr lv q) (BrSErr _ _)))
                                                      ((BrOk out cbs seen2)
                                                        (match many bsc2 _
                                                          ((BrSOk a9 b9 c9 d9 wf2 g2)
                                                            (MkBranchesDec _ _ _ _ _ _ _ (BrOk out (Cons _ (MkBranch c fids core) cbs) seen2)
                                                              (EBCons ctx s tc ctors seen rt cs fnames items rest scope c cty fs ret names ctxF fids frefs ctxR ctxB core ids ctx1 out cbs seen2 sc n mc ns t cn an mt rf rf2 eb crr lv q)
                                                              (BrSOk _ _ _ _ wf2 (grew-trans ctx ctx1 out g1 g2))))))))))))))))))))))))))))))))
  (many elab-items : (many (Ctx) ctx) (many (WF ctx) wf) (subterm many (List (Raw)) raws) (subterm many (POuter (PInner)) is ph) (subterm many (Nil (Raw)) is tl) -> (many (ItemsDec ctx raws) r)
    (match many raws _
      ((Nil a) (MkItemsDec _ _ (AOk ctx (Nil _) (Nil _)) (EINil ctx) (AOOk _ _ _ _ wf (grew-refl ctx) (has-all-nil ctx))))
      ((Cons a r rest)
        (match many (elab-expr ctx wf r (POuter (PInner)) (Nil _)) _
          ((ExprStuck b c) (ItemsStuck _ _))
          ((MkExprDec b c out p esc)
            (match many out _
              ((EErr e) (MkItemsDec _ _ (AErr e) (EIErr ctx r rest e p) (AOErr _ _)))
              ((EOk ctx1 core ids)
                (match many esc _
                  ((ESOk b1 c1 d1 e1 wf1 g1 h1)
                    (match many (one-dec ids) _
                      ((OneNo d n) (MkItemsDec _ _ (AErr (RSize)) (EISize ctx r rest ctx1 core ids p n) (AOErr _ _)))
                      ((OneYes x)
                        (let (erased hx) (erased hx0) (has-all-parts ctx1 x (Nil _) h1))
                        (match many (elab-items ctx1 wf1 rest (POuter (PInner)) (Nil _)) _
                          ((ItemsStuck d e) (ItemsStuck _ _))
                          ((MkItemsDec d e rout q rsc)
                            (match many rout _
                              ((AErr e2) (MkItemsDec _ _ (AErr e2) (EIRestErr ctx r rest ctx1 core x e2 p q) (AOErr _ _)))
                              ((AOk out cores ids2)
                                (match many rsc _
                                  ((AOOk y1 y2 y3 y4 wf2 g2 h2)
                                    (MkItemsDec _ _ (AOk out (Cons _ core cores) (Cons _ x ids2)) (EICons ctx r rest ctx1 core x out cores ids2 p q)
                                      (AOOk _ _ _ _ wf2 (grew-trans ctx ctx1 out g1 g2) (has-all-cons out x ids2 (has-grew ctx1 out x g2 hx) h2))))))))))))))))))))
  (many elab-body : (many (Ctx) ctx) (many (WF ctx) wf) (subterm many (List (Raw)) items) (subterm many (POuter (PInner)) is ph) (subterm many (Nil (Raw)) is tl) -> (many (BodyDec ctx items) r)
    (match many items _
      ((Nil a) (BodyStuck _ _))
      ((Cons a first rest)
        (match many rest _
          ((Nil b)
            (match many (elab-expr ctx wf first (POuter (PInner)) (Nil _)) _
              ((ExprStuck c d) (BodyStuck _ _))
              ((MkExprDec c d out p esc) (MkBodyDec _ _ out (BodyFinal ctx first out p) esc))))
          ((Cons b second more)
            (match many (elab-stmt ctx wf first (POuter (PInner)) (Nil _)) _
              ((StmtStuck c d) (BodyStuck _ _))
              ((MkStmtDec c d sout p ssc)
                (match many sout _
                  ((SErr e) (MkBodyDec _ _ (EErr e) (BodyStmtErr ctx first second more e p) (ESErr _ _)))
                  ((SOk ctx1 st)
                    (match many ssc _
                      ((SSOk c1 d1 e1 wf1 g1)
                        (match many (elab-body ctx1 wf1 rest (POuter (PInner)) (Nil _)) _
                          ((BodyStuck c2 d2) (BodyStuck _ _))
                          ((MkBodyDec c2 d2 bout q bsc)
                            (match many bout _
                              ((EErr e) (MkBodyDec _ _ (EErr e) (BodyRestErr ctx first second more ctx1 st e p q) (ESErr _ _)))
                              ((EOk out core ids)
                                (match many bsc _
                                  ((ESOk y1 y2 y3 y4 wf2 g2 h2)
                                    (MkBodyDec _ _ (EOk out (CStmt st core) ids) (BodyStmt ctx first second more ctx1 st out core ids p q) (ESOk _ _ _ _ wf2 (grew-trans ctx ctx1 out g1 g2) h2)))))))))))))))))))
  (many elab-stmt : (many (Ctx) ctx) (many (WF ctx) wf) (subterm many (Raw) raw) (subterm many (POuter (PInner)) is ph) (subterm many (Nil (Raw)) is tl) -> (many (StmtDec ctx raw) r)
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
                          ((RList binders) (elab-let ctx wf binders body rest (POuter (PInner)) (Nil _)))
                          (else (StmtStuck _ _))))
                      (else (StmtStuck _ _))))
                  ((KDefLvl)
                    (match many rest _
                      ((Cons b lr rest2)
                        (match many rest2 _
                          ((Nil c)
                            (match many lr _
                              ((RAtom ls)
                                (let (many x) (many out) (erased m) (many wf2) (erased g2) (erased eis) (mint ctx wf (Some _ ls) level-ty (KLevel) (None _) (sc-level-ty ctx wf) (scm-none ctx) (ROkNone _)))
                                (MkStmtDec _ _ (SOk out (SDefLvl x)) (STDefLvl ctx ls x out m) (SSOk _ _ _ wf2 g2)))
                              (else (StmtStuck _ _))))
                          (else (StmtStuck _ _))))
                      (else (StmtStuck _ _))))
                  ((KDefFns)
                    (match many rest _
                      ((Cons b lr defs) (elab-def-fns ctx wf lr defs rest (POuter (PInner)) (Nil _)))
                      (else (StmtStuck _ _))))
                  ((KDefAdts) (elab-def-adts ctx wf rest))
                  (else (StmtStuck _ _))))
              (else (StmtStuck _ _))))
          (else (StmtStuck _ _))))
      (else (StmtStuck _ _))))
  (many elab-let : (many (Ctx) ctx) (many (WF ctx) wf) (many (List (Raw)) binders) (many (List (Raw)) items) (subterm many (Cons (Raw) (RList binders) items) is rest) (subterm many (POuter (PInner)) is ph)
      (subterm many (Nil (Raw)) is tl) -> (many (StmtDec ctx (RList (Cons (Raw) (RKey (KLet)) rest))) r)
    (match many (elab-body ctx wf items (POuter (PInner)) (Nil _)) _
      ((BodyStuck a b) (StmtStuck _ _))
      ((MkBodyDec a b bout p bsc)
        (match many bout _
          ((EErr r) (MkStmtDec _ _ (SErr r) (STLetErr ctx binders items r p) (SSErr _ _)))
          ((EOk ctx1 core ids)
            (match many bsc _
              ((ESOk a1 b1 c1 d1 wf1 g1 hids)
                (let (many scope) (erased sc) (many ctxH) (erased h) (many wfH) (erased gH) (erased gi) (hide ctx1 wf1 ctx wf g1))
                (match many (bind-let ctxH wfH binders ids (has-all-grew ctx1 ctxH ids gi hids)) _
                  ((BindLetStuck c d e) (StmtStuck _ _))
                  ((MkBindLetDec c d e lout bl lsc nc)
                    (match many lout _
                      ((AErr r) (MkStmtDec _ _ (SErr r) (STLetBindErr ctx binders items ctx1 core ids scope ctxH r p sc h bl) (SSErr _ _)))
                      ((AOk out cores aids)
                        (match erased nc _
                          ((NCOk z1 z2)
                            (match many lsc _
                              ((AOOk y1 y2 y3 y4 wf2 g2 haids)
                                (MkStmtDec _ _ (SOk out (SLet aids core)) (STLet ctx binders items ctx1 core ids scope ctxH out aids p sc h bl) (SSOk _ _ _ wf2 (grew-trans ctx ctxH out gH g2))))))))))))))))))
  (many elab-def-fns : (many (Ctx) ctx) (many (WF ctx) wf) (many (Raw) lr) (many (List (Raw)) defs) (subterm many (Cons (Raw) lr defs) is rest) (subterm many (POuter (PInner)) is ph) (subterm many (Nil (Raw)) is tl) ->
      (many (StmtDec ctx (RList (Cons (Raw) (RKey (KDefFns)) rest))) r)
    (match many (elab-term ctx wf lr (POuter (PInner))) _
      ((TermStuck a b) (StmtStuck _ _))
      ((MkTermDec a b lout p tsc)
        (match many lout _
          ((TErr r) (MkStmtDec _ _ (SErr r) (STDefFnsLevelErr ctx lr defs r p) (SSErr _ _)))
          ((TOk l lty)
            (match erased tsc _
              ((TSOk a2 b2 c2 sl slty)
                (match many (same-dec ctx wf lty level-ty slty (sc-level-ty ctx wf)) _
                  ((SDDiffer c d e df) (MkStmtDec _ _ (SErr (RNotLevel)) (STDefFnsNotLevel ctx lr defs l lty p df) (SSErr _ _)))
                  ((SDSame c d e sm)
                    (match many (mint-fns ctx wf l sl defs (POuter (PInner))) _
                      ((FnsStuck c2 d2 e2) (StmtStuck _ _))
                      ((MkFnsDec c2 d2 e2 fout mf fsc fl)
                        (match many fout _
                          ((FErr r) (MkStmtDec _ _ (SErr r) (STDefFnsSigErr ctx lr defs l lty r p sm mf) (SSErr _ _)))
                          ((FOk ctx1 sigs)
                            (match many fsc _
                              ((FSOk x1 x2 x3 wf1 g1 ssigs)
                                (match erased fl _
                                  ((FLOk w1 w2 w3 le)
                                    (match many (elab-bodies ctx1 wf1 l (sc-grew ctx ctx1 _ l g1 sl) sigs ssigs defs le (POuter (PInner)) (Nil _)) _
                                      ((BodiesStuck c3 d3 e3 g3) (StmtStuck _ _))
                                      ((MkBodiesDec c3 d3 e3 g3 bout eb bsc)
                                        (match many bout _
                                          ((BsErr r) (MkStmtDec _ _ (SErr r) (STDefFnsBodyErr ctx lr defs l lty ctx1 sigs r p sm mf eb) (SSErr _ _)))
                                          ((BsOk out fds)
                                            (match many bsc _
                                              ((BsSOk y1 y2 y3 wf2 g2) (MkStmtDec _ _ (SOk out (SDefFns fds)) (STDefFns ctx lr defs l lty ctx1 sigs out fds p sm mf eb) (SSOk _ _ _ wf2 (grew-trans ctx ctx1 out g1 g2))))))))))))))))))))))))))
  (many elab-bodies : (many (Ctx) ctx) (many (WF ctx) wf) (many (Term) l) (erased (Sc ctx (Zero) l) sl) (many (List (Sig)) sigs) (erased (SigsSc ctx sigs) ssigs) (subterm many (List (Raw)) defs) (erased (LenEq (Raw) (Sig) defs sigs) le)
      (subterm many (POuter (PInner)) is ph) (subterm many (Nil (Raw)) is tl) -> (many (BodiesDec ctx l sigs defs) r)
    (match many sigs _
      ((Nil a) (match many defs _ ((Nil b) (MkBodiesDec _ _ _ _ (BsOk ctx (Nil _)) (BdNil ctx l) (BsSOk _ _ _ wf (grew-refl ctx)))) ((Cons b x y) (match erased le _))))
      ((Cons a sig srest)
        (match many defs _
          ((Nil b) (match erased le _))
          ((Cons b def rest)
            (match erased le _
              ((LECons c1 c2 c3 c4 c5 c6 le2)
                (match many sig _
                  ((MkSig fid pt pn rt)
                    (match erased ssigs _
                      ((SigsCons d1 d2 d3 d4 d5 d6 dd1 dd2 spt srt lpn ssrest)
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
                                                  ((RList rs) (elab-fn-body ctx wf l sl fid pt pn rt _ _ spt srt lpn srest ssrest fn ps rs items rest le2 defs (PInner) (Nil _)))
                                                  (else (BodiesStuck _ _ _ _))))
                                              (else (BodiesStuck _ _ _ _))))
                                          (else (BodiesStuck _ _ _ _))))
                                      (else (BodiesStuck _ _ _ _))))
                                  (else (BodiesStuck _ _ _ _))))
                              (else (BodiesStuck _ _ _ _))))
                          (else (BodiesStuck _ _ _ _))))))))))))))
  (many elab-fn-body : (many (Ctx) ctx) (many (WF ctx) wf) (many (Term) l) (erased (Sc ctx (Zero) l) sl) (many (Nat) fid) (many (List (Entry)) pt) (many (List (Maybe (String))) pn) (many (List (Entry)) rt)
      (erased (Nat) d1) (erased (Nat) d2) (erased (ScT ctx (Zero) pt d1) spt) (erased (ScT ctx d1 rt d2) srt) (erased (LenEq (Entry) (Maybe (String)) pt pn) lpn) (many (List (Sig)) sigs) (erased (SigsSc ctx sigs) ssigs)
      (many (String) fn) (many (List (Raw)) ps) (many (List (Raw)) rs) (many (List (Raw)) items) (many (List (Raw)) rest) (erased (LenEq (Raw) (Sig) rest sigs) le)
      (subterm many (Cons (Raw) (RList (Cons (Raw) (RAtom fn) (Cons (Raw) (RList ps) (Cons (Raw) (RList rs) items)))) rest) is defs) (subterm many (PInner) is ph) (subterm many (Nil (Raw)) is tl) ->
      (many (BodiesDec ctx l (Cons (Sig) (MkSig fid pt pn rt) sigs) defs) r)
    (match many (mint-tele ctx wf (Nil _) _ (scs-nil ctx) pt _ spt pn lpn) _
      ((MTMinted a b c d ctxP pids wfP gP hpids le2 m)
        (let (many subargs) (erased mk) (marked pt pids le2))
        (let (many ctxE) (erased en) (many wfE) (erased gE) (enter ctxP wfP l subargs (sc-grew ctx ctxP _ l gP sl) (marked-scoped ctxP pt pids subargs hpids mk)))
        (match many (elab-body ctxE wfE items (POuter (PInner)) (Nil _)) _
          ((BodyStuck h k) (BodiesStuck _ _ _ _))
          ((MkBodyDec h k bout eb bsc)
            (match many bout _
              ((EErr r) (MkBodiesDec _ _ _ _ (BsErr r) (BdBodyErr ctx l fid pt pn rt sigs fn ps rs items rest ctxP pids subargs ctxE r m mk en eb) (BsSErr _ _)))
              ((EOk ctxB core ids)
                (match many bsc _
                  ((ESOk h1 k1 l1 m1 wfB gB hids)
                    (let (many prefs) (erased rf) (refs pids))
                    (let (many sub) (erased so) (somes prefs))
                    (let (erased gPB) (grew-trans ctxP ctxE ctxB gE gB))
                    (let (erased gB0) (grew-trans ctx ctxP ctxB gP gPB))
                    (let (many rout) (erased cr) (check-rets ctxB wfB sub _ (sc-somes ctxB prefs sub _ (refs-length pids prefs _ rf (tele-ids-length ctx pt pids _ spt le2)) (refs-scoped ctxB pids prefs (has-all-grew ctxP ctxB pids gPB hpids) rf) so) rt _ (sct-grew ctx ctxB _ rt _ gB0 srt) ids hids))
                    (match many rout _
                      ((RErr r) (MkBodiesDec _ _ _ _ (BsErr r) (BdRetsErr ctx l fid pt pn rt sigs fn ps rs items rest ctxP pids subargs ctxE ctxB core ids prefs sub r m mk en eb rf so cr) (BsSErr _ _)))
                      ((ROk)
                        (let (many ctx1) (erased lv) (many wf1) (erased g1) (leave ctxB ctx wf gB0))
                        (match many (elab-bodies ctx1 wf1 l (sc-grew ctx ctx1 _ l g1 sl) sigs (sigs-grew ctx ctx1 sigs g1 ssigs) rest le (POuter (PInner)) (Nil _)) _
                          ((BodiesStuck a3 b3 c3 d3) (BodiesStuck _ _ _ _))
                          ((MkBodiesDec a3 b3 c3 d3 bsout q bsc2)
                            (match many bsout _
                              ((BsErr r) (MkBodiesDec _ _ _ _ (BsErr r) (BdRestErr ctx l fid pt pn rt sigs fn ps rs items rest ctxP pids subargs ctxE ctxB core ids prefs sub ctx1 r m mk en eb rf so cr lv q) (BsSErr _ _)))
                              ((BsOk out fds)
                                (match many bsc2 _
                                  ((BsSOk y1 y2 y3 wf2 g2)
                                    (MkBodiesDec _ _ _ _ (BsOk out (Cons _ (MkFnDef fid pids core) fds)) (BdCons ctx l fid pt pn rt sigs fn ps rs items rest ctxP pids subargs ctxE ctxB core ids prefs sub ctx1 out fds m mk en eb rf so cr lv q)
                                      (BsSOk _ _ _ wf2 (grew-trans ctx ctx1 out g1 g2)))))))))))))))))))))

; ---- A program, in the initial context, whose well-formedness is spelled out here.
(let (many (WF init-ctx) init-wf)
  (MkWF _ _ _ _ _ _ _ (Cons _ (Zero) (Nil _)) (Succ (Zero)) (VFCons _ _ _ _ _ _ _ (BlUniv _ _ _) (VFNil _ _)) (ALCons _ _ _ (LtZ _) (ALNil _))
    (BECons _ _ _ _ _ (LtS _ _ (LtS _ _ (LtS _ _ (LtZ _)))) (BECons _ _ _ _ _ (LtS _ _ (LtS _ _ (LtZ _))) (BECons _ _ _ _ _ (LtS _ _ (LtZ _)) (BECons _ _ _ _ _ (LtZ _) (BENil _)))))
    (SECons _ _ _ _ _ (ScUniv _ _)
      (SECons _ _ _ _ _ (ScTyCtor _ _ _ _ (ScTCons _ _ _ _ _ _ _ (ScUniv _ _) (ScTCons _ _ _ _ _ _ _ (ScBound _ _ _ (LtZ _)) (ScTCons _ _ _ _ _ _ _ (ScUniv _ _) (ScTCons _ _ _ _ _ _ _ (ScBound _ _ _ (LtZ _)) (ScTNil _ _))))))
        (SECons _ _ _ _ _ (ScTyCtor _ _ _ _ (ScTCons _ _ _ _ _ _ _ (ScUniv _ _) (ScTCons _ _ _ _ _ _ _ (ScBound _ _ _ (LtZ _)) (ScTCons _ _ _ _ _ _ _ (ScTyApp _ _ _ _ _ _ (ScRef _ _ _ (HEThere _ _ _ (HEThere _ _ _ (HEThere _ _ _ (HEHere _ _ _ _))))) (ScTNil _ _) (ScNil _ _) (LENil _ _)) (ScTNil _ _)))))
          (SECons _ _ _ _ _ (ScTyCtor _ _ _ _ (ScTNil _ _)) (SENil _)))))
    (SSCons _ _ _ _ (HEHere _ _ _ _) (SSCons _ _ _ _ (HEThere _ _ _ (HEHere _ _ _ _)) (SSCons _ _ _ _ (HEThere _ _ _ (HEThere _ _ _ (HEHere _ _ _ _))) (SSCons _ _ _ _ (HEThere _ _ _ (HEThere _ _ _ (HEThere _ _ _ (HEHere _ _ _ _)))) (SSNil _)))))
    (SRCons _ _ _ _ (ScUniv _ _) (SRNil _)) (SANil _) (SMNone _) (ScNil _ _)
    (MkBuiltins _ (HEThere _ _ _ (HEThere _ _ _ (HEThere _ _ _ (HEHere _ _ _ _)))) (HEThere _ _ _ (HEThere _ _ _ (HEHere _ _ _ _))) (HEThere _ _ _ (HEHere _ _ _ _)))
    (RPCons _ _ _ _ _ _ (EntHere _ _ _ _) (NDPlain) (RPNil _))))

(def-adts
  (ProgramDec : ((List (Raw)) items) -> Type
    enum
    (many MkProgramDec : (erased (List (Raw)) items) (many (POut) out) (erased (ElabProgram items out) p) -> (ProgramDec items))
    (many ProgramStuck : (erased (List (Raw)) items) -> (ProgramDec items))))
(def-fns _ $ many elab-program : (many (List (Raw)) items) -> (many (ProgramDec items) r)
  (match many (elab-body init-ctx init-wf items (POuter (PInner)) (Nil _)) _
    ((BodyStuck a b) (ProgramStuck _))
    ((MkBodyDec a b out p esc)
      (match many out _
        ((EErr r) (MkProgramDec _ (PErr r) (ProgramErr items r p)))
        ((EOk ctx core ids)
          (match many esc _
            ((ESOk a1 b1 c1 d1 wf g h)
              (match many (one-dec ids) _
                ((OneNo c n) (MkProgramDec _ (PErr (RSize)) (ProgramSize items ctx core ids p n)))
                ((OneYes x)
                  (let (erased hx) (erased hx0) (has-all-parts ctx x (Nil _) h))
                  (let (many ty) (many k) (erased t) (erased kq) (erased sty) (erased e2) (erased ee) (erased eo) (type-of ctx wf x hx))
                  (MkProgramDec _ (POk core ty) (ProgramOk items ctx core x ty p t)))))))))))

(MkUnit)
