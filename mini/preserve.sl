; mini/preserve.sl -- groundwork for the preservation argument mini/README.md leaves open: canonicalization
; is a function of the rules, and an elaborated term of the grammar has the type elaboration gave it. One
; session's proposal, loaded after mini/elab.sl.

(def-fns _ $ (erased rule-of-unique : (erased (List (Rule)) rules) (erased (Nat) x) (erased (Term) r) (erased (Term) r2) (subterm erased (RuleOf rules x r) p) (erased (RuleOf rules x r2) q) ->
    (erased (Eq (Term) r r2) e))
  (match erased p _
    ((RuleHere _ _ _)
      (match erased q _
        ((RuleHere _ _ _) (Refl (Term) r))
        (absurd (RuleThere _ _ _ _ _ n _) (neq-irrefl x n))))
    ((RuleThere _ _ _ _ rest n p2)
      (match erased q _
        (absurd (RuleHere _ _ _) (neq-irrefl x n))
        ((RuleThere _ _ _ _ _ _ q2) (rule-of-unique rest x r r2 p2 q2))))))

(def-fns _
  ((erased canon-unique : (erased (List (Rule)) rules) (erased (Term) t) (erased (Term) u) (erased (Term) u2) (subterm erased (Canon rules t u) p) (erased (Canon rules t u2) q) -> (erased (Eq (Term) u u2) e))
    (match erased p _
      ((CanRule _ x r _ rp cp)
        (let-match erased q (CanRule _ _ r2 _ rq cq)
          (absurd (CanFree _ _ nq) (rule-of-no-rule rules x r rp nq)))
        (match erased (rule-of-unique rules x r r2 rp rq) _ ((Refl _ _) (canon-unique rules r u u2 cp cq))))
      ((CanFree _ x np)
        (match erased q _
          (absurd (CanRule _ _ r2 _ rq _) (rule-of-no-rule rules x r2 rq np))
          ((CanFree _ _ _) (Refl (Term) (Ref x)))))
      ((CanBound _ k3) (match erased q _ ((CanBound _ _) (Refl (Term) (Bound k3)))))
      ((CanTyApp _ h h2 ps as as2 ph pas)
        (let-match erased q (CanTyApp _ _ h3 _ _ as3 qh qas))
        (let-match erased (canon-unique rules h h2 h3 ph qh) (Refl _ _))
        (match erased (canon-unique-list rules as as2 as3 pas qas) _ ((Refl _ _) (Refl (Term) (TyApp h2 ps as2)))))
      ((CanValApp _ h h2 ps r as as2 ph pas)
        (let-match erased q (CanValApp _ _ h3 _ _ _ as3 qh qas))
        (let-match erased (canon-unique rules h h2 h3 ph qh) (Refl _ _))
        (match erased (canon-unique-list rules as as2 as3 pas qas) _ ((Refl _ _) (Refl (Term) (ValApp h2 ps r as2)))))
      ((CanUniv _) (match erased q _ ((CanUniv _) (Refl (Term) (TUniv)))))
      ((CanFn _ l l2b ps ps2 rs rs2 pl pps prs)
        (let-match erased q (CanFn _ _ l3b _ ps3 _ rs3 ql qps qrs))
        (let-match erased (canon-unique rules l l2b l3b pl ql) (Refl _ _))
        (let-match erased (canon-unique-tele rules ps ps2 ps3 pps qps) (Refl _ _))
        (match erased (canon-unique-tele rules rs rs2 rs3 prs qrs) _ ((Refl _ _) (Refl (Term) (TFn l2b ps2 rs2)))))
      ((CanTyCtor _ ps ps2 pps)
        (let-match erased q (CanTyCtor _ _ ps3 qps))
        (match erased (canon-unique-tele rules ps ps2 ps3 pps qps) _ ((Refl _ _) (Refl (Term) (TTyCtor ps2)))))
      ((CanValCtor _ ps ps2 r r2 pps pr)
        (let-match erased q (CanValCtor _ _ ps3 _ r3 qps qr))
        (let-match erased (canon-unique-tele rules ps ps2 ps3 pps qps) (Refl _ _))
        (match erased (canon-unique rules r r2 r3 pr qr) _ ((Refl _ _) (Refl (Term) (TValCtor ps2 r2)))))))
  ((erased canon-unique-list : (erased (List (Rule)) rules) (erased (List (Term)) ts) (erased (List (Term)) us) (erased (List (Term)) us2) (subterm erased (CanonList rules ts us) p) (erased (CanonList rules ts us2) q) ->
      (erased (Eq (List (Term)) us us2) e))
    (let-match erased p (CanCons _ t u ts2 us3 pt pts)
      ((CanNil _) (match erased q _ ((CanNil _) (Refl (List (Term)) (Nil (Term)))))))
    (let-match erased q (CanCons _ _ u0 _ us0 qt qts))
    (let-match erased (canon-unique rules t u u0 pt qt) (Refl _ _))
    (match erased (canon-unique-list rules ts2 us3 us0 pts qts) _ ((Refl _ _) (Refl (List (Term)) (Cons (Term) u us3)))))
  ((erased canon-unique-tele : (erased (List (Rule)) rules) (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (List (Entry)) fs2) (subterm erased (CanonTele rules es fs) p) (erased (CanonTele rules es fs2) q) ->
      (erased (Eq (List (Entry)) fs fs2) e))
    (let-match erased p (CanTCons _ s i t u es2 fs3 pt pes)
      ((CanTNil _) (match erased q _ ((CanTNil _) (Refl (List (Entry)) (Nil (Entry)))))))
    (let-match erased q (CanTCons _ _ _ _ u0 _ fs0 qt qes))
    (let-match erased (canon-unique rules t u u0 pt qt) (Refl _ _))
    (match erased (canon-unique-tele rules es2 fs3 fs0 pes qes) _ ((Refl _ _) (Refl (List (Entry)) (Cons (Entry) (MkEntry s i u) fs3))))))

; A term elaboration accepts has the type it gave it: [ElabTerm] forms only what [TypeOfTerm] types.
(def-fns _ $ (erased elab-term-typed : (erased (Ctx) ctx) (erased (Sexp) raw) (erased (Term) t) (erased (Term) ty) (subterm erased (ElabTerm ctx raw (TOk t ty)) p) -> (erased (Typed ctx t ty) q))
  (let-match erased ctx (MkCtx n0 s0 e0 r0 a0 l0b sa0))
  (let-match erased p (ETName _ _ x _ _ _ _ tp)
    ((ETTyApp _ _ _ ht _ ps ts _ _ _) (TypedBy ctx (TyApp ht ps ts) (TUniv) e0 r0 (EntsOf n0 s0 e0 r0 a0 l0b sa0) (RulesOf n0 s0 e0 r0 a0 l0b sa0) (TotTyApp e0 r0 ht ps ts)))
    ((ETValApp _ _ _ ht _ ps ret ts sub2 _ _ _ _ so sb)
      (TypedBy ctx (ValApp ht ps ret ts) ty e0 r0 (EntsOf n0 s0 e0 r0 a0 l0b sa0) (RulesOf n0 s0 e0 r0 a0 l0b sa0) (TotValApp e0 r0 ht ps ret ts sub2 ty so sb)))
    ((ETFn _ _ _ _ l _ _ pt _ _ _ _ rt _ _ _ _ _ _ _) (TypedBy ctx (TFn l pt rt) (TUniv) e0 r0 (EntsOf n0 s0 e0 r0 a0 l0b sa0) (RulesOf n0 s0 e0 r0 a0 l0b sa0) (TotFn e0 r0 l pt rt)))
    ((ETTyCtor _ _ _ pt _ _ _) (TypedBy ctx (TTyCtor pt) (TUniv) e0 r0 (EntsOf n0 s0 e0 r0 a0 l0b sa0) (RulesOf n0 s0 e0 r0 a0 l0b sa0) (TotTyCtor e0 r0 pt)))
    ((ETValCtor _ _ _ _ pt _ _ _ _ _ _ _ _ _ _ ret2 _ _ _ _ _ _ _ _)
      (TypedBy ctx (TValCtor pt ret2) (TUniv) e0 r0 (EntsOf n0 s0 e0 r0 a0 l0b sa0) (RulesOf n0 s0 e0 r0 a0 l0b sa0) (TotValCtor e0 r0 pt ret2))))
  (let-match erased tp (TypeOfBy _ _ _ k3 _ ee eo))
  (match erased ee _ ((EntsOf _ _ _ _ _ _ _) (TypedBy ctx (Ref x) ty e0 r0 (EntsOf n0 s0 e0 r0 a0 l0b sa0) (RulesOf n0 s0 e0 r0 a0 l0b sa0) (TotRef e0 r0 x ty k3 eo)))))

(MkUnit)
