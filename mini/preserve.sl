; mini/preserve.sl -- groundwork for the preservation argument mini/README.md leaves open: canonicalization
; is a function of the rules, and an elaborated term of the grammar has the type elaboration gave it. One
; session's proposal, loaded after mini/elab.sl.

(def-fns _ $ (erased rule-of-unique : (erased (List (Rule)) rules) (erased (Nat) x) (erased (Term) r) (erased (Term) r2) (subterm erased (RuleOf rules x r) p) (erased (RuleOf rules x r2) q) ->
    (erased (Eq (Term) r r2) e))
  (match erased p _
    ((RuleHere _ b rest)
      (match erased q _
        ((RuleHere a2 b2 rest2) (Refl (Term) r))
        (absurd (RuleThere a2 y b2 s rest2 n q2) (neq-irrefl x n))))
    ((RuleThere _ y b s rest n p2)
      (match erased q _
        (absurd (RuleHere a2 b2 rest2) (neq-irrefl x n))
        ((RuleThere a2 y2 b2 s2 rest2 n2 q2) (rule-of-unique rest x r r2 p2 q2))))))

(def-fns _
  ((erased canon-unique : (erased (List (Rule)) rules) (erased (Term) t) (erased (Term) u) (erased (Term) u2) (subterm erased (Canon rules t u) p) (erased (Canon rules t u2) q) -> (erased (Eq (Term) u u2) e))
    (match erased p _
      ((CanRule _ x r b rp cp)
        (match erased q _
          ((CanRule a2 x2 r2 b2 rq cq) (match erased (rule-of-unique rules x r r2 rp rq) _ ((Refl c d) (canon-unique rules r u u2 cp cq))))
          (absurd (CanFree a2 x2 nq) (rule-of-no-rule rules x r rp nq))))
      ((CanFree _ x np)
        (match erased q _
          (absurd (CanRule a2 x2 r2 b2 rq cq) (rule-of-no-rule rules x r2 rq np))
          ((CanFree a2 x2 nq) (Refl (Term) (Ref x)))))
      ((CanBound _ k3) (match erased q _ ((CanBound a2 k2) (Refl (Term) (Bound k3)))))
      ((CanTyApp _ h h2 ps as as2 ph pas)
        (let-match erased q (CanTyApp a2 h0 h3 ps0 as0 as3 qh qas))
        (match erased (canon-unique rules h h2 h3 ph qh) _
          ((Refl c d) (match erased (canon-unique-list rules as as2 as3 pas qas) _ ((Refl c2 d2) (Refl (Term) (TyApp h2 ps as2)))))))
      ((CanValApp _ h h2 ps r as as2 ph pas)
        (let-match erased q (CanValApp a2 h0 h3 ps0 r0 as0 as3 qh qas))
        (match erased (canon-unique rules h h2 h3 ph qh) _
          ((Refl c d) (match erased (canon-unique-list rules as as2 as3 pas qas) _ ((Refl c2 d2) (Refl (Term) (ValApp h2 ps r as2)))))))
      ((CanUniv _) (match erased q _ ((CanUniv a2) (Refl (Term) (TUniv)))))
      ((CanFn _ l l2b ps ps2 rs rs2 pl pps prs)
        (let-match erased q (CanFn a2 _ l3b ps0 ps3 rs0 rs3 ql qps qrs))
        (let-match erased (canon-unique rules l l2b l3b pl ql) (Refl c d))
        (match erased (canon-unique-tele rules ps ps2 ps3 pps qps) _
          ((Refl c2 d2) (match erased (canon-unique-tele rules rs rs2 rs3 prs qrs) _ ((Refl c3 d3) (Refl (Term) (TFn l2b ps2 rs2)))))))
      ((CanTyCtor _ ps ps2 pps)
        (match erased q _ ((CanTyCtor a2 ps0 ps3 qps) (match erased (canon-unique-tele rules ps ps2 ps3 pps qps) _ ((Refl c d) (Refl (Term) (TTyCtor ps2)))))))
      ((CanValCtor _ ps ps2 r r2 pps pr)
        (let-match erased q (CanValCtor a2 ps0 ps3 r0 r3 qps qr))
        (match erased (canon-unique-tele rules ps ps2 ps3 pps qps) _
          ((Refl c d) (match erased (canon-unique rules r r2 r3 pr qr) _ ((Refl c2 d2) (Refl (Term) (TValCtor ps2 r2)))))))))
  ((erased canon-unique-list : (erased (List (Rule)) rules) (erased (List (Term)) ts) (erased (List (Term)) us) (erased (List (Term)) us2) (subterm erased (CanonList rules ts us) p) (erased (CanonList rules ts us2) q) ->
      (erased (Eq (List (Term)) us us2) e))
    (let-match erased p (CanCons _ t u ts2 us3 pt pts)
      ((CanNil _) (match erased q _ ((CanNil a2) (Refl (List (Term)) (Nil (Term)))))))
    (let-match erased q (CanCons a2 t0 u0 ts0 us0 qt qts))
    (match erased (canon-unique rules t u u0 pt qt) _
      ((Refl c d) (match erased (canon-unique-list rules ts2 us3 us0 pts qts) _ ((Refl c2 d2) (Refl (List (Term)) (Cons (Term) u us3)))))))
  ((erased canon-unique-tele : (erased (List (Rule)) rules) (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (List (Entry)) fs2) (subterm erased (CanonTele rules es fs) p) (erased (CanonTele rules es fs2) q) ->
      (erased (Eq (List (Entry)) fs fs2) e))
    (let-match erased p (CanTCons _ s i t u es2 fs3 pt pes)
      ((CanTNil _) (match erased q _ ((CanTNil a2) (Refl (List (Entry)) (Nil (Entry)))))))
    (let-match erased q (CanTCons a2 s0 i0 t0 u0 es0 fs0 qt qes))
    (match erased (canon-unique rules t u u0 pt qt) _
      ((Refl c d) (match erased (canon-unique-tele rules es2 fs3 fs0 pes qes) _ ((Refl c2 d2) (Refl (List (Entry)) (Cons (Entry) (MkEntry s i u) fs3))))))))

; A term elaboration accepts has the type it gave it: [ElabTerm] forms only what [TypeOfTerm] types.
(def-fns _ $ (erased elab-term-typed : (erased (Ctx) ctx) (erased (Raw) raw) (erased (Term) t) (erased (Term) ty) (subterm erased (ElabTerm ctx raw (TOk t ty)) p) -> (erased (Typed ctx t ty) q))
  (let-match erased ctx (MkCtx n0 s0 e0 r0 a0 l0b sa0))
  (match erased p _
    ((ETName _ s x b scope sc n tp)
      (match erased tp _
        ((TypeOfBy c d g k3 ents ee eo)
          (match erased ee _ ((EntsOf n1 s1 e1 r1 a1 _ sa1) (TypedBy ctx (Ref x) ty e0 r0 (EntsOf n0 s0 e0 r0 a0 l0b sa0) (RulesOf n0 s0 e0 r0 a0 l0b sa0) (TotRef e0 r0 x ty k3 eo)))))))
    ((ETTyApp _ h args ht hty ps ts ph c ar) (TypedBy ctx (TyApp ht ps ts) (TUniv) e0 r0 (EntsOf n0 s0 e0 r0 a0 l0b sa0) (RulesOf n0 s0 e0 r0 a0 l0b sa0) (TotTyApp e0 r0 ht ps ts)))
    ((ETValApp _ h args ht hty ps ret ts sub2 b ph c ar so sb)
      (TypedBy ctx (ValApp ht ps ret ts) ty e0 r0 (EntsOf n0 s0 e0 r0 a0 l0b sa0) (RulesOf n0 s0 e0 r0 a0 l0b sa0) (TotValApp e0 r0 ht ps ret ts sub2 ty so sb)))
    ((ETFn _ lr ps rs l lty ctx1 pt pids pn acc ctx2 rt rids rn pl sl ep b er) (TypedBy ctx (TFn l pt rt) (TUniv) e0 r0 (EntsOf n0 s0 e0 r0 a0 l0b sa0) (RulesOf n0 s0 e0 r0 a0 l0b sa0) (TotFn e0 r0 l pt rt)))
    ((ETTyCtor _ ps ctx1 pt pids pn ep) (TypedBy ctx (TTyCtor pt) (TUniv) e0 r0 (EntsOf n0 s0 e0 r0 a0 l0b sa0) (RulesOf n0 s0 e0 r0 a0 l0b sa0) (TotTyCtor e0 r0 pt)))
    ((ETValCtor _ ps rr ctx1 pt pids pn acc ret rty tc aps args tty tps ret2 ep er cr nm tt ct b ab)
      (TypedBy ctx (TValCtor pt ret2) (TUniv) e0 r0 (EntsOf n0 s0 e0 r0 a0 l0b sa0) (RulesOf n0 s0 e0 r0 a0 l0b sa0) (TotValCtor e0 r0 pt ret2)))))

(MkUnit)
