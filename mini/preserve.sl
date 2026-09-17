; mini/preserve.sl -- groundwork for the preservation argument mini/README.md leaves open: canonicalization
; is a function of the rules, and an elaborated term of the grammar has the type elaboration gave it. One
; session's proposal, loaded after mini/elab.sl.

(def-fns _ $ erased rule-of-unique : (erased (List (Rule)) rules) (erased (Nat) x) (erased (Term) r) (erased (Term) r2) (subterm erased (RuleOf rules x r) p) (erased (RuleOf rules x r2) q) ->
    (erased (Eq (Term) r r2) e)
  (match erased p _
    ((RuleHere a b rest)
      (match erased q _
        ((RuleHere a2 b2 rest2) (Refl (Term) r))
        ((RuleThere a2 y b2 s rest2 n q2) (match erased (neq-irrefl x n) _))))
    ((RuleThere a y b s rest n p2)
      (match erased q _
        ((RuleHere a2 b2 rest2) (match erased (neq-irrefl x n) _))
        ((RuleThere a2 y2 b2 s2 rest2 n2 q2) (rule-of-unique rest x r r2 p2 q2))))))

(def-fns _
  (erased canon-unique : (erased (List (Rule)) rules) (erased (Term) t) (erased (Term) u) (erased (Term) u2) (subterm erased (Canon rules t u) p) (erased (Canon rules t u2) q) -> (erased (Eq (Term) u u2) e)
    (match erased p _
      ((CanRule a x r b rp cp)
        (match erased q _
          ((CanRule a2 x2 r2 b2 rq cq) (match erased (rule-of-unique rules x r r2 rp rq) _ ((Refl c d) (canon-unique rules r u u2 cp cq))))
          ((CanFree a2 x2 nq) (match erased (rule-of-no-rule rules x r rp nq) _))))
      ((CanFree a x np)
        (match erased q _
          ((CanRule a2 x2 r2 b2 rq cq) (match erased (rule-of-no-rule rules x r2 rq np) _))
          ((CanFree a2 x2 nq) (Refl (Term) (Ref x)))))
      ((CanBound a k) (match erased q _ ((CanBound a2 k2) (Refl (Term) (Bound k)))))
      ((CanApp a h h2 as as2 ph pas)
        (match erased q _
          ((CanApp a2 h0 h3 as0 as3 qh qas)
            (match erased (canon-unique rules h h2 h3 ph qh) _
              ((Refl c d) (match erased (canon-unique-list rules as as2 as3 pas qas) _ ((Refl c2 d2) (Refl (Term) (App h2 as2)))))))))
      ((CanUniv a) (match erased q _ ((CanUniv a2) (Refl (Term) (Univ)))))
      ((CanFn a l l2 ps ps2 rs rs2 pl pps prs)
        (match erased q _
          ((CanFn a2 l0 l3 ps0 ps3 rs0 rs3 ql qps qrs)
            (match erased (canon-unique rules l l2 l3 pl ql) _
              ((Refl c d)
                (match erased (canon-unique-tele rules ps ps2 ps3 pps qps) _
                  ((Refl c2 d2) (match erased (canon-unique-tele rules rs rs2 rs3 prs qrs) _ ((Refl c3 d3) (Refl (Term) (Fn l2 ps2 rs2)))))))))))
      ((CanTyCtor a ps ps2 pps)
        (match erased q _ ((CanTyCtor a2 ps0 ps3 qps) (match erased (canon-unique-tele rules ps ps2 ps3 pps qps) _ ((Refl c d) (Refl (Term) (TyCtor ps2)))))))
      ((CanValCtor a ps ps2 r r2 pps pr)
        (match erased q _
          ((CanValCtor a2 ps0 ps3 r0 r3 qps qr)
            (match erased (canon-unique-tele rules ps ps2 ps3 pps qps) _
              ((Refl c d) (match erased (canon-unique rules r r2 r3 pr qr) _ ((Refl c2 d2) (Refl (Term) (ValCtor ps2 r2)))))))))))
  (erased canon-unique-list : (erased (List (Rule)) rules) (erased (List (Term)) ts) (erased (List (Term)) us) (erased (List (Term)) us2) (subterm erased (CanonList rules ts us) p) (erased (CanonList rules ts us2) q) ->
      (erased (Eq (List (Term)) us us2) e)
    (match erased p _
      ((CanNil a) (match erased q _ ((CanNil a2) (Refl (List (Term)) (Nil (Term))))))
      ((CanCons a t u ts2 us3 pt pts)
        (match erased q _
          ((CanCons a2 t0 u0 ts0 us0 qt qts)
            (match erased (canon-unique rules t u u0 pt qt) _
              ((Refl c d) (match erased (canon-unique-list rules ts2 us3 us0 pts qts) _ ((Refl c2 d2) (Refl (List (Term)) (Cons (Term) u us3)))))))))))
  (erased canon-unique-tele : (erased (List (Rule)) rules) (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (List (Entry)) fs2) (subterm erased (CanonTele rules es fs) p) (erased (CanonTele rules es fs2) q) ->
      (erased (Eq (List (Entry)) fs fs2) e)
    (match erased p _
      ((CanTNil a) (match erased q _ ((CanTNil a2) (Refl (List (Entry)) (Nil (Entry))))))
      ((CanTCons a s i t u es2 fs3 pt pes)
        (match erased q _
          ((CanTCons a2 s0 i0 t0 u0 es0 fs0 qt qes)
            (match erased (canon-unique rules t u u0 pt qt) _
              ((Refl c d) (match erased (canon-unique-tele rules es2 fs3 fs0 pes qes) _ ((Refl c2 d2) (Refl (List (Entry)) (Cons (Entry) (MkEntry s i u) fs3))))))))))))

; A term elaboration accepts has the type it gave it: [ElabTerm] forms only what [TypeOfTerm] types.
(def-fns _ $ erased typed-in : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
    (erased (Term) t) (erased (Term) ty) (erased (Typed (MkCtx n s e r a l sa) t ty) p) -> (erased (TypeOfTerm e r t ty) q)
  (match erased p _ ((TypedBy c d g ents rules ee rr tot) (match erased ee _ ((EntsOf n1 s1 e1 r1 a1 l1 sa1) (match erased rr _ ((RulesOf n2 s2 e2 r2 a2 l2 sa2) tot)))))))
(def-fns _ $ erased canon-in : (erased (Nat) n) (erased (List (Name)) s) (erased (List (Ent)) e) (erased (List (Rule)) r) (erased (List (Adt)) a) (erased (Maybe (Term)) l) (erased (List (Term)) sa)
    (erased (Term) t) (erased (Term) u) (erased (Canonical (MkCtx n s e r a l sa) t u) p) -> (erased (Canon r t u) q)
  (match erased p _ ((CanonicalBy c d g rules rr cn) (match erased rr _ ((RulesOf n2 s2 e2 r2 a2 l2 sa2) cn)))))
(def-fns _ $ erased elab-term-typed : (erased (Ctx) ctx) (erased (Raw) raw) (erased (Term) t) (erased (Term) ty) (subterm erased (ElabTerm ctx raw (TOk t ty)) p) -> (erased (Typed ctx t ty) q)
  (let-match erased ctx (MkCtx n0 s0 e0 r0 a0 l0 sa0))
  (match erased p _
    ((ETName a s x b scope sc n tp)
      (match erased tp _
        ((TypeOfBy c d g k ents ee eo)
          (match erased ee _ ((EntsOf n1 s1 e1 r1 a1 l1 sa1) (TypedBy ctx (Ref x) ty e0 r0 (EntsOf n0 s0 e0 r0 a0 l0 sa0) (RulesOf n0 s0 e0 r0 a0 l0 sa0) (TotRef e0 r0 x ty k eo)))))))
    ((ETTyApp a h args ht hty ps ts ph c ar)
      (TypedBy ctx (App ht ts) (Univ) e0 r0 (EntsOf n0 s0 e0 r0 a0 l0 sa0) (RulesOf n0 s0 e0 r0 a0 l0 sa0)
        (TotTyApp e0 r0 ht ts hty ps (typed-in n0 s0 e0 r0 a0 l0 sa0 ht hty (elab-term-typed ctx h ht hty ph)) (canon-in n0 s0 e0 r0 a0 l0 sa0 hty (TyCtor ps) c))))
    ((ETValApp a h args ht hty ps ret ts sub b ph c ar so sb)
      (TypedBy ctx (App ht ts) ty e0 r0 (EntsOf n0 s0 e0 r0 a0 l0 sa0) (RulesOf n0 s0 e0 r0 a0 l0 sa0)
        (TotValApp e0 r0 ht ts hty ps ret sub ty (typed-in n0 s0 e0 r0 a0 l0 sa0 ht hty (elab-term-typed ctx h ht hty ph)) (canon-in n0 s0 e0 r0 a0 l0 sa0 hty (ValCtor ps ret) c) so sb)))
    ((ETFn a lr ps rs l lty ctx1 pt pids pn acc ctx2 rt rids rn pl sl ep b er) (TypedBy ctx (Fn l pt rt) (Univ) e0 r0 (EntsOf n0 s0 e0 r0 a0 l0 sa0) (RulesOf n0 s0 e0 r0 a0 l0 sa0) (TotFn e0 r0 l pt rt)))
    ((ETTyCtor a ps ctx1 pt pids pn ep) (TypedBy ctx (TyCtor pt) (Univ) e0 r0 (EntsOf n0 s0 e0 r0 a0 l0 sa0) (RulesOf n0 s0 e0 r0 a0 l0 sa0) (TotTyCtor e0 r0 pt)))
    ((ETValCtor a ps rr ctx1 pt pids pn acc ret rty tc args tty tps ret2 ep er cr nm tt ct b ab)
      (TypedBy ctx (ValCtor pt ret2) (Univ) e0 r0 (EntsOf n0 s0 e0 r0 a0 l0 sa0) (RulesOf n0 s0 e0 r0 a0 l0 sa0) (TotValCtor e0 r0 pt ret2)))))

(MkUnit)
