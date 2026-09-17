; mini/canon.sl -- the fact table's rewrite rules and canonicalization (DESIGN.md sections 3, 5 and 18) for
; the minimal language: a rule maps an entry to a term, and a term's canonical form replaces every entry
; that has a rule by the canonical form of that rule's term, structurally. Rules are kept oldest first and
; a rule's term is canonical against the rules older than it when minted (section 18), so canonicalizing
; it needs only the rules after it, which is what makes canonicalization structural on the rules and the
; term together. One session's proposal.

(def-adts $ Rule : -> Type
  enum
  (many MkRule : (many (Nat) id) (many (Term) rhs) -> (Rule)))

; The rule an entry has, the oldest first, with the rules after it, or evidence that it has none.
(def-adts
  (RuleOf : ((List (Rule)) rules) ((Nat) x) ((Term) r) ((List (Rule)) rest) -> Type
    enum
    (many RuleHere : (erased (Nat) x) (erased (Term) r) (erased (List (Rule)) rest) -> (RuleOf (Cons (Rule) (MkRule x r) rest) x r rest))
    (many RuleThere : (erased (Nat) x) (erased (Nat) y) (erased (Term) r) (erased (Term) s) (erased (List (Rule)) rest) (erased (List (Rule)) after) (erased (Neq x y) n)
       (erased (RuleOf rest x r after) p) -> (RuleOf (Cons (Rule) (MkRule y s) rest) x r after)))
  (NoRule : ((List (Rule)) rules) ((Nat) x) -> Type
    enum
    (many NoRuleNil : (erased (Nat) x) -> (NoRule (Nil (Rule)) x))
    (many NoRuleCons : (erased (Nat) x) (erased (Nat) y) (erased (Term) s) (erased (List (Rule)) rest) (erased (Neq x y) n) (erased (NoRule rest x) p) ->
       (NoRule (Cons (Rule) (MkRule y s) rest) x)))
  (RuleDec : ((List (Rule)) rules) ((Nat) x) -> Type
    enum
    (many RuleHit : (erased (List (Rule)) rules) (erased (Nat) x) (many (Term) r) (many (List (Rule)) rest) (erased (RuleOf rules x r rest) p)
       (erased (Subterm (List (Rule)) rest (List (Rule)) rules) s) -> (RuleDec rules x))
    (many RuleMiss : (erased (List (Rule)) rules) (erased (Nat) x) (erased (NoRule rules x) p) -> (RuleDec rules x))))

(def-fns _ $ many rule-dec : (subterm many (List (Rule)) rules) (many (Nat) x) -> (many (RuleDec rules x) r)
  (match many rules _
    ((Nil a) (RuleMiss _ _ $ NoRuleNil x))
    ((Cons a rule rest)
      (match many rule _
        ((MkRule y s)
          (match many (nat-dec x y) _
            ((NDSame z) (RuleHit _ _ s rest (RuleHere x s rest) (prove-subterm rest rules)))
            ((NDDiff z w n)
              (match many (rule-dec rest x) _
                ((RuleHit l z2 r after p sb) (RuleHit _ _ r after (RuleThere x y r s rest after n p) (subterm-trans sb (prove-subterm rest rules))))
                ((RuleMiss l z2 p) (RuleMiss _ _ $ NoRuleCons x y s rest n p))))))))))

(def-adts
  (Canon : ((List (Rule)) rules) ((Term) t) ((Term) u) -> Type
    enum
    (many CanRule : (erased (List (Rule)) rules) (erased (Nat) x) (erased (Term) r) (erased (List (Rule)) rest) (erased (Term) u) (erased (RuleOf rules x r rest) p) (erased (Canon rest r u) q) ->
       (Canon rules (Ref x) u))
    (many CanFree : (erased (List (Rule)) rules) (erased (Nat) x) (erased (NoRule rules x) p) -> (Canon rules (Ref x) (Ref x)))
    (many CanBound : (erased (List (Rule)) rules) (erased (Nat) k) -> (Canon rules (Bound k) (Bound k)))
    (many CanApp : (erased (List (Rule)) rules) (erased (Term) h) (erased (Term) h2) (erased (List (Term)) as) (erased (List (Term)) as2)
       (erased (Canon rules h h2) p) (erased (CanonList rules as as2) q) -> (Canon rules (App h as) (App h2 as2)))
    (many CanUniv : (erased (List (Rule)) rules) -> (Canon rules (Univ) (Univ)))
    (many CanFn : (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) l2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2)
       (erased (List (Entry)) rs) (erased (List (Entry)) rs2)
       (erased (Canon rules l l2) p) (erased (CanonTele rules ps ps2) q) (erased (CanonTele rules rs rs2) r) -> (Canon rules (Fn l ps rs) (Fn l2 ps2 rs2)))
    (many CanTyCtor : (erased (List (Rule)) rules) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (CanonTele rules ps ps2) q) ->
       (Canon rules (TyCtor ps) (TyCtor ps2)))
    (many CanValCtor : (erased (List (Rule)) rules) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (Term) r) (erased (Term) r2)
       (erased (CanonTele rules ps ps2) q) (erased (Canon rules r r2) p) -> (Canon rules (ValCtor ps r) (ValCtor ps2 r2))))
  (CanonList : ((List (Rule)) rules) ((List (Term)) ts) ((List (Term)) us) -> Type
    enum
    (many CanNil : (erased (List (Rule)) rules) -> (CanonList rules (Nil (Term)) (Nil (Term))))
    (many CanCons : (erased (List (Rule)) rules) (erased (Term) t) (erased (Term) u) (erased (List (Term)) ts) (erased (List (Term)) us)
       (erased (Canon rules t u) p) (erased (CanonList rules ts us) q) -> (CanonList rules (Cons (Term) t ts) (Cons (Term) u us))))
  (CanonTele : ((List (Rule)) rules) ((List (Entry)) es) ((List (Entry)) fs) -> Type
    enum
    (many CanTNil : (erased (List (Rule)) rules) -> (CanonTele rules (Nil (Entry)) (Nil (Entry))))
    (many CanTCons : (erased (List (Rule)) rules) (erased (Bool) s) (erased (Bool) i) (erased (Term) t) (erased (Term) u) (erased (List (Entry)) es) (erased (List (Entry)) fs)
       (erased (Canon rules t u) p) (erased (CanonTele rules es fs) q) -> (CanonTele rules (Cons (Entry) (MkEntry s i t) es) (Cons (Entry) (MkEntry s i u) fs)))))

(def-fns _
  (many canon : (subterm many (List (Rule)) rules) (subterm many (Term) t) -> (many (Term) u) (erased (Canon rules t u) p)
    (match many t _
      ((Ref x)
        (match many (rule-dec rules x) _
          ((RuleMiss l y p) (values (Ref x) (CanFree rules x p)))
          ((RuleHit l y r rest p sb)
            (let (many u) (erased q) (canon (subterm sb) rest r))
            (values u (CanRule rules x r rest u p q)))))
      ((Bound k) (values (Bound k) (CanBound rules k)))
      ((App h as)
        (let (many h2) (erased p) (canon rules h))
        (let (many as2) (erased q) (canon-list rules as))
        (values (App h2 as2) (CanApp rules h h2 as as2 p q)))
      ((Univ) (values (Univ) (CanUniv rules)))
      ((Fn l ps rs)
        (let (many l2) (erased p) (canon rules l))
        (let (many ps2) (erased q) (canon-tele rules ps))
        (let (many rs2) (erased r) (canon-tele rules rs))
        (values (Fn l2 ps2 rs2) (CanFn rules l l2 ps ps2 rs rs2 p q r)))
      ((TyCtor ps)
        (let (many ps2) (erased q) (canon-tele rules ps))
        (values (TyCtor ps2) (CanTyCtor rules ps ps2 q)))
      ((ValCtor ps r)
        (let (many ps2) (erased q) (canon-tele rules ps))
        (let (many r2) (erased p) (canon rules r))
        (values (ValCtor ps2 r2) (CanValCtor rules ps ps2 r r2 q p)))))
  (many canon-list : (subterm many (List (Rule)) rules) (subterm many (List (Term)) ts) -> (many (List (Term)) us) (erased (CanonList rules ts us) p)
    (match many ts _
      ((Nil a) (values (Nil _) (CanNil rules)))
      ((Cons a t rest)
        (let (many u) (erased p) (canon rules t))
        (let (many us) (erased q) (canon-list rules rest))
        (values (Cons _ u us) (CanCons rules t u rest us p q)))))
  (many canon-tele : (subterm many (List (Rule)) rules) (subterm many (List (Entry)) es) -> (many (List (Entry)) fs) (erased (CanonTele rules es fs) p)
    (match many es _
      ((Nil a) (values (Nil _) (CanTNil rules)))
      ((Cons a e rest)
        (match many e _
          ((MkEntry s i t)
            (let (many u) (erased p) (canon rules t))
            (let (many fs) (erased q) (canon-tele rules rest))
            (values (Cons _ (MkEntry s i u) fs) (CanTCons rules s i t u rest fs p q))))))))

(MkUnit)
