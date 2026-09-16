; mini/canon.sl -- the fact table's rewrite rules and canonicalization (DESIGN.md sections 3, 5 and 18) for
; the minimal language: a rule maps an entry to a term, and a term's canonical form replaces every entry
; that has a rule by the canonical form of that rule's term, structurally. One session's proposal.

(def-adts $ Rule : -> Type
  enum
  (many MkRule : (many (Nat) id) (many (Term) rhs) -> (Rule)))

; The rule an entry has, the newest first, or evidence that it has none.
(def-adts
  (RuleOf : ((List (Rule)) rules) ((Nat) x) ((Term) r) -> Type
    enum
    (many RuleHere : (erased (Nat) x) (erased (Term) r) (erased (List (Rule)) rest) -> (RuleOf (Cons (Rule) (MkRule x r) rest) x r))
    (many RuleThere : (erased (Nat) x) (erased (Nat) y) (erased (Term) r) (erased (Term) s) (erased (List (Rule)) rest) (erased (Neq x y) n) (erased (RuleOf rest x r) p) ->
       (RuleOf (Cons (Rule) (MkRule y s) rest) x r)))
  (NoRule : ((List (Rule)) rules) ((Nat) x) -> Type
    enum
    (many NoRuleNil : (erased (Nat) x) -> (NoRule (Nil (Rule)) x))
    (many NoRuleCons : (erased (Nat) x) (erased (Nat) y) (erased (Term) s) (erased (List (Rule)) rest) (erased (Neq x y) n) (erased (NoRule rest x) p) ->
       (NoRule (Cons (Rule) (MkRule y s) rest) x)))
  (RuleDec : ((List (Rule)) rules) ((Nat) x) -> Type
    enum
    (many RuleHit : (erased (List (Rule)) rules) (erased (Nat) x) (many (Term) r) (erased (RuleOf rules x r) p) -> (RuleDec rules x))
    (many RuleMiss : (erased (List (Rule)) rules) (erased (Nat) x) (erased (NoRule rules x) p) -> (RuleDec rules x))))

(def-fns _ $ many rule-dec : (subterm many (List (Rule)) rules) (many (Nat) x) -> (many (RuleDec rules x) r)
  (match many rules _
    ((Nil a) (RuleMiss _ _ $ NoRuleNil x))
    ((Cons a rule rest)
      (match many rule _
        ((MkRule y s)
          (match many (nat-dec x y) _
            ((NDSame z) (RuleHit _ _ s $ RuleHere x s rest))
            ((NDDiff z w n)
              (match many (rule-dec rest x) _
                ((RuleHit l z2 r p) (RuleHit _ _ r $ RuleThere x y r s rest n p))
                ((RuleMiss l z2 p) (RuleMiss _ _ $ NoRuleCons x y s rest n p))))))))))

(def-adts
  (Canon : ((List (Rule)) rules) ((Term) t) ((Term) u) -> Type
    enum
    (many CanRule : (erased (List (Rule)) rules) (erased (Nat) x) (erased (Term) r) (erased (Term) u) (erased (RuleOf rules x r) p) (erased (Canon rules r u) q) ->
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

(def-adts
  (Canoned : ((List (Rule)) rules) ((Term) t) -> Type
    enum
    (many MkCanoned : (erased (List (Rule)) rules) (erased (Term) t) (many (Term) u) (erased (Canon rules t u) p) -> (Canoned rules t))
    (many CanonStuck : (erased (List (Rule)) rules) (erased (Term) t) -> (Canoned rules t)))
  (CanonedList : ((List (Rule)) rules) ((List (Term)) ts) -> Type
    enum
    (many MkCanonedList : (erased (List (Rule)) rules) (erased (List (Term)) ts) (many (List (Term)) us) (erased (CanonList rules ts us) p) -> (CanonedList rules ts))
    (many CanonListStuck : (erased (List (Rule)) rules) (erased (List (Term)) ts) -> (CanonedList rules ts)))
  (CanonedTele : ((List (Rule)) rules) ((List (Entry)) es) -> Type
    enum
    (many MkCanonedTele : (erased (List (Rule)) rules) (erased (List (Entry)) es) (many (List (Entry)) fs) (erased (CanonTele rules es fs) p) -> (CanonedTele rules es))
    (many CanonTeleStuck : (erased (List (Rule)) rules) (erased (List (Entry)) es) -> (CanonedTele rules es))))

(def-fns _
  (many canon : (subterm many (Nat) fuel) (many (List (Rule)) rules) (many (Term) t) -> (many (Canoned rules t) r)
    (match many fuel _
      ((Zero) (CanonStuck _ _))
      ((Succ f)
        (match many t _
          ((Ref x)
            (match many (rule-dec rules x) _
              ((RuleMiss l y p) (MkCanoned _ _ (Ref x) $ CanFree rules x p))
              ((RuleHit l y r p)
                (match many (canon f rules r) _
                  ((CanonStuck s1 t1) (CanonStuck _ _))
                  ((MkCanoned s1 t1 u q) (MkCanoned _ _ u $ CanRule rules x r u p q))))))
          ((Bound k) (MkCanoned _ _ (Bound k) $ CanBound rules k))
          ((App h as)
            (match many (canon f rules h) _
              ((CanonStuck s1 t1) (CanonStuck _ _))
              ((MkCanoned s1 t1 h2 p)
                (match many (canon-list f rules as) _
                  ((CanonListStuck s2 t2) (CanonStuck _ _))
                  ((MkCanonedList s2 t2 as2 q) (MkCanoned _ _ (App h2 as2) $ CanApp rules h h2 as as2 p q))))))
          ((Univ) (MkCanoned _ _ (Univ) $ CanUniv rules))
          ((Fn l ps rs)
            (match many (canon f rules l) _
              ((CanonStuck s1 t1) (CanonStuck _ _))
              ((MkCanoned s1 t1 l2 p)
                (match many (canon-tele f rules ps) _
                  ((CanonTeleStuck s2 t2) (CanonStuck _ _))
                  ((MkCanonedTele s2 t2 ps2 q)
                    (match many (canon-tele f rules rs) _
                      ((CanonTeleStuck s3 t3) (CanonStuck _ _))
                      ((MkCanonedTele s3 t3 rs2 r) (MkCanoned _ _ (Fn l2 ps2 rs2) $ CanFn rules l l2 ps ps2 rs rs2 p q r))))))))
          ((TyCtor ps)
            (match many (canon-tele f rules ps) _
              ((CanonTeleStuck s2 t2) (CanonStuck _ _))
              ((MkCanonedTele s2 t2 ps2 q) (MkCanoned _ _ (TyCtor ps2) $ CanTyCtor rules ps ps2 q))))
          ((ValCtor ps r)
            (match many (canon-tele f rules ps) _
              ((CanonTeleStuck s2 t2) (CanonStuck _ _))
              ((MkCanonedTele s2 t2 ps2 q)
                (match many (canon f rules r) _
                  ((CanonStuck s1 t1) (CanonStuck _ _))
                  ((MkCanoned s1 t1 r2 p) (MkCanoned _ _ (ValCtor ps2 r2) $ CanValCtor rules ps ps2 r r2 q p))))))))))
  (many canon-list : (subterm many (Nat) fuel) (many (List (Rule)) rules) (many (List (Term)) ts) -> (many (CanonedList rules ts) r)
    (match many fuel _
      ((Zero) (CanonListStuck _ _))
      ((Succ f)
        (match many ts _
          ((Nil a) (MkCanonedList _ _ (Nil _) $ CanNil rules))
          ((Cons a t rest)
            (match many (canon f rules t) _
              ((CanonStuck s1 t1) (CanonListStuck _ _))
              ((MkCanoned s1 t1 u p)
                (match many (canon-list f rules rest) _
                  ((CanonListStuck s2 t2) (CanonListStuck _ _))
                  ((MkCanonedList s2 t2 us q) (MkCanonedList _ _ (Cons _ u us) $ CanCons rules t u rest us p q))))))))))
  (many canon-tele : (subterm many (Nat) fuel) (many (List (Rule)) rules) (many (List (Entry)) es) -> (many (CanonedTele rules es) r)
    (match many fuel _
      ((Zero) (CanonTeleStuck _ _))
      ((Succ f)
        (match many es _
          ((Nil a) (MkCanonedTele _ _ (Nil _) $ CanTNil rules))
          ((Cons a e rest)
            (match many e _
              ((MkEntry s i t)
                (match many (canon f rules t) _
                  ((CanonStuck s1 t1) (CanonTeleStuck _ _))
                  ((MkCanoned s1 t1 u p)
                    (match many (canon-tele f rules rest) _
                      ((CanonTeleStuck s2 t2) (CanonTeleStuck _ _))
                      ((MkCanonedTele s2 t2 fs q) (MkCanonedTele _ _ (Cons _ (MkEntry s i u) fs) $ CanTCons rules s i t u rest fs p q)))))))))))))

(MkUnit)
