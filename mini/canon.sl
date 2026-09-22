; mini/canon.sl -- the fact table's rewrite rules and canonicalization (DESIGN.md sections 3, 5 and 18) for
; the minimal language: a rule maps an entry to a term, and a term's canonical form replaces every entry
; that has a rule by the canonical form of that rule's term, structurally. The function that derives it recurses
; on a rank: beside the rules the functions carry a rank per rule under which every rule's term sits below
; its own rank, so a rule's term is canonicalized under a lower bound than the term that mentioned it.
; One session's proposal.

(def-adts $ (Rule : -> Type)
  enum
  (many MkRule : (many (Nat) id) (many (Term) rhs) -> (Rule)))

; The rule an entry has, the newest first, or evidence that it has none.
(def-adts
  ((RuleOf : ((List (Rule)) rules) ((Nat) x) ((Term) r) -> Type)
    enum
    (many RuleHere : (erased (Nat) x) (erased (Term) r) (erased (List (Rule)) rest) -> (RuleOf (Cons (Rule) (MkRule x r) rest) x r))
    (many RuleThere : (erased (Nat) x) (erased (Nat) y) (erased (Term) r) (erased (Term) s) (erased (List (Rule)) rest) (erased (Neq x y) n) (erased (RuleOf rest x r) p)
       -> (RuleOf (Cons (Rule) (MkRule y s) rest) x r)))
  ((NoRule : ((List (Rule)) rules) ((Nat) x) -> Type)
    enum
    (many NoRuleNil : (erased (Nat) x) -> (NoRule (Nil (Rule)) x))
    (many NoRuleCons : (erased (Nat) x) (erased (Nat) y) (erased (Term) s) (erased (List (Rule)) rest) (erased (Neq x y) n) (erased (NoRule rest x) p)
       -> (NoRule (Cons (Rule) (MkRule y s) rest) x)))
  ((RuleDec : ((List (Rule)) rules) ((Nat) x) -> Type)
    enum
    (many RuleHit : (erased (List (Rule)) rules) (erased (Nat) x) (many (Term) r) (erased (RuleOf rules x r) p) -> (RuleDec rules x))
    (many RuleMiss : (erased (List (Rule)) rules) (erased (Nat) x) (erased (NoRule rules x) p) -> (RuleDec rules x))))

(def-fns _ $ (many rule-dec : (subterm many (List (Rule)) rules) (many (Nat) x) -> (many (RuleDec rules x) r))
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
  ((Canon : ((List (Rule)) rules) ((Term) t) ((Term) u) -> Type)
    enum
    (many CanRule : (erased (List (Rule)) rules) (erased (Nat) x) (erased (Term) r) (erased (Term) u) (erased (RuleOf rules x r) p) (erased (Canon rules r u) q)
       -> (Canon rules (Ref x) u))
    (many CanFree : (erased (List (Rule)) rules) (erased (Nat) x) (erased (NoRule rules x) p) -> (Canon rules (Ref x) (Ref x)))
    (many CanBound : (erased (List (Rule)) rules) (erased (Nat) k) -> (Canon rules (Bound k) (Bound k)))
    (many CanTyApp : (erased (List (Rule)) rules) (erased (Term) h) (erased (Term) h2) (erased (List (Entry)) ps) (erased (List (Term)) as) (erased (List (Term)) as2)
       (erased (Canon rules h h2) p) (erased (CanonList rules as as2) q) -> (Canon rules (TyApp h ps as) (TyApp h2 ps as2)))
    (many CanValApp : (erased (List (Rule)) rules) (erased (Term) h) (erased (Term) h2) (erased (List (Entry)) ps) (erased (Term) r) (erased (List (Term)) as) (erased (List (Term)) as2)
       (erased (Canon rules h h2) p) (erased (CanonList rules as as2) q) -> (Canon rules (ValApp h ps r as) (ValApp h2 ps r as2)))
    (many CanUniv : (erased (List (Rule)) rules) -> (Canon rules (TUniv) (TUniv)))
    (many CanFn : (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) l2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2)
       (erased (List (Entry)) rs) (erased (List (Entry)) rs2)
       (erased (Canon rules l l2) p) (erased (CanonTele rules ps ps2) q) (erased (CanonTele rules rs rs2) r) -> (Canon rules (TFn l ps rs) (TFn l2 ps2 rs2)))
    (many CanTyCtor : (erased (List (Rule)) rules) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (CanonTele rules ps ps2) q)
       -> (Canon rules (TTyCtor ps) (TTyCtor ps2)))
    (many CanValCtor : (erased (List (Rule)) rules) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (Term) r) (erased (Term) r2)
       (erased (CanonTele rules ps ps2) q) (erased (Canon rules r r2) p) -> (Canon rules (TValCtor ps r) (TValCtor ps2 r2))))
  ((CanonList : ((List (Rule)) rules) ((List (Term)) ts) ((List (Term)) us) -> Type)
    enum
    (many CanNil : (erased (List (Rule)) rules) -> (CanonList rules (Nil (Term)) (Nil (Term))))
    (many CanCons : (erased (List (Rule)) rules) (erased (Term) t) (erased (Term) u) (erased (List (Term)) ts) (erased (List (Term)) us)
       (erased (Canon rules t u) p) (erased (CanonList rules ts us) q) -> (CanonList rules (Cons (Term) t ts) (Cons (Term) u us))))
  ((CanonTele : ((List (Rule)) rules) ((List (Entry)) es) ((List (Entry)) fs) -> Type)
    enum
    (many CanTNil : (erased (List (Rule)) rules) -> (CanonTele rules (Nil (Entry)) (Nil (Entry))))
    (many CanTCons : (erased (List (Rule)) rules) (erased (Bool) s) (erased (Bool) i) (erased (Term) t) (erased (Term) u) (erased (List (Entry)) es) (erased (List (Entry)) fs)
       (erased (Canon rules t u) p) (erased (CanonTele rules es fs) q) -> (CanonTele rules (Cons (Entry) (MkEntry s i t) es) (Cons (Entry) (MkEntry s i u) fs)))))

; ---- Ranks. [RuleRank] reads a rule and its rank together; [Below] says every entry a term mentions that
; has a rule has that rule's rank below [k]; [ValidFrom all ar rs ks] says the rules [rs] with ranks [ks], a
; suffix of the table [all] with ranks [ar], each sit below their own rank in that table.
(def-adts
  ((RuleRank : ((List (Rule)) rules) ((List (Nat)) ranks) ((Nat) x) ((Term) r) ((Nat) k) -> Type)
    enum
    (many RRHere : (erased (Nat) x) (erased (Term) r) (erased (Nat) k) (erased (List (Rule)) rest) (erased (List (Nat)) ks) -> (RuleRank (Cons (Rule) (MkRule x r) rest) (Cons (Nat) k ks) x r k))
    (many RRThere : (erased (Nat) x) (erased (Nat) y) (erased (Term) r) (erased (Term) s) (erased (Nat) k) (erased (Nat) k2) (erased (List (Rule)) rest) (erased (List (Nat)) ks)
       (erased (Neq x y) n) (erased (RuleRank rest ks x r k) p) -> (RuleRank (Cons (Rule) (MkRule y s) rest) (Cons (Nat) k2 ks) x r k)))
  ((Below : ((List (Rule)) rules) ((List (Nat)) ranks) ((Term) t) ((Nat) k) -> Type)
    enum
    (many BlFree : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (Nat) x) (erased (Nat) k) (erased (NoRule rules x) p) -> (Below rules ranks (Ref x) k))
    (many BlRuled : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (Nat) x) (erased (Nat) k) (erased (Term) r) (erased (Nat) j) (erased (RuleRank rules ranks x r j) p) (erased (Lt j k) lt)
       -> (Below rules ranks (Ref x) k))
    (many BlBound : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (Nat) i) (erased (Nat) k) -> (Below rules ranks (Bound i) k))
    (many BlTyApp : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (Term) h) (erased (List (Entry)) ps) (erased (List (Term)) as) (erased (Nat) k)
       (erased (Below rules ranks h k) p) (erased (BelowList rules ranks as k) q) -> (Below rules ranks (TyApp h ps as) k))
    (many BlValApp : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (Term) h) (erased (List (Entry)) ps) (erased (Term) r) (erased (List (Term)) as) (erased (Nat) k)
       (erased (Below rules ranks h k) p) (erased (BelowList rules ranks as k) q) -> (Below rules ranks (ValApp h ps r as) k))
    (many BlUniv : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (Nat) k) -> (Below rules ranks (TUniv) k))
    (many BlFn : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs) (erased (Nat) k)
       (erased (Below rules ranks l k) p) (erased (BelowTele rules ranks ps k) q) (erased (BelowTele rules ranks rs k) r) -> (Below rules ranks (TFn l ps rs) k))
    (many BlTyCtor : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (List (Entry)) ps) (erased (Nat) k) (erased (BelowTele rules ranks ps k) q) -> (Below rules ranks (TTyCtor ps) k))
    (many BlValCtor : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (List (Entry)) ps) (erased (Term) r) (erased (Nat) k) (erased (BelowTele rules ranks ps k) q) (erased (Below rules ranks r k) p)
       -> (Below rules ranks (TValCtor ps r) k)))
  ((BelowList : ((List (Rule)) rules) ((List (Nat)) ranks) ((List (Term)) ts) ((Nat) k) -> Type)
    enum
    (many BlNil : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (Nat) k) -> (BelowList rules ranks (Nil (Term)) k))
    (many BlCons : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (Term) t) (erased (List (Term)) ts) (erased (Nat) k) (erased (Below rules ranks t k) p) (erased (BelowList rules ranks ts k) q)
       -> (BelowList rules ranks (Cons (Term) t ts) k)))
  ((BelowTele : ((List (Rule)) rules) ((List (Nat)) ranks) ((List (Entry)) es) ((Nat) k) -> Type)
    enum
    (many BlTNil : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (Nat) k) -> (BelowTele rules ranks (Nil (Entry)) k))
    (many BlTCons : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (Bool) s) (erased (Bool) i) (erased (Term) t) (erased (List (Entry)) es) (erased (Nat) k)
       (erased (Below rules ranks t k) p) (erased (BelowTele rules ranks es k) q) -> (BelowTele rules ranks (Cons (Entry) (MkEntry s i t) es) k)))
  ((ValidFrom : ((List (Rule)) all) ((List (Nat)) ar) ((List (Rule)) rs) ((List (Nat)) ks) -> Type)
    enum
    (many VFNil : (erased (List (Rule)) all) (erased (List (Nat)) ar) -> (ValidFrom all ar (Nil (Rule)) (Nil (Nat))))
    (many VFCons : (erased (List (Rule)) all) (erased (List (Nat)) ar) (erased (Nat) x) (erased (Term) r) (erased (Nat) k) (erased (List (Rule)) rs) (erased (List (Nat)) ks)
       (erased (Below all ar r k) b) (erased (ValidFrom all ar rs ks) p) -> (ValidFrom all ar (Cons (Rule) (MkRule x r) rs) (Cons (Nat) k ks))))
  ((AllLt : ((List (Nat)) ks) ((Nat) m) -> Type)
    enum
    (many ALNil : (erased (Nat) m) -> (AllLt (Nil (Nat)) m))
    (many ALCons : (erased (Nat) k) (erased (List (Nat)) ks) (erased (Nat) m) (erased (Lt k m) p) (erased (AllLt ks m) q) -> (AllLt (Cons (Nat) k ks) m)))
  ; The rule an entry has with its rank, or evidence that it has none. Ranks parallel the rules by [ValidFrom].
  ((RankDec : ((List (Rule)) rules) ((List (Nat)) ranks) ((Nat) x) -> Type)
    enum
    (many RankHit : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (Nat) x) (many (Term) r) (many (Nat) k) (erased (RuleRank rules ranks x r k) p) -> (RankDec rules ranks x))
    (many RankMiss : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (Nat) x) (erased (NoRule rules x) p) -> (RankDec rules ranks x)))
  ((SameRank : ((Term) r) ((Nat) k) ((Term) r2) ((Nat) k2) -> Type)
    enum
    (many SameRankRefl : (erased (Term) r) (erased (Nat) k) -> (SameRank r k r k))))

(def-fns _ $ (many rank-dec : (erased (List (Rule)) all) (erased (List (Nat)) ar) (subterm many (List (Rule)) rules) (many (List (Nat)) ranks) (erased (ValidFrom all ar rules ranks) v) (many (Nat) x) ->
    (many (RankDec rules ranks x) d))
  (match many rules _
    ((Nil a) (match erased v _ ((VFNil b c) (RankMiss _ _ _ (NoRuleNil x)))))
    ((Cons a rule rest)
      (match many rule _
        ((MkRule y s)
          (match erased v _
            ((VFCons b c y2 s2 k rest2 ks bl v2)
              (match many ranks _
                ((Cons d k0 ks0)
                  (match many (nat-dec x y) _
                    ((NDSame z) (RankHit _ _ _ s k0 (RRHere x s k0 rest ks0)))
                    ((NDDiff z w n)
                      (match many (rank-dec all ar rest ks0 v2 x) _
                        ((RankHit e g h r k5 p) (RankHit _ _ _ r k5 (RRThere x y r s k5 k0 rest ks0 n p)))
                        ((RankMiss e g h p) (RankMiss _ _ _ (NoRuleCons x y s rest n p)))))))))))))))

(def-fns _ $ (erased rule-rank-of : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (Nat) x) (erased (Term) r) (erased (Nat) k) (subterm erased (RuleRank rules ranks x r k) p) -> (erased (RuleOf rules x r) q))
  (match erased p _
    ((RRHere a b c rest ks) (RuleHere x r rest))
    ((RRThere a y b s c k2 rest ks n p2) (RuleThere x y r s rest n (rule-rank-of rest ks x r k p2)))))

(def-fns _ $ (erased rule-rank-unique : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (Nat) x) (erased (Term) r) (erased (Nat) k) (erased (Term) r2) (erased (Nat) k2)
    (subterm erased (RuleRank rules ranks x r k) p) (erased (RuleRank rules ranks x r2 k2) q) -> (erased (SameRank r k r2 k2) s))
  (match erased p _
    ((RRHere a b c rest ks)
      (match erased q _
        ((RRHere a2 b2 c2 rest2 ks2) (SameRankRefl r k))
        ((RRThere a2 y b2 s c2 k3 rest2 ks2 n q2) (match erased (neq-irrefl x n) _))))
    ((RRThere a y b s c k3 rest ks n p2)
      (match erased q _
        ((RRHere a2 b2 c2 rest2 ks2) (match erased (neq-irrefl x n) _))
        ((RRThere a2 y2 b2 s2 c2 k4 rest2 ks2 n2 q2) (rule-rank-unique rest ks x r k r2 k2 p2 q2))))))

(def-fns _ $ (erased rule-of-no-rule : (erased (List (Rule)) rules) (erased (Nat) x) (erased (Term) r) (subterm erased (RuleOf rules x r) p) (erased (NoRule rules x) q) -> (erased (False) f))
  (match erased p _
    ((RuleHere y s rest) (match erased q _ ((NoRuleCons a b c d n e) (neq-irrefl x n))))
    ((RuleThere a y s t rest n p2) (match erased q _ ((NoRuleCons a2 b2 c2 d2 n2 q2) (rule-of-no-rule rest x r p2 q2))))))

(def-fns _ $ (erased valid-below : (erased (List (Rule)) all) (erased (List (Nat)) ar) (erased (List (Rule)) rs) (erased (List (Nat)) ks) (erased (Nat) x) (erased (Term) r) (erased (Nat) k)
    (erased (ValidFrom all ar rs ks) v) (subterm erased (RuleRank rs ks x r k) p) -> (erased (Below all ar r k) b))
  (match erased p _
    ((RRHere a b c rest ks2) (match erased v _ ((VFCons d e x2 r2 k2 rs2 ks3 bl v2) bl)))
    ((RRThere a y b s c k2 rest ks2 n p2) (match erased v _ ((VFCons d e y2 s2 k3 rs2 ks3 bl v2) (valid-below all ar rest ks2 x r k v2 p2))))))

; Under a bound above every rank, every term is below it.
(def-fns _ $ (erased rank-lt : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (Nat) x) (erased (Term) r) (erased (Nat) k) (erased (Nat) m) (subterm erased (RuleRank rules ranks x r k) p) (erased (AllLt ranks m) a) ->
    (erased (Lt k m) lt))
  (match erased p _
    ((RRHere b c d rest ks) (match erased a _ ((ALCons e g h lt q) lt)))
    ((RRThere b y c s d k2 rest ks n p2) (match erased a _ ((ALCons e g h lt q) (rank-lt rest ks x r k m p2 q))))))

(def-fns _
  ((erased below-all : (erased (List (Rule)) all) (erased (List (Nat)) ar) (erased (Nat) m) (erased (ValidFrom all ar all ar) v) (erased (AllLt ar m) a) (subterm erased (Term) t) -> (erased (Below all ar t m) b))
    (match erased t _
      ((Ref x)
        (match erased (rank-dec all ar all ar v x) _
          ((RankMiss c d e p) (BlFree all ar x m p))
          ((RankHit c d e r k p) (BlRuled all ar x m r k p (rank-lt all ar x r k m p a)))))
      ((Bound i) (BlBound all ar i m))
      ((TyApp h ps as) (BlTyApp all ar h ps as m (below-all all ar m v a h) (below-all-list all ar m v a as)))
      ((ValApp h ps r as) (BlValApp all ar h ps r as m (below-all all ar m v a h) (below-all-list all ar m v a as)))
      ((TUniv) (BlUniv all ar m))
      ((TFn l ps rs) (BlFn all ar l ps rs m (below-all all ar m v a l) (below-all-tele all ar m v a ps) (below-all-tele all ar m v a rs)))
      ((TTyCtor ps) (BlTyCtor all ar ps m (below-all-tele all ar m v a ps)))
      ((TValCtor ps r) (BlValCtor all ar ps r m (below-all-tele all ar m v a ps) (below-all all ar m v a r)))))
  ((erased below-all-list : (erased (List (Rule)) all) (erased (List (Nat)) ar) (erased (Nat) m) (erased (ValidFrom all ar all ar) v) (erased (AllLt ar m) a) (subterm erased (List (Term)) ts) -> (erased (BelowList all ar ts m) b))
    (match erased ts _
      ((Nil c) (BlNil all ar m))
      ((Cons c t rest) (BlCons all ar t rest m (below-all all ar m v a t) (below-all-list all ar m v a rest)))))
  ((erased below-all-tele : (erased (List (Rule)) all) (erased (List (Nat)) ar) (erased (Nat) m) (erased (ValidFrom all ar all ar) v) (erased (AllLt ar m) a) (subterm erased (List (Entry)) es) -> (erased (BelowTele all ar es m) b))
    (match erased es _
      ((Nil c) (BlTNil all ar m))
      ((Cons c e rest) (match erased e _ ((MkEntry s i t) (BlTCons all ar s i t rest m (below-all all ar m v a t) (below-all-tele all ar m v a rest))))))))

; ---- The functions: canonicalization recurses on the bound and then the term.
(def-fns _
  ((many canon : (many (List (Rule)) rules) (many (List (Nat)) ranks) (erased (ValidFrom rules ranks rules ranks) v) (subterm erased (Nat) n) (subterm many (Term) t) (erased (Below rules ranks t n) b) ->
      (many (Term) u) (erased (Canon rules t u) p))
    (match many t _
      ((Ref x)
        (match many (rank-dec rules ranks rules ranks v x) _
          ((RankMiss a c d p) (values (Ref x) (CanFree rules x p)))
          ((RankHit a c d r k p)
            (match erased b _
              (absurd (BlFree a2 c2 d2 e2 nr) (rule-of-no-rule rules x r (rule-rank-of rules ranks x r k p) nr))
              ((BlRuled a2 c2 d2 e2 r2 j p2 lt)
                (match erased (rule-rank-unique rules ranks x r k r2 j p p2) _
                  ((SameRankRefl g h)
                    (let ((many u) (erased q)) (canon rules ranks v (subterm (lt-subterm k n lt)) k r (valid-below rules ranks rules ranks x r k v p)))
                    (values u (CanRule rules x r u (rule-rank-of rules ranks x r k p) q)))))))))
      ((Bound k) (values (Bound k) (CanBound rules k)))
      ((TyApp h ps as)
        (match erased b _
          ((BlTyApp a c d e g k bh bas)
            (let ((many h2) (erased p)) (canon rules ranks v n h bh))
            (let ((many as2) (erased q)) (canon-list rules ranks v n as bas))
            (values (TyApp h2 ps as2) (CanTyApp rules h h2 ps as as2 p q)))))
      ((ValApp h ps r as)
        (match erased b _
          ((BlValApp a c d e g k j bh bas)
            (let ((many h2) (erased p)) (canon rules ranks v n h bh))
            (let ((many as2) (erased q)) (canon-list rules ranks v n as bas))
            (values (ValApp h2 ps r as2) (CanValApp rules h h2 ps r as as2 p q)))))
      ((TUniv) (values (TUniv) (CanUniv rules)))
      ((TFn l ps rs)
        (match erased b _
          ((BlFn a c d e g h bl bps brs)
            (let ((many l2) (erased p)) (canon rules ranks v n l bl))
            (let ((many ps2) (erased q)) (canon-tele rules ranks v n ps bps))
            (let ((many rs2) (erased r)) (canon-tele rules ranks v n rs brs))
            (values (TFn l2 ps2 rs2) (CanFn rules l l2 ps ps2 rs rs2 p q r)))))
      ((TTyCtor ps)
        (match erased b _
          ((BlTyCtor a c d e bps)
            (let ((many ps2) (erased q)) (canon-tele rules ranks v n ps bps))
            (values (TTyCtor ps2) (CanTyCtor rules ps ps2 q)))))
      ((TValCtor ps r)
        (match erased b _
          ((BlValCtor a c d e g bps br)
            (let ((many ps2) (erased q)) (canon-tele rules ranks v n ps bps))
            (let ((many r2) (erased p)) (canon rules ranks v n r br))
            (values (TValCtor ps2 r2) (CanValCtor rules ps ps2 r r2 q p)))))))
  ((many canon-list : (many (List (Rule)) rules) (many (List (Nat)) ranks) (erased (ValidFrom rules ranks rules ranks) v) (subterm erased (Nat) n) (subterm many (List (Term)) ts) (erased (BelowList rules ranks ts n) b) ->
      (many (List (Term)) us) (erased (CanonList rules ts us) p))
    (match many ts _
      ((Nil a) (values (Nil _) (CanNil rules)))
      ((Cons a t rest)
        (match erased b _
          ((BlCons c d e g h bt brest)
            (let ((many u) (erased p)) (canon rules ranks v n t bt))
            (let ((many us) (erased q)) (canon-list rules ranks v n rest brest))
            (values (Cons _ u us) (CanCons rules t u rest us p q)))))))
  ((many canon-tele : (many (List (Rule)) rules) (many (List (Nat)) ranks) (erased (ValidFrom rules ranks rules ranks) v) (subterm erased (Nat) n) (subterm many (List (Entry)) es) (erased (BelowTele rules ranks es n) b) ->
      (many (List (Entry)) fs) (erased (CanonTele rules es fs) p))
    (match many es _
      ((Nil a) (values (Nil _) (CanTNil rules)))
      ((Cons a e rest)
        (match many e _
          ((MkEntry s i t)
            (match erased b _
              ((BlTCons c d s2 i2 t2 es2 g bt brest)
                (let ((many u) (erased p)) (canon rules ranks v n t bt))
                (let ((many fs) (erased q)) (canon-tele rules ranks v n rest brest))
                (values (Cons _ (MkEntry s i u) fs) (CanTCons rules s i t u rest fs p q))))))))))

; ---- What canonicalization gives: a term whose entries with rules are all gone ([Canonical]), and a bound
; kept when the rules' terms keep it.
(def-adts
  ((Canonical : ((List (Rule)) rules) ((Term) t) -> Type)
    enum
    (many CnRef : (erased (List (Rule)) rules) (erased (Nat) x) (erased (NoRule rules x) p) -> (Canonical rules (Ref x)))
    (many CnBound : (erased (List (Rule)) rules) (erased (Nat) k) -> (Canonical rules (Bound k)))
    (many CnTyApp : (erased (List (Rule)) rules) (erased (Term) h) (erased (List (Entry)) ps) (erased (List (Term)) as) (erased (Canonical rules h) p) (erased (CanonicalList rules as) q) -> (Canonical rules (TyApp h ps as)))
    (many CnValApp : (erased (List (Rule)) rules) (erased (Term) h) (erased (List (Entry)) ps) (erased (Term) r) (erased (List (Term)) as) (erased (Canonical rules h) p) (erased (CanonicalList rules as) q)
       -> (Canonical rules (ValApp h ps r as)))
    (many CnUniv : (erased (List (Rule)) rules) -> (Canonical rules (TUniv)))
    (many CnFn : (erased (List (Rule)) rules) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs) (erased (Canonical rules l) p) (erased (CanonicalTele rules ps) q) (erased (CanonicalTele rules rs) r)
       -> (Canonical rules (TFn l ps rs)))
    (many CnTyCtor : (erased (List (Rule)) rules) (erased (List (Entry)) ps) (erased (CanonicalTele rules ps) q) -> (Canonical rules (TTyCtor ps)))
    (many CnValCtor : (erased (List (Rule)) rules) (erased (List (Entry)) ps) (erased (Term) r) (erased (CanonicalTele rules ps) q) (erased (Canonical rules r) p) -> (Canonical rules (TValCtor ps r))))
  ((CanonicalList : ((List (Rule)) rules) ((List (Term)) ts) -> Type)
    enum
    (many CnNil : (erased (List (Rule)) rules) -> (CanonicalList rules (Nil (Term))))
    (many CnCons : (erased (List (Rule)) rules) (erased (Term) t) (erased (List (Term)) ts) (erased (Canonical rules t) p) (erased (CanonicalList rules ts) q) -> (CanonicalList rules (Cons (Term) t ts))))
  ((CanonicalTele : ((List (Rule)) rules) ((List (Entry)) es) -> Type)
    enum
    (many CnTNil : (erased (List (Rule)) rules) -> (CanonicalTele rules (Nil (Entry))))
    (many CnTCons : (erased (List (Rule)) rules) (erased (Bool) s) (erased (Bool) i) (erased (Term) t) (erased (List (Entry)) es) (erased (Canonical rules t) p) (erased (CanonicalTele rules es) q)
       -> (CanonicalTele rules (Cons (Entry) (MkEntry s i t) es)))))

(def-fns _
  ((erased canon-canonical : (erased (List (Rule)) rules) (erased (Term) t) (erased (Term) u) (subterm erased (Canon rules t u) d) -> (erased (Canonical rules u) c))
    (match erased d _
      ((CanRule a x r u2 p q) (canon-canonical rules r u q))
      ((CanFree a x p) (CnRef rules x p))
      ((CanBound a k) (CnBound rules k))
      ((CanTyApp a h h2 ps as as2 p q) (CnTyApp rules h2 ps as2 (canon-canonical rules h h2 p) (canon-canonical-list rules as as2 q)))
      ((CanValApp a h h2 ps r as as2 p q) (CnValApp rules h2 ps r as2 (canon-canonical rules h h2 p) (canon-canonical-list rules as as2 q)))
      ((CanUniv a) (CnUniv rules))
      ((CanFn a l l2 ps ps2 rs rs2 p q r) (CnFn rules l2 ps2 rs2 (canon-canonical rules l l2 p) (canon-canonical-tele rules ps ps2 q) (canon-canonical-tele rules rs rs2 r)))
      ((CanTyCtor a ps ps2 q) (CnTyCtor rules ps2 (canon-canonical-tele rules ps ps2 q)))
      ((CanValCtor a ps ps2 r r2 q p) (CnValCtor rules ps2 r2 (canon-canonical-tele rules ps ps2 q) (canon-canonical rules r r2 p)))))
  ((erased canon-canonical-list : (erased (List (Rule)) rules) (erased (List (Term)) ts) (erased (List (Term)) us) (subterm erased (CanonList rules ts us) d) -> (erased (CanonicalList rules us) c))
    (match erased d _
      ((CanNil a) (CnNil rules))
      ((CanCons a t u ts2 us2 p q) (CnCons rules u us2 (canon-canonical rules t u p) (canon-canonical-list rules ts2 us2 q)))))
  ((erased canon-canonical-tele : (erased (List (Rule)) rules) (erased (List (Entry)) es) (erased (List (Entry)) fs) (subterm erased (CanonTele rules es fs) d) -> (erased (CanonicalTele rules fs) c))
    (match erased d _
      ((CanTNil a) (CnTNil rules))
      ((CanTCons a s i t u es2 fs2 p q) (CnTCons rules s i u fs2 (canon-canonical rules t u p) (canon-canonical-tele rules es2 fs2 q))))))

(def-fns _
  ((erased canonical-fix : (erased (List (Rule)) rules) (erased (Term) t) (subterm erased (Canonical rules t) c) -> (erased (Canon rules t t) d))
    (match erased c _
      ((CnRef a x p) (CanFree rules x p))
      ((CnBound a k) (CanBound rules k))
      ((CnTyApp a h ps as p q) (CanTyApp rules h h ps as as (canonical-fix rules h p) (canonical-fix-list rules as q)))
      ((CnValApp a h ps r as p q) (CanValApp rules h h ps r as as (canonical-fix rules h p) (canonical-fix-list rules as q)))
      ((CnUniv a) (CanUniv rules))
      ((CnFn a l ps rs p q r) (CanFn rules l l ps ps rs rs (canonical-fix rules l p) (canonical-fix-tele rules ps q) (canonical-fix-tele rules rs r)))
      ((CnTyCtor a ps q) (CanTyCtor rules ps ps (canonical-fix-tele rules ps q)))
      ((CnValCtor a ps r q p) (CanValCtor rules ps ps r r (canonical-fix-tele rules ps q) (canonical-fix rules r p)))))
  ((erased canonical-fix-list : (erased (List (Rule)) rules) (erased (List (Term)) ts) (subterm erased (CanonicalList rules ts) c) -> (erased (CanonList rules ts ts) d))
    (match erased c _
      ((CnNil a) (CanNil rules))
      ((CnCons a t ts2 p q) (CanCons rules t t ts2 ts2 (canonical-fix rules t p) (canonical-fix-list rules ts2 q)))))
  ((erased canonical-fix-tele : (erased (List (Rule)) rules) (erased (List (Entry)) es) (subterm erased (CanonicalTele rules es) c) -> (erased (CanonTele rules es es) d))
    (match erased c _
      ((CnTNil a) (CanTNil rules))
      ((CnTCons a s i t es2 p q) (CanTCons rules s i t t es2 es2 (canonical-fix rules t p) (canonical-fix-tele rules es2 q))))))

(MkUnit)
