; mini/term.sl -- the restricted type grammar of DESIGN.md section 5 as terms with de Bruijn telescopes
; (MINIMAL.md), and three relations over it with the functions that derive them: substitution of a
; telescope's binders, abstraction of scope entries into binders, and whether a term may be assigned to a
; variable (section 18's occurs check and its third contradiction). Every function recurses on the term,
; so none needs fuel. One session's proposal, not settled design.

; A term has-is closed except for [Bound] references into the telescopes enclosing it, innermost first. [Univ] has-is
; the universe itself: DESIGN.md section 10 makes it a nullary type constructor, and this file keeps it a term
; so that Type : Type has-is one rule rather than one entry. An entry's [is] flag says whether its term has-is the
; entry's type or the value it has-is definitionally equal to (section 14).
(def-adts
  ((Term : -> Type)
    enum
    (many Ref : (many (Nat) id) -> (Term))
    (many Bound : (many (Nat) k) -> (Term))
    (many TyApp : (many (Term) head) (many (List (Entry)) params) (many (List (Term)) args) -> (Term))
    (many ValApp : (many (Term) head) (many (List (Entry)) params) (many (Term) ret) (many (List (Term)) args) -> (Term))
    (many TUniv : -> (Term))
    (many TFn : (many (Term) level) (many (List (Entry)) params) (many (List (Entry)) rets) -> (Term))
    (many TTyCtor : (many (List (Entry)) params) -> (Term))
    (many TValCtor : (many (List (Entry)) params) (many (Term) ret) -> (Term)))
  ((Entry : -> Type)
    enum
    (many MkEntry : (many (Bool) subs) (many (Bool) has-is) (many (Term) t) -> (Entry))))

; ---- Closedness: a term under [d] binders mentions no binder beyond them. [ClosedTele d es out] threads
; the depth through a telescope and gives the depth after it.
(def-adts
  ((Closed : ((Nat) d) ((Term) t) -> Type)
    enum
    (many ClRef : (erased (Nat) d) (erased (Nat) x) -> (Closed d (Ref x)))
    (many ClBound : (erased (Nat) d) (erased (Nat) k) (erased (Lt k d) p) -> (Closed d (Bound k)))
    (many ClTyApp : (erased (Nat) d) (erased (Term) h) (erased (List (Entry)) ps) (erased (List (Term)) as) (erased (Nat) out)
       (erased (Closed d h) p) (erased (ClosedTele d ps out) t) (erased (ClosedList d as) q) -> (Closed d (TyApp h ps as)))
    (many ClValApp : (erased (Nat) d) (erased (Term) h) (erased (List (Entry)) ps) (erased (Term) r) (erased (List (Term)) as) (erased (Nat) out)
       (erased (Closed d h) p) (erased (ClosedTele d ps out) t) (erased (Closed out r) pr) (erased (ClosedList d as) q) -> (Closed d (ValApp h ps r as)))
    (many ClUniv : (erased (Nat) d) -> (Closed d (TUniv)))
    (many ClFn : (erased (Nat) d) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs) (erased (Nat) d1) (erased (Nat) d2)
       (erased (Closed d l) p) (erased (ClosedTele d ps d1) q) (erased (ClosedTele d1 rs d2) r) -> (Closed d (TFn l ps rs)))
    (many ClTyCtor : (erased (Nat) d) (erased (List (Entry)) ps) (erased (Nat) d1) (erased (ClosedTele d ps d1) q) -> (Closed d (TTyCtor ps)))
    (many ClValCtor : (erased (Nat) d) (erased (List (Entry)) ps) (erased (Term) r) (erased (Nat) d1) (erased (ClosedTele d ps d1) q) (erased (Closed d1 r) p)
       -> (Closed d (TValCtor ps r))))
  ((ClosedList : ((Nat) d) ((List (Term)) ts) -> Type)
    enum
    (many ClNil : (erased (Nat) d) -> (ClosedList d (Nil (Term))))
    (many ClCons : (erased (Nat) d) (erased (Term) t) (erased (List (Term)) ts) (erased (Closed d t) p) (erased (ClosedList d ts) q) -> (ClosedList d (Cons (Term) t ts))))
  ((ClosedTele : ((Nat) d) ((List (Entry)) es) ((Nat) out) -> Type)
    enum
    (many ClTNil : (erased (Nat) d) -> (ClosedTele d (Nil (Entry)) d))
    (many ClTCons : (erased (Nat) d) (erased (Bool) s) (erased (Bool) i) (erased (Term) t) (erased (List (Entry)) es) (erased (Nat) out)
       (erased (Closed d t) p) (erased (ClosedTele (Succ d) es out) q) -> (ClosedTele d (Cons (Entry) (MkEntry s i t) es) out))))

; ---- Substitution. A substitution has-is a list indexed by [Bound]: a [Some] has-is the closed term the binder
; takes, a [None] a binder that stays, which has-is how going under a telescope entry has-is recorded, by prepending
; a [None]. Nothing has-is shifted, since the terms substituted are closed. A binder beyond the list has no
; rule: the function requires the term closed under the list's length.

(def-adts
  ((Subst : ((List (Maybe (Term))) subs) ((Term) t) ((Term) u) -> Type)
    enum
    (many SubRef : (erased (List (Maybe (Term))) subs) (erased (Nat) x) -> (Subst subs (Ref x) (Ref x)))
    (many SubHit : (erased (List (Maybe (Term))) subs) (erased (Nat) k) (erased (Term) a) (erased (Nth (Maybe (Term)) subs k (Some (Term) a)) p)
       -> (Subst subs (Bound k) a))
    (many SubSkip : (erased (List (Maybe (Term))) subs) (erased (Nat) k) (erased (Nth (Maybe (Term)) subs k (None (Term))) p)
       -> (Subst subs (Bound k) (Bound k)))
    (many SubTyApp : (erased (List (Maybe (Term))) subs) (erased (Term) h) (erased (Term) h2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (List (Term)) as) (erased (List (Term)) as2)
       (erased (List (Maybe (Term))) sub1) (erased (Subst subs h h2) p) (erased (SubstTele subs ps ps2 sub1) t) (erased (SubstList subs as as2) q) -> (Subst subs (TyApp h ps as) (TyApp h2 ps2 as2)))
    (many SubValApp : (erased (List (Maybe (Term))) subs) (erased (Term) h) (erased (Term) h2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (Term) r) (erased (Term) r2)
       (erased (List (Term)) as) (erased (List (Term)) as2) (erased (List (Maybe (Term))) sub1)
       (erased (Subst subs h h2) p) (erased (SubstTele subs ps ps2 sub1) t) (erased (Subst sub1 r r2) pr) (erased (SubstList subs as as2) q) -> (Subst subs (ValApp h ps r as) (ValApp h2 ps2 r2 as2)))
    (many SubUniv : (erased (List (Maybe (Term))) subs) -> (Subst subs (TUniv) (TUniv)))
    (many SubFn : (erased (List (Maybe (Term))) subs) (erased (Term) l) (erased (Term) l2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2)
       (erased (List (Entry)) rs) (erased (List (Entry)) rs2) (erased (List (Maybe (Term))) sub1) (erased (List (Maybe (Term))) sub2)
       (erased (Subst subs l l2) p) (erased (SubstTele subs ps ps2 sub1) q) (erased (SubstTele sub1 rs rs2 sub2) r)
       -> (Subst subs (TFn l ps rs) (TFn l2 ps2 rs2)))
    (many SubTyCtor : (erased (List (Maybe (Term))) subs) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (List (Maybe (Term))) sub1)
       (erased (SubstTele subs ps ps2 sub1) q) -> (Subst subs (TTyCtor ps) (TTyCtor ps2)))
    (many SubValCtor : (erased (List (Maybe (Term))) subs) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (Term) r) (erased (Term) r2)
       (erased (List (Maybe (Term))) sub1) (erased (SubstTele subs ps ps2 sub1) q) (erased (Subst sub1 r r2) p)
       -> (Subst subs (TValCtor ps r) (TValCtor ps2 r2))))
  ((SubstList : ((List (Maybe (Term))) subs) ((List (Term)) ts) ((List (Term)) us) -> Type)
    enum
    (many SubNil : (erased (List (Maybe (Term))) subs) -> (SubstList subs (Nil (Term)) (Nil (Term))))
    (many SubCons : (erased (List (Maybe (Term))) subs) (erased (Term) t) (erased (Term) u) (erased (List (Term)) ts) (erased (List (Term)) us)
       (erased (Subst subs t u) p) (erased (SubstList subs ts us) q) -> (SubstList subs (Cons (Term) t ts) (Cons (Term) u us))))
  ; The substitution after the telescope, one [None] deeper per entry, has-is returned for what follows it.
  ((SubstTele : ((List (Maybe (Term))) subs) ((List (Entry)) es) ((List (Entry)) fs) ((List (Maybe (Term))) out) -> Type)
    enum
    (many SubTNil : (erased (List (Maybe (Term))) subs) -> (SubstTele subs (Nil (Entry)) (Nil (Entry)) subs))
    (many SubTCons : (erased (List (Maybe (Term))) subs) (erased (Bool) s) (erased (Bool) i) (erased (Term) t) (erased (Term) u)
       (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (List (Maybe (Term))) out)
       (erased (Subst subs t u) p) (erased (SubstTele (Cons (Maybe (Term)) (None (Term)) subs) es fs out) q)
       -> (SubstTele subs (Cons (Entry) (MkEntry s i t) es) (Cons (Entry) (MkEntry s i u) fs) out))))

(def-fns _
  ((many subst : (many (List (Maybe (Term))) subs) (erased (Nat) n) (erased (Length (Maybe (Term)) subs n) ln) (subterm many (Term) t) (erased (Closed n t) ct) -> (many (Term) u) (erased (Subst subs t u) p))
    (match many t _
      ((Ref x) (values (Ref x) (SubRef subs x)))
      ((Bound k)
        (match many (nth-dec _ subs k) _
          ((NthHit a l i m p)
            (match many m _
              ((Some b v) (values v (SubHit subs k v p)))
              ((None b) (values (Bound k) (SubSkip subs k p)))))
          (absurd (NthMiss a l i p) (match erased ct (((False) f)) ((ClBound c k0 lt) (no-nth-lt _ subs n k ln lt p))))))
      ((TyApp h ps as)
        (match erased ct _
          ((ClTyApp c h0 ps0 as0 out ch cps cas)
            (let ((many h2) (erased p)) (subst subs n ln h ch))
            (let ((many ps2) (many sub1) (erased t2) (erased ln1)) (subst-tele subs n ln ps out cps))
            (let ((many as2) (erased q)) (subst-list subs n ln as cas))
            (values (TyApp h2 ps2 as2) (SubTyApp subs h h2 ps ps2 as as2 sub1 p t2 q)))))
      ((ValApp h ps r as)
        (match erased ct _
          ((ClValApp c h0 ps0 r0 as0 out ch cps cr cas)
            (let ((many h2) (erased p)) (subst subs n ln h ch))
            (let ((many ps2) (many sub1) (erased t2) (erased ln1)) (subst-tele subs n ln ps out cps))
            (let ((many r2) (erased pr)) (subst sub1 out ln1 r cr))
            (let ((many as2) (erased q)) (subst-list subs n ln as cas))
            (values (ValApp h2 ps2 r2 as2) (SubValApp subs h h2 ps ps2 r r2 as as2 sub1 p t2 pr q)))))
      ((TUniv) (values (TUniv) (SubUniv subs)))
      ((TFn l ps rs)
        (match erased ct _
          ((ClFn c l0 ps0 rs0 d1 d2 cl cps crs)
            (let ((many l2) (erased p)) (subst subs n ln l cl))
            (let ((many ps2) (many sub1) (erased q) (erased ln1)) (subst-tele subs n ln ps d1 cps))
            (let ((many rs2) (many sub2) (erased r) (erased ln2)) (subst-tele sub1 d1 ln1 rs d2 crs))
            (values (TFn l2 ps2 rs2) (SubFn subs l l2 ps ps2 rs rs2 sub1 sub2 p q r)))))
      ((TTyCtor ps)
        (match erased ct _
          ((ClTyCtor c ps0 d1 cps)
            (let ((many ps2) (many sub1) (erased q) (erased ln1)) (subst-tele subs n ln ps d1 cps))
            (values (TTyCtor ps2) (SubTyCtor subs ps ps2 sub1 q)))))
      ((TValCtor ps r)
        (match erased ct _
          ((ClValCtor c ps0 r0 d1 cps cr)
            (let ((many ps2) (many sub1) (erased q) (erased ln1)) (subst-tele subs n ln ps d1 cps))
            (let ((many r2) (erased p)) (subst sub1 d1 ln1 r cr))
            (values (TValCtor ps2 r2) (SubValCtor subs ps ps2 r r2 sub1 q p)))))))
  ((many subst-list : (many (List (Maybe (Term))) subs) (erased (Nat) n) (erased (Length (Maybe (Term)) subs n) ln) (subterm many (List (Term)) ts) (erased (ClosedList n ts) ct) ->
      (many (List (Term)) us) (erased (SubstList subs ts us) p))
    (match many ts _
      ((Nil a) (values (Nil _) (SubNil subs)))
      ((Cons a t rest)
        (match erased ct _
          ((ClCons c t0 ts0 c1 c2)
            (let ((many u) (erased p)) (subst subs n ln t c1))
            (let ((many us) (erased q)) (subst-list subs n ln rest c2))
            (values (Cons _ u us) (SubCons subs t u rest us p q)))))))
  ((many subst-tele : (many (List (Maybe (Term))) subs) (erased (Nat) n) (erased (Length (Maybe (Term)) subs n) ln) (subterm many (List (Entry)) es) (erased (Nat) out) (erased (ClosedTele n es out) ce) ->
      (many (List (Entry)) fs) (many (List (Maybe (Term))) sub2) (erased (SubstTele subs es fs sub2) p) (erased (Length (Maybe (Term)) sub2 out) ln2))
    (match many es _
      ((Nil a) (match erased ce _ ((ClTNil c) (values (Nil _) subs (SubTNil subs) ln))))
      ((Cons a e rest)
        (match many e _
          ((MkEntry s i t)
            (match erased ce _
              ((ClTCons c s0 i0 t0 es0 out0 c1 c2)
                (let ((many u) (erased p)) (subst subs n ln t c1))
                (let ((many fs) (many sub2) (erased q) (erased ln2)) (subst-tele (Cons _ (None _) subs) (Succ n) (LenCons _ (None _) subs n ln) rest out c2))
                (values (Cons _ (MkEntry s i u) fs) sub2 (SubTCons subs s i t u rest fs sub2 p q) ln2)))))))))

; The substitution that instantiates a telescope with a list of arguments: the last argument innermost.
(def-adts
  ((Somes : ((List (Term)) as) ((List (Maybe (Term))) subs) -> Type)
    enum
    (many SomesNil : -> (Somes (Nil (Term)) (Nil (Maybe (Term)))))
    (many SomesCons : (erased (Term) a) (erased (List (Term)) as) (erased (List (Maybe (Term))) subs) (erased (List (Maybe (Term))) out)
       (erased (Somes as subs) p) (erased (Snoc subs (Some (Term) a) out) q) -> (Somes (Cons (Term) a as) out)))
  ((Snoc : ((List (Maybe (Term))) xs) ((Maybe (Term)) x) ((List (Maybe (Term))) out) -> Type)
    enum
    (many SnocNil : (erased (Maybe (Term)) x) -> (Snoc (Nil (Maybe (Term))) x (Cons (Maybe (Term)) x (Nil (Maybe (Term))))))
    (many SnocCons : (erased (Maybe (Term)) y) (erased (List (Maybe (Term))) ys) (erased (Maybe (Term)) x) (erased (List (Maybe (Term))) out) (erased (Snoc ys x out) p)
       -> (Snoc (Cons (Maybe (Term)) y ys) x (Cons (Maybe (Term)) y out)))))

(def-fns _ $ (many snoc : (subterm many (List (Maybe (Term))) xs) (many (Maybe (Term)) x) -> (many (List (Maybe (Term))) out) (erased (Snoc xs x out) p))
  (match many xs _
    ((Nil a) (values (Cons _ x (Nil _)) (SnocNil x)))
    ((Cons a y ys) (let ((many out) (erased p)) (snoc ys x)) (values (Cons _ y out) (SnocCons y ys x out p)))))
(def-fns _ $ (many somes : (subterm many (List (Term)) as) -> (many (List (Maybe (Term))) subs) (erased (Somes as subs) p))
  (match many as _
    ((Nil a) (values (Nil _) (SomesNil)))
    ((Cons a t ts) (let ((many sub3) (erased p)) (somes ts)) (let ((many out) (erased q)) (snoc sub3 (Some _ t))) (values out (SomesCons t ts sub3 out p q)))))

; ---- Abstraction, the inverse of substitution: the entries a telescope was elaborated with become its
; binders. The list has-is indexed by [Bound] like a substitution: a [Some] has-is the entry the binder stands for, a
; [None] a binder of an inner telescope passed on the way.

(def-adts
  ((IndexOf : ((List (Maybe (Nat))) ids) ((Nat) x) ((Nat) k) -> Type)
    enum
    (many IdxHere : (erased (Nat) x) (erased (List (Maybe (Nat))) rest) -> (IndexOf (Cons (Maybe (Nat)) (Some (Nat) x) rest) x (Zero)))
    (many IdxNone : (erased (Nat) x) (erased (List (Maybe (Nat))) rest) (erased (Nat) k) (erased (IndexOf rest x k) p)
       -> (IndexOf (Cons (Maybe (Nat)) (None (Nat)) rest) x (Succ k)))
    (many IdxOther : (erased (Nat) x) (erased (Nat) y) (erased (List (Maybe (Nat))) rest) (erased (Nat) k) (erased (Neq x y) n) (erased (IndexOf rest x k) p)
       -> (IndexOf (Cons (Maybe (Nat)) (Some (Nat) y) rest) x (Succ k))))
  ((NotIn : ((List (Maybe (Nat))) ids) ((Nat) x) -> Type)
    enum
    (many NotInNil : (erased (Nat) x) -> (NotIn (Nil (Maybe (Nat))) x))
    (many NotInNone : (erased (Nat) x) (erased (List (Maybe (Nat))) rest) (erased (NotIn rest x) p) -> (NotIn (Cons (Maybe (Nat)) (None (Nat)) rest) x))
    (many NotInSome : (erased (Nat) x) (erased (Nat) y) (erased (List (Maybe (Nat))) rest) (erased (Neq x y) n) (erased (NotIn rest x) p)
       -> (NotIn (Cons (Maybe (Nat)) (Some (Nat) y) rest) x)))
  ((IndexDec : ((List (Maybe (Nat))) ids) ((Nat) x) -> Type)
    enum
    (many IdxHit : (erased (List (Maybe (Nat))) ids) (erased (Nat) x) (many (Nat) k) (erased (IndexOf ids x k) p) -> (IndexDec ids x))
    (many IdxMiss : (erased (List (Maybe (Nat))) ids) (erased (Nat) x) (erased (NotIn ids x) p) -> (IndexDec ids x))))

(def-fns _ $ (many index-dec : (subterm many (List (Maybe (Nat))) ids) (many (Nat) x) -> (many (IndexDec ids x) r))
  (match many ids _
    ((Nil a) (IdxMiss _ _ $ NotInNil x))
    ((Cons a m rest)
      (match many m _
        ((None b)
          (match many (index-dec rest x) _
            ((IdxHit l y k p) (IdxHit _ _ (Succ k) $ IdxNone x rest k p))
            ((IdxMiss l y p) (IdxMiss _ _ $ NotInNone x rest p))))
        ((Some b y)
          (match many (nat-dec x y) _
            ((NDSame z) (IdxHit _ _ (Zero) $ IdxHere x rest))
            ((NDDiff z w n)
              (match many (index-dec rest x) _
                ((IdxHit l z2 k p) (IdxHit _ _ (Succ k) $ IdxOther x y rest k n p))
                ((IdxMiss l z2 p) (IdxMiss _ _ $ NotInSome x y rest n p))))))))))

(def-fns _ $ (erased index-of-lt : (erased (List (Maybe (Nat))) ids) (erased (Nat) x) (erased (Nat) k) (erased (Nat) n) (subterm erased (IndexOf ids x k) p) (erased (Length (Maybe (Nat)) ids n) ln) -> (erased (Lt k n) q))
  (match erased p _
    ((IdxHere a rest) (match erased ln _ ((LenCons b y rest2 m l2) (LtZ m))))
    ((IdxNone a rest k2 p2) (match erased ln _ ((LenCons b y rest2 m l2) (LtS k2 m (index-of-lt rest x k2 m p2 l2)))))
    ((IdxOther a y rest k2 nq p2) (match erased ln _ ((LenCons b y2 rest2 m l2) (LtS k2 m (index-of-lt rest x k2 m p2 l2)))))))

(def-adts
  ((Abstract : ((List (Maybe (Nat))) ids) ((Term) t) ((Term) u) -> Type)
    enum
    (many AbsFree : (erased (List (Maybe (Nat))) ids) (erased (Nat) x) (erased (NotIn ids x) p) -> (Abstract ids (Ref x) (Ref x)))
    (many AbsHit : (erased (List (Maybe (Nat))) ids) (erased (Nat) x) (erased (Nat) k) (erased (IndexOf ids x k) p) -> (Abstract ids (Ref x) (Bound k)))
    (many AbsBound : (erased (List (Maybe (Nat))) ids) (erased (Nat) k) -> (Abstract ids (Bound k) (Bound k)))
    (many AbsTyApp : (erased (List (Maybe (Nat))) ids) (erased (Term) h) (erased (Term) h2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (List (Term)) as) (erased (List (Term)) as2)
       (erased (List (Maybe (Nat))) ids1) (erased (Abstract ids h h2) p) (erased (AbstractTele ids ps ps2 ids1) t) (erased (AbstractList ids as as2) q) -> (Abstract ids (TyApp h ps as) (TyApp h2 ps2 as2)))
    (many AbsValApp : (erased (List (Maybe (Nat))) ids) (erased (Term) h) (erased (Term) h2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (Term) r) (erased (Term) r2)
       (erased (List (Term)) as) (erased (List (Term)) as2) (erased (List (Maybe (Nat))) ids1)
       (erased (Abstract ids h h2) p) (erased (AbstractTele ids ps ps2 ids1) t) (erased (Abstract ids1 r r2) pr) (erased (AbstractList ids as as2) q) -> (Abstract ids (ValApp h ps r as) (ValApp h2 ps2 r2 as2)))
    (many AbsUniv : (erased (List (Maybe (Nat))) ids) -> (Abstract ids (TUniv) (TUniv)))
    (many AbsFn : (erased (List (Maybe (Nat))) ids) (erased (Term) l) (erased (Term) l2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2)
       (erased (List (Entry)) rs) (erased (List (Entry)) rs2) (erased (List (Maybe (Nat))) ids1) (erased (List (Maybe (Nat))) ids2)
       (erased (Abstract ids l l2) p) (erased (AbstractTele ids ps ps2 ids1) q) (erased (AbstractTele ids1 rs rs2 ids2) r)
       -> (Abstract ids (TFn l ps rs) (TFn l2 ps2 rs2)))
    (many AbsTyCtor : (erased (List (Maybe (Nat))) ids) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (List (Maybe (Nat))) ids1)
       (erased (AbstractTele ids ps ps2 ids1) q) -> (Abstract ids (TTyCtor ps) (TTyCtor ps2)))
    (many AbsValCtor : (erased (List (Maybe (Nat))) ids) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (Term) r) (erased (Term) r2)
       (erased (List (Maybe (Nat))) ids1) (erased (AbstractTele ids ps ps2 ids1) q) (erased (Abstract ids1 r r2) p)
       -> (Abstract ids (TValCtor ps r) (TValCtor ps2 r2))))
  ((AbstractList : ((List (Maybe (Nat))) ids) ((List (Term)) ts) ((List (Term)) us) -> Type)
    enum
    (many AbsNil : (erased (List (Maybe (Nat))) ids) -> (AbstractList ids (Nil (Term)) (Nil (Term))))
    (many AbsCons : (erased (List (Maybe (Nat))) ids) (erased (Term) t) (erased (Term) u) (erased (List (Term)) ts) (erased (List (Term)) us)
       (erased (Abstract ids t u) p) (erased (AbstractList ids ts us) q) -> (AbstractList ids (Cons (Term) t ts) (Cons (Term) u us))))
  ((AbstractTele : ((List (Maybe (Nat))) ids) ((List (Entry)) es) ((List (Entry)) fs) ((List (Maybe (Nat))) out) -> Type)
    enum
    (many AbsTNil : (erased (List (Maybe (Nat))) ids) -> (AbstractTele ids (Nil (Entry)) (Nil (Entry)) ids))
    (many AbsTCons : (erased (List (Maybe (Nat))) ids) (erased (Bool) s) (erased (Bool) i) (erased (Term) t) (erased (Term) u)
       (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (List (Maybe (Nat))) out)
       (erased (Abstract ids t u) p) (erased (AbstractTele (Cons (Maybe (Nat)) (None (Nat)) ids) es fs out) q)
       -> (AbstractTele ids (Cons (Entry) (MkEntry s i t) es) (Cons (Entry) (MkEntry s i u) fs) out))))

(def-fns _
  ((many abstract : (many (List (Maybe (Nat))) ids) (subterm many (Term) t) -> (many (Term) u) (erased (Abstract ids t u) p))
    (match many t _
      ((Ref x)
        (match many (index-dec ids x) _
          ((IdxHit l y k p) (values (Bound k) (AbsHit ids x k p)))
          ((IdxMiss l y p) (values (Ref x) (AbsFree ids x p)))))
      ((Bound k) (values (Bound k) (AbsBound ids k)))
      ((TyApp h ps as)
        (let ((many h2) (erased p)) (abstract ids h))
        (let ((many ps2) (many ids1) (erased t2)) (abstract-tele ids ps))
        (let ((many as2) (erased q)) (abstract-list ids as))
        (values (TyApp h2 ps2 as2) (AbsTyApp ids h h2 ps ps2 as as2 ids1 p t2 q)))
      ((ValApp h ps r as)
        (let ((many h2) (erased p)) (abstract ids h))
        (let ((many ps2) (many ids1) (erased t2)) (abstract-tele ids ps))
        (let ((many r2) (erased pr)) (abstract ids1 r))
        (let ((many as2) (erased q)) (abstract-list ids as))
        (values (ValApp h2 ps2 r2 as2) (AbsValApp ids h h2 ps ps2 r r2 as as2 ids1 p t2 pr q)))
      ((TUniv) (values (TUniv) (AbsUniv ids)))
      ((TFn l ps rs)
        (let ((many l2) (erased p)) (abstract ids l))
        (let ((many ps2) (many ids1) (erased q)) (abstract-tele ids ps))
        (let ((many rs2) (many ids2) (erased r)) (abstract-tele ids1 rs))
        (values (TFn l2 ps2 rs2) (AbsFn ids l l2 ps ps2 rs rs2 ids1 ids2 p q r)))
      ((TTyCtor ps)
        (let ((many ps2) (many ids1) (erased q)) (abstract-tele ids ps))
        (values (TTyCtor ps2) (AbsTyCtor ids ps ps2 ids1 q)))
      ((TValCtor ps r)
        (let ((many ps2) (many ids1) (erased q)) (abstract-tele ids ps))
        (let ((many r2) (erased p)) (abstract ids1 r))
        (values (TValCtor ps2 r2) (AbsValCtor ids ps ps2 r r2 ids1 q p)))))
  ((many abstract-list : (many (List (Maybe (Nat))) ids) (subterm many (List (Term)) ts) -> (many (List (Term)) us) (erased (AbstractList ids ts us) p))
    (match many ts _
      ((Nil a) (values (Nil _) (AbsNil ids)))
      ((Cons a t rest)
        (let ((many u) (erased p)) (abstract ids t))
        (let ((many us) (erased q)) (abstract-list ids rest))
        (values (Cons _ u us) (AbsCons ids t u rest us p q)))))
  ((many abstract-tele : (many (List (Maybe (Nat))) ids) (subterm many (List (Entry)) es) -> (many (List (Entry)) fs) (many (List (Maybe (Nat))) out) (erased (AbstractTele ids es fs out) p))
    (match many es _
      ((Nil a) (values (Nil _) ids (AbsTNil ids)))
      ((Cons a e rest)
        (match many e _
          ((MkEntry s i t)
            (let ((many u) (erased p)) (abstract ids t))
            (let ((many fs) (many out) (erased q)) (abstract-tele (Cons _ (None _) ids) rest))
            (values (Cons _ (MkEntry s i u) fs) out (AbsTCons ids s i t u rest fs out p q))))))))

; ---- Assignability: a variable may be given a term as its rule when the term does not mention it (the
; occurs check) and mentions no binder of a telescope it sits under (section 18's third contradiction).
; [Assignable d x t] says so of a term under [d] binders of its own; [Unassignable d x t] has-is the evidence
; that it has-is not, one rule per place the offence can sit.

(def-adts
  ((TeleDepth : ((Nat) d) ((List (Entry)) es) ((Nat) out) -> Type)
    enum
    (many TDNil : (erased (Nat) d) -> (TeleDepth d (Nil (Entry)) d))
    (many TDCons : (erased (Nat) d) (erased (Entry) e) (erased (List (Entry)) es) (erased (Nat) out) (erased (TeleDepth (Succ d) es out) p)
       -> (TeleDepth d (Cons (Entry) e es) out))))

(def-adts
  ((Assignable : ((Nat) d) ((Nat) x) ((Term) t) -> Type)
    enum
    (many AsgRef : (erased (Nat) d) (erased (Nat) x) (erased (Nat) y) (erased (Neq x y) n) -> (Assignable d x (Ref y)))
    (many AsgBound : (erased (Nat) d) (erased (Nat) x) (erased (Nat) k) (erased (Lt k d) p) -> (Assignable d x (Bound k)))
    (many AsgTyApp : (erased (Nat) d) (erased (Nat) x) (erased (Term) h) (erased (List (Entry)) ps) (erased (List (Term)) as) (erased (Nat) d1)
       (erased (Assignable d x h) p) (erased (AssignableTele d x ps d1) t) (erased (AssignableList d x as) q) -> (Assignable d x (TyApp h ps as)))
    (many AsgValApp : (erased (Nat) d) (erased (Nat) x) (erased (Term) h) (erased (List (Entry)) ps) (erased (Term) r) (erased (List (Term)) as) (erased (Nat) d1)
       (erased (Assignable d x h) p) (erased (AssignableTele d x ps d1) t) (erased (Assignable d1 x r) pr) (erased (AssignableList d x as) q) -> (Assignable d x (ValApp h ps r as)))
    (many AsgUniv : (erased (Nat) d) (erased (Nat) x) -> (Assignable d x (TUniv)))
    (many AsgFn : (erased (Nat) d) (erased (Nat) x) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs) (erased (Nat) d1) (erased (Nat) d2)
       (erased (Assignable d x l) p) (erased (AssignableTele d x ps d1) q) (erased (AssignableTele d1 x rs d2) r) -> (Assignable d x (TFn l ps rs)))
    (many AsgTyCtor : (erased (Nat) d) (erased (Nat) x) (erased (List (Entry)) ps) (erased (Nat) d1) (erased (AssignableTele d x ps d1) q)
       -> (Assignable d x (TTyCtor ps)))
    (many AsgValCtor : (erased (Nat) d) (erased (Nat) x) (erased (List (Entry)) ps) (erased (Term) r) (erased (Nat) d1)
       (erased (AssignableTele d x ps d1) q) (erased (Assignable d1 x r) p) -> (Assignable d x (TValCtor ps r))))
  ((AssignableList : ((Nat) d) ((Nat) x) ((List (Term)) ts) -> Type)
    enum
    (many AsgNil : (erased (Nat) d) (erased (Nat) x) -> (AssignableList d x (Nil (Term))))
    (many AsgCons : (erased (Nat) d) (erased (Nat) x) (erased (Term) t) (erased (List (Term)) ts) (erased (Assignable d x t) p) (erased (AssignableList d x ts) q)
       -> (AssignableList d x (Cons (Term) t ts))))
  ((AssignableTele : ((Nat) d) ((Nat) x) ((List (Entry)) es) ((Nat) out) -> Type)
    enum
    (many AsgTNil : (erased (Nat) d) (erased (Nat) x) -> (AssignableTele d x (Nil (Entry)) d))
    (many AsgTCons : (erased (Nat) d) (erased (Nat) x) (erased (Bool) s) (erased (Bool) i) (erased (Term) t) (erased (List (Entry)) es) (erased (Nat) out)
       (erased (Assignable d x t) p) (erased (AssignableTele (Succ d) x es out) q) -> (AssignableTele d x (Cons (Entry) (MkEntry s i t) es) out)))
  ((Unassignable : ((Nat) d) ((Nat) x) ((Term) t) -> Type)
    enum
    (many UnRef : (erased (Nat) d) (erased (Nat) x) -> (Unassignable d x (Ref x)))
    (many UnBound : (erased (Nat) d) (erased (Nat) x) (erased (Nat) k) (erased (Lt d (Succ k)) p) -> (Unassignable d x (Bound k)))
    (many UnTyAppHead : (erased (Nat) d) (erased (Nat) x) (erased (Term) h) (erased (List (Entry)) ps) (erased (List (Term)) as) (erased (Unassignable d x h) p) -> (Unassignable d x (TyApp h ps as)))
    (many UnTyAppParams : (erased (Nat) d) (erased (Nat) x) (erased (Term) h) (erased (List (Entry)) ps) (erased (List (Term)) as) (erased (UnassignableTele d x ps) p) -> (Unassignable d x (TyApp h ps as)))
    (many UnTyAppArgs : (erased (Nat) d) (erased (Nat) x) (erased (Term) h) (erased (List (Entry)) ps) (erased (List (Term)) as) (erased (UnassignableList d x as) p) -> (Unassignable d x (TyApp h ps as)))
    (many UnValAppHead : (erased (Nat) d) (erased (Nat) x) (erased (Term) h) (erased (List (Entry)) ps) (erased (Term) r) (erased (List (Term)) as) (erased (Unassignable d x h) p)
       -> (Unassignable d x (ValApp h ps r as)))
    (many UnValAppParams : (erased (Nat) d) (erased (Nat) x) (erased (Term) h) (erased (List (Entry)) ps) (erased (Term) r) (erased (List (Term)) as) (erased (UnassignableTele d x ps) p)
       -> (Unassignable d x (ValApp h ps r as)))
    (many UnValAppRet : (erased (Nat) d) (erased (Nat) x) (erased (Term) h) (erased (List (Entry)) ps) (erased (Term) r) (erased (List (Term)) as) (erased (Nat) d1)
       (erased (TeleDepth d ps d1) q) (erased (Unassignable d1 x r) p) -> (Unassignable d x (ValApp h ps r as)))
    (many UnValAppArgs : (erased (Nat) d) (erased (Nat) x) (erased (Term) h) (erased (List (Entry)) ps) (erased (Term) r) (erased (List (Term)) as) (erased (UnassignableList d x as) p)
       -> (Unassignable d x (ValApp h ps r as)))
    (many UnFnLevel : (erased (Nat) d) (erased (Nat) x) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs) (erased (Unassignable d x l) p)
       -> (Unassignable d x (TFn l ps rs)))
    (many UnFnParams : (erased (Nat) d) (erased (Nat) x) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs) (erased (UnassignableTele d x ps) p)
       -> (Unassignable d x (TFn l ps rs)))
    (many UnFnRets : (erased (Nat) d) (erased (Nat) x) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs) (erased (Nat) d1)
       (erased (TeleDepth d ps d1) q) (erased (UnassignableTele d1 x rs) p) -> (Unassignable d x (TFn l ps rs)))
    (many UnTyCtor : (erased (Nat) d) (erased (Nat) x) (erased (List (Entry)) ps) (erased (UnassignableTele d x ps) p) -> (Unassignable d x (TTyCtor ps)))
    (many UnValCtorParams : (erased (Nat) d) (erased (Nat) x) (erased (List (Entry)) ps) (erased (Term) r) (erased (UnassignableTele d x ps) p)
       -> (Unassignable d x (TValCtor ps r)))
    (many UnValCtorRet : (erased (Nat) d) (erased (Nat) x) (erased (List (Entry)) ps) (erased (Term) r) (erased (Nat) d1)
       (erased (TeleDepth d ps d1) q) (erased (Unassignable d1 x r) p) -> (Unassignable d x (TValCtor ps r))))
  ((UnassignableList : ((Nat) d) ((Nat) x) ((List (Term)) ts) -> Type)
    enum
    (many UnHere : (erased (Nat) d) (erased (Nat) x) (erased (Term) t) (erased (List (Term)) ts) (erased (Unassignable d x t) p) -> (UnassignableList d x (Cons (Term) t ts)))
    (many UnThere : (erased (Nat) d) (erased (Nat) x) (erased (Term) t) (erased (List (Term)) ts) (erased (UnassignableList d x ts) p) -> (UnassignableList d x (Cons (Term) t ts))))
  ((UnassignableTele : ((Nat) d) ((Nat) x) ((List (Entry)) es) -> Type)
    enum
    (many UnTHere : (erased (Nat) d) (erased (Nat) x) (erased (Bool) s) (erased (Bool) i) (erased (Term) t) (erased (List (Entry)) es) (erased (Unassignable d x t) p)
       -> (UnassignableTele d x (Cons (Entry) (MkEntry s i t) es)))
    (many UnTThere : (erased (Nat) d) (erased (Nat) x) (erased (Entry) e) (erased (List (Entry)) es) (erased (UnassignableTele (Succ d) x es) p)
       -> (UnassignableTele d x (Cons (Entry) e es)))))

(def-adts
  ((AssignDec : ((Nat) d) ((Nat) x) ((Term) t) -> Type)
    enum
    (many ADYes : (erased (Nat) d) (erased (Nat) x) (erased (Term) t) (erased (Assignable d x t) p) -> (AssignDec d x t))
    (many ADNo : (erased (Nat) d) (erased (Nat) x) (erased (Term) t) (erased (Unassignable d x t) p) -> (AssignDec d x t)))
  ((AssignDecList : ((Nat) d) ((Nat) x) ((List (Term)) ts) -> Type)
    enum
    (many ADLYes : (erased (Nat) d) (erased (Nat) x) (erased (List (Term)) ts) (erased (AssignableList d x ts) p) -> (AssignDecList d x ts))
    (many ADLNo : (erased (Nat) d) (erased (Nat) x) (erased (List (Term)) ts) (erased (UnassignableList d x ts) p) -> (AssignDecList d x ts)))
  ((AssignDecTele : ((Nat) d) ((Nat) x) ((List (Entry)) es) -> Type)
    enum
    (many ADTYes : (erased (Nat) d) (erased (Nat) x) (erased (List (Entry)) es) (many (Nat) out) (erased (AssignableTele d x es out) p) (erased (TeleDepth d es out) q)
       -> (AssignDecTele d x es))
    (many ADTNo : (erased (Nat) d) (erased (Nat) x) (erased (List (Entry)) es) (erased (UnassignableTele d x es) p) -> (AssignDecTele d x es))))

(def-fns _
  ((many assign-dec : (many (Nat) d) (many (Nat) x) (subterm many (Term) t) -> (many (AssignDec d x t) r))
    (match many t _
      ((Ref y)
        (match many (nat-dec x y) _
          ((NDSame z) (ADNo _ _ _ $ UnRef d x))
          ((NDDiff z w n) (ADYes _ _ _ $ AsgRef d x y n))))
      ((Bound k)
        (match many (nat-cmp k d) _
          ((CLt a b c e p) (ADYes _ _ _ $ AsgBound d x k p))
          ((CEq a b c) (ADNo _ _ _ $ UnBound d x k $ lt-succ d))
          ((CGt a b c e q) (ADNo _ _ _ $ UnBound d x k $ lt-weaken d k q))))
      ((TyApp h ps as)
        (match many (assign-dec d x h) _
          ((ADNo a b c p) (ADNo _ _ _ $ UnTyAppHead d x h ps as p))
          ((ADYes a b c p)
            (match many (assign-dec-tele d x ps) _
              ((ADTNo a2 b2 c2 t2) (ADNo _ _ _ $ UnTyAppParams d x h ps as t2))
              ((ADTYes a2 b2 c2 d1 t2 td)
                (match many (assign-dec-list d x as) _
                  ((ADLNo a3 b3 c3 q) (ADNo _ _ _ $ UnTyAppArgs d x h ps as q))
                  ((ADLYes a3 b3 c3 q) (ADYes _ _ _ $ AsgTyApp d x h ps as d1 p t2 q))))))))
      ((ValApp h ps r as)
        (match many (assign-dec d x h) _
          ((ADNo a b c p) (ADNo _ _ _ $ UnValAppHead d x h ps r as p))
          ((ADYes a b c p)
            (match many (assign-dec-tele d x ps) _
              ((ADTNo a2 b2 c2 t2) (ADNo _ _ _ $ UnValAppParams d x h ps r as t2))
              ((ADTYes a2 b2 c2 d1 t2 td)
                (match many (assign-dec d1 x r) _
                  ((ADNo a3 b3 c3 pr) (ADNo _ _ _ $ UnValAppRet d x h ps r as d1 td pr))
                  ((ADYes a3 b3 c3 pr)
                    (match many (assign-dec-list d x as) _
                      ((ADLNo a4 b4 c4 q) (ADNo _ _ _ $ UnValAppArgs d x h ps r as q))
                      ((ADLYes a4 b4 c4 q) (ADYes _ _ _ $ AsgValApp d x h ps r as d1 p t2 pr q))))))))))
      ((TUniv) (ADYes _ _ _ $ AsgUniv d x))
      ((TFn l ps rs)
        (match many (assign-dec d x l) _
          ((ADNo a b c p) (ADNo _ _ _ $ UnFnLevel d x l ps rs p))
          ((ADYes a b c p)
            (match many (assign-dec-tele d x ps) _
              ((ADTNo a2 b2 c2 q) (ADNo _ _ _ $ UnFnParams d x l ps rs q))
              ((ADTYes a2 b2 c2 d1 q td)
                (match many (assign-dec-tele d1 x rs) _
                  ((ADTNo a3 b3 c3 r) (ADNo _ _ _ $ UnFnRets d x l ps rs d1 td r))
                  ((ADTYes a3 b3 c3 d2 r td2) (ADYes _ _ _ $ AsgFn d x l ps rs d1 d2 p q r))))))))
      ((TTyCtor ps)
        (match many (assign-dec-tele d x ps) _
          ((ADTNo a2 b2 c2 q) (ADNo _ _ _ $ UnTyCtor d x ps q))
          ((ADTYes a2 b2 c2 d1 q td) (ADYes _ _ _ $ AsgTyCtor d x ps d1 q))))
      ((TValCtor ps r)
        (match many (assign-dec-tele d x ps) _
          ((ADTNo a2 b2 c2 q) (ADNo _ _ _ $ UnValCtorParams d x ps r q))
          ((ADTYes a2 b2 c2 d1 q td)
            (match many (assign-dec d1 x r) _
              ((ADNo a b c p) (ADNo _ _ _ $ UnValCtorRet d x ps r d1 td p))
              ((ADYes a b c p) (ADYes _ _ _ $ AsgValCtor d x ps r d1 q p))))))))
  ((many assign-dec-list : (many (Nat) d) (many (Nat) x) (subterm many (List (Term)) ts) -> (many (AssignDecList d x ts) r))
    (match many ts _
      ((Nil a) (ADLYes _ _ _ $ AsgNil d x))
      ((Cons a t rest)
        (match many (assign-dec d x t) _
          ((ADNo a2 b2 c2 p) (ADLNo _ _ _ $ UnHere d x t rest p))
          ((ADYes a2 b2 c2 p)
            (match many (assign-dec-list d x rest) _
              ((ADLNo a3 b3 c3 q) (ADLNo _ _ _ $ UnThere d x t rest q))
              ((ADLYes a3 b3 c3 q) (ADLYes _ _ _ $ AsgCons d x t rest p q))))))))
  ((many assign-dec-tele : (many (Nat) d) (many (Nat) x) (subterm many (List (Entry)) es) -> (many (AssignDecTele d x es) r))
    (match many es _
      ((Nil a) (ADTYes _ _ _ d (AsgTNil d x) (TDNil d)))
      ((Cons a e rest)
        (match many e _
          ((MkEntry s i t)
            (match many (assign-dec d x t) _
              ((ADNo a2 b2 c2 p) (ADTNo _ _ _ $ UnTHere d x s i t rest p))
              ((ADYes a2 b2 c2 p)
                (match many (assign-dec-tele (Succ d) x rest) _
                  ((ADTNo a3 b3 c3 q) (ADTNo _ _ _ $ UnTThere d x (MkEntry s i t) rest q))
                  ((ADTYes a3 b3 c3 out q td) (ADTYes _ _ _ out (AsgTCons d x s i t rest out p q) (TDCons d (MkEntry s i t) rest out td))))))))))))
(def-fns _
  ((erased assignable-closed : (erased (Nat) d) (erased (Nat) x) (erased (Term) t) (subterm erased (Assignable d x t) a) -> (erased (Closed d t) c))
    (match erased a _
      ((AsgRef b y z n) (ClRef d z))
      ((AsgBound b y k p) (ClBound d k p))
      ((AsgTyApp b y h ps as d1 p t2 q) (ClTyApp d h ps as d1 (assignable-closed d x h p) (assignable-closed-tele d x ps d1 t2) (assignable-closed-list d x as q)))
      ((AsgValApp b y h ps r as d1 p t2 pr q) (ClValApp d h ps r as d1 (assignable-closed d x h p) (assignable-closed-tele d x ps d1 t2) (assignable-closed d1 x r pr) (assignable-closed-list d x as q)))
      ((AsgUniv b y) (ClUniv d))
      ((AsgFn b y l ps rs d1 d2 p q r) (ClFn d l ps rs d1 d2 (assignable-closed d x l p) (assignable-closed-tele d x ps d1 q) (assignable-closed-tele d1 x rs d2 r)))
      ((AsgTyCtor b y ps d1 q) (ClTyCtor d ps d1 (assignable-closed-tele d x ps d1 q)))
      ((AsgValCtor b y ps r d1 q p) (ClValCtor d ps r d1 (assignable-closed-tele d x ps d1 q) (assignable-closed d1 x r p)))))
  ((erased assignable-closed-list : (erased (Nat) d) (erased (Nat) x) (erased (List (Term)) ts) (subterm erased (AssignableList d x ts) a) -> (erased (ClosedList d ts) c))
    (match erased a _
      ((AsgNil b y) (ClNil d))
      ((AsgCons b y t ts2 p q) (ClCons d t ts2 (assignable-closed d x t p) (assignable-closed-list d x ts2 q)))))
  ((erased assignable-closed-tele : (erased (Nat) d) (erased (Nat) x) (erased (List (Entry)) es) (erased (Nat) out) (subterm erased (AssignableTele d x es out) a) -> (erased (ClosedTele d es out) c))
    (match erased a _
      ((AsgTNil b y) (ClTNil d))
      ((AsgTCons b y s i t es2 out2 p q) (ClTCons d s i t es2 out (assignable-closed d x t p) (assignable-closed-tele (Succ d) x es2 out q))))))

(MkUnit)
