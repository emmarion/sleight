; mini/unify.sl -- forced unification (DESIGN.md section 7) for the minimal language, as a walk over a list
; of equations: each is canonicalized, then identical atoms and binders are dropped, applications and
; formers are split into the equations of their parts, and a variable meets a term either by taking it as
; its rule ([Force], entering a branch) or by failing ([Check], comparing two types for identity, section 9).
; The three contradictions are the [UFail] rules: an unassignable term (the occurs check and a telescope
; binder), two rigid atoms, and two shapes that differ. The function that derives it walks the two terms of
; an equation nested rather than over the list, on a bound on the entries without a rule and then the term,
; and an erased lemma turns its walk into the derivation over the list. One session's proposal.

(def-adts $ (Mode : -> Type)
  enum
  (many Force : -> (Mode))
  (many Check : -> (Mode)))

(def-adts $ (Eqn : -> Type)
  enum
  (many MkEqn : (many (Term) l) (many (Term) r) -> (Eqn)))

; Pairing two argument lists, or two telescopes with their marks, in front of the equations still to do.
(def-adts
  ((Zip : ((List (Term)) as) ((List (Term)) bs) ((List (Eqn)) rest) ((List (Eqn)) out) -> Type)
    enum
    (many ZipNil : (erased (List (Eqn)) rest) -> (Zip (Nil (Term)) (Nil (Term)) rest rest))
    (many ZipCons : (erased (Term) a) (erased (Term) b) (erased (List (Term)) as) (erased (List (Term)) bs) (erased (List (Eqn)) rest) (erased (List (Eqn)) out)
       (erased (Zip as bs rest out) p) -> (Zip (Cons (Term) a as) (Cons (Term) b bs) rest (Cons (Eqn) (MkEqn a b) out))))
  ((ZipFail : ((List (Term)) as) ((List (Term)) bs) -> Type)
    enum
    (many ZFNilCons : (erased (Term) b) (erased (List (Term)) bs) -> (ZipFail (Nil (Term)) (Cons (Term) b bs)))
    (many ZFConsNil : (erased (Term) a) (erased (List (Term)) as) -> (ZipFail (Cons (Term) a as) (Nil (Term))))
    (many ZFCons : (erased (Term) a) (erased (Term) b) (erased (List (Term)) as) (erased (List (Term)) bs) (erased (ZipFail as bs) p)
       -> (ZipFail (Cons (Term) a as) (Cons (Term) b bs))))
  ((ZipTele : ((List (Entry)) es) ((List (Entry)) fs) ((List (Eqn)) rest) ((List (Eqn)) out) -> Type)
    enum
    (many ZTNil : (erased (List (Eqn)) rest) -> (ZipTele (Nil (Entry)) (Nil (Entry)) rest rest))
    (many ZTCons : (erased (Bool) s) (erased (Bool) i) (erased (Term) t) (erased (Term) u) (erased (List (Entry)) es) (erased (List (Entry)) fs)
       (erased (List (Eqn)) rest) (erased (List (Eqn)) out) (erased (ZipTele es fs rest out) p)
       -> (ZipTele (Cons (Entry) (MkEntry s i t) es) (Cons (Entry) (MkEntry s i u) fs) rest (Cons (Eqn) (MkEqn t u) out))))
  ((ZipTeleFail : ((List (Entry)) es) ((List (Entry)) fs) -> Type)
    enum
    (many ZTFNilCons : (erased (Entry) f) (erased (List (Entry)) fs) -> (ZipTeleFail (Nil (Entry)) (Cons (Entry) f fs)))
    (many ZTFConsNil : (erased (Entry) e) (erased (List (Entry)) es) -> (ZipTeleFail (Cons (Entry) e es) (Nil (Entry))))
    (many ZTFSub : (erased (Bool) s) (erased (Bool) s2) (erased (Bool) i) (erased (Bool) i2) (erased (Term) t) (erased (Term) u) (erased (List (Entry)) es) (erased (List (Entry)) fs)
       (erased (BoolNeq s s2) n) -> (ZipTeleFail (Cons (Entry) (MkEntry s i t) es) (Cons (Entry) (MkEntry s2 i2 u) fs)))
    (many ZTFIs : (erased (Bool) s) (erased (Bool) s2) (erased (Bool) i) (erased (Bool) i2) (erased (Term) t) (erased (Term) u) (erased (List (Entry)) es) (erased (List (Entry)) fs)
       (erased (BoolNeq i i2) n) -> (ZipTeleFail (Cons (Entry) (MkEntry s i t) es) (Cons (Entry) (MkEntry s2 i2 u) fs)))
    (many ZTFCons : (erased (Entry) e) (erased (Entry) f) (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (ZipTeleFail es fs) p)
       -> (ZipTeleFail (Cons (Entry) e es) (Cons (Entry) f fs))))
  ((ZipDec : ((List (Term)) as) ((List (Term)) bs) ((List (Eqn)) rest) -> Type)
    enum
    (many ZDOk : (erased (List (Term)) as) (erased (List (Term)) bs) (erased (List (Eqn)) rest) (many (List (Eqn)) out) (erased (Zip as bs rest out) p) -> (ZipDec as bs rest))
    (many ZDFail : (erased (List (Term)) as) (erased (List (Term)) bs) (erased (List (Eqn)) rest) (erased (ZipFail as bs) p) -> (ZipDec as bs rest)))
  ((ZipTeleDec : ((List (Entry)) es) ((List (Entry)) fs) ((List (Eqn)) rest) -> Type)
    enum
    (many ZTDOk : (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (List (Eqn)) rest) (many (List (Eqn)) out) (erased (ZipTele es fs rest out) p) -> (ZipTeleDec es fs rest))
    (many ZTDFail : (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (List (Eqn)) rest) (erased (ZipTeleFail es fs) p) -> (ZipTeleDec es fs rest))))

(def-fns _ $ (many zip-dec : (subterm many (List (Term)) as) (many (List (Term)) bs) (many (List (Eqn)) rest) -> (many (ZipDec as bs rest) r))
  (match many as _
    ((Nil _)
      (match many bs _
        ((Nil _) (ZDOk _ _ _ rest $ ZipNil rest))
        ((Cons _ y ys) (ZDFail _ _ _ $ ZFNilCons y ys))))
    ((Cons _ x xs)
      (let-match many bs (Cons _ y ys) ((Nil _) (ZDFail _ _ _ $ ZFConsNil x xs)))
      (match many (notail $ zip-dec xs ys rest) _
        ((ZDOk _ _ _ out p) (ZDOk _ _ _ (Cons _ (MkEqn x y) out) $ ZipCons x y xs ys rest out p))
        ((ZDFail _ _ _ p) (ZDFail _ _ _ $ ZFCons x y xs ys p))))))

(def-fns _ $ (many zip-tele-dec : (subterm many (List (Entry)) es) (many (List (Entry)) fs) (many (List (Eqn)) rest) -> (many (ZipTeleDec es fs rest) r))
  (match many es _
    ((Nil _)
      (match many fs _
        ((Nil _) (ZTDOk _ _ _ rest $ ZTNil rest))
        ((Cons _ f fs2) (ZTDFail _ _ _ $ ZTFNilCons f fs2))))
    ((Cons _ e es2)
      (let-match many fs (Cons _ f fs2) ((Nil _) (ZTDFail _ _ _ $ ZTFConsNil e es2)))
      (let-match many e (MkEntry s i t))
      (let-match many f (MkEntry s2 i2 u))
      (let-match many (bool-dec s s2) (BDSame _) ((BDDiff _ _ n) (ZTDFail _ _ _ $ ZTFSub s s2 i i2 t u es2 fs2 n)))
      (let-match many (bool-dec i i2) (BDSame _) ((BDDiff _ _ n) (ZTDFail _ _ _ $ ZTFIs s s i i2 t u es2 fs2 n)))
      (match many (notail $ zip-tele-dec es2 fs2 rest) _
        ((ZTDOk _ _ _ out p) (ZTDOk _ _ _ (Cons _ (MkEqn t u) out) $ ZTCons s i t u es2 fs2 rest out p))
        ((ZTDFail _ _ _ p) (ZTDFail _ _ _ $ ZTFCons (MkEntry s i t) (MkEntry s i u) es2 fs2 p))))))

; A term's shape as a code, so that two canonical terms of different shapes are told apart by one rule.
(def-adts
  ((ShapeOf : ((Term) t) ((Nat) s) -> Type)
    enum
    (many ShRef : (erased (Nat) x) -> (ShapeOf (Ref x) (Zero)))
    (many ShBound : (erased (Nat) k) -> (ShapeOf (Bound k) (Succ (Zero))))
    (many ShTyApp : (erased (Term) h) (erased (List (Entry)) ps) (erased (List (Term)) as) -> (ShapeOf (TyApp h ps as) (Succ (Succ (Zero)))))
    (many ShUniv : -> (ShapeOf (TUniv) (Succ (Succ (Succ (Zero))))))
    (many ShFn : (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs) -> (ShapeOf (TFn l ps rs) (Succ (Succ (Succ (Succ (Zero)))))))
    (many ShTyCtor : (erased (List (Entry)) ps) -> (ShapeOf (TTyCtor ps) (Succ (Succ (Succ (Succ (Succ (Zero))))))))
    (many ShValCtor : (erased (List (Entry)) ps) (erased (Term) r) -> (ShapeOf (TValCtor ps r) (Succ (Succ (Succ (Succ (Succ (Succ (Zero)))))))))
    (many ShValApp : (erased (Term) h) (erased (List (Entry)) ps) (erased (Term) r) (erased (List (Term)) as) -> (ShapeOf (ValApp h ps r as) (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Zero)))))))))))
  ((NonRef : ((Term) t) -> Type)
    enum
    (many NRBound : (erased (Nat) k) -> (NonRef (Bound k)))
    (many NRTyApp : (erased (Term) h) (erased (List (Entry)) ps) (erased (List (Term)) as) -> (NonRef (TyApp h ps as)))
    (many NRValApp : (erased (Term) h) (erased (List (Entry)) ps) (erased (Term) r) (erased (List (Term)) as) -> (NonRef (ValApp h ps r as)))
    (many NRUniv : -> (NonRef (TUniv)))
    (many NRFn : (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs) -> (NonRef (TFn l ps rs)))
    (many NRTyCtor : (erased (List (Entry)) ps) -> (NonRef (TTyCtor ps)))
    (many NRValCtor : (erased (List (Entry)) ps) (erased (Term) r) -> (NonRef (TValCtor ps r))))
  ((NotDecl : ((Kind) k) -> Type)
    enum
    (many NDPlain : -> (NotDecl (KPlain)))
    (many NDLevel : -> (NotDecl (KLevel)))))

(def-fns _ $ (many shape-of : (many (Term) t) -> (many (Nat) s) (erased (ShapeOf t s) p))
  (match many t _
    ((Ref x) (values (Zero) (ShRef x)))
    ((Bound k) (values (Succ (Zero)) (ShBound k)))
    ((TyApp h ps as) (values (Succ (Succ (Zero))) (ShTyApp h ps as)))
    ((ValApp h ps r as) (values (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Zero)))))))) (ShValApp h ps r as)))
    ((TUniv) (values (Succ (Succ (Succ (Zero)))) (ShUniv)))
    ((TFn l ps rs) (values (Succ (Succ (Succ (Succ (Zero))))) (ShFn l ps rs)))
    ((TTyCtor ps) (values (Succ (Succ (Succ (Succ (Succ (Zero)))))) (ShTyCtor ps)))
    ((TValCtor ps r) (values (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))) (ShValCtor ps r)))))

; Which side of an equation a variable sits on: [Sided s v t l r] reads the equation l = r, both sides
; canonical, as the variable v against the term t.
; The type of a closed term of the grammar (section 10): an entry's, an application's from its head's
; canonical former, and the universe for the universe and the formers.
(def-adts $ (TypeOfTerm : ((List (Ent)) ents) ((List (Rule)) rules) ((Term) t) ((Term) ty) -> Type)
  enum
  (many TotRef : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (EntOf ents x ty k) p) -> (TypeOfTerm ents rules (Ref x) ty))
  (many TotTyApp : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) h) (erased (List (Entry)) ps) (erased (List (Term)) as) -> (TypeOfTerm ents rules (TyApp h ps as) (TUniv)))
  (many TotValApp : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) h) (erased (List (Entry)) ps) (erased (Term) ret) (erased (List (Term)) as)
     (erased (List (Maybe (Term))) subs) (erased (Term) ty) (erased (Somes as subs) s) (erased (Subst subs ret ty) q) -> (TypeOfTerm ents rules (ValApp h ps ret as) ty))
  (many TotUniv : (erased (List (Ent)) ents) (erased (List (Rule)) rules) -> (TypeOfTerm ents rules (TUniv) (TUniv)))
  (many TotFn : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (List (Entry)) ps) (erased (List (Entry)) rs) -> (TypeOfTerm ents rules (TFn l ps rs) (TUniv)))
  (many TotTyCtor : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Entry)) ps) -> (TypeOfTerm ents rules (TTyCtor ps) (TUniv)))
  (many TotValCtor : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Entry)) ps) (erased (Term) r) -> (TypeOfTerm ents rules (TValCtor ps r) (TUniv))))

(def-adts
  ((Side : -> Type)
    enum
    (many SL : -> (Side))
    (many SR : -> (Side)))
  ((Sided : ((Side) s) ((Term) v) ((Term) t) ((Term) l) ((Term) r) -> Type)
    enum
    (many SidedL : (erased (Term) v) (erased (Term) t) -> (Sided (SL) v t v t))
    (many SidedR : (erased (Term) v) (erased (Term) t) -> (Sided (SR) v t t v))))

(def-adts $ (UOut : -> Type)
  enum
  (many UOk : (many (List (Rule)) rules) -> (UOut))
  (many UFail : -> (UOut)))

(def-adts
  ((Unify : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((List (Eqn)) eqs) ((UOut) out) -> Type)
    enum
    (many UDone : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) -> (Unify m ents rules (Nil (Eqn)) (UOk rules)))
    ; identical atoms and binders
    (many USame : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Nat) x) (erased (UOut) out)
       (erased (Canon rules l (Ref x)) cl) (erased (Canon rules r (Ref x)) cr) (erased (Unify m ents rules rest out) p) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) out))
    (many UBound : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Nat) k) (erased (UOut) out)
       (erased (Canon rules l (Bound k)) cl) (erased (Canon rules r (Bound k)) cr) (erased (Unify m ents rules rest out) p) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) out))
    (many UBoundNeq : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Nat) j) (erased (Nat) k)
       (erased (Canon rules l (Bound j)) cl) (erased (Canon rules r (Bound k)) cr) (erased (Neq j k) n) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    ; applications and formers split into their parts
    (many UTyApp : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest)
       (erased (Term) h) (erased (Term) h2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (List (Term)) as) (erased (List (Term)) as2) (erased (List (Eqn)) eqs) (erased (UOut) out)
       (erased (Canon rules l (TyApp h ps as)) cl) (erased (Canon rules r (TyApp h2 ps2 as2)) cr) (erased (Zip as as2 rest eqs) z)
       (erased (Unify m ents rules (Cons (Eqn) (MkEqn h h2) eqs) out) p) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) out))
    (many UTyAppArity : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest)
       (erased (Term) h) (erased (Term) h2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (List (Term)) as) (erased (List (Term)) as2)
       (erased (Canon rules l (TyApp h ps as)) cl) (erased (Canon rules r (TyApp h2 ps2 as2)) cr) (erased (ZipFail as as2) z) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    (many UValApp : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest)
       (erased (Term) h) (erased (Term) h2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (Term) ret) (erased (Term) ret2) (erased (List (Term)) as) (erased (List (Term)) as2) (erased (List (Eqn)) eqs) (erased (UOut) out)
       (erased (Canon rules l (ValApp h ps ret as)) cl) (erased (Canon rules r (ValApp h2 ps2 ret2 as2)) cr) (erased (Zip as as2 rest eqs) z)
       (erased (Unify m ents rules (Cons (Eqn) (MkEqn h h2) eqs) out) p) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) out))
    (many UValAppArity : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest)
       (erased (Term) h) (erased (Term) h2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (Term) ret) (erased (Term) ret2) (erased (List (Term)) as) (erased (List (Term)) as2)
       (erased (Canon rules l (ValApp h ps ret as)) cl) (erased (Canon rules r (ValApp h2 ps2 ret2 as2)) cr) (erased (ZipFail as as2) z) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    (many UUniv : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (UOut) out)
       (erased (Canon rules l (TUniv)) cl) (erased (Canon rules r (TUniv)) cr) (erased (Unify m ents rules rest out) p) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) out))
    (many UFn : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest)
       (erased (Term) lv) (erased (Term) lv2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (List (Entry)) rs) (erased (List (Entry)) rs2)
       (erased (List (Eqn)) e1) (erased (List (Eqn)) e2) (erased (UOut) out)
       (erased (Canon rules l (TFn lv ps rs)) cl) (erased (Canon rules r (TFn lv2 ps2 rs2)) cr) (erased (ZipTele rs rs2 rest e1) z1) (erased (ZipTele ps ps2 e1 e2) z2)
       (erased (Unify m ents rules (Cons (Eqn) (MkEqn lv lv2) e2) out) p) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) out))
    (many UFnParams : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest)
       (erased (Term) lv) (erased (Term) lv2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (List (Entry)) rs) (erased (List (Entry)) rs2)
       (erased (Canon rules l (TFn lv ps rs)) cl) (erased (Canon rules r (TFn lv2 ps2 rs2)) cr) (erased (ZipTeleFail ps ps2) z) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    (many UFnRets : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest)
       (erased (Term) lv) (erased (Term) lv2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (List (Entry)) rs) (erased (List (Entry)) rs2)
       (erased (Canon rules l (TFn lv ps rs)) cl) (erased (Canon rules r (TFn lv2 ps2 rs2)) cr) (erased (ZipTeleFail rs rs2) z) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    (many UTyCtor : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest)
       (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (List (Eqn)) e1) (erased (UOut) out)
       (erased (Canon rules l (TTyCtor ps)) cl) (erased (Canon rules r (TTyCtor ps2)) cr) (erased (ZipTele ps ps2 rest e1) z)
       (erased (Unify m ents rules e1 out) p) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) out))
    (many UTyCtorFail : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest)
       (erased (List (Entry)) ps) (erased (List (Entry)) ps2)
       (erased (Canon rules l (TTyCtor ps)) cl) (erased (Canon rules r (TTyCtor ps2)) cr) (erased (ZipTeleFail ps ps2) z) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    (many UValCtor : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest)
       (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (Term) ret) (erased (Term) ret2) (erased (List (Eqn)) e1) (erased (UOut) out)
       (erased (Canon rules l (TValCtor ps ret)) cl) (erased (Canon rules r (TValCtor ps2 ret2)) cr) (erased (ZipTele ps ps2 (Cons (Eqn) (MkEqn ret ret2) rest) e1) z)
       (erased (Unify m ents rules e1 out) p) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) out))
    (many UValCtorFail : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest)
       (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (Term) ret) (erased (Term) ret2)
       (erased (Canon rules l (TValCtor ps ret)) cl) (erased (Canon rules r (TValCtor ps2 ret2)) cr) (erased (ZipTeleFail ps ps2) z) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    ; two shapes that differ, neither a variable
    (many UMismatch : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest)
       (erased (Term) l2) (erased (Term) r2) (erased (Nat) a) (erased (Nat) b)
       (erased (Canon rules l l2) cl) (erased (Canon rules r r2) cr) (erased (NonRef l2) nl) (erased (NonRef r2) nr) (erased (ShapeOf l2 a) sa) (erased (ShapeOf r2 b) sb) (erased (Neq a b) n)
       -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    ; a variable against a term that is not one, on either side: in [Check] mode a failure, in [Force] mode a
    ; rule if the term may be assigned and the variable is not rigid, and their types are equated next
    (many UCheckRef : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Side) s) (erased (Nat) x) (erased (Term) t) (erased (Term) l2) (erased (Term) r2)
       (erased (Canon rules l l2) cl) (erased (Canon rules r r2) cr) (erased (Sided s (Ref x) t l2 r2) sd) (erased (NonRef t) nt) -> (Unify (Check) ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    (many UAssign : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Side) s) (erased (Nat) x) (erased (Term) t) (erased (Term) l2) (erased (Term) r2)
       (erased (Term) ty) (erased (Kind) k) (erased (Term) tt) (erased (UOut) out)
       (erased (Canon rules l l2) cl) (erased (Canon rules r r2) cr) (erased (Sided s (Ref x) t l2 r2) sd) (erased (NonRef t) nt) (erased (EntOf ents x ty k) e) (erased (NotDecl k) nd) (erased (Assignable (Zero) x t) a)
       (erased (TypeOfTerm ents rules t tt) tp) (erased (Unify (Force) ents (Cons (Rule) (MkRule x t) rules) (Cons (Eqn) (MkEqn ty tt) rest) out) p) -> (Unify (Force) ents rules (Cons (Eqn) (MkEqn l r) rest) out))
    (many UOccurs : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Side) s) (erased (Nat) x) (erased (Term) t) (erased (Term) l2) (erased (Term) r2)
       (erased (Canon rules l l2) cl) (erased (Canon rules r r2) cr) (erased (Sided s (Ref x) t l2 r2) sd) (erased (NonRef t) nt) (erased (Unassignable (Zero) x t) u) -> (Unify (Force) ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    (many URigid : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Side) s) (erased (Nat) x) (erased (Term) t) (erased (Term) l2) (erased (Term) r2) (erased (Term) ty)
       (erased (Canon rules l l2) cl) (erased (Canon rules r r2) cr) (erased (Sided s (Ref x) t l2 r2) sd) (erased (NonRef t) nt) (erased (EntOf ents x ty (KDecl)) e) -> (Unify (Force) ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    (many UCheckRefRef : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Nat) x) (erased (Nat) y)
       (erased (Canon rules l (Ref x)) cl) (erased (Canon rules r (Ref y)) cr) (erased (Neq x y) n) -> (Unify (Check) ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    ; two distinct variables: the one that is not rigid, else the newer, becomes an alias of the other, and
    ; their types are equated next (section 7's signature check); two rigid ones contradict
    (many UAlias : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Nat) x) (erased (Nat) y)
       (erased (Term) tx) (erased (Term) ty) (erased (Kind) kx) (erased (Kind) ky) (erased (Nat) z) (erased (Nat) w) (erased (Term) tz) (erased (Term) tw) (erased (UOut) out)
       (erased (Canon rules l (Ref x)) cl) (erased (Canon rules r (Ref y)) cr) (erased (Neq x y) n) (erased (EntOf ents x tx kx) ex) (erased (EntOf ents y ty ky) ey)
       (erased (Orient x tx kx y ty ky z tz w tw) o)
       (erased (Unify (Force) ents (Cons (Rule) (MkRule z (Ref w)) rules) (Cons (Eqn) (MkEqn tz tw) rest) out) p) -> (Unify (Force) ents rules (Cons (Eqn) (MkEqn l r) rest) out))
    (many URigidRigid : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Nat) x) (erased (Nat) y) (erased (Term) tx) (erased (Term) ty)
       (erased (Canon rules l (Ref x)) cl) (erased (Canon rules r (Ref y)) cr) (erased (Neq x y) n) (erased (EntOf ents x tx (KDecl)) ex) (erased (EntOf ents y ty (KDecl)) ey)
       -> (Unify (Force) ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail))))
  ; Which of two distinct variables takes the rule: [z] is aliased to [w].
  ((Orient : ((Nat) x) ((Term) tx) ((Kind) kx) ((Nat) y) ((Term) ty) ((Kind) ky) ((Nat) z) ((Term) tz) ((Nat) w) ((Term) tw) -> Type)
    enum
    (many OrRigidL : (erased (Nat) x) (erased (Term) tx) (erased (Nat) y) (erased (Term) ty) (erased (Kind) ky) (erased (NotDecl ky) n) -> (Orient x tx (KDecl) y ty ky y ty x tx))
    (many OrRigidR : (erased (Nat) x) (erased (Term) tx) (erased (Kind) kx) (erased (Nat) y) (erased (Term) ty) (erased (NotDecl kx) n) -> (Orient x tx kx y ty (KDecl) x tx y ty))
    (many OrNewerL : (erased (Nat) x) (erased (Term) tx) (erased (Kind) kx) (erased (Nat) y) (erased (Term) ty) (erased (Kind) ky) (erased (NotDecl kx) nx) (erased (NotDecl ky) ny) (erased (Lt y x) lt)
       -> (Orient x tx kx y ty ky x tx y ty))
    (many OrNewerR : (erased (Nat) x) (erased (Term) tx) (erased (Kind) kx) (erased (Nat) y) (erased (Term) ty) (erased (Kind) ky) (erased (NotDecl kx) nx) (erased (NotDecl ky) ny) (erased (Lt x y) lt)
       -> (Orient x tx kx y ty ky y ty x tx))))
; ---- The function side. The walk over the two terms of one equation, nested: on canonical terms
; ([UnifyC]), on the parts of an application or former that are still to walk ([UnifyListC],
; [UnifyTeleC], each part read through the table when its turn comes, as the list above does), and what
; follows an outcome ([After]). [conv] below turns a walk into a derivation of [Unify].
(def-adts
  ((SameLen : ((List (Term)) as) ((List (Term)) bs) -> Type)
    enum
    (many SLNil : -> (SameLen (Nil (Term)) (Nil (Term))))
    (many SLCons : (erased (Term) a) (erased (Term) b) (erased (List (Term)) as) (erased (List (Term)) bs) (erased (SameLen as bs) p) -> (SameLen (Cons (Term) a as) (Cons (Term) b bs))))
  ((SameTele : ((List (Entry)) es) ((List (Entry)) fs) -> Type)
    enum
    (many STNil : -> (SameTele (Nil (Entry)) (Nil (Entry))))
    (many STCons : (erased (Bool) s) (erased (Bool) i) (erased (Term) t) (erased (Term) u) (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (SameTele es fs) p)
       -> (SameTele (Cons (Entry) (MkEntry s i t) es) (Cons (Entry) (MkEntry s i u) fs))))
  ((UnifyC : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((Term) l) ((Term) r) ((UOut) out) -> Type)
    enum
    (many UCSame : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) -> (UnifyC m ents rules (Ref x) (Ref x) (UOk rules)))
    (many UCBound : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) k) -> (UnifyC m ents rules (Bound k) (Bound k) (UOk rules)))
    (many UCBoundNeq : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) j) (erased (Nat) k) (erased (Neq j k) n) -> (UnifyC m ents rules (Bound j) (Bound k) (UFail)))
    (many UCUniv : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) -> (UnifyC m ents rules (TUniv) (TUniv) (UOk rules)))
    (many UCTyApp : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) h) (erased (Term) h2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (List (Term)) as) (erased (List (Term)) as2)
       (erased (UOut) o1) (erased (UOut) out)
       (erased (SameLen as as2) sl) (erased (UnifyC m ents rules h h2 o1) p) (erased (AfterList m ents rules o1 as as2 out) q) -> (UnifyC m ents rules (TyApp h ps as) (TyApp h2 ps2 as2) out))
    (many UCTyAppArity : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) h) (erased (Term) h2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (List (Term)) as) (erased (List (Term)) as2)
       (erased (ZipFail as as2) z) -> (UnifyC m ents rules (TyApp h ps as) (TyApp h2 ps2 as2) (UFail)))
    (many UCValApp : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) h) (erased (Term) h2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (Term) ret) (erased (Term) ret2)
       (erased (List (Term)) as) (erased (List (Term)) as2) (erased (UOut) o1) (erased (UOut) out)
       (erased (SameLen as as2) sl) (erased (UnifyC m ents rules h h2 o1) p) (erased (AfterList m ents rules o1 as as2 out) q) -> (UnifyC m ents rules (ValApp h ps ret as) (ValApp h2 ps2 ret2 as2) out))
    (many UCValAppArity : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) h) (erased (Term) h2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (Term) ret) (erased (Term) ret2)
       (erased (List (Term)) as) (erased (List (Term)) as2)
       (erased (ZipFail as as2) z) -> (UnifyC m ents rules (ValApp h ps ret as) (ValApp h2 ps2 ret2 as2) (UFail)))
    (many UCFn : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) lv) (erased (Term) lv2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2)
       (erased (List (Entry)) rs) (erased (List (Entry)) rs2) (erased (UOut) o1) (erased (UOut) o2) (erased (UOut) out)
       (erased (SameTele rs rs2) st1) (erased (SameTele ps ps2) st2) (erased (UnifyC m ents rules lv lv2 o1) p) (erased (AfterTele m ents rules o1 ps ps2 o2) q) (erased (AfterTele m ents rules o2 rs rs2 out) r)
       -> (UnifyC m ents rules (TFn lv ps rs) (TFn lv2 ps2 rs2) out))
    (many UCFnRets : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) lv) (erased (Term) lv2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2)
       (erased (List (Entry)) rs) (erased (List (Entry)) rs2) (erased (ZipTeleFail rs rs2) z) -> (UnifyC m ents rules (TFn lv ps rs) (TFn lv2 ps2 rs2) (UFail)))
    (many UCFnParams : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) lv) (erased (Term) lv2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2)
       (erased (List (Entry)) rs) (erased (List (Entry)) rs2) (erased (SameTele rs rs2) st1) (erased (ZipTeleFail ps ps2) z) -> (UnifyC m ents rules (TFn lv ps rs) (TFn lv2 ps2 rs2) (UFail)))
    (many UCTyCtor : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (UOut) out)
       (erased (SameTele ps ps2) st) (erased (UnifyTeleC m ents rules ps ps2 out) p) -> (UnifyC m ents rules (TTyCtor ps) (TTyCtor ps2) out))
    (many UCTyCtorFail : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (ZipTeleFail ps ps2) z)
       -> (UnifyC m ents rules (TTyCtor ps) (TTyCtor ps2) (UFail)))
    (many UCValCtor : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (Term) ret) (erased (Term) ret2) (erased (UOut) o1) (erased (UOut) out)
       (erased (SameTele ps ps2) st) (erased (UnifyTeleC m ents rules ps ps2 o1) p) (erased (After m ents rules o1 ret ret2 out) q) -> (UnifyC m ents rules (TValCtor ps ret) (TValCtor ps2 ret2) out))
    (many UCValCtorFail : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (Term) ret) (erased (Term) ret2)
       (erased (ZipTeleFail ps ps2) z) -> (UnifyC m ents rules (TValCtor ps ret) (TValCtor ps2 ret2) (UFail)))
    (many UCMismatch : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (Nat) a) (erased (Nat) b)
       (erased (NonRef l) nl) (erased (NonRef r) nr) (erased (ShapeOf l a) sa) (erased (ShapeOf r b) sb) (erased (Neq a b) n) -> (UnifyC m ents rules l r (UFail)))
    (many UCCheckRef : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Side) s) (erased (Nat) x) (erased (Term) t) (erased (Term) l) (erased (Term) r)
       (erased (Sided s (Ref x) t l r) sd) (erased (NonRef t) nt) -> (UnifyC (Check) ents rules l r (UFail)))
    (many UCRigid : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Side) s) (erased (Nat) x) (erased (Term) t) (erased (Term) l) (erased (Term) r) (erased (Term) ty)
       (erased (Sided s (Ref x) t l r) sd) (erased (NonRef t) nt) (erased (EntOf ents x ty (KDecl)) e) -> (UnifyC (Force) ents rules l r (UFail)))
    (many UCOccurs : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Side) s) (erased (Nat) x) (erased (Term) t) (erased (Term) l) (erased (Term) r)
       (erased (Sided s (Ref x) t l r) sd) (erased (NonRef t) nt) (erased (Unassignable (Zero) x t) u) -> (UnifyC (Force) ents rules l r (UFail)))
    (many UCAssign : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Side) s) (erased (Nat) x) (erased (Term) t) (erased (Term) l) (erased (Term) r) (erased (Term) ty) (erased (Kind) k)
       (erased (Term) tt) (erased (Term) ty2) (erased (Term) tt2) (erased (UOut) out)
       (erased (Sided s (Ref x) t l r) sd) (erased (NonRef t) nt) (erased (EntOf ents x ty k) e) (erased (NotDecl k) nd) (erased (Assignable (Zero) x t) a) (erased (TypeOfTerm ents rules t tt) tp)
       (erased (Canon (Cons (Rule) (MkRule x t) rules) ty ty2) cty) (erased (Canon (Cons (Rule) (MkRule x t) rules) tt tt2) ctt)
       (erased (UnifyC (Force) ents (Cons (Rule) (MkRule x t) rules) ty2 tt2 out) p) -> (UnifyC (Force) ents rules l r out))
    (many UCCheckRefRef : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) (erased (Nat) y) (erased (Neq x y) n) -> (UnifyC (Check) ents rules (Ref x) (Ref y) (UFail)))
    (many UCRigidRigid : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) (erased (Nat) y) (erased (Term) tx) (erased (Term) ty)
       (erased (Neq x y) n) (erased (EntOf ents x tx (KDecl)) ex) (erased (EntOf ents y ty (KDecl)) ey) -> (UnifyC (Force) ents rules (Ref x) (Ref y) (UFail)))
    (many UCAlias : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) (erased (Nat) y) (erased (Term) tx) (erased (Kind) kx) (erased (Term) ty) (erased (Kind) ky)
       (erased (Nat) z) (erased (Term) tz) (erased (Nat) w) (erased (Term) tw) (erased (Term) tz2) (erased (Term) tw2) (erased (UOut) out)
       (erased (Neq x y) n) (erased (EntOf ents x tx kx) ex) (erased (EntOf ents y ty ky) ey) (erased (Orient x tx kx y ty ky z tz w tw) o)
       (erased (Canon (Cons (Rule) (MkRule z (Ref w)) rules) tz tz2) ctz) (erased (Canon (Cons (Rule) (MkRule z (Ref w)) rules) tw tw2) ctw)
       (erased (UnifyC (Force) ents (Cons (Rule) (MkRule z (Ref w)) rules) tz2 tw2 out) p) -> (UnifyC (Force) ents rules (Ref x) (Ref y) out)))
  ((UnifyListC : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((List (Term)) as) ((List (Term)) bs) ((UOut) out) -> Type)
    enum
    (many ULNil : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) -> (UnifyListC m ents rules (Nil (Term)) (Nil (Term)) (UOk rules)))
    (many ULCons : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) a) (erased (Term) b) (erased (Term) a2) (erased (Term) b2) (erased (List (Term)) as) (erased (List (Term)) bs)
       (erased (UOut) o1) (erased (UOut) out)
       (erased (Canon rules a a2) ca) (erased (Canon rules b b2) cb) (erased (UnifyC m ents rules a2 b2 o1) p) (erased (AfterList m ents rules o1 as bs out) q)
       -> (UnifyListC m ents rules (Cons (Term) a as) (Cons (Term) b bs) out)))
  ((UnifyTeleC : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((List (Entry)) es) ((List (Entry)) fs) ((UOut) out) -> Type)
    enum
    (many UTNil : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) -> (UnifyTeleC m ents rules (Nil (Entry)) (Nil (Entry)) (UOk rules)))
    (many UTCons : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Bool) s) (erased (Bool) i) (erased (Term) t) (erased (Term) u) (erased (Term) t2) (erased (Term) u2)
       (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (UOut) o1) (erased (UOut) out)
       (erased (Canon rules t t2) ct) (erased (Canon rules u u2) cu) (erased (UnifyC m ents rules t2 u2 o1) p) (erased (AfterTele m ents rules o1 es fs out) q)
       -> (UnifyTeleC m ents rules (Cons (Entry) (MkEntry s i t) es) (Cons (Entry) (MkEntry s i u) fs) out)))
  ((After : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((UOut) o1) ((Term) t) ((Term) u) ((UOut) out) -> Type)
    enum
    (many AFail : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) t) (erased (Term) u) -> (After m ents rules (UFail) t u (UFail)))
    (many AOk : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Rule)) rules1) (erased (Term) t) (erased (Term) u) (erased (Term) t2) (erased (Term) u2) (erased (UOut) out)
       (erased (Canon rules1 t t2) ct) (erased (Canon rules1 u u2) cu) (erased (UnifyC m ents rules1 t2 u2 out) p) -> (After m ents rules (UOk rules1) t u out)))
  ((AfterList : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((UOut) o1) ((List (Term)) as) ((List (Term)) bs) ((UOut) out) -> Type)
    enum
    (many ALFail : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Term)) as) (erased (List (Term)) bs) -> (AfterList m ents rules (UFail) as bs (UFail)))
    (many ALOk : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Rule)) rules1) (erased (List (Term)) as) (erased (List (Term)) bs) (erased (UOut) out)
       (erased (UnifyListC m ents rules1 as bs out) p) -> (AfterList m ents rules (UOk rules1) as bs out)))
  ((AfterTele : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((UOut) o1) ((List (Entry)) es) ((List (Entry)) fs) ((UOut) out) -> Type)
    enum
    (many ATFail : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Entry)) es) (erased (List (Entry)) fs) -> (AfterTele m ents rules (UFail) es fs (UFail)))
    (many ATOk : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Rule)) rules1) (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (UOut) out)
       (erased (UnifyTeleC m ents rules1 es fs out) p) -> (AfterTele m ents rules (UOk rules1) es fs out)))
  ; The derivation of the equations after an outcome: the rest under the table it left, or nothing.
  ((Cont : ((Mode) m) ((List (Ent)) ents) ((UOut) o1) ((List (Eqn)) rest) ((UOut) out) -> Type)
    enum
    (many ContOk : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules1) (erased (List (Eqn)) rest) (erased (UOut) out)
       (erased (Unify m ents rules1 rest out) p) -> (Cont m ents (UOk rules1) rest out))
    (many ContFail : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Eqn)) rest) -> (Cont m ents (UFail) rest (UFail)))))

; ---- From the walk to the derivation over the list of equations.
(def-fns _ $ (erased zip-of-samelen : (erased (List (Term)) as) (erased (List (Term)) bs) (erased (List (Eqn)) rest) (subterm erased (SameLen as bs) sl) -> (erased (List (Eqn)) eqs) (erased (Zip as bs rest eqs) z))
  (let-match erased sl (SLCons a b as2 bs2 p)
    ((SLNil) (values rest (ZipNil rest))))
  (let ((erased eqs) (erased z)) (zip-of-samelen as2 bs2 rest p))
  (values (Cons _ (MkEqn a b) eqs) (ZipCons a b as2 bs2 rest eqs z)))

(def-fns _ $ (erased zip-tele-of-same : (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (List (Eqn)) rest) (subterm erased (SameTele es fs) st) -> (erased (List (Eqn)) eqs) (erased (ZipTele es fs rest eqs) z))
  (let-match erased st (STCons s i t u es2 fs2 p)
    ((STNil) (values rest (ZTNil rest))))
  (let ((erased eqs) (erased z)) (zip-tele-of-same es2 fs2 rest p))
  (values (Cons _ (MkEqn t u) eqs) (ZTCons s i t u es2 fs2 rest eqs z)))

(def-fns _ $ (erased zip-samelen : (erased (List (Term)) as) (erased (List (Term)) bs) (erased (List (Eqn)) rest) (erased (List (Eqn)) eqs) (subterm erased (Zip as bs rest eqs) z) -> (erased (SameLen as bs) sl))
  (match erased z _
    ((ZipNil _) (SLNil))
    ((ZipCons a b as2 bs2 _ eqs2 p) (SLCons a b as2 bs2 (zip-samelen as2 bs2 rest eqs2 p)))))

(def-fns _ $ (erased zip-tele-same : (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (List (Eqn)) rest) (erased (List (Eqn)) eqs) (subterm erased (ZipTele es fs rest eqs) z) -> (erased (SameTele es fs) st))
  (match erased z _
    ((ZTNil _) (STNil))
    ((ZTCons s i t u es2 fs2 _ eqs2 p) (STCons s i t u es2 fs2 (zip-tele-same es2 fs2 rest eqs2 p)))))

(def-fns _
  ((erased conv : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (Term) l2) (erased (Term) r2) (erased (UOut) o1) (erased (List (Eqn)) rest) (erased (UOut) out)
      (subterm erased (UnifyC m ents rules l2 r2 o1) d) (erased (Canon rules l l2) cl) (erased (Canon rules r r2) cr) (erased (Cont m ents o1 rest out) k) -> (erased (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) out) u))
    (match erased d _
      ((UCSame _ _ _ x) (match erased k _ ((ContOk _ _ _ _ _ kk) (USame m ents rules l r rest x out cl cr kk))))
      ((UCBound _ _ _ j) (match erased k _ ((ContOk _ _ _ _ _ kk) (UBound m ents rules l r rest j out cl cr kk))))
      ((UCBoundNeq _ _ _ j j2 n) (match erased k _ ((ContFail _ _ _) (UBoundNeq m ents rules l r rest j j2 cl cr n))))
      ((UCUniv _ _ _) (match erased k _ ((ContOk _ _ _ _ _ kk) (UUniv m ents rules l r rest out cl cr kk))))
      ((UCTyApp _ _ _ h h2 ps ps2 as as2 o oo sl p q)
        (let ((erased eqs) (erased z)) (zip-of-samelen as as2 rest sl))
        (let-match erased (canon-canonical rules l l2 cl) (CnTyApp _ _ _ _ ch _))
        (match erased (canon-canonical rules r r2 cr) _
          ((CnTyApp _ _ _ _ ch2 _)
            (UTyApp m ents rules l r rest h h2 ps ps2 as as2 eqs out cl cr z (conv m ents rules h h2 h h2 o eqs out p (canonical-fix rules h ch) (canonical-fix rules h2 ch2) (conv-after-list m ents rules o as as2 oo rest eqs out q z k))))))
      ((UCTyAppArity _ _ _ h h2 ps ps2 as as2 z) (match erased k _ ((ContFail _ _ _) (UTyAppArity m ents rules l r rest h h2 ps ps2 as as2 cl cr z))))
      ((UCValApp _ _ _ h h2 ps ps2 ret ret2 as as2 o oo sl p q)
        (let ((erased eqs) (erased z)) (zip-of-samelen as as2 rest sl))
        (let-match erased (canon-canonical rules l l2 cl) (CnValApp _ _ _ _ _ ch _))
        (match erased (canon-canonical rules r r2 cr) _
          ((CnValApp _ _ _ _ _ ch2 _)
            (UValApp m ents rules l r rest h h2 ps ps2 ret ret2 as as2 eqs out cl cr z (conv m ents rules h h2 h h2 o eqs out p (canonical-fix rules h ch) (canonical-fix rules h2 ch2) (conv-after-list m ents rules o as as2 oo rest eqs out q z k))))))
      ((UCValAppArity _ _ _ h h2 ps ps2 ret ret2 as as2 z) (match erased k _ ((ContFail _ _ _) (UValAppArity m ents rules l r rest h h2 ps ps2 ret ret2 as as2 cl cr z))))
      ((UCFn _ _ _ lv lv2 ps ps2 rs rs2 o o2 oo st1 st2 p q rr)
        (let ((erased e1) (erased z1)) (zip-tele-of-same rs rs2 rest st1))
        (let ((erased e2) (erased z2)) (zip-tele-of-same ps ps2 e1 st2))
        (let-match erased (canon-canonical rules l l2 cl) (CnFn _ _ _ _ clv _ _))
        (let-match erased (canon-canonical rules r r2 cr) (CnFn _ _ _ _ clv2 _ _))
        (UFn m ents rules l r rest lv lv2 ps ps2 rs rs2 e1 e2 out cl cr z1 z2
          (conv m ents rules lv lv2 lv lv2 o e2 out p (canonical-fix rules lv clv) (canonical-fix rules lv2 clv2)
            (conv-after-tele m ents rules o ps ps2 o2 e1 e2 out q z2 (conv-after-tele m ents rules o2 rs rs2 oo rest e1 out rr z1 k)))))
      ((UCFnRets _ _ _ lv lv2 ps ps2 rs rs2 z) (match erased k _ ((ContFail _ _ _) (UFnRets m ents rules l r rest lv lv2 ps ps2 rs rs2 cl cr z))))
      ((UCFnParams _ _ _ lv lv2 ps ps2 rs rs2 _ z) (match erased k _ ((ContFail _ _ _) (UFnParams m ents rules l r rest lv lv2 ps ps2 rs rs2 cl cr z))))
      ((UCTyCtor _ _ _ ps ps2 oo st p)
        (let ((erased e1) (erased z)) (zip-tele-of-same ps ps2 rest st))
        (UTyCtor m ents rules l r rest ps ps2 e1 out cl cr z (conv-tele m ents rules ps ps2 oo rest e1 out p z k)))
      ((UCTyCtorFail _ _ _ ps ps2 z) (match erased k _ ((ContFail _ _ _) (UTyCtorFail m ents rules l r rest ps ps2 cl cr z))))
      ((UCValCtor _ _ _ ps ps2 ret ret2 o oo st p q)
        (let ((erased e1) (erased z)) (zip-tele-of-same ps ps2 (Cons _ (MkEqn ret ret2) rest) st))
        (UValCtor m ents rules l r rest ps ps2 ret ret2 e1 out cl cr z (conv-tele m ents rules ps ps2 o (Cons _ (MkEqn ret ret2) rest) e1 out p z (conv-after m ents rules o ret ret2 oo rest out q k))))
      ((UCValCtorFail _ _ _ ps ps2 ret ret2 z) (match erased k _ ((ContFail _ _ _) (UValCtorFail m ents rules l r rest ps ps2 ret ret2 cl cr z))))
      ((UCMismatch _ _ _ _ _ sa0 sb0 nl nr sa sb n) (match erased k _ ((ContFail _ _ _) (UMismatch m ents rules l r rest l2 r2 sa0 sb0 cl cr nl nr sa sb n))))
      ((UCCheckRef _ _ s x t _ _ sd nt) (match erased k _ ((ContFail _ _ _) (UCheckRef ents rules l r rest s x t l2 r2 cl cr sd nt))))
      ((UCRigid _ _ s x t _ _ ty sd nt e) (match erased k _ ((ContFail _ _ _) (URigid ents rules l r rest s x t l2 r2 ty cl cr sd nt e))))
      ((UCOccurs _ _ s x t _ _ sd nt un) (match erased k _ ((ContFail _ _ _) (UOccurs ents rules l r rest s x t l2 r2 cl cr sd nt un))))
      ((UCAssign _ _ s x t _ _ ty kd tt ty2 tt2 oo sd nt e nd asg tp cty ctt p)
        (UAssign ents rules l r rest s x t l2 r2 ty kd tt out cl cr sd nt e nd asg tp (conv (Force) ents (Cons _ (MkRule x t) rules) ty tt ty2 tt2 oo rest out p cty ctt k)))
      ((UCCheckRefRef _ _ x y n) (match erased k _ ((ContFail _ _ _) (UCheckRefRef ents rules l r rest x y cl cr n))))
      ((UCRigidRigid _ _ x y tx ty n ex ey) (match erased k _ ((ContFail _ _ _) (URigidRigid ents rules l r rest x y tx ty cl cr n ex ey))))
      ((UCAlias _ _ x y tx kx ty ky z tz w tw tz2 tw2 oo n ex ey o ctz ctw p)
        (UAlias ents rules l r rest x y tx ty kx ky z w tz tw out cl cr n ex ey o (conv (Force) ents (Cons _ (MkRule z (Ref w)) rules) tz tw tz2 tw2 oo rest out p ctz ctw k)))))
  ((erased conv-list : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Term)) as) (erased (List (Term)) bs) (erased (UOut) o1) (erased (List (Eqn)) rest) (erased (List (Eqn)) eqs) (erased (UOut) out)
      (subterm erased (UnifyListC m ents rules as bs o1) d) (erased (Zip as bs rest eqs) z) (erased (Cont m ents o1 rest out) k) -> (erased (Unify m ents rules eqs out) u))
    (match erased d _
      ((ULNil _ _ _)
        (let-match erased z (ZipNil _))
        (match erased k _ ((ContOk _ _ _ _ _ kk) kk)))
      ((ULCons _ _ _ a1 b1 a2 b2 as2 bs2 o oo ca cb p q)
        (match erased z _ ((ZipCons _ _ _ _ _ eqs2 z2) (conv m ents rules a1 b1 a2 b2 o eqs2 out p ca cb (conv-after-list m ents rules o as2 bs2 oo rest eqs2 out q z2 k)))))))
  ((erased conv-tele : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (UOut) o1) (erased (List (Eqn)) rest) (erased (List (Eqn)) eqs) (erased (UOut) out)
      (subterm erased (UnifyTeleC m ents rules es fs o1) d) (erased (ZipTele es fs rest eqs) z) (erased (Cont m ents o1 rest out) k) -> (erased (Unify m ents rules eqs out) u))
    (match erased d _
      ((UTNil _ _ _)
        (let-match erased z (ZTNil _))
        (match erased k _ ((ContOk _ _ _ _ _ kk) kk)))
      ((UTCons _ _ _ _ _ t u t2 u2 es2 fs2 o oo ct cu p q)
        (match erased z _ ((ZTCons _ _ _ _ _ _ _ eqs2 z2) (conv m ents rules t u t2 u2 o eqs2 out p ct cu (conv-after-tele m ents rules o es2 fs2 oo rest eqs2 out q z2 k)))))))
  ((erased conv-after : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (UOut) o0) (erased (Term) t) (erased (Term) u) (erased (UOut) o1) (erased (List (Eqn)) rest) (erased (UOut) out)
      (subterm erased (After m ents rules o0 t u o1) d) (erased (Cont m ents o1 rest out) k) -> (erased (Cont m ents o0 (Cons (Eqn) (MkEqn t u) rest) out) c))
    (let-match erased d (AFail _ _ _ _ _)
      ((AOk _ _ _ rules1 _ _ t2 u2 _ ct cu p) (ContOk m ents rules1 (Cons _ (MkEqn t u) rest) out (conv m ents rules1 t u t2 u2 o1 rest out p ct cu k))))
    (match erased k _ ((ContFail _ _ _) (ContFail m ents (Cons _ (MkEqn t u) rest)))))
  ((erased conv-after-list : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (UOut) o0) (erased (List (Term)) as) (erased (List (Term)) bs) (erased (UOut) o1) (erased (List (Eqn)) rest) (erased (List (Eqn)) eqs) (erased (UOut) out)
      (subterm erased (AfterList m ents rules o0 as bs o1) d) (erased (Zip as bs rest eqs) z) (erased (Cont m ents o1 rest out) k) -> (erased (Cont m ents o0 eqs out) c))
    (let-match erased d (ALFail _ _ _ _ _)
      ((ALOk _ _ _ rules1 _ _ _ p) (ContOk m ents rules1 eqs out (conv-list m ents rules1 as bs o1 rest eqs out p z k))))
    (match erased k _ ((ContFail _ _ _) (ContFail m ents eqs))))
  ((erased conv-after-tele : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (UOut) o0) (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (UOut) o1) (erased (List (Eqn)) rest) (erased (List (Eqn)) eqs) (erased (UOut) out)
      (subterm erased (AfterTele m ents rules o0 es fs o1) d) (erased (ZipTele es fs rest eqs) z) (erased (Cont m ents o1 rest out) k) -> (erased (Cont m ents o0 eqs out) c))
    (let-match erased d (ATFail _ _ _ _ _)
      ((ATOk _ _ _ rules1 _ _ _ p) (ContOk m ents rules1 eqs out (conv-tele m ents rules1 es fs o1 rest eqs out p z k))))
    (match erased k _ ((ContFail _ _ _) (ContFail m ents eqs)))))

; ---- The bound the walk lowers: at most [n] entries have no rule, and a mint for one that has none lowers
; it. A rule consed for such an entry leaves every other rule found.
(def-adts
  ((FreeCount : ((List (Ent)) ents) ((List (Rule)) rules) ((Nat) n) -> Type)
    enum
    (many FCNil : (erased (List (Rule)) rules) -> (FreeCount (Nil (Ent)) rules (Zero)))
    (many FCBound : (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (List (Ent)) rest) (erased (List (Rule)) rules) (erased (Term) r) (erased (Nat) n)
       (erased (RuleOf rules x r) p) (erased (FreeCount rest rules n) q) -> (FreeCount (Cons (Ent) (MkEnt x ty k) rest) rules n))
    (many FCFree : (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (List (Ent)) rest) (erased (List (Rule)) rules) (erased (Nat) n)
       (erased (FreeCount rest rules n) q) -> (FreeCount (Cons (Ent) (MkEnt x ty k) rest) rules (Succ n)))))

(def-fns _ $ (many free-count : (subterm many (List (Ent)) ents) (many (List (Rule)) rules) -> (many (Nat) n) (erased (FreeCount ents rules n) p))
  (let-match many ents (Cons _ e rest) ((Nil _) (values (Zero) (FCNil rules))))
  (let-match many e (MkEnt x ty k))
  (let ((many n) (erased q)) (notail $ free-count rest rules))
  (match many (rule-dec rules x) _
    ((RuleHit _ _ r p) (values n (FCBound x ty k rest rules r n p q)))
    ((RuleMiss _ _ _) (values (Succ n) (FCFree x ty k rest rules n q)))))

(def-fns _ $ (erased rule-neq : (erased (List (Rule)) rules) (erased (Nat) y) (erased (Term) r) (erased (Nat) x) (subterm erased (RuleOf rules y r) p) (erased (NoRule rules x) q) -> (erased (Neq y x) n))
  (match erased p _
    ((RuleHere _ _ _) (match erased q _ ((NoRuleCons _ _ _ _ n2 _) (neq-sym x y n2))))
    ((RuleThere _ _ _ _ rest _ p2) (match erased q _ ((NoRuleCons _ _ _ _ _ q2) (rule-neq rest y r x p2 q2))))))

(def-fns _ $ (erased fc-cons : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) n) (erased (Nat) x) (erased (Term) t) (subterm erased (FreeCount ents rules n) fc) (erased (NoRule rules x) nr) ->
    (erased (FreeCount ents (Cons (Rule) (MkRule x t) rules) n) fc2))
  (match erased fc _
    ((FCNil _) (FCNil _))
    ((FCBound y ty k rest _ r m p c) (FCBound y ty k rest _ r m (RuleThere y x r t rules (rule-neq rules y r x p nr) p) (fc-cons rest rules m x t c nr)))
    ((FCFree y ty k rest _ m c) (FCFree y ty k rest _ m (fc-cons rest rules m x t c nr)))))

(def-fns _ $ (erased assign-count : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) n) (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (Term) t)
    (erased (FreeCount ents rules n) fc) (subterm erased (EntOf ents x ty k) e) (erased (NoRule rules x) nr) ->
    (erased (Nat) m) (erased (Lt m n) lt) (erased (FreeCount ents (Cons (Rule) (MkRule x t) rules) m) fc2))
  (match erased e _
    ((EntHere _ _ _ rest)
      (match erased fc _
        (absurd (FCBound _ _ _ _ _ r _ p _) (rule-of-no-rule rules x r p nr))
        ((FCFree _ _ _ _ _ m c2) (values m (lt-succ m) (FCBound x ty k rest _ t m (RuleHere x t rules) (fc-cons rest rules m x t c2 nr))))))
    ((EntThere _ y _ ty2 _ k2 rest _ e2)
      (match erased fc _
        ((FCBound _ _ _ _ _ r m p c2)
          (let ((erased m2) (erased lt) (erased fc3)) (assign-count rest rules m x ty k t c2 e2 nr))
          (values m2 lt (FCBound y ty2 k2 rest _ r m2 (RuleThere y x r t rules (rule-neq rules y r x p nr) p) fc3)))
        ((FCFree _ _ _ _ _ m c2)
          (let ((erased m2) (erased lt) (erased fc3)) (assign-count rest rules m x ty k t c2 e2 nr))
          (values (Succ m2) (LtS m2 m lt) (FCFree y ty2 k2 rest _ m2 fc3)))))))

; ---- The table beside the rules: their ranking and their scope, kept through a unification mint by
; giving the new rule rank zero and every other rule one more; its canonical term has no ruled entry.
(def-adts
  ((Table : ((List (Ent)) ents) ((List (Rule)) rules) -> Type)
    enum
    (many MkTable : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (many (List (Nat)) ranks) (many (Nat) top) (erased (ValidFrom rules ranks rules ranks) v) (erased (AllLt ranks top) al)
       (erased (ScopedRules ents rules) sr) (erased (RulesPlain ents rules) rp) -> (Table ents rules)))
  ((RulesPlain : ((List (Ent)) ents) ((List (Rule)) rules) -> Type)
    enum
    (many RPNil : (erased (List (Ent)) ents) -> (RulesPlain ents (Nil (Rule))))
    (many RPCons : (erased (List (Ent)) ents) (erased (Nat) x) (erased (Term) t) (erased (List (Rule)) rest) (erased (Term) ty) (erased (Kind) k) (erased (EntOf ents x ty k) e) (erased (NotDecl k) nd)
       (erased (RulesPlain ents rest) q) -> (RulesPlain ents (Cons (Rule) (MkRule x t) rest))))
  ((Shift : ((List (Nat)) ks) ((List (Nat)) ks2) -> Type)
    enum
    (many ShNil : -> (Shift (Nil (Nat)) (Nil (Nat))))
    (many ShCons : (erased (Nat) k) (erased (List (Nat)) ks) (erased (List (Nat)) ks2) (erased (Shift ks ks2) p) -> (Shift (Cons (Nat) k ks) (Cons (Nat) (Succ k) ks2)))))

(def-fns _ $ (many shift : (subterm many (List (Nat)) ks) -> (many (List (Nat)) ks2) (erased (Shift ks ks2) p))
  (let-match many ks (Cons _ k rest)
    ((Nil _) (values (Nil _) (ShNil))))
  (let ((many rest2) (erased p)) (notail $ shift rest))
  (values (Cons _ (Succ k) rest2) (ShCons k rest rest2 p)))

(def-fns _ $ (erased rule-rank-shift : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (List (Nat)) ranks2) (erased (Nat) z) (erased (Term) r) (erased (Nat) j)
    (subterm erased (RuleRank rules ranks z r j) p) (erased (Shift ranks ranks2) sh) -> (erased (RuleRank rules ranks2 z r (Succ j)) q))
  (match erased p _
    ((RRHere _ _ _ rest _) (match erased sh _ ((ShCons _ _ ks2 _) (RRHere z r (Succ j) rest ks2))))
    ((RRThere _ y _ s _ k2 rest ks n p2) (match erased sh _ ((ShCons _ _ ks2 s2) (RRThere z y r s (Succ j) (Succ k2) rest ks2 n (rule-rank-shift rest ks ks2 z r j p2 s2)))))))

(def-fns _ $ (erased all-lt-shift : (erased (List (Nat)) ks) (erased (List (Nat)) ks2) (erased (Nat) top) (subterm erased (AllLt ks top) a) (erased (Shift ks ks2) sh) -> (erased (AllLt ks2 (Succ top)) b))
  (match erased a _
    ((ALNil _) (match erased sh _ ((ShNil) (ALNil (Succ top)))))
    ((ALCons k rest _ lt q) (match erased sh _ ((ShCons _ _ ks3 s2) (ALCons (Succ k) ks3 (Succ top) (LtS k top lt) (all-lt-shift rest ks3 top q s2)))))))

(def-fns _
  ((erased below-shift : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (List (Nat)) ranks2) (erased (Term) t) (erased (Nat) k) (erased (Nat) x) (erased (Term) s)
      (erased (NoRule rules x) nr) (erased (Shift ranks ranks2) sh) (subterm erased (Below rules ranks t k) b) -> (erased (Below (Cons (Rule) (MkRule x s) rules) (Cons (Nat) (Zero) ranks2) t (Succ k)) c))
    (let-match erased b (BlFree _ _ z _ p)
      ((BlRuled _ _ z _ r j p lt) (BlRuled _ _ z (Succ k) r (Succ j) (RRThere z x r s (Succ j) (Zero) rules ranks2 (rule-neq rules z r x (rule-rank-of rules ranks z r j p) nr) (rule-rank-shift rules ranks ranks2 z r j p sh)) (LtS j k lt)))
      ((BlBound _ _ i _) (BlBound _ _ i (Succ k)))
      ((BlTyApp _ _ h ps as _ p q) (BlTyApp _ _ h ps as (Succ k) (below-shift rules ranks ranks2 h k x s nr sh p) (below-shift-list rules ranks ranks2 as k x s nr sh q)))
      ((BlValApp _ _ h ps r as _ p q) (BlValApp _ _ h ps r as (Succ k) (below-shift rules ranks ranks2 h k x s nr sh p) (below-shift-list rules ranks ranks2 as k x s nr sh q)))
      ((BlUniv _ _ _) (BlUniv _ _ (Succ k)))
      ((BlFn _ _ l ps rs _ p q r) (BlFn _ _ l ps rs (Succ k) (below-shift rules ranks ranks2 l k x s nr sh p) (below-shift-tele rules ranks ranks2 ps k x s nr sh q) (below-shift-tele rules ranks ranks2 rs k x s nr sh r)))
      ((BlTyCtor _ _ ps _ q) (BlTyCtor _ _ ps (Succ k) (below-shift-tele rules ranks ranks2 ps k x s nr sh q)))
      ((BlValCtor _ _ ps r _ q p) (BlValCtor _ _ ps r (Succ k) (below-shift-tele rules ranks ranks2 ps k x s nr sh q) (below-shift rules ranks ranks2 r k x s nr sh p))))
    (match erased (nat-dec z x) _
      ((NDSame _) (BlRuled _ _ z (Succ k) s (Zero) (RRHere x s (Zero) rules ranks2) (LtZ k)))
      ((NDDiff _ _ n) (BlFree _ _ z (Succ k) (NoRuleCons z x s rules n p)))))
  ((erased below-shift-list : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (List (Nat)) ranks2) (erased (List (Term)) ts) (erased (Nat) k) (erased (Nat) x) (erased (Term) s)
      (erased (NoRule rules x) nr) (erased (Shift ranks ranks2) sh) (subterm erased (BelowList rules ranks ts k) b) -> (erased (BelowList (Cons (Rule) (MkRule x s) rules) (Cons (Nat) (Zero) ranks2) ts (Succ k)) c))
    (match erased b _
      ((BlNil _ _ _) (BlNil _ _ (Succ k)))
      ((BlCons _ _ t ts2 _ p q) (BlCons _ _ t ts2 (Succ k) (below-shift rules ranks ranks2 t k x s nr sh p) (below-shift-list rules ranks ranks2 ts2 k x s nr sh q)))))
  ((erased below-shift-tele : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (List (Nat)) ranks2) (erased (List (Entry)) es) (erased (Nat) k) (erased (Nat) x) (erased (Term) s)
      (erased (NoRule rules x) nr) (erased (Shift ranks ranks2) sh) (subterm erased (BelowTele rules ranks es k) b) -> (erased (BelowTele (Cons (Rule) (MkRule x s) rules) (Cons (Nat) (Zero) ranks2) es (Succ k)) c))
    (match erased b _
      ((BlTNil _ _ _) (BlTNil _ _ (Succ k)))
      ((BlTCons _ _ s0 i t es2 _ p q) (BlTCons _ _ s0 i t es2 (Succ k) (below-shift rules ranks ranks2 t k x s nr sh p) (below-shift-tele rules ranks ranks2 es2 k x s nr sh q))))))

(def-fns _ $ (erased valid-shift : (erased (List (Rule)) all) (erased (List (Nat)) ar) (erased (List (Nat)) ar2) (erased (List (Rule)) rs) (erased (List (Nat)) ks) (erased (List (Nat)) ks2) (erased (Nat) x) (erased (Term) s)
    (erased (NoRule all x) nr) (erased (Shift ar ar2) sha) (erased (Shift ks ks2) shk) (subterm erased (ValidFrom all ar rs ks) v) -> (erased (ValidFrom (Cons (Rule) (MkRule x s) all) (Cons (Nat) (Zero) ar2) rs ks2) w))
  (match erased v _
    ((VFNil _ _) (match erased shk _ ((ShNil) (VFNil _ _))))
    ((VFCons _ _ y r k rs2 ks3 bl p) (match erased shk _ ((ShCons _ _ ks4 s2) (VFCons _ _ y r (Succ k) rs2 ks4 (below-shift all ar ar2 r k x s nr sha bl) (valid-shift all ar ar2 rs2 ks3 ks4 x s nr sha s2 p)))))))

; A canonical term the new entry does not occur in has no ruled entry under the new rule.
(def-fns _
  ((erased below-zero : (erased (List (Rule)) rules) (erased (List (Nat)) ranks2) (erased (Nat) x) (erased (Term) s) (erased (Term) t) (erased (Nat) d)
      (erased (Assignable d x t) a) (subterm erased (Canonical rules t) c) -> (erased (Below (Cons (Rule) (MkRule x s) rules) ranks2 t (Zero)) b))
    (match erased c _
      ((CnRef _ z p) (match erased a _ ((AsgRef _ _ _ n) (BlFree _ _ z (Zero) (NoRuleCons z x s rules (neq-sym x z n) p)))))
      ((CnBound _ k) (BlBound _ _ k (Zero)))
      ((CnTyApp _ h ps as p q) (match erased a _ ((AsgTyApp _ _ _ _ _ _ pa _ qa) (BlTyApp _ _ h ps as (Zero) (below-zero rules ranks2 x s h d pa p) (below-zero-list rules ranks2 x s as d qa q)))))
      ((CnValApp _ h ps r as p q) (match erased a _ ((AsgValApp _ _ _ _ _ _ _ pa _ _ qa) (BlValApp _ _ h ps r as (Zero) (below-zero rules ranks2 x s h d pa p) (below-zero-list rules ranks2 x s as d qa q)))))
      ((CnUniv _) (BlUniv _ _ (Zero)))
      ((CnFn _ l ps rs p q r)
        (match erased a _ ((AsgFn _ _ _ _ _ d1 d3 pa qa ra) (BlFn _ _ l ps rs (Zero) (below-zero rules ranks2 x s l d pa p) (below-zero-tele rules ranks2 x s ps d d1 qa q) (below-zero-tele rules ranks2 x s rs d1 d3 ra r)))))
      ((CnTyCtor _ ps q) (match erased a _ ((AsgTyCtor _ _ _ d1 qa) (BlTyCtor _ _ ps (Zero) (below-zero-tele rules ranks2 x s ps d d1 qa q)))))
      ((CnValCtor _ ps r q p) (match erased a _ ((AsgValCtor _ _ _ _ d1 qa pa) (BlValCtor _ _ ps r (Zero) (below-zero-tele rules ranks2 x s ps d d1 qa q) (below-zero rules ranks2 x s r d1 pa p)))))))
  ((erased below-zero-list : (erased (List (Rule)) rules) (erased (List (Nat)) ranks2) (erased (Nat) x) (erased (Term) s) (erased (List (Term)) ts) (erased (Nat) d)
      (erased (AssignableList d x ts) a) (subterm erased (CanonicalList rules ts) c) -> (erased (BelowList (Cons (Rule) (MkRule x s) rules) ranks2 ts (Zero)) b))
    (let-match erased c (CnCons _ t ts2 p q)
      ((CnNil _) (BlNil _ _ (Zero))))
    (match erased a _ ((AsgCons _ _ _ _ pa qa) (BlCons _ _ t ts2 (Zero) (below-zero rules ranks2 x s t d pa p) (below-zero-list rules ranks2 x s ts2 d qa q)))))
  ((erased below-zero-tele : (erased (List (Rule)) rules) (erased (List (Nat)) ranks2) (erased (Nat) x) (erased (Term) s) (erased (List (Entry)) es) (erased (Nat) d) (erased (Nat) out)
      (erased (AssignableTele d x es out) a) (subterm erased (CanonicalTele rules es) c) -> (erased (BelowTele (Cons (Rule) (MkRule x s) rules) ranks2 es (Zero)) b))
    (let-match erased c (CnTCons _ s0 i t es2 p q)
      ((CnTNil _) (BlTNil _ _ (Zero))))
    (match erased a _ ((AsgTCons _ _ _ _ _ _ _ pa qa) (BlTCons _ _ s0 i t es2 (Zero) (below-zero rules ranks2 x s t d pa p) (below-zero-tele rules ranks2 x s es2 (Succ d) out qa q))))))

(def-fns _ $ (many table-mint : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (many (Table ents rules) tb) (erased (Nat) x) (erased (Term) s) (erased (NoRule rules x) nr) (erased (Canonical rules s) cs)
    (erased (Assignable (Zero) x s) asg) (erased (Scoped ents (Zero) s) ss) (erased (Term) ty) (erased (Kind) k) (erased (EntOf ents x ty k) e) (erased (NotDecl k) nd) -> (many (Table ents (Cons (Rule) (MkRule x s) rules)) tb2))
  (let-match many tb (MkTable _ _ ranks top v al sr rp))
  (let ((many ranks2) (erased sh)) (shift ranks))
  (MkTable _ _ (Cons _ (Zero) ranks2) (Succ top) (VFCons _ _ x s (Zero) rules ranks2 (below-zero rules (Cons _ (Zero) ranks2) x s s (Zero) asg cs) (valid-shift rules ranks ranks2 rules ranks ranks2 x s nr sh sh v))
    (ALCons (Zero) ranks2 (Succ top) (LtZ top) (all-lt-shift ranks ranks2 top al sh)) (SRCons _ x s rules ss sr) (RPCons _ x s rules ty k e nd rp)))

; Canonicalization under a table.
(def-fns _ $ (many canon-tb : (erased (List (Ent)) ents) (many (List (Rule)) rules) (many (Table ents rules) tb) (many (Term) t) -> (many (Term) u) (erased (Canon rules t u) p))
  (match many tb _ ((MkTable _ _ ranks top v al _ _) (canon rules ranks v top t (below-all rules ranks top v al t)))))
(def-fns _ $ (many canon-list-tb : (erased (List (Ent)) ents) (many (List (Rule)) rules) (many (Table ents rules) tb) (many (List (Term)) ts) -> (many (List (Term)) us) (erased (CanonList rules ts us) p))
  (match many tb _ ((MkTable _ _ ranks top v al _ _) (canon-list rules ranks v top ts (below-all-list rules ranks top v al ts)))))
(def-fns _ $ (many canon-tele-tb : (erased (List (Ent)) ents) (many (List (Rule)) rules) (many (Table ents rules) tb) (many (List (Entry)) es) -> (many (List (Entry)) fs) (erased (CanonTele rules es fs) p))
  (match many tb _ ((MkTable _ _ ranks top v al _ _) (canon-tele rules ranks v top es (below-all-tele rules ranks top v al es)))))
(def-fns _ $ (erased table-scoped : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Table ents rules) tb) -> (erased (ScopedRules ents rules) sr))
  (match erased tb _ ((MkTable _ _ _ _ _ _ sr _) sr)))

; ---- The walk. Each function answers the outcome with its derivation and a [Step]: the table unchanged,
; The type of a closed term.
; Two telescopes of one shape at one depth end at one depth.
(def-fns _ $ (erased stele-same-out : (erased (List (Ent)) ents) (erased (Nat) d) (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (Nat) out) (erased (Nat) out2) (subterm erased (SameTele es fs) st)
    (erased (ScopedTele ents d es out) p) (erased (ScopedTele ents d fs out2) q) -> (erased (Eq (Nat) out out2) e))
  (match erased st _
    ((STNil)
      (let-match erased p (ScTNil _ _))
      (match erased q _ ((ScTNil _ _) (Refl (Nat) d))))
    ((STCons _ _ _ _ es2 fs2 st2)
      (let-match erased p (ScTCons _ _ _ _ _ _ _ _ p2))
      (match erased q _ ((ScTCons _ _ _ _ _ _ _ _ q2) (stele-same-out ents (Succ d) es2 fs2 out out2 st2 p2 q2))))))

(def-adts $ (TypeOfTermDec : ((List (Ent)) ents) ((List (Rule)) rules) ((Term) t) -> Type)
  enum
  (many TotIs : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) t) (many (Term) ty) (erased (TypeOfTerm ents rules t ty) p) (erased (Scoped ents (Zero) ty) sc) -> (TypeOfTermDec ents rules t)))
(def-fns _ $ (many type-of-term : (many (List (Ent)) ents) (erased (ScopedEnts ents ents) se) (erased (List (Rule)) rules) (many (Table ents rules) _tb) (subterm many (Term) t) (erased (Scoped ents (Zero) t) st) ->
    (many (TypeOfTermDec ents rules t) r))
  (match many t _
    ((Ref x)
      (let-match erased st (ScRef _ _ _ hx))
      (match many (ent-dec ents x) _
        (absurd (EntMiss _ _ ne) (has-ent-no-ent ents x hx ne))
        ((EntHit _ _ ty k e) (TotIs _ _ _ ty (TotRef ents rules x ty k e) (ent-of-scoped ents ents x ty k se e)))))
    (absurd (Bound _) (let-match erased st (ScBound _ _ _ lt)) lt)
    ((TyApp h ps as) (TotIs _ _ _ (TUniv) (TotTyApp ents rules h ps as) (ScUniv ents (Zero))))
    ((ValApp h ps ret as)
      (let-match erased st (ScValApp _ _ _ _ _ _ out _ sps sret sas le))
      (let ((erased sub2) (erased so) (many ty) (erased q) (erased sty)) (inst-ret ents out ps ret as sps sret sas le))
      (TotIs _ _ _ ty (TotValApp ents rules h ps ret as sub2 ty so q) sty))
    ((TUniv) (TotIs _ _ _ (TUniv) (TotUniv ents rules) (ScUniv ents (Zero))))
    ((TFn l ps rs) (TotIs _ _ _ (TUniv) (TotFn ents rules l ps rs) (ScUniv ents (Zero))))
    ((TTyCtor ps) (TotIs _ _ _ (TUniv) (TotTyCtor ents rules ps) (ScUniv ents (Zero))))
    ((TValCtor ps r) (TotIs _ _ _ (TUniv) (TotValCtor ents rules ps r) (ScUniv ents (Zero))))))

; or a new table with the bound it lowered to, or no table. A third subterm argument, a phase, lets a
; function hand its own arguments to a helper (the second can only decrease when the first stays).
(def-adts
  ((UStep : ((Nat) n) ((List (Ent)) ents) ((List (Rule)) rules) ((UOut) o) -> Type)
    enum
    (many StSame : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) -> (UStep n ents rules (UOk rules)))
    (many StMint : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (many (List (Rule)) rules1) (many (Table ents rules1) tb1) (erased (Nat) n1) (erased (Lt n1 n) lt) (erased (FreeCount ents rules1 n1) fc)
       -> (UStep n ents rules (UOk rules1)))
    (many StFail : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) -> (UStep n ents rules (UFail))))
  ((Phase : -> Type)
    enum
    (many PInner : -> (Phase))
    (many POuter : (many (Phase) inner) -> (Phase)))
  ((NonRefDec : ((Term) t) -> Type)
    enum
    (many IsRef : (many (Nat) x) -> (NonRefDec (Ref x)))
    (many IsNonRef : (erased (Term) t) (erased (NonRef t) p) -> (NonRefDec t)))
  ((Oriented : ((List (Ent)) ents) ((Nat) x) ((Term) tx) ((Kind) kx) ((Nat) y) ((Term) ty) ((Kind) ky) -> Type)
    enum
    (many OrSome : (erased (List (Ent)) ents) (erased (Nat) x) (erased (Term) tx) (erased (Kind) kx) (erased (Nat) y) (erased (Term) ty) (erased (Kind) ky)
       (many (Nat) z) (many (Term) tz) (many (Nat) w) (many (Term) tw) (erased (Kind) kz) (erased (EntOf ents z tz kz) ez) (erased (NotDecl kz) nz) (erased (Orient x tx kx y ty ky z tz w tw) o) -> (Oriented ents x tx kx y ty ky))
    (many OrNone : (erased (List (Ent)) ents) (erased (Nat) x) (erased (Term) tx) (erased (Nat) y) (erased (Term) ty) -> (Oriented ents x tx (KDecl) y ty (KDecl)))))

(def-fns _ $ (many step-seq : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Rule)) rules1) (many (UStep n ents rules (UOk rules1)) st1)
      (erased (Nat) n1) (erased (Lt n1 (Succ n)) le) (erased (UOut) o2) (many (UStep n1 ents rules1 o2) st2) -> (many (UStep n ents rules o2) st))
    (match many st2 _
      ((StSame _ _ _) st1)
      ((StMint _ _ _ rules2 tb2 n2 lt2 fc2) (StMint _ _ _ rules2 tb2 n2 (lt-le-trans n2 n1 n lt2 le) fc2))
      ((StFail _ _ _) (StFail _ _ _))))

(def-fns _ $ (many nonref-dec : (many (Term) t) -> (many (NonRefDec t) r))
  (match many t _
    ((Ref x) (IsRef x))
    ((Bound k) (IsNonRef _ (NRBound k)))
    ((TyApp h ps as) (IsNonRef _ (NRTyApp h ps as)))
    ((ValApp h ps r as) (IsNonRef _ (NRValApp h ps r as)))
    ((TUniv) (IsNonRef _ (NRUniv)))
    ((TFn l ps rs) (IsNonRef _ (NRFn l ps rs)))
    ((TTyCtor ps) (IsNonRef _ (NRTyCtor ps)))
    ((TValCtor ps r) (IsNonRef _ (NRValCtor ps r)))))

(def-fns _ $ (many orient-age : (erased (List (Ent)) ents) (many (Nat) x) (many (Term) tx) (erased (Kind) kx) (erased (NotDecl kx) nx) (erased (EntOf ents x tx kx) ex)
      (many (Nat) y) (many (Term) ty) (erased (Kind) ky) (erased (NotDecl ky) ny) (erased (EntOf ents y ty ky) ey) (erased (Neq x y) n) -> (many (Oriented ents x tx kx y ty ky) r))
    (match many (nat-cmp x y) _
      ((CLt _ _ _ _ lt) (OrSome _ _ _ _ _ _ _ y ty x tx ky ey ny (OrNewerR x tx kx y ty ky nx ny lt)))
      (absurd (CEq _ _ _) (neq-irrefl x n))
      ((CGt _ _ _ _ lt) (OrSome _ _ _ _ _ _ _ x tx y ty kx ex nx (OrNewerL x tx kx y ty ky nx ny lt)))))

(def-fns _ $ (many orient-plain : (erased (List (Ent)) ents) (many (Nat) x) (many (Term) tx) (erased (Kind) kx) (erased (NotDecl kx) nx) (erased (EntOf ents x tx kx) ex)
      (many (Nat) y) (many (Term) ty) (many (Kind) ky) (erased (EntOf ents y ty ky) ey) (erased (Neq x y) n) -> (many (Oriented ents x tx kx y ty ky) r))
    (match many ky _
      ((KDecl) (OrSome _ _ _ _ _ _ _ x tx y ty kx ex nx (OrRigidR x tx kx y ty nx)))
      ((KPlain) (orient-age ents x tx kx nx ex y ty (KPlain) (NDPlain) ey n))
      ((KLevel) (orient-age ents x tx kx nx ex y ty (KLevel) (NDLevel) ey n))))

(def-fns _ $ (many orient : (erased (List (Ent)) ents) (many (Nat) x) (many (Term) tx) (many (Kind) kx) (erased (EntOf ents x tx kx) ex) (many (Nat) y) (many (Term) ty) (many (Kind) ky) (erased (EntOf ents y ty ky) ey)
      (erased (Neq x y) n) -> (many (Oriented ents x tx kx y ty ky) r))
    (let-match many kx (KDecl)
      ((KPlain) (orient-plain ents x tx (KPlain) (NDPlain) ex y ty ky ey n))
      ((KLevel) (orient-plain ents x tx (KLevel) (NDLevel) ex y ty ky ey n)))
    (match many ky _
      ((KDecl) (OrNone _ x tx y ty))
      ((KPlain) (OrSome _ _ _ _ _ _ _ y ty x tx (KPlain) ey (NDPlain) (OrRigidL x tx y ty (KPlain) (NDPlain))))
      ((KLevel) (OrSome _ _ _ _ _ _ _ y ty x tx (KLevel) ey (NDLevel) (OrRigidL x tx y ty (KLevel) (NDLevel))))))

; What an orientation says of the alias: the two are distinct and each is one of the two variables.
(def-fns _ $ (erased orient-neq : (erased (Nat) x) (erased (Term) tx) (erased (Kind) kx) (erased (Nat) y) (erased (Term) ty) (erased (Kind) ky) (erased (Nat) z) (erased (Term) tz) (erased (Nat) w) (erased (Term) tw)
    (erased (Orient x tx kx y ty ky z tz w tw) o) (erased (Neq x y) n) -> (erased (Neq z w) m))
  (match erased o _
    ((OrRigidL _ _ _ _ _ _) (neq-sym x y n))
    ((OrRigidR _ _ _ _ _ _) n)
    ((OrNewerL _ _ _ _ _ _ _ _ _) n)
    ((OrNewerR _ _ _ _ _ _ _ _ _) (neq-sym x y n))))

(def-fns _ $ (erased orient-free : (erased (List (Rule)) rules) (erased (Nat) x) (erased (Term) tx) (erased (Kind) kx) (erased (Nat) y) (erased (Term) ty) (erased (Kind) ky) (erased (Nat) z) (erased (Term) tz) (erased (Nat) w) (erased (Term) tw)
    (erased (Orient x tx kx y ty ky z tz w tw) o) (erased (NoRule rules x) nx) (erased (NoRule rules y) ny) -> (erased (NoRule rules z) nz) (erased (NoRule rules w) nw))
  (match erased o _
    ((OrRigidL _ _ _ _ _ _) (values ny nx))
    ((OrRigidR _ _ _ _ _ _) (values nx ny))
    ((OrNewerL _ _ _ _ _ _ _ _ _) (values nx ny))
    ((OrNewerR _ _ _ _ _ _ _ _ _) (values ny nx))))

(def-fns _ $ (erased orient-has : (erased (List (Ent)) ents) (erased (Nat) x) (erased (Term) tx) (erased (Kind) kx) (erased (Nat) y) (erased (Term) ty) (erased (Kind) ky) (erased (Nat) z) (erased (Term) tz) (erased (Nat) w) (erased (Term) tw)
    (erased (Orient x tx kx y ty ky z tz w tw) o) (erased (HasEnt ents x) hx) (erased (HasEnt ents y) hy) -> (erased (HasEnt ents w) hw))
  (match erased o _
    ((OrRigidL _ _ _ _ _ _) hx)
    ((OrRigidR _ _ _ _ _ _) hy)
    ((OrNewerL _ _ _ _ _ _ _ _ _) hy)
    ((OrNewerR _ _ _ _ _ _ _ _ _) hx)))

(def-fns _ $ (erased orient-scoped : (erased (List (Ent)) ents) (erased (Nat) x) (erased (Term) tx) (erased (Kind) kx) (erased (Nat) y) (erased (Term) ty) (erased (Kind) ky) (erased (Nat) z) (erased (Term) tz) (erased (Nat) w) (erased (Term) tw)
    (erased (Orient x tx kx y ty ky z tz w tw) o) (erased (Scoped ents (Zero) tx) sx) (erased (Scoped ents (Zero) ty) sy) -> (erased (Scoped ents (Zero) tz) sz))
  (match erased o _
    ((OrRigidL _ _ _ _ _ _) sy)
    ((OrRigidR _ _ _ _ _ _) sx)
    ((OrNewerL _ _ _ _ _ _ _ _ _) sx)
    ((OrNewerR _ _ _ _ _ _ _ _ _) sy)))

(def-fns _ $ (erased orient-scoped-w : (erased (List (Ent)) ents) (erased (Nat) x) (erased (Term) tx) (erased (Kind) kx) (erased (Nat) y) (erased (Term) ty) (erased (Kind) ky) (erased (Nat) z) (erased (Term) tz) (erased (Nat) w) (erased (Term) tw)
    (erased (Orient x tx kx y ty ky z tz w tw) o) (erased (Scoped ents (Zero) tx) sx) (erased (Scoped ents (Zero) ty) sy) -> (erased (Scoped ents (Zero) tw) sw))
  (match erased o _
    ((OrRigidL _ _ _ _ _ _) sx)
    ((OrRigidR _ _ _ _ _ _) sy)
    ((OrNewerL _ _ _ _ _ _ _ _ _) sy)
    ((OrNewerR _ _ _ _ _ _ _ _ _) sx)))

; A variable against a term that is not one, in [Force] mode: refused, or the rule minted with what unifying
; the two types next needs.
(def-adts $ (RefStep : ((Mode) m) ((Nat) n) ((List (Ent)) ents) ((List (Rule)) rules) ((Term) l) ((Term) r) -> Type)
  enum
  (many RefDone : (erased (Mode) m) (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (UOut) o) (many (UStep n ents rules o) st)
     (erased (UnifyC m ents rules l r o) p) -> (RefStep m n ents rules l r))
  (many RefMint : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r)
     (many (Nat) x) (many (Term) t) (many (Term) ty) (many (Term) tt) (many (Table ents (Cons (Rule) (MkRule x t) rules)) tb1) (erased (Nat) n1) (erased (Lt n1 n) lt)
     (erased (FreeCount ents (Cons (Rule) (MkRule x t) rules) n1) fc) (erased (Side) s) (erased (Kind) k) (erased (Sided s (Ref x) t l r) sd) (erased (NonRef t) nt) (erased (EntOf ents x ty k) e) (erased (NotDecl k) nd)
     (erased (Assignable (Zero) x t) a) (erased (TypeOfTerm ents rules t tt) tp) (erased (Scoped ents (Zero) ty) sty) (erased (Scoped ents (Zero) tt) stt) -> (RefStep (Force) n ents rules l r)))

(def-fns _ $ (many assign : (many (List (Ent)) ents) (erased (ScopedEnts ents ents) se) (erased (List (Rule)) rules) (many (Table ents rules) tb) (erased (Nat) n) (erased (FreeCount ents rules n) fc) (erased (Side) s) (many (Nat) x) (many (Term) t)
      (erased (Term) l) (erased (Term) r) (many (Term) ty) (erased (Kind) k) (erased (Sided s (Ref x) t l r) sd) (erased (NonRef t) nt) (erased (EntOf ents x ty k) e) (erased (NotDecl k) nd)
      (erased (NoRule rules x) nx) (erased (Canonical rules t) ct) (erased (Nat) d) (erased (Scoped ents d t) st) -> (many (RefStep (Force) n ents rules l r) rs))
    (let-match many (assign-dec (Zero) x t) (ADYes _ _ _ ok)
      ((ADNo _ _ _ un) (RefDone _ _ _ _ _ _ (UFail) (StFail _ _ _) (UCOccurs ents rules s x t l r sd nt un))))
    (let ((erased st0)) (scoped-tighten ents d (Zero) t st (assignable-closed (Zero) x t ok)))
    (let-match many (type-of-term ents se rules tb t st0) (TotIs _ _ _ tt tp stt))
    (let ((erased n1) (erased lt) (erased fc1)) (assign-count ents rules n x ty k t fc e nx))
    (RefMint _ _ _ _ _ x t ty tt (table-mint ents rules tb x t nx ct ok st0 ty k e nd) n1 lt fc1 s k sd nt e nd ok tp (ent-of-scoped ents ents x ty k se e) stt))

(def-fns _ $ (many unify-ref : (many (Mode) m) (many (List (Ent)) ents) (erased (ScopedEnts ents ents) se) (erased (List (Rule)) rules) (many (Table ents rules) tb) (erased (Nat) n) (erased (FreeCount ents rules n) fc) (erased (Side) s) (many (Nat) x) (many (Term) t)
      (erased (Term) l) (erased (Term) r) (erased (Sided s (Ref x) t l r) sd) (erased (NonRef t) nt) (erased (NoRule rules x) nx) (erased (HasEnt ents x) hx) (erased (Canonical rules t) ct) (erased (Nat) d) (erased (Scoped ents d t) st) ->
      (many (RefStep m n ents rules l r) rs))
    (let-match many m (Force) ((Check) (RefDone _ _ _ _ _ _ (UFail) (StFail _ _ _) (UCCheckRef ents rules s x t l r sd nt))))
    (let-match many (ent-dec ents x) (EntHit _ _ ty k e) (absurd (EntMiss _ _ ne) (has-ent-no-ent ents x hx ne)))
    (match many k _
      ((KDecl) (RefDone _ _ _ _ _ _ (UFail) (StFail _ _ _) (UCRigid ents rules s x t l r ty sd nt e)))
      ((KPlain) (assign ents se rules tb n fc s x t l r ty (KPlain) sd nt e (NDPlain) nx ct d st))
      ((KLevel) (assign ents se rules tb n fc s x t l r ty (KLevel) sd nt e (NDLevel) nx ct d st))))

; Two distinct variables in [Force] mode, up to the alias: what remains is to unify the types.
(def-adts $ (AliasStep : ((Nat) n) ((List (Ent)) ents) ((List (Rule)) rules) ((Nat) x) ((Nat) y) -> Type)
  enum
  (many AliasFail : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) (erased (Nat) y) (erased (UnifyC (Force) ents rules (Ref x) (Ref y) (UFail)) p) -> (AliasStep n ents rules x y))
  (many AliasMint : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) (erased (Nat) y)
     (many (Nat) z) (many (Term) tz) (many (Nat) w) (many (Term) tw) (many (Table ents (Cons (Rule) (MkRule z (Ref w)) rules)) tb1) (erased (Nat) n1) (erased (Lt n1 n) lt)
     (erased (FreeCount ents (Cons (Rule) (MkRule z (Ref w)) rules) n1) fc) (erased (Term) tx) (erased (Kind) kx) (erased (Term) ty) (erased (Kind) ky) (erased (Kind) kz)
     (erased (EntOf ents x tx kx) ex) (erased (EntOf ents y ty ky) ey) (erased (EntOf ents z tz kz) ez) (erased (NotDecl kz) nz) (erased (Orient x tx kx y ty ky z tz w tw) o) -> (AliasStep n ents rules x y)))

(def-fns _ $ (many alias-step : (many (List (Ent)) ents) (erased (List (Rule)) rules) (many (Table ents rules) tb) (erased (Nat) n) (erased (FreeCount ents rules n) fc) (many (Nat) x) (many (Nat) y) (erased (Neq x y) nq)
      (erased (NoRule rules x) nx) (erased (NoRule rules y) ny) (erased (HasEnt ents x) hx) (erased (HasEnt ents y) hy) -> (many (AliasStep n ents rules x y) r))
    (let-match many (ent-dec ents x) (EntHit _ _ tx kx ex) (absurd (EntMiss _ _ ne) (has-ent-no-ent ents x hx ne)))
    (let-match many (ent-dec ents y) (EntHit _ _ ty ky ey) (absurd (EntMiss _ _ ne) (has-ent-no-ent ents y hy ne)))
    (let-match many (orient ents x tx kx ex y ty ky ey nq) (OrSome _ _ _ _ _ _ _ z tz w tw kz ez ndz o)
      ((OrNone _ _ _ _ _) (AliasFail _ _ _ _ _ (UCRigidRigid ents rules x y tx ty nq ex ey))))
    (let ((erased nz) (erased nw)) (orient-free rules x tx kx y ty ky z tz w tw o nx ny))
    (let ((erased n1) (erased lt) (erased fc1)) (assign-count ents rules n z tz kz (Ref w) fc ez nz))
    (AliasMint _ _ _ _ _ z tz w tw
      (table-mint ents rules tb z (Ref w) nz (CnRef rules w nw) (AsgRef (Zero) z w (orient-neq x tx kx y ty ky z tz w tw o nq)) (ScRef ents (Zero) w (orient-has ents x tx kx y ty ky z tz w tw o hx hy)) tz kz ez ndz)
      n1 lt fc1 tx kx ty ky kz ex ey ez ndz o))

; What the walk answers: a step with its derivation.
(def-adts
  ((WalkDec : ((Mode) m) ((Nat) n) ((List (Ent)) ents) ((List (Rule)) rules) ((Term) l) ((Term) r) -> Type)
    enum
    (many MkWalk : (erased (Mode) m) (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (UOut) o) (many (UStep n ents rules o) st)
       (erased (UnifyC m ents rules l r o) p) -> (WalkDec m n ents rules l r)))
  ((ListDec : ((Mode) m) ((Nat) n) ((List (Ent)) ents) ((List (Rule)) rules) ((List (Term)) as) ((List (Term)) bs) -> Type)
    enum
    (many MkList : (erased (Mode) m) (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Term)) as) (erased (List (Term)) bs) (erased (UOut) o) (many (UStep n ents rules o) st)
       (erased (UnifyListC m ents rules as bs o) p) -> (ListDec m n ents rules as bs)))
  ((TeleDec : ((Mode) m) ((Nat) n) ((List (Ent)) ents) ((List (Rule)) rules) ((List (Entry)) es) ((List (Entry)) fs) -> Type)
    enum
    (many MkTele : (erased (Mode) m) (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (UOut) o) (many (UStep n ents rules o) st)
       (erased (UnifyTeleC m ents rules es fs o) p) -> (TeleDec m n ents rules es fs)))
  ((AfterDec : ((Mode) m) ((Nat) n) ((List (Ent)) ents) ((List (Rule)) rules) ((UOut) o1) ((Term) t) ((Term) u) -> Type)
    enum
    (many MkAfter : (erased (Mode) m) (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (UOut) o1) (erased (Term) t) (erased (Term) u) (erased (UOut) o) (many (UStep n ents rules o) st)
       (erased (After m ents rules o1 t u o) p) -> (AfterDec m n ents rules o1 t u)))
  ((AfterListDec : ((Mode) m) ((Nat) n) ((List (Ent)) ents) ((List (Rule)) rules) ((UOut) o1) ((List (Term)) as) ((List (Term)) bs) -> Type)
    enum
    (many MkAfterList : (erased (Mode) m) (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (UOut) o1) (erased (List (Term)) as) (erased (List (Term)) bs) (erased (UOut) o)
       (many (UStep n ents rules o) st) (erased (AfterList m ents rules o1 as bs o) p) -> (AfterListDec m n ents rules o1 as bs)))
  ((AfterTeleDec : ((Mode) m) ((Nat) n) ((List (Ent)) ents) ((List (Rule)) rules) ((UOut) o1) ((List (Entry)) es) ((List (Entry)) fs) -> Type)
    enum
    (many MkAfterTele : (erased (Mode) m) (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (UOut) o1) (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (UOut) o)
       (many (UStep n ents rules o) st) (erased (AfterTele m ents rules o1 es fs o) p) -> (AfterTeleDec m n ents rules o1 es fs))))

(def-fns _
  ((many unify-canon : (many (Mode) m) (many (List (Ent)) ents) (erased (ScopedEnts ents ents) se) (many (List (Rule)) rules) (many (Table ents rules) tb) (subterm erased (Nat) n) (erased (FreeCount ents rules n) fc)
      (subterm many (Term) l) (many (Term) r) (erased (Canonical rules l) cl) (erased (Canonical rules r) cr) (erased (Nat) d) (erased (Scoped ents d l) sl) (erased (Scoped ents d r) sr) (subterm many (POuter (PInner)) is phase) ->
      (many (WalkDec m n ents rules l r) w))
    (match many (nonref-dec l) _
      ((IsRef x)
        (let-match erased cl (CnRef _ _ nx))
        (let-match erased sl (ScRef _ _ _ hx))
        (let-match many (nonref-dec r) (IsRef y)
          ((IsNonRef _ nr) (tail $ ref-step m ents se rules tb n fc (Ref x) r (unify-ref m ents se rules tb n fc (SL) x r (Ref x) r (SidedL (Ref x) r) nr nx hx cr d sr) (PInner))))
        (let-match erased cr (CnRef _ _ ny))
        (let-match erased sr (ScRef _ _ _ hy))
        (let-match many (nat-dec x y) (NDDiff _ _ nq)
          ((NDSame _) (MkWalk _ _ _ _ _ _ (UOk rules) (StSame _ _ _) (UCSame m ents rules x))))
        (let-match many m (Force)
          ((Check) (MkWalk _ _ _ _ _ _ (UFail) (StFail _ _ _) (UCCheckRefRef ents rules x y nq))))
        (let-match many (alias-step ents rules tb n fc x y nq nx ny hx hy) (AliasMint _ _ _ _ _ z3 tz w3 tw tb1 n1 lt fc1 tx kx ty ky _ ex ey _ _ o)
          ((AliasFail _ _ _ _ _ p) (MkWalk _ _ _ _ _ _ (UFail) (StFail _ _ _) p)))
        (let ((many tz2) (erased ctz)) (canon-tb ents (Cons _ (MkRule z3 (Ref w3)) rules) tb1 tz))
        (let ((many tw2) (erased ctw)) (canon-tb ents (Cons _ (MkRule z3 (Ref w3)) rules) tb1 tw))
        (let ((erased stz)) (orient-scoped ents x tx kx y ty ky z3 tz w3 tw o (ent-of-scoped ents ents x tx kx se ex) (ent-of-scoped ents ents y ty ky se ey)))
        (let ((erased stw)) (orient-scoped-w ents x tx kx y ty ky z3 tz w3 tw o (ent-of-scoped ents ents x tx kx se ex) (ent-of-scoped ents ents y ty ky se ey)))
        (let-match many (notail $ unify-canon m ents se (Cons _ (MkRule z3 (Ref w3)) rules) tb1 (subterm (lt-subterm n1 n lt)) n1 fc1 tz2 tw2
            (canon-canonical _ tz tz2 ctz) (canon-canonical _ tw tw2 ctw) (Zero) (canon-scoped ents _ (Zero) tz tz2 (table-scoped ents _ tb1) stz ctz) (canon-scoped ents _ (Zero) tw tw2 (table-scoped ents _ tb1) stw ctw) phase) (MkWalk _ _ _ _ _ _ o2 st2 q))
        (MkWalk _ _ _ _ _ _ o2 (step-seq n ents rules _ (StMint _ _ _ (Cons _ (MkRule z3 (Ref w3)) rules) tb1 n1 lt fc1) n1 (lt-weaken n1 n lt) o2 st2)
          (UCAlias ents rules x y tx kx ty ky z3 tz w3 tw tz2 tw2 o2 nq ex ey o ctz ctw q)))
      ((IsNonRef _ nl)
        (let-match many (nonref-dec r) (IsNonRef _ nr)
          ((IsRef y)
            (let-match erased cr (CnRef _ _ ny))
            (match erased sr _ ((ScRef _ _ _ hy) (tail $ ref-step m ents se rules tb n fc l (Ref y) (unify-ref m ents se rules tb n fc (SR) y l l (Ref y) (SidedR (Ref y) l) nl ny hy cl d sl) (PInner))))))
        (let ((many b) (erased sb)) (shape-of r))
        (match many l _
          (absurd (Ref _) nl)
          ((Bound j)
            (let-match many (nat-dec (Succ (Zero)) b) (NDSame _)
              ((NDDiff _ _ nq) (MkWalk _ _ _ _ _ _ (UFail) (StFail _ _ _) (UCMismatch m ents rules l r (Succ (Zero)) b nl nr (ShBound j) sb nq))))
            (let-match erased sb (ShBound _))
            (let-match many r (Bound k))
            (match many (nat-dec j k) _
              ((NDSame _) (MkWalk _ _ _ _ _ _ (UOk rules) (StSame _ _ _) (UCBound m ents rules j)))
              ((NDDiff _ _ nq) (MkWalk _ _ _ _ _ _ (UFail) (StFail _ _ _) (UCBoundNeq m ents rules j k nq)))))
          ((TyApp h ps as)
            (let-match many (nat-dec (Succ (Succ (Zero))) b) (NDSame _)
              ((NDDiff _ _ nq) (MkWalk _ _ _ _ _ _ (UFail) (StFail _ _ _) (UCMismatch m ents rules l r (Succ (Succ (Zero))) b nl nr (ShTyApp h ps as) sb nq))))
            (let-match erased sb (ShTyApp _ _ _))
            (let-match many r (TyApp h2 ps2 as2))
            (let-match erased cl (CnTyApp _ _ _ _ ch cas))
            (let-match erased cr (CnTyApp _ _ _ _ ch2 cas2))
            (let-match erased sl (ScTyApp _ _ _ _ _ _ sh _ sas _))
            (let-match erased sr (ScTyApp _ _ _ _ _ _ sh2 _ sas2 _))
            (let-match many (zip-dec as as2 (Nil _)) (ZDOk _ _ _ eqs z3)
              ((ZDFail _ _ _ zf) (MkWalk _ _ _ _ _ _ (UFail) (StFail _ _ _) (UCTyAppArity m ents rules h h2 ps ps2 as as2 zf))))
            (let-match many (notail $ unify-canon m ents se rules tb n fc h h2 ch ch2 d sh sh2 phase) (MkWalk _ _ _ _ _ _ o1 st1 p))
            (let-match many (notail $ after-list m ents se rules tb n fc _ l o1 st1 as as2 as as2 (canonical-fix-list rules as cas) (canonical-fix-list rules as2 cas2) (prove-subterm as l) d sas sas2 (zip-samelen as as2 (Nil _) eqs z3) (PInner)) (MkAfterList _ _ _ _ _ _ _ o2 st2 q))
            (MkWalk _ _ _ _ _ _ o2 st2 (UCTyApp m ents rules h h2 ps ps2 as as2 o1 o2 (zip-samelen as as2 (Nil _) eqs z3) p q)))
          ((ValApp h ps ret as)
            (let-match many (nat-dec (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Zero)))))))) b) (NDSame _)
              ((NDDiff _ _ nq) (MkWalk _ _ _ _ _ _ (UFail) (StFail _ _ _) (UCMismatch m ents rules l r (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Zero)))))))) b nl nr (ShValApp h ps ret as) sb nq))))
            (let-match erased sb (ShValApp _ _ _ _))
            (let-match many r (ValApp h2 ps2 ret2 as2))
            (let-match erased cl (CnValApp _ _ _ _ _ ch cas))
            (let-match erased cr (CnValApp _ _ _ _ _ ch2 cas2))
            (let-match erased sl (ScValApp _ _ _ _ _ _ _ sh _ _ sas _))
            (let-match erased sr (ScValApp _ _ _ _ _ _ _ sh2 _ _ sas2 _))
            (let-match many (zip-dec as as2 (Nil _)) (ZDOk _ _ _ eqs z3)
              ((ZDFail _ _ _ zf) (MkWalk _ _ _ _ _ _ (UFail) (StFail _ _ _) (UCValAppArity m ents rules h h2 ps ps2 ret ret2 as as2 zf))))
            (let-match many (notail $ unify-canon m ents se rules tb n fc h h2 ch ch2 d sh sh2 phase) (MkWalk _ _ _ _ _ _ o1 st1 p))
            (let-match many (notail $ after-list m ents se rules tb n fc _ l o1 st1 as as2 as as2 (canonical-fix-list rules as cas) (canonical-fix-list rules as2 cas2) (prove-subterm as l) d sas sas2 (zip-samelen as as2 (Nil _) eqs z3) (PInner)) (MkAfterList _ _ _ _ _ _ _ o2 st2 q))
            (MkWalk _ _ _ _ _ _ o2 st2 (UCValApp m ents rules h h2 ps ps2 ret ret2 as as2 o1 o2 (zip-samelen as as2 (Nil _) eqs z3) p q)))
          ((TUniv)
            (let-match many (nat-dec (Succ (Succ (Succ (Zero)))) b) (NDSame _)
              ((NDDiff _ _ nq) (MkWalk _ _ _ _ _ _ (UFail) (StFail _ _ _) (UCMismatch m ents rules l r (Succ (Succ (Succ (Zero)))) b nl nr (ShUniv) sb nq))))
            (let-match erased sb (ShUniv))
            (match many r _ ((TUniv) (MkWalk _ _ _ _ _ _ (UOk rules) (StSame _ _ _) (UCUniv m ents rules)))))
          ((TFn lv ps rs)
            (let-match many (nat-dec (Succ (Succ (Succ (Succ (Zero))))) b) (NDSame _)
              ((NDDiff _ _ nq) (MkWalk _ _ _ _ _ _ (UFail) (StFail _ _ _) (UCMismatch m ents rules l r (Succ (Succ (Succ (Succ (Zero))))) b nl nr (ShFn lv ps rs) sb nq))))
            (let-match erased sb (ShFn _ _ _))
            (let-match many r (TFn lv2 ps2 rs2))
            (let-match erased cl (CnFn _ _ _ _ clv cps crs))
            (let-match erased cr (CnFn _ _ _ _ clv2 cps2 crs2))
            (let-match erased sl (ScFn _ _ _ _ _ e3 _ slv sps srs))
            (let-match erased sr (ScFn _ _ _ _ _ e4 _ slv2 sps2 srs2))
            (let-match many (zip-tele-dec rs rs2 (Nil _)) (ZTDOk _ _ _ e1 z1)
              ((ZTDFail _ _ _ zf) (MkWalk _ _ _ _ _ _ (UFail) (StFail _ _ _) (UCFnRets m ents rules lv lv2 ps ps2 rs rs2 zf))))
            (let-match many (zip-tele-dec ps ps2 (Nil _)) (ZTDOk _ _ _ e2 z2)
              ((ZTDFail _ _ _ zf) (MkWalk _ _ _ _ _ _ (UFail) (StFail _ _ _) (UCFnParams m ents rules lv lv2 ps ps2 rs rs2 (zip-tele-same rs rs2 (Nil _) e1 z1) zf))))
            (let-match many (notail $ unify-canon m ents se rules tb n fc lv lv2 clv clv2 d slv slv2 phase) (MkWalk _ _ _ _ _ _ o1 st1 p))
            (let-match many (notail $ after-tele m ents se rules tb n fc _ l o1 st1 ps ps2 ps ps2 (canonical-fix-tele rules ps cps) (canonical-fix-tele rules ps2 cps2) (prove-subterm ps l) d _ _ sps sps2 (zip-tele-same ps ps2 (Nil _) e2 z2) (PInner)) (MkAfterTele _ _ _ _ _ _ _ o2 st2 q))
            (let-match erased (stele-same-out ents d ps ps2 e3 e4 (zip-tele-same ps ps2 (Nil _) e2 z2) sps sps2) (Refl _ _))
            (let-match many (notail $ after-tele m ents se rules tb n fc _ l o2 st2 rs rs2 rs rs2 (canonical-fix-tele rules rs crs) (canonical-fix-tele rules rs2 crs2) (prove-subterm rs l) e3 _ _ srs srs2 (zip-tele-same rs rs2 (Nil _) e1 z1) (PInner)) (MkAfterTele _ _ _ _ _ _ _ o3 st3 q2))
            (MkWalk _ _ _ _ _ _ o3 st3 (UCFn m ents rules lv lv2 ps ps2 rs rs2 o1 o2 o3 (zip-tele-same rs rs2 (Nil _) e1 z1) (zip-tele-same ps ps2 (Nil _) e2 z2) p q q2)))
          ((TTyCtor ps)
            (let-match many (nat-dec (Succ (Succ (Succ (Succ (Succ (Zero)))))) b) (NDSame _)
              ((NDDiff _ _ nq) (MkWalk _ _ _ _ _ _ (UFail) (StFail _ _ _) (UCMismatch m ents rules l r (Succ (Succ (Succ (Succ (Succ (Zero)))))) b nl nr (ShTyCtor ps) sb nq))))
            (let-match erased sb (ShTyCtor _))
            (let-match many r (TTyCtor ps2))
            (let-match erased cl (CnTyCtor _ _ cps))
            (let-match erased cr (CnTyCtor _ _ cps2))
            (let-match erased sl (ScTyCtor _ _ _ _ sps))
            (let-match erased sr (ScTyCtor _ _ _ _ sps2))
            (let-match many (zip-tele-dec ps ps2 (Nil _)) (ZTDOk _ _ _ e1 z1)
              ((ZTDFail _ _ _ zf) (MkWalk _ _ _ _ _ _ (UFail) (StFail _ _ _) (UCTyCtorFail m ents rules ps ps2 zf))))
            (let-match many (notail $ unify-tele m ents se rules tb n fc ps ps2 ps ps2 (canonical-fix-tele rules ps cps) (canonical-fix-tele rules ps2 cps2) d _ _ sps sps2 (zip-tele-same ps ps2 (Nil _) e1 z1) phase) (MkTele _ _ _ _ _ _ o1 st1 p))
            (MkWalk _ _ _ _ _ _ o1 st1 (UCTyCtor m ents rules ps ps2 o1 (zip-tele-same ps ps2 (Nil _) e1 z1) p)))
          ((TValCtor ps ret)
            (let-match many (nat-dec (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))) b) (NDSame _)
              ((NDDiff _ _ nq) (MkWalk _ _ _ _ _ _ (UFail) (StFail _ _ _) (UCMismatch m ents rules l r (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))) b nl nr (ShValCtor ps ret) sb nq))))
            (let-match erased sb (ShValCtor _ _))
            (let-match many r (TValCtor ps2 ret2))
            (let-match erased cl (CnValCtor _ _ _ cps cret))
            (let-match erased cr (CnValCtor _ _ _ cps2 cret2))
            (let-match erased sl (ScValCtor _ _ _ _ e3 sps sret))
            (let-match erased sr (ScValCtor _ _ _ _ e4 sps2 sret2))
            (let-match many (zip-tele-dec ps ps2 (Nil _)) (ZTDOk _ _ _ e1 z1)
              ((ZTDFail _ _ _ zf) (MkWalk _ _ _ _ _ _ (UFail) (StFail _ _ _) (UCValCtorFail m ents rules ps ps2 ret ret2 zf))))
            (let-match many (notail $ unify-tele m ents se rules tb n fc ps ps2 ps ps2 (canonical-fix-tele rules ps cps) (canonical-fix-tele rules ps2 cps2) d _ _ sps sps2 (zip-tele-same ps ps2 (Nil _) e1 z1) phase) (MkTele _ _ _ _ _ _ o1 st1 p))
            (let-match erased (stele-same-out ents d ps ps2 e3 e4 (zip-tele-same ps ps2 (Nil _) e1 z1) sps sps2) (Refl _ _))
            (let-match many (notail $ after m ents se rules tb n fc _ l o1 st1 ret ret2 (prove-subterm ret l) cret cret2 e3 sret sret2 (PInner)) (MkAfter _ _ _ _ _ _ _ o2 st2 q))
            (MkWalk _ _ _ _ _ _ o2 st2 (UCValCtor m ents rules ps ps2 ret ret2 o1 o2 (zip-tele-same ps ps2 (Nil _) e1 z1) p q)))))))
  ; a variable against a term: the rule's types unified next, under the bound the mint lowered to
  ((many ref-step : (erased (Mode) m) (many (List (Ent)) ents) (erased (ScopedEnts ents ents) se) (many (List (Rule)) rules) (many (Table ents rules) _tb) (subterm erased (Nat) n) (erased (FreeCount ents rules n) _fc)
      (subterm erased (Term) l) (erased (Term) r) (many (RefStep m n ents rules l r) rs) (subterm erased (PInner) is _phase) -> (many (WalkDec m n ents rules l r) w))
    (let-match many rs (RefMint _ _ _ _ _ x t ty tt tb1 n1 lt fc1 s k sd nt ent nd asg tp sty stt)
      ((RefDone _ _ _ _ _ _ o st p) (MkWalk _ _ _ _ _ _ o st p)))
    (let ((many ty2) (erased cty)) (canon-tb ents (Cons _ (MkRule x t) rules) tb1 ty))
    (let ((many tt2) (erased ctt)) (canon-tb ents (Cons _ (MkRule x t) rules) tb1 tt))
    (let-match many (notail $ unify-canon (Force) ents se (Cons _ (MkRule x t) rules) tb1 (subterm (lt-subterm n1 n lt)) n1 fc1 ty2 tt2 (canon-canonical _ ty ty2 cty) (canon-canonical _ tt tt2 ctt)
                  (Zero) (canon-scoped ents _ (Zero) ty ty2 (table-scoped ents _ tb1) sty cty) (canon-scoped ents _ (Zero) tt tt2 (table-scoped ents _ tb1) stt ctt) (POuter (PInner))) (MkWalk _ _ _ _ _ _ o2 st2 q))
    (MkWalk _ _ _ _ _ _ o2 (step-seq n ents rules _ (StMint _ _ _ (Cons _ (MkRule x t) rules) tb1 n1 lt fc1) n1 (lt-weaken n1 n lt) o2 st2)
          (UCAssign ents rules s x t l r ty k tt ty2 tt2 o2 sd nt ent nd asg tp cty ctt q)))
  ; the parts of an application, originals beside their canonical forms under the current table
  ((many unify-list : (many (Mode) m) (many (List (Ent)) ents) (erased (ScopedEnts ents ents) se) (many (List (Rule)) rules) (many (Table ents rules) tb) (subterm erased (Nat) n) (erased (FreeCount ents rules n) fc)
      (many (List (Term)) as) (many (List (Term)) bs) (subterm many (List (Term)) as2) (many (List (Term)) bs2) (erased (CanonList rules as as2) ca) (erased (CanonList rules bs bs2) cb)
      (erased (Nat) d) (erased (ScopedList ents d as) sa) (erased (ScopedList ents d bs) sb) (erased (SameLen as bs) sl) (subterm many (POuter (PInner)) is phase) ->
      (many (ListDec m n ents rules as bs) w))
    (let-match many as2 (Cons _ a2 rest2)
      ((Nil _)
        (let-match erased ca (CanNil _))
        (let-match erased sl (SLNil))
        (match erased cb _ ((CanNil _) (MkList _ _ _ _ _ _ (UOk rules) (StSame _ _ _) (ULNil m ents rules))))))
    (let-match erased ca (CanCons _ _ _ _ _ pa qa))
    (let-match erased sl (SLCons _ _ _ _ sl2))
    (let-match erased cb (CanCons _ _ _ _ _ pb qb))
    (let-match many as (Cons _ a rest))
    (let-match many bs (Cons _ b brest))
    (let-match many bs2 (Cons _ b2 brest2m))
    (let-match erased sa (ScCons _ _ _ _ sa1 sa2))
    (let-match erased sb (ScCons _ _ _ _ sb1 sb2))
    (let-match many (notail $ unify-canon m ents se rules tb n fc a2 b2 (canon-canonical rules a a2 pa) (canon-canonical rules b b2 pb)
        d (canon-scoped ents rules d a a2 (table-scoped ents rules tb) sa1 pa) (canon-scoped ents rules d b b2 (table-scoped ents rules tb) sb1 pb) phase) (MkWalk _ _ _ _ _ _ o1 st1 p))
    (let-match many (notail $ after-list m ents se rules tb n fc _ as2 o1 st1 rest brest rest2 brest2m qa qb (prove-subterm rest2 as2) d sa2 sb2 sl2 (PInner)) (MkAfterList _ _ _ _ _ _ _ o2 st2 q))
    (MkList _ _ _ _ _ _ o2 st2 (ULCons m ents rules a b a2 b2 rest brest o1 o2 pa pb p q)))
  ((many unify-tele : (many (Mode) m) (many (List (Ent)) ents) (erased (ScopedEnts ents ents) se) (many (List (Rule)) rules) (many (Table ents rules) tb) (subterm erased (Nat) n) (erased (FreeCount ents rules n) fc)
      (many (List (Entry)) es) (many (List (Entry)) fs) (subterm many (List (Entry)) es2) (many (List (Entry)) fs2) (erased (CanonTele rules es es2) ce) (erased (CanonTele rules fs fs2) cf)
      (erased (Nat) d) (erased (Nat) out) (erased (Nat) out2) (erased (ScopedTele ents d es out) se2) (erased (ScopedTele ents d fs out2) sf) (erased (SameTele es fs) st) (subterm many (POuter (PInner)) is phase) ->
      (many (TeleDec m n ents rules es fs) w))
    (let-match many es2 (Cons _ e2 rest2)
      ((Nil _)
        (let-match erased ce (CanTNil _))
        (let-match erased st (STNil))
        (match erased cf _ ((CanTNil _) (MkTele _ _ _ _ _ _ (UOk rules) (StSame _ _ _) (UTNil m ents rules))))))
    (let-match many e2 (MkEntry s i t2))
    (let-match erased ce (CanTCons _ _ _ _ _ _ _ pt qt))
    (let-match erased st (STCons _ _ _ _ _ _ st2))
    (let-match erased cf (CanTCons _ _ _ _ _ _ _ pu qu))
    (let-match many es (Cons _ e rest))
    (let-match many e (MkEntry _ _ t))
    (let-match many fs (Cons _ f frest))
    (let-match many f (MkEntry _ _ u))
    (let-match many fs2 (Cons _ f2 frest2m))
    (let-match many f2 (MkEntry _ _ u2))
    (let-match erased se2 (ScTCons _ _ _ _ _ _ _ st1 sc2))
    (let-match erased sf (ScTCons _ _ _ _ _ _ _ su1 sd2))
    (let-match many (notail $ unify-canon m ents se rules tb n fc t2 u2 (canon-canonical rules t t2 pt) (canon-canonical rules u u2 pu)
        d (canon-scoped ents rules d t t2 (table-scoped ents rules tb) st1 pt) (canon-scoped ents rules d u u2 (table-scoped ents rules tb) su1 pu) phase) (MkWalk _ _ _ _ _ _ o1 stp1 p))
    (let-match many (notail $ after-tele m ents se rules tb n fc _ es2 o1 stp1 rest frest rest2 frest2m qt qu (prove-subterm rest2 es2) (Succ d) _ _ sc2 sd2 st2 (PInner)) (MkAfterTele _ _ _ _ _ _ _ o2 stp2 q))
    (MkTele _ _ _ _ _ _ o2 stp2 (UTCons m ents rules s i t u t2 u2 rest frest o1 o2 pt pu p q)))
  ; After a step: nothing when it left no table; the parts as they are when it left the table alone; the
  ; parts read again through the new table when it minted, the bound being lower then.
  ((many after : (many (Mode) m) (many (List (Ent)) ents) (erased (ScopedEnts ents ents) se) (many (List (Rule)) rules) (many (Table ents rules) tb) (subterm erased (Nat) n) (erased (FreeCount ents rules n) fc)
      (erased Type P) (subterm erased P parent) (erased (UOut) o1) (many (UStep n ents rules o1) st1) (many (Term) t) (many (Term) u) (erased (Subterm (Term) t P parent) subs)
      (erased (Canonical rules t) ct) (erased (Canonical rules u) cu) (erased (Nat) d) (erased (Scoped ents d t) st) (erased (Scoped ents d u) su) (subterm erased (PInner) is _phase) ->
      (many (AfterDec m n ents rules o1 t u) w))
    (match many st1 _
      ((StFail _ _ _) (MkAfter _ _ _ _ _ _ _ (UFail) (StFail _ _ _) (AFail m ents rules t u)))
      ((StSame _ _ _)
        (let-match many (notail $ unify-canon m ents se rules tb n fc (subterm subs) t u ct cu d st su (POuter (PInner))) (MkWalk _ _ _ _ _ _ o stp q))
        (MkAfter _ _ _ _ _ _ _ o stp (AOk m ents rules rules t u t u o (canonical-fix rules t ct) (canonical-fix rules u cu) q)))
      ((StMint _ _ _ rules1 tb1 n1 lt fc1)
        (let ((many t2) (erased c1)) (canon-tb ents rules1 tb1 t))
        (let ((many u2) (erased c2)) (canon-tb ents rules1 tb1 u))
        (let-match many (notail $ unify-canon m ents se rules1 tb1 (subterm (lt-subterm n1 n lt)) n1 fc1 t2 u2 (canon-canonical rules1 t t2 c1) (canon-canonical rules1 u u2 c2)
            d (canon-scoped ents rules1 d t t2 (table-scoped ents rules1 tb1) st c1) (canon-scoped ents rules1 d u u2 (table-scoped ents rules1 tb1) su c2) (POuter (PInner))) (MkWalk _ _ _ _ _ _ o stp2 q))
        (MkAfter _ _ _ _ _ _ _ o (step-seq n ents rules rules1 st1 n1 (lt-weaken n1 n lt) o stp2) (AOk m ents rules rules1 t u t2 u2 o c1 c2 q)))))
  ((many after-list : (many (Mode) m) (many (List (Ent)) ents) (erased (ScopedEnts ents ents) se) (many (List (Rule)) rules) (many (Table ents rules) tb) (subterm erased (Nat) n) (erased (FreeCount ents rules n) fc)
      (erased Type P) (subterm erased P parent) (erased (UOut) o1) (many (UStep n ents rules o1) st1) (many (List (Term)) as) (many (List (Term)) bs) (many (List (Term)) as2) (many (List (Term)) bs2)
      (erased (CanonList rules as as2) ca) (erased (CanonList rules bs bs2) cb) (erased (Subterm (List (Term)) as2 P parent) subs) (erased (Nat) d) (erased (ScopedList ents d as) sa) (erased (ScopedList ents d bs) sb) (erased (SameLen as bs) sl)
      (subterm erased (PInner) is _phase) -> (many (AfterListDec m n ents rules o1 as bs) w))
    (match many st1 _
      ((StFail _ _ _) (MkAfterList _ _ _ _ _ _ _ (UFail) (StFail _ _ _) (ALFail m ents rules as bs)))
      ((StSame _ _ _)
        (let-match many (notail $ unify-list m ents se rules tb n fc as bs (subterm subs) as2 bs2 ca cb d sa sb sl (POuter (PInner))) (MkList _ _ _ _ _ _ o stp q))
        (MkAfterList _ _ _ _ _ _ _ o stp (ALOk m ents rules rules as bs o q)))
      ((StMint _ _ _ rules1 tb1 n1 lt fc1)
        (let ((many as3) (erased c1)) (canon-list-tb ents rules1 tb1 as))
        (let ((many bs3) (erased c2)) (canon-list-tb ents rules1 tb1 bs))
        (let-match many (notail $ unify-list m ents se rules1 tb1 (subterm (lt-subterm n1 n lt)) n1 fc1 as bs as3 bs3 c1 c2 d sa sb sl (POuter (PInner))) (MkList _ _ _ _ _ _ o stp2 q))
        (MkAfterList _ _ _ _ _ _ _ o (step-seq n ents rules rules1 st1 n1 (lt-weaken n1 n lt) o stp2) (ALOk m ents rules rules1 as bs o q)))))
  ((many after-tele : (many (Mode) m) (many (List (Ent)) ents) (erased (ScopedEnts ents ents) se) (many (List (Rule)) rules) (many (Table ents rules) tb) (subterm erased (Nat) n) (erased (FreeCount ents rules n) fc)
      (erased Type P) (subterm erased P parent) (erased (UOut) o1) (many (UStep n ents rules o1) st1) (many (List (Entry)) es) (many (List (Entry)) fs) (many (List (Entry)) es2) (many (List (Entry)) fs2)
      (erased (CanonTele rules es es2) ce) (erased (CanonTele rules fs fs2) cf) (erased (Subterm (List (Entry)) es2 P parent) subs) (erased (Nat) d) (erased (Nat) out) (erased (Nat) out2) (erased (ScopedTele ents d es out) se2) (erased (ScopedTele ents d fs out2) sf) (erased (SameTele es fs) st)
      (subterm erased (PInner) is _phase) -> (many (AfterTeleDec m n ents rules o1 es fs) w))
    (match many st1 _
      ((StFail _ _ _) (MkAfterTele _ _ _ _ _ _ _ (UFail) (StFail _ _ _) (ATFail m ents rules es fs)))
      ((StSame _ _ _)
        (let-match many (notail $ unify-tele m ents se rules tb n fc es fs (subterm subs) es2 fs2 ce cf d _ _ se2 sf st (POuter (PInner))) (MkTele _ _ _ _ _ _ o stp q))
        (MkAfterTele _ _ _ _ _ _ _ o stp (ATOk m ents rules rules es fs o q)))
      ((StMint _ _ _ rules1 tb1 n1 lt fc1)
        (let ((many es3) (erased c1)) (canon-tele-tb ents rules1 tb1 es))
        (let ((many fs3) (erased c2)) (canon-tele-tb ents rules1 tb1 fs))
        (let-match many (notail $ unify-tele m ents se rules1 tb1 (subterm (lt-subterm n1 n lt)) n1 fc1 es fs es3 fs3 c1 c2 d _ _ se2 sf st (POuter (PInner))) (MkTele _ _ _ _ _ _ o stp2 q))
        (MkAfterTele _ _ _ _ _ _ _ o (step-seq n ents rules rules1 st1 n1 (lt-weaken n1 n lt) o stp2) (ATOk m ents rules rules1 es fs o q))))))

; ---- A list of equations as written: the entry point, deriving [Unify] through [conv]. The outcome's
; table comes with its ranking and scope when there is one.
(def-adts
  ((ScopedEqs : ((List (Ent)) ents) ((List (Eqn)) eqs) -> Type)
    enum
    (many SqNil : (erased (List (Ent)) ents) -> (ScopedEqs ents (Nil (Eqn))))
    (many SqCons : (erased (List (Ent)) ents) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Scoped ents (Zero) l) p) (erased (Scoped ents (Zero) r) q) (erased (ScopedEqs ents rest) s)
       -> (ScopedEqs ents (Cons (Eqn) (MkEqn l r) rest))))
  ((OutTable : ((List (Ent)) ents) ((UOut) o) -> Type)
    enum
    (many OTOk : (erased (List (Ent)) ents) (many (List (Rule)) rules) (many (Table ents rules) tb) -> (OutTable ents (UOk rules)))
    (many OTFail : (erased (List (Ent)) ents) -> (OutTable ents (UFail)))))

(def-adts $ (EqsDec : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((List (Eqn)) eqs) -> Type)
  enum
  (many MkEqs : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Eqn)) eqs) (many (UOut) o) (many (OutTable ents o) ot) (erased (Unify m ents rules eqs o) p) -> (EqsDec m ents rules eqs)))
(def-fns _ $ (many unify-eqs : (many (Mode) m) (many (List (Ent)) ents) (erased (ScopedEnts ents ents) se) (many (List (Rule)) rules) (many (Table ents rules) tb) (erased (Nat) n) (erased (FreeCount ents rules n) fc)
    (subterm many (List (Eqn)) eqs) (erased (ScopedEqs ents eqs) sq) -> (many (EqsDec m ents rules eqs) r))
  (let-match many eqs (Cons _ eqn rest) ((Nil _) (MkEqs _ _ _ _ (UOk rules) (OTOk _ rules tb) (UDone m ents rules))))
  (let-match many eqn (MkEqn l r))
  (let-match erased sq (SqCons _ _ _ _ sl sr sq2))
  (let ((many l2) (erased cl)) (canon-tb ents rules tb l))
  (let ((many r2) (erased cr)) (canon-tb ents rules tb r))
  (let-match many (unify-canon m ents se rules tb n fc l2 r2 (canon-canonical rules l l2 cl) (canon-canonical rules r r2 cr) (Zero) (canon-scoped ents rules (Zero) l l2 (table-scoped ents rules tb) sl cl) (canon-scoped ents rules (Zero) r r2 (table-scoped ents rules tb) sr cr) (POuter (PInner))) (MkWalk _ _ _ _ _ _ _ st1 d))
  (match many st1 _
        ((StFail _ _ _) (MkEqs _ _ _ _ (UFail) (OTFail _) (conv m ents rules l r l2 r2 (UFail) rest (UFail) d cl cr (ContFail m ents rest))))
        ((StSame _ _ _)
          (match many (notail $ unify-eqs m ents se rules tb n fc rest sq2) _
            ((MkEqs _ _ _ _ o ot q) (MkEqs _ _ _ _ o ot (conv m ents rules l r l2 r2 (UOk rules) rest o d cl cr (ContOk m ents rules rest o q))))))
        ((StMint _ _ _ rules1 tb1 n1 _ fc1)
          (match many (notail $ unify-eqs m ents se rules1 tb1 n1 fc1 rest sq2) _
            ((MkEqs _ _ _ _ o ot q) (MkEqs _ _ _ _ o ot (conv m ents rules l r l2 r2 (UOk rules1) rest o d cl cr (ContOk m ents rules1 rest o q))))))))
(MkUnit)
