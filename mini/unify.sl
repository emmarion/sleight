; mini/unify.sl -- forced unification (DESIGN.md section 18) for the minimal language, as a walk over a list
; of equations: each is canonicalized, then identical atoms and binders are dropped, applications and
; formers are split into the equations of their parts, and a variable meets a term either by taking it as
; its rule ([Force], entering a branch) or by failing ([Check], comparing two types for identity, section 5).
; The three contradictions are the [UFail] rules: an unassignable term (the occurs check and a telescope
; binder), two rigid atoms, and two shapes that differ. One session's proposal.

(def-adts $ Mode : -> Type
  enum
  (many Force : -> (Mode))
  (many Check : -> (Mode)))

(def-adts $ Eqn : -> Type
  enum
  (many MkEqn : (many (Term) l) (many (Term) r) -> (Eqn)))

; Pairing two argument lists, or two telescopes with their marks, in front of the equations still to do.
(def-adts
  (Zip : ((List (Term)) as) ((List (Term)) bs) ((List (Eqn)) rest) ((List (Eqn)) out) -> Type
    enum
    (many ZipNil : (erased (List (Eqn)) rest) -> (Zip (Nil (Term)) (Nil (Term)) rest rest))
    (many ZipCons : (erased (Term) a) (erased (Term) b) (erased (List (Term)) as) (erased (List (Term)) bs) (erased (List (Eqn)) rest) (erased (List (Eqn)) out)
       (erased (Zip as bs rest out) p) -> (Zip (Cons (Term) a as) (Cons (Term) b bs) rest (Cons (Eqn) (MkEqn a b) out))))
  (ZipFail : ((List (Term)) as) ((List (Term)) bs) -> Type
    enum
    (many ZFNilCons : (erased (Term) b) (erased (List (Term)) bs) -> (ZipFail (Nil (Term)) (Cons (Term) b bs)))
    (many ZFConsNil : (erased (Term) a) (erased (List (Term)) as) -> (ZipFail (Cons (Term) a as) (Nil (Term))))
    (many ZFCons : (erased (Term) a) (erased (Term) b) (erased (List (Term)) as) (erased (List (Term)) bs) (erased (ZipFail as bs) p) ->
       (ZipFail (Cons (Term) a as) (Cons (Term) b bs))))
  (ZipTele : ((List (Entry)) es) ((List (Entry)) fs) ((List (Eqn)) rest) ((List (Eqn)) out) -> Type
    enum
    (many ZTNil : (erased (List (Eqn)) rest) -> (ZipTele (Nil (Entry)) (Nil (Entry)) rest rest))
    (many ZTCons : (erased (Bool) s) (erased (Bool) i) (erased (Term) t) (erased (Term) u) (erased (List (Entry)) es) (erased (List (Entry)) fs)
       (erased (List (Eqn)) rest) (erased (List (Eqn)) out) (erased (ZipTele es fs rest out) p) ->
       (ZipTele (Cons (Entry) (MkEntry s i t) es) (Cons (Entry) (MkEntry s i u) fs) rest (Cons (Eqn) (MkEqn t u) out))))
  (ZipTeleFail : ((List (Entry)) es) ((List (Entry)) fs) -> Type
    enum
    (many ZTFNilCons : (erased (Entry) f) (erased (List (Entry)) fs) -> (ZipTeleFail (Nil (Entry)) (Cons (Entry) f fs)))
    (many ZTFConsNil : (erased (Entry) e) (erased (List (Entry)) es) -> (ZipTeleFail (Cons (Entry) e es) (Nil (Entry))))
    (many ZTFSub : (erased (Bool) s) (erased (Bool) s2) (erased (Bool) i) (erased (Bool) i2) (erased (Term) t) (erased (Term) u) (erased (List (Entry)) es) (erased (List (Entry)) fs)
       (erased (BoolNeq s s2) n) -> (ZipTeleFail (Cons (Entry) (MkEntry s i t) es) (Cons (Entry) (MkEntry s2 i2 u) fs)))
    (many ZTFIs : (erased (Bool) s) (erased (Bool) s2) (erased (Bool) i) (erased (Bool) i2) (erased (Term) t) (erased (Term) u) (erased (List (Entry)) es) (erased (List (Entry)) fs)
       (erased (BoolNeq i i2) n) -> (ZipTeleFail (Cons (Entry) (MkEntry s i t) es) (Cons (Entry) (MkEntry s2 i2 u) fs)))
    (many ZTFCons : (erased (Entry) e) (erased (Entry) f) (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (ZipTeleFail es fs) p) ->
       (ZipTeleFail (Cons (Entry) e es) (Cons (Entry) f fs))))
  (ZipDec : ((List (Term)) as) ((List (Term)) bs) ((List (Eqn)) rest) -> Type
    enum
    (many ZDOk : (erased (List (Term)) as) (erased (List (Term)) bs) (erased (List (Eqn)) rest) (many (List (Eqn)) out) (erased (Zip as bs rest out) p) -> (ZipDec as bs rest))
    (many ZDFail : (erased (List (Term)) as) (erased (List (Term)) bs) (erased (List (Eqn)) rest) (erased (ZipFail as bs) p) -> (ZipDec as bs rest)))
  (ZipTeleDec : ((List (Entry)) es) ((List (Entry)) fs) ((List (Eqn)) rest) -> Type
    enum
    (many ZTDOk : (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (List (Eqn)) rest) (many (List (Eqn)) out) (erased (ZipTele es fs rest out) p) -> (ZipTeleDec es fs rest))
    (many ZTDFail : (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (List (Eqn)) rest) (erased (ZipTeleFail es fs) p) -> (ZipTeleDec es fs rest))))

(def-fns _ $ many zip-dec : (subterm many (List (Term)) as) (many (List (Term)) bs) (many (List (Eqn)) rest) -> (many (ZipDec as bs rest) r)
  (match many as _
    ((Nil a)
      (match many bs _
        ((Nil b) (ZDOk _ _ _ rest $ ZipNil rest))
        ((Cons b y ys) (ZDFail _ _ _ $ ZFNilCons y ys))))
    ((Cons a x xs)
      (match many bs _
        ((Nil b) (ZDFail _ _ _ $ ZFConsNil x xs))
        ((Cons b y ys)
          (match many (zip-dec xs ys rest) _
            ((ZDOk c d e out p) (ZDOk _ _ _ (Cons _ (MkEqn x y) out) $ ZipCons x y xs ys rest out p))
            ((ZDFail c d e p) (ZDFail _ _ _ $ ZFCons x y xs ys p))))))))

(def-fns _ $ many zip-tele-dec : (subterm many (List (Entry)) es) (many (List (Entry)) fs) (many (List (Eqn)) rest) -> (many (ZipTeleDec es fs rest) r)
  (match many es _
    ((Nil a)
      (match many fs _
        ((Nil b) (ZTDOk _ _ _ rest $ ZTNil rest))
        ((Cons b f fs2) (ZTDFail _ _ _ $ ZTFNilCons f fs2))))
    ((Cons a e es2)
      (match many fs _
        ((Nil b) (ZTDFail _ _ _ $ ZTFConsNil e es2))
        ((Cons b f fs2)
          (match many e _
            ((MkEntry s i t)
              (match many f _
                ((MkEntry s2 i2 u)
                  (match many (bool-dec s s2) _
                    ((BDDiff c d n) (ZTDFail _ _ _ $ ZTFSub s s2 i i2 t u es2 fs2 n))
                    ((BDSame c)
                      (match many (bool-dec i i2) _
                        ((BDDiff d g n) (ZTDFail _ _ _ $ ZTFIs s s i i2 t u es2 fs2 n))
                        ((BDSame d)
                          (match many (zip-tele-dec es2 fs2 rest) _
                            ((ZTDOk g h k out p) (ZTDOk _ _ _ (Cons _ (MkEqn t u) out) $ ZTCons s i t u es2 fs2 rest out p))
                            ((ZTDFail g h k p) (ZTDFail _ _ _ $ ZTFCons (MkEntry s i t) (MkEntry s i u) es2 fs2 p))))))))))))))))

; A term's shape as a code, so that two canonical terms of different shapes are told apart by one rule.
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

(def-adts $ UOut : -> Type
  enum
  (many UOk : (many (List (Rule)) rules) -> (UOut))
  (many UFail : -> (UOut)))

(def-adts
  (Unify : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((List (Eqn)) eqs) ((UOut) out) -> Type
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
    (many UApp : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest)
       (erased (Term) h) (erased (Term) h2) (erased (List (Term)) as) (erased (List (Term)) as2) (erased (List (Eqn)) eqs) (erased (UOut) out)
       (erased (Canon rules l (App h as)) cl) (erased (Canon rules r (App h2 as2)) cr) (erased (Zip as as2 rest eqs) z)
       (erased (Unify m ents rules (Cons (Eqn) (MkEqn h h2) eqs) out) p) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) out))
    (many UAppArity : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest)
       (erased (Term) h) (erased (Term) h2) (erased (List (Term)) as) (erased (List (Term)) as2)
       (erased (Canon rules l (App h as)) cl) (erased (Canon rules r (App h2 as2)) cr) (erased (ZipFail as as2) z) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    (many UUniv : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (UOut) out)
       (erased (Canon rules l (Univ)) cl) (erased (Canon rules r (Univ)) cr) (erased (Unify m ents rules rest out) p) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) out))
    (many UFn : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest)
       (erased (Term) lv) (erased (Term) lv2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (List (Entry)) rs) (erased (List (Entry)) rs2)
       (erased (List (Eqn)) e1) (erased (List (Eqn)) e2) (erased (UOut) out)
       (erased (Canon rules l (Fn lv ps rs)) cl) (erased (Canon rules r (Fn lv2 ps2 rs2)) cr) (erased (ZipTele rs rs2 rest e1) z1) (erased (ZipTele ps ps2 e1 e2) z2)
       (erased (Unify m ents rules (Cons (Eqn) (MkEqn lv lv2) e2) out) p) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) out))
    (many UFnParams : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest)
       (erased (Term) lv) (erased (Term) lv2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (List (Entry)) rs) (erased (List (Entry)) rs2)
       (erased (Canon rules l (Fn lv ps rs)) cl) (erased (Canon rules r (Fn lv2 ps2 rs2)) cr) (erased (ZipTeleFail ps ps2) z) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    (many UFnRets : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest)
       (erased (Term) lv) (erased (Term) lv2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (List (Entry)) rs) (erased (List (Entry)) rs2)
       (erased (Canon rules l (Fn lv ps rs)) cl) (erased (Canon rules r (Fn lv2 ps2 rs2)) cr) (erased (ZipTeleFail rs rs2) z) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    (many UTyCtor : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest)
       (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (List (Eqn)) e1) (erased (UOut) out)
       (erased (Canon rules l (TyCtor ps)) cl) (erased (Canon rules r (TyCtor ps2)) cr) (erased (ZipTele ps ps2 rest e1) z)
       (erased (Unify m ents rules e1 out) p) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) out))
    (many UTyCtorFail : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest)
       (erased (List (Entry)) ps) (erased (List (Entry)) ps2)
       (erased (Canon rules l (TyCtor ps)) cl) (erased (Canon rules r (TyCtor ps2)) cr) (erased (ZipTeleFail ps ps2) z) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    (many UValCtor : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest)
       (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (Term) ret) (erased (Term) ret2) (erased (List (Eqn)) e1) (erased (UOut) out)
       (erased (Canon rules l (ValCtor ps ret)) cl) (erased (Canon rules r (ValCtor ps2 ret2)) cr) (erased (ZipTele ps ps2 (Cons (Eqn) (MkEqn ret ret2) rest) e1) z)
       (erased (Unify m ents rules e1 out) p) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) out))
    (many UValCtorFail : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest)
       (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (Term) ret) (erased (Term) ret2)
       (erased (Canon rules l (ValCtor ps ret)) cl) (erased (Canon rules r (ValCtor ps2 ret2)) cr) (erased (ZipTeleFail ps ps2) z) -> (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    ; two shapes that differ, neither a variable
    (many UMismatch : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest)
       (erased (Term) l2) (erased (Term) r2) (erased (Nat) a) (erased (Nat) b)
       (erased (Canon rules l l2) cl) (erased (Canon rules r r2) cr) (erased (NonRef l2) nl) (erased (NonRef r2) nr) (erased (ShapeOf l2 a) sa) (erased (ShapeOf r2 b) sb) (erased (Neq a b) n) ->
       (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    ; a variable against a term: in [Check] mode a failure, in [Force] mode a rule if the term may be
    ; assigned and the variable is not rigid, in either order
    (many UCheckRef : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Nat) x) (erased (Term) t)
       (erased (Canon rules l (Ref x)) cl) (erased (Canon rules r t) cr) (erased (NonRef t) nt) -> (Unify (Check) ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    (many UCheckRefR : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Nat) x) (erased (Term) t)
       (erased (Canon rules l t) cl) (erased (Canon rules r (Ref x)) cr) (erased (NonRef t) nt) -> (Unify (Check) ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    (many UCheckRefRef : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Nat) x) (erased (Nat) y)
       (erased (Canon rules l (Ref x)) cl) (erased (Canon rules r (Ref y)) cr) (erased (Neq x y) n) -> (Unify (Check) ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    (many UAssign : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Nat) x) (erased (Term) t)
       (erased (Term) ty) (erased (Kind) k) (erased (UOut) out)
       (erased (Canon rules l (Ref x)) cl) (erased (Canon rules r t) cr) (erased (NonRef t) nt) (erased (EntOf ents x ty k) e) (erased (NotDecl k) nd) (erased (Assignable (Zero) x t) a)
       (erased (Unify (Force) ents (Cons (Rule) (MkRule x t) rules) rest out) p) -> (Unify (Force) ents rules (Cons (Eqn) (MkEqn l r) rest) out))
    (many UAssignR : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Nat) x) (erased (Term) t)
       (erased (Term) ty) (erased (Kind) k) (erased (UOut) out)
       (erased (Canon rules l t) cl) (erased (Canon rules r (Ref x)) cr) (erased (NonRef t) nt) (erased (EntOf ents x ty k) e) (erased (NotDecl k) nd) (erased (Assignable (Zero) x t) a)
       (erased (Unify (Force) ents (Cons (Rule) (MkRule x t) rules) rest out) p) -> (Unify (Force) ents rules (Cons (Eqn) (MkEqn l r) rest) out))
    (many UOccurs : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Nat) x) (erased (Term) t)
       (erased (Canon rules l (Ref x)) cl) (erased (Canon rules r t) cr) (erased (NonRef t) nt) (erased (Unassignable (Zero) x t) u) -> (Unify (Force) ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    (many UOccursR : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Nat) x) (erased (Term) t)
       (erased (Canon rules l t) cl) (erased (Canon rules r (Ref x)) cr) (erased (NonRef t) nt) (erased (Unassignable (Zero) x t) u) -> (Unify (Force) ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    (many URigid : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Nat) x) (erased (Term) t) (erased (Term) ty)
       (erased (Canon rules l (Ref x)) cl) (erased (Canon rules r t) cr) (erased (NonRef t) nt) (erased (EntOf ents x ty (KDecl)) e) -> (Unify (Force) ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    (many URigidR : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Nat) x) (erased (Term) t) (erased (Term) ty)
       (erased (Canon rules l t) cl) (erased (Canon rules r (Ref x)) cr) (erased (NonRef t) nt) (erased (EntOf ents x ty (KDecl)) e) -> (Unify (Force) ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    ; two distinct variables: the one that is not rigid, else the newer, becomes an alias of the other, and
    ; their types are equated next (section 18's signature check); two rigid ones contradict
    (many UAlias : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Nat) x) (erased (Nat) y)
       (erased (Term) tx) (erased (Term) ty) (erased (Kind) kx) (erased (Kind) ky) (erased (Nat) z) (erased (Nat) w) (erased (Term) tz) (erased (Term) tw) (erased (UOut) out)
       (erased (Canon rules l (Ref x)) cl) (erased (Canon rules r (Ref y)) cr) (erased (Neq x y) n) (erased (EntOf ents x tx kx) ex) (erased (EntOf ents y ty ky) ey)
       (erased (Orient x tx kx y ty ky z tz w tw) o)
       (erased (Unify (Force) ents (Cons (Rule) (MkRule z (Ref w)) rules) (Cons (Eqn) (MkEqn tz tw) rest) out) p) -> (Unify (Force) ents rules (Cons (Eqn) (MkEqn l r) rest) out))
    (many URigidRigid : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Nat) x) (erased (Nat) y) (erased (Term) tx) (erased (Term) ty)
       (erased (Canon rules l (Ref x)) cl) (erased (Canon rules r (Ref y)) cr) (erased (Neq x y) n) (erased (EntOf ents x tx (KDecl)) ex) (erased (EntOf ents y ty (KDecl)) ey) ->
       (Unify (Force) ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail))))
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
  (Oriented : ((Nat) x) ((Term) tx) ((Kind) kx) ((Nat) y) ((Term) ty) ((Kind) ky) -> Type
    enum
    (many OrSome : (erased (Nat) x) (erased (Term) tx) (erased (Kind) kx) (erased (Nat) y) (erased (Term) ty) (erased (Kind) ky)
       (many (Nat) z) (many (Term) tz) (many (Nat) w) (many (Term) tw) (erased (Orient x tx kx y ty ky z tz w tw) o) -> (Oriented x tx kx y ty ky))
    (many OrNone : (erased (Nat) x) (erased (Term) tx) (erased (Nat) y) (erased (Term) ty) -> (Oriented x tx (KDecl) y ty (KDecl)))
    (many OrStuck : (erased (Nat) x) (erased (Term) tx) (erased (Kind) kx) (erased (Nat) y) (erased (Term) ty) (erased (Kind) ky) -> (Oriented x tx kx y ty ky))))

(def-fns _ $ many orient-age : (many (Nat) x) (many (Term) tx) (many (Kind) kx) (erased (NotDecl kx) nx) (many (Nat) y) (many (Term) ty) (many (Kind) ky) (erased (NotDecl ky) ny) (erased (Neq x y) n) ->
      (many (Oriented x tx kx y ty ky) r)
    (match many (nat-cmp x y) _
      ((CLt a b c d lt) (OrSome _ _ _ _ _ _ y ty x tx $ OrNewerR x tx kx y ty ky nx ny lt))
      ((CEq a b c) (OrStuck _ _ _ _ _ _))
      ((CGt a b c d lt) (OrSome _ _ _ _ _ _ x tx y ty $ OrNewerL x tx kx y ty ky nx ny lt))))

(def-fns _ $ many orient-plain : (many (Nat) x) (many (Term) tx) (many (Kind) kx) (erased (NotDecl kx) nx) (many (Nat) y) (many (Term) ty) (many (Kind) ky) (erased (Neq x y) n) ->
      (many (Oriented x tx kx y ty ky) r)
    (match many ky _
      ((KDecl) (OrSome _ _ _ _ _ _ x tx y ty $ OrRigidR x tx kx y ty nx))
      ((KPlain) (orient-age x tx kx nx y ty (KPlain) (NDPlain) n))
      ((KLevel) (orient-age x tx kx nx y ty (KLevel) (NDLevel) n))))

(def-fns _ $ many orient : (many (Nat) x) (many (Term) tx) (many (Kind) kx) (many (Nat) y) (many (Term) ty) (many (Kind) ky) (erased (Neq x y) n) -> (many (Oriented x tx kx y ty ky) r)
    (match many kx _
      ((KDecl)
        (match many ky _
          ((KDecl) (OrNone x tx y ty))
          ((KPlain) (OrSome _ _ _ _ _ _ y ty x tx $ OrRigidL x tx y ty (KPlain) (NDPlain)))
          ((KLevel) (OrSome _ _ _ _ _ _ y ty x tx $ OrRigidL x tx y ty (KLevel) (NDLevel)))))
      ((KPlain) (orient-plain x tx (KPlain) (NDPlain) y ty ky n))
      ((KLevel) (orient-plain x tx (KLevel) (NDLevel) y ty ky n))))

(def-adts
  (Unified : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((List (Eqn)) eqs) -> Type
    enum
    (many MkUnified : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Eqn)) eqs) (many (UOut) out) (erased (Unify m ents rules eqs out) p) ->
       (Unified m ents rules eqs))
    (many UnifyStuck : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Eqn)) eqs) -> (Unified m ents rules eqs))))

; Two canonical shapes that differ, neither a variable.
(def-fns _ $ many mismatch : (many (Mode) m) (many (List (Ent)) ents) (many (List (Rule)) rules) (many (Term) l) (many (Term) r) (many (List (Eqn)) rest) (many (Term) l2) (many (Term) r2)
      (erased (Canon rules l l2) cl) (erased (Canon rules r r2) cr) (erased (NonRef l2) nl) (erased (NonRef r2) nr) -> (many (Unified m ents rules (Cons (Eqn) (MkEqn l r) rest)) u)
    (let (many a) (erased sa) (shape-of l2))
    (let (many b) (erased sb) (shape-of r2))
    (match many (nat-dec a b) _
      ((NDSame z) (UnifyStuck _ _ _ _))
      ((NDDiff z w n) (MkUnified _ _ _ _ (UFail) $ UMismatch m ents rules l r rest l2 r2 a b cl cr nl nr sa sb n))))

(def-fns _
  (many unify : (subterm many (Nat) fuel) (many (Mode) m) (many (List (Ent)) ents) (many (List (Rule)) rules) (many (List (Eqn)) eqs) -> (many (Unified m ents rules eqs) r)
    (match many fuel _
      ((Zero) (UnifyStuck _ _ _ _))
      ((Succ f)
        (match many eqs _
          ((Nil a) (MkUnified _ _ _ _ (UOk rules) $ UDone m ents rules))
          ((Cons a eqn rest)
            (match many eqn _
              ((MkEqn l r)
                (match many (canon f rules l) _
                  ((CanonStuck a1 b1) (UnifyStuck _ _ _ _))
                  ((MkCanoned a1 b1 l2 cl)
                    (match many (canon f rules r) _
                      ((CanonStuck a2 b2) (UnifyStuck _ _ _ _))
                      ((MkCanoned a2 b2 r2 cr)
                        (match many l2 _
                          ((Ref x)
                            (match many r2 _
                              ((Ref y) (unify-refs f m ents rules l r rest x y cl cr))
                              ((Bound k) (unify-ref f m ents rules l r rest x (Bound k) cl cr (NRBound k)))
                              ((App h as) (unify-ref f m ents rules l r rest x (App h as) cl cr (NRApp h as)))
                              ((Univ) (unify-ref f m ents rules l r rest x (Univ) cl cr (NRUniv)))
                              ((Fn lv ps rs) (unify-ref f m ents rules l r rest x (Fn lv ps rs) cl cr (NRFn lv ps rs)))
                              ((TyCtor ps) (unify-ref f m ents rules l r rest x (TyCtor ps) cl cr (NRTyCtor ps)))
                              ((ValCtor ps ret) (unify-ref f m ents rules l r rest x (ValCtor ps ret) cl cr (NRValCtor ps ret)))))
                          ((Bound j)
                            (match many r2 _
                              ((Ref y) (unify-ref-r f m ents rules l r rest y (Bound j) cl cr (NRBound j)))
                              ((Bound k)
                                (match many (nat-dec j k) _
                                  ((NDSame z)
                                    (match many (unify f m ents rules rest) _
                                      ((UnifyStuck a3 b3 c3 d3) (UnifyStuck _ _ _ _))
                                      ((MkUnified a3 b3 c3 d3 out p) (MkUnified _ _ _ _ out $ UBound m ents rules l r rest j out cl cr p))))
                                  ((NDDiff z w n) (MkUnified _ _ _ _ (UFail) $ UBoundNeq m ents rules l r rest j k cl cr n))))
                              ((App h as) (mismatch m ents rules l r rest (Bound j) (App h as) cl cr (NRBound j) (NRApp h as)))
                              ((Univ) (mismatch m ents rules l r rest (Bound j) (Univ) cl cr (NRBound j) (NRUniv)))
                              ((Fn lv ps rs) (mismatch m ents rules l r rest (Bound j) (Fn lv ps rs) cl cr (NRBound j) (NRFn lv ps rs)))
                              ((TyCtor ps) (mismatch m ents rules l r rest (Bound j) (TyCtor ps) cl cr (NRBound j) (NRTyCtor ps)))
                              ((ValCtor ps ret) (mismatch m ents rules l r rest (Bound j) (ValCtor ps ret) cl cr (NRBound j) (NRValCtor ps ret)))))
                          ((App h as)
                            (match many r2 _
                              ((Ref y) (unify-ref-r f m ents rules l r rest y (App h as) cl cr (NRApp h as)))
                              ((Bound k) (mismatch m ents rules l r rest (App h as) (Bound k) cl cr (NRApp h as) (NRBound k)))
                              ((App h2 as2)
                                (match many (zip-dec as as2 rest) _
                                  ((ZDFail a3 b3 c3 z) (MkUnified _ _ _ _ (UFail) $ UAppArity m ents rules l r rest h h2 as as2 cl cr z))
                                  ((ZDOk a3 b3 c3 eqs2 z)
                                    (match many (unify f m ents rules (Cons _ (MkEqn h h2) eqs2)) _
                                      ((UnifyStuck a4 b4 c4 d4) (UnifyStuck _ _ _ _))
                                      ((MkUnified a4 b4 c4 d4 out p) (MkUnified _ _ _ _ out $ UApp m ents rules l r rest h h2 as as2 eqs2 out cl cr z p))))))
                              ((Univ) (mismatch m ents rules l r rest (App h as) (Univ) cl cr (NRApp h as) (NRUniv)))
                              ((Fn lv ps rs) (mismatch m ents rules l r rest (App h as) (Fn lv ps rs) cl cr (NRApp h as) (NRFn lv ps rs)))
                              ((TyCtor ps) (mismatch m ents rules l r rest (App h as) (TyCtor ps) cl cr (NRApp h as) (NRTyCtor ps)))
                              ((ValCtor ps ret) (mismatch m ents rules l r rest (App h as) (ValCtor ps ret) cl cr (NRApp h as) (NRValCtor ps ret)))))
                          ((Univ)
                            (match many r2 _
                              ((Ref y) (unify-ref-r f m ents rules l r rest y (Univ) cl cr (NRUniv)))
                              ((Bound k) (mismatch m ents rules l r rest (Univ) (Bound k) cl cr (NRUniv) (NRBound k)))
                              ((App h2 as2) (mismatch m ents rules l r rest (Univ) (App h2 as2) cl cr (NRUniv) (NRApp h2 as2)))
                              ((Univ)
                                (match many (unify f m ents rules rest) _
                                  ((UnifyStuck a3 b3 c3 d3) (UnifyStuck _ _ _ _))
                                  ((MkUnified a3 b3 c3 d3 out p) (MkUnified _ _ _ _ out $ UUniv m ents rules l r rest out cl cr p))))
                              ((Fn lv ps rs) (mismatch m ents rules l r rest (Univ) (Fn lv ps rs) cl cr (NRUniv) (NRFn lv ps rs)))
                              ((TyCtor ps) (mismatch m ents rules l r rest (Univ) (TyCtor ps) cl cr (NRUniv) (NRTyCtor ps)))
                              ((ValCtor ps ret) (mismatch m ents rules l r rest (Univ) (ValCtor ps ret) cl cr (NRUniv) (NRValCtor ps ret)))))
                          ((Fn lv ps rs)
                            (match many r2 _
                              ((Ref y) (unify-ref-r f m ents rules l r rest y (Fn lv ps rs) cl cr (NRFn lv ps rs)))
                              ((Bound k) (mismatch m ents rules l r rest (Fn lv ps rs) (Bound k) cl cr (NRFn lv ps rs) (NRBound k)))
                              ((App h2 as2) (mismatch m ents rules l r rest (Fn lv ps rs) (App h2 as2) cl cr (NRFn lv ps rs) (NRApp h2 as2)))
                              ((Univ) (mismatch m ents rules l r rest (Fn lv ps rs) (Univ) cl cr (NRFn lv ps rs) (NRUniv)))
                              ((Fn lv2 ps2 rs2)
                                (match many (zip-tele-dec rs rs2 rest) _
                                  ((ZTDFail a3 b3 c3 z) (MkUnified _ _ _ _ (UFail) $ UFnRets m ents rules l r rest lv lv2 ps ps2 rs rs2 cl cr z))
                                  ((ZTDOk a3 b3 c3 e1 z1)
                                    (match many (zip-tele-dec ps ps2 e1) _
                                      ((ZTDFail a4 b4 c4 z) (MkUnified _ _ _ _ (UFail) $ UFnParams m ents rules l r rest lv lv2 ps ps2 rs rs2 cl cr z))
                                      ((ZTDOk a4 b4 c4 e2 z2)
                                        (match many (unify f m ents rules (Cons _ (MkEqn lv lv2) e2)) _
                                          ((UnifyStuck a5 b5 c5 d5) (UnifyStuck _ _ _ _))
                                          ((MkUnified a5 b5 c5 d5 out p) (MkUnified _ _ _ _ out $ UFn m ents rules l r rest lv lv2 ps ps2 rs rs2 e1 e2 out cl cr z1 z2 p))))))))
                              ((TyCtor ps2) (mismatch m ents rules l r rest (Fn lv ps rs) (TyCtor ps2) cl cr (NRFn lv ps rs) (NRTyCtor ps2)))
                              ((ValCtor ps2 ret) (mismatch m ents rules l r rest (Fn lv ps rs) (ValCtor ps2 ret) cl cr (NRFn lv ps rs) (NRValCtor ps2 ret)))))
                          ((TyCtor ps)
                            (match many r2 _
                              ((Ref y) (unify-ref-r f m ents rules l r rest y (TyCtor ps) cl cr (NRTyCtor ps)))
                              ((Bound k) (mismatch m ents rules l r rest (TyCtor ps) (Bound k) cl cr (NRTyCtor ps) (NRBound k)))
                              ((App h2 as2) (mismatch m ents rules l r rest (TyCtor ps) (App h2 as2) cl cr (NRTyCtor ps) (NRApp h2 as2)))
                              ((Univ) (mismatch m ents rules l r rest (TyCtor ps) (Univ) cl cr (NRTyCtor ps) (NRUniv)))
                              ((Fn lv2 ps2 rs2) (mismatch m ents rules l r rest (TyCtor ps) (Fn lv2 ps2 rs2) cl cr (NRTyCtor ps) (NRFn lv2 ps2 rs2)))
                              ((TyCtor ps2)
                                (match many (zip-tele-dec ps ps2 rest) _
                                  ((ZTDFail a3 b3 c3 z) (MkUnified _ _ _ _ (UFail) $ UTyCtorFail m ents rules l r rest ps ps2 cl cr z))
                                  ((ZTDOk a3 b3 c3 e1 z)
                                    (match many (unify f m ents rules e1) _
                                      ((UnifyStuck a5 b5 c5 d5) (UnifyStuck _ _ _ _))
                                      ((MkUnified a5 b5 c5 d5 out p) (MkUnified _ _ _ _ out $ UTyCtor m ents rules l r rest ps ps2 e1 out cl cr z p))))))
                              ((ValCtor ps2 ret) (mismatch m ents rules l r rest (TyCtor ps) (ValCtor ps2 ret) cl cr (NRTyCtor ps) (NRValCtor ps2 ret)))))
                          ((ValCtor ps ret)
                            (match many r2 _
                              ((Ref y) (unify-ref-r f m ents rules l r rest y (ValCtor ps ret) cl cr (NRValCtor ps ret)))
                              ((Bound k) (mismatch m ents rules l r rest (ValCtor ps ret) (Bound k) cl cr (NRValCtor ps ret) (NRBound k)))
                              ((App h2 as2) (mismatch m ents rules l r rest (ValCtor ps ret) (App h2 as2) cl cr (NRValCtor ps ret) (NRApp h2 as2)))
                              ((Univ) (mismatch m ents rules l r rest (ValCtor ps ret) (Univ) cl cr (NRValCtor ps ret) (NRUniv)))
                              ((Fn lv2 ps2 rs2) (mismatch m ents rules l r rest (ValCtor ps ret) (Fn lv2 ps2 rs2) cl cr (NRValCtor ps ret) (NRFn lv2 ps2 rs2)))
                              ((TyCtor ps2) (mismatch m ents rules l r rest (ValCtor ps ret) (TyCtor ps2) cl cr (NRValCtor ps ret) (NRTyCtor ps2)))
                              ((ValCtor ps2 ret2)
                                (match many (zip-tele-dec ps ps2 (Cons _ (MkEqn ret ret2) rest)) _
                                  ((ZTDFail a3 b3 c3 z) (MkUnified _ _ _ _ (UFail) $ UValCtorFail m ents rules l r rest ps ps2 ret ret2 cl cr z))
                                  ((ZTDOk a3 b3 c3 e1 z)
                                    (match many (unify f m ents rules e1) _
                                      ((UnifyStuck a5 b5 c5 d5) (UnifyStuck _ _ _ _))
                                      ((MkUnified a5 b5 c5 d5 out p) (MkUnified _ _ _ _ out $ UValCtor m ents rules l r rest ps ps2 ret ret2 e1 out cl cr z p))))))))))))))))))))
  ; a variable on the left against a term that is not one
  (many unify-ref : (subterm many (Nat) fuel) (many (Mode) m) (many (List (Ent)) ents) (many (List (Rule)) rules) (many (Term) l) (many (Term) r) (many (List (Eqn)) rest) (many (Nat) x) (many (Term) t)
      (erased (Canon rules l (Ref x)) cl) (erased (Canon rules r t) cr) (erased (NonRef t) nt) -> (many (Unified m ents rules (Cons (Eqn) (MkEqn l r) rest)) u)
    (match many fuel _
      ((Zero) (UnifyStuck _ _ _ _))
      ((Succ f)
    (match many m _
      ((Check) (MkUnified _ _ _ _ (UFail) $ UCheckRef ents rules l r rest x t cl cr nt))
      ((Force)
        (match many (ent-dec ents x) _
          ((EntMiss a b e) (UnifyStuck _ _ _ _))
          ((EntHit a b ty k e)
            (match many k _
              ((KDecl) (MkUnified _ _ _ _ (UFail) $ URigid ents rules l r rest x t ty cl cr nt e))
              ((KPlain) (assign f ents rules l r rest x t ty (KPlain) cl cr nt e (NDPlain)))
              ((KLevel) (assign f ents rules l r rest x t ty (KLevel) cl cr nt e (NDLevel)))))))))))
  (many assign : (subterm many (Nat) fuel) (many (List (Ent)) ents) (many (List (Rule)) rules) (many (Term) l) (many (Term) r) (many (List (Eqn)) rest) (many (Nat) x) (many (Term) t)
      (erased (Term) ty) (erased (Kind) k) (erased (Canon rules l (Ref x)) cl) (erased (Canon rules r t) cr) (erased (NonRef t) nt) (erased (EntOf ents x ty k) e) (erased (NotDecl k) nd) ->
      (many (Unified (Force) ents rules (Cons (Eqn) (MkEqn l r) rest)) u)
    (match many fuel _
      ((Zero) (UnifyStuck _ _ _ _))
      ((Succ f)
        (match many (assign-dec f (Zero) x t) _
          ((ADStuck a b c) (UnifyStuck _ _ _ _))
          ((ADNo a b c un) (MkUnified _ _ _ _ (UFail) $ UOccurs ents rules l r rest x t cl cr nt un))
          ((ADYes a b c ok)
            (match many (unify f (Force) ents (Cons _ (MkRule x t) rules) rest) _
              ((UnifyStuck a3 b3 c3 d3) (UnifyStuck _ _ _ _))
              ((MkUnified a3 b3 c3 d3 out p) (MkUnified _ _ _ _ out $ UAssign ents rules l r rest x t ty k out cl cr nt e nd ok p))))))))
  ; the same with the variable on the right
  (many unify-ref-r : (subterm many (Nat) fuel) (many (Mode) m) (many (List (Ent)) ents) (many (List (Rule)) rules) (many (Term) l) (many (Term) r) (many (List (Eqn)) rest) (many (Nat) x) (many (Term) t)
      (erased (Canon rules l t) cl) (erased (Canon rules r (Ref x)) cr) (erased (NonRef t) nt) -> (many (Unified m ents rules (Cons (Eqn) (MkEqn l r) rest)) u)
    (match many fuel _
      ((Zero) (UnifyStuck _ _ _ _))
      ((Succ f)
    (match many m _
      ((Check) (MkUnified _ _ _ _ (UFail) $ UCheckRefR ents rules l r rest x t cl cr nt))
      ((Force)
        (match many (ent-dec ents x) _
          ((EntMiss a b e) (UnifyStuck _ _ _ _))
          ((EntHit a b ty k e)
            (match many k _
              ((KDecl) (MkUnified _ _ _ _ (UFail) $ URigidR ents rules l r rest x t ty cl cr nt e))
              ((KPlain) (assign-r f ents rules l r rest x t ty (KPlain) cl cr nt e (NDPlain)))
              ((KLevel) (assign-r f ents rules l r rest x t ty (KLevel) cl cr nt e (NDLevel)))))))))))
  (many assign-r : (subterm many (Nat) fuel) (many (List (Ent)) ents) (many (List (Rule)) rules) (many (Term) l) (many (Term) r) (many (List (Eqn)) rest) (many (Nat) x) (many (Term) t)
      (erased (Term) ty) (erased (Kind) k) (erased (Canon rules l t) cl) (erased (Canon rules r (Ref x)) cr) (erased (NonRef t) nt) (erased (EntOf ents x ty k) e) (erased (NotDecl k) nd) ->
      (many (Unified (Force) ents rules (Cons (Eqn) (MkEqn l r) rest)) u)
    (match many fuel _
      ((Zero) (UnifyStuck _ _ _ _))
      ((Succ f)
        (match many (assign-dec f (Zero) x t) _
          ((ADStuck a b c) (UnifyStuck _ _ _ _))
          ((ADNo a b c un) (MkUnified _ _ _ _ (UFail) $ UOccursR ents rules l r rest x t cl cr nt un))
          ((ADYes a b c ok)
            (match many (unify f (Force) ents (Cons _ (MkRule x t) rules) rest) _
              ((UnifyStuck a3 b3 c3 d3) (UnifyStuck _ _ _ _))
              ((MkUnified a3 b3 c3 d3 out p) (MkUnified _ _ _ _ out $ UAssignR ents rules l r rest x t ty k out cl cr nt e nd ok p))))))))
  ; two variables
  (many unify-refs : (subterm many (Nat) fuel) (many (Mode) m) (many (List (Ent)) ents) (many (List (Rule)) rules) (many (Term) l) (many (Term) r) (many (List (Eqn)) rest) (many (Nat) x) (many (Nat) y)
      (erased (Canon rules l (Ref x)) cl) (erased (Canon rules r (Ref y)) cr) -> (many (Unified m ents rules (Cons (Eqn) (MkEqn l r) rest)) u)
    (match many fuel _
      ((Zero) (UnifyStuck _ _ _ _))
      ((Succ f)
        (match many (nat-dec x y) _
          ((NDSame z)
            (match many (unify f m ents rules rest) _
              ((UnifyStuck a3 b3 c3 d3) (UnifyStuck _ _ _ _))
              ((MkUnified a3 b3 c3 d3 out p) (MkUnified _ _ _ _ out $ USame m ents rules l r rest x out cl cr p))))
          ((NDDiff z w n)
            (match many m _
              ((Check) (MkUnified _ _ _ _ (UFail) $ UCheckRefRef ents rules l r rest x y cl cr n))
              ((Force)
                (match many (ent-dec ents x) _
                  ((EntMiss a b e) (UnifyStuck _ _ _ _))
                  ((EntHit a b tx kx ex)
                    (match many (ent-dec ents y) _
                      ((EntMiss a2 b2 e2) (UnifyStuck _ _ _ _))
                      ((EntHit a2 b2 ty ky ey)
                        (match many (orient x tx kx y ty ky n) _
                          ((OrStuck a3 b3 c3 d3 e3 g3) (UnifyStuck _ _ _ _))
                          ((OrNone a3 b3 c3 d3) (MkUnified _ _ _ _ (UFail) $ URigidRigid ents rules l r rest x y tx ty cl cr n ex ey))
                          ((OrSome a3 b3 c3 d3 e3 g3 z2 tz w tw o)
                            (match many (unify f (Force) ents (Cons _ (MkRule z2 (Ref w)) rules) (Cons _ (MkEqn tz tw) rest)) _
                              ((UnifyStuck a4 b4 c4 d4) (UnifyStuck _ _ _ _))
                              ((MkUnified a4 b4 c4 d4 out p)
                                (MkUnified _ _ _ _ out $ UAlias ents rules l r rest x y tx ty kx ky z2 w tz tw out cl cr n ex ey o p)))))))))))))))))

(MkUnit)
