; mini/unify.sl -- forced unification (DESIGN.md section 18) for the minimal language, as a walk over a list
; of equations: each is canonicalized, then identical atoms and binders are dropped, applications and
; formers are split into the equations of their parts, and a variable meets a term either by taking it as
; its rule ([Force], entering a branch) or by failing ([Check], comparing two types for identity, section 5).
; The three contradictions are the [UFail] rules: an unassignable term (the occurs check and a telescope
; binder), two rigid atoms, and two shapes that differ. The function that derives it walks the two terms of
; an equation nested rather than over the list, on a bound on the entries without a rule and then the term,
; and an erased lemma turns its walk into the derivation over the list. One session's proposal.

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

; Which side of an equation a variable sits on: [Sided s v t l r] reads the equation l = r, both sides
; canonical, as the variable v against the term t.
(def-adts
  (Side : -> Type
    enum
    (many SL : -> (Side))
    (many SR : -> (Side)))
  (Sided : ((Side) s) ((Term) v) ((Term) t) ((Term) l) ((Term) r) -> Type
    enum
    (many SidedL : (erased (Term) v) (erased (Term) t) -> (Sided (SL) v t v t))
    (many SidedR : (erased (Term) v) (erased (Term) t) -> (Sided (SR) v t t v))))

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
    ; a variable against a term that is not one, on either side: in [Check] mode a failure, in [Force] mode a
    ; rule if the term may be assigned and the variable is not rigid
    (many UCheckRef : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Side) s) (erased (Nat) x) (erased (Term) t) (erased (Term) l2) (erased (Term) r2)
       (erased (Canon rules l l2) cl) (erased (Canon rules r r2) cr) (erased (Sided s (Ref x) t l2 r2) sd) (erased (NonRef t) nt) -> (Unify (Check) ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    (many UAssign : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Side) s) (erased (Nat) x) (erased (Term) t) (erased (Term) l2) (erased (Term) r2)
       (erased (Term) ty) (erased (Kind) k) (erased (UOut) out)
       (erased (Canon rules l l2) cl) (erased (Canon rules r r2) cr) (erased (Sided s (Ref x) t l2 r2) sd) (erased (NonRef t) nt) (erased (EntOf ents x ty k) e) (erased (NotDecl k) nd) (erased (Assignable (Zero) x t) a)
       (erased (Unify (Force) ents (Cons (Rule) (MkRule x t) rules) rest out) p) -> (Unify (Force) ents rules (Cons (Eqn) (MkEqn l r) rest) out))
    (many UOccurs : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Side) s) (erased (Nat) x) (erased (Term) t) (erased (Term) l2) (erased (Term) r2)
       (erased (Canon rules l l2) cl) (erased (Canon rules r r2) cr) (erased (Sided s (Ref x) t l2 r2) sd) (erased (NonRef t) nt) (erased (Unassignable (Zero) x t) u) -> (Unify (Force) ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    (many URigid : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Side) s) (erased (Nat) x) (erased (Term) t) (erased (Term) l2) (erased (Term) r2) (erased (Term) ty)
       (erased (Canon rules l l2) cl) (erased (Canon rules r r2) cr) (erased (Sided s (Ref x) t l2 r2) sd) (erased (NonRef t) nt) (erased (EntOf ents x ty (KDecl)) e) -> (Unify (Force) ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
    (many UCheckRefRef : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Nat) x) (erased (Nat) y)
       (erased (Canon rules l (Ref x)) cl) (erased (Canon rules r (Ref y)) cr) (erased (Neq x y) n) -> (Unify (Check) ents rules (Cons (Eqn) (MkEqn l r) rest) (UFail)))
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
; ---- The function side. The walk over the two terms of one equation, nested: on canonical terms
; ([UnifyC]), on the parts of an application or former that are still to walk ([UnifyListC],
; [UnifyTeleC], each part read through the table when its turn comes, as the list above does), and what
; follows an outcome ([After]). [conv] below turns a walk into a derivation of [Unify].
(def-adts
  (SameLen : ((List (Term)) as) ((List (Term)) bs) -> Type
    enum
    (many SLNil : -> (SameLen (Nil (Term)) (Nil (Term))))
    (many SLCons : (erased (Term) a) (erased (Term) b) (erased (List (Term)) as) (erased (List (Term)) bs) (erased (SameLen as bs) p) -> (SameLen (Cons (Term) a as) (Cons (Term) b bs))))
  (SameTele : ((List (Entry)) es) ((List (Entry)) fs) -> Type
    enum
    (many STNil : -> (SameTele (Nil (Entry)) (Nil (Entry))))
    (many STCons : (erased (Bool) s) (erased (Bool) i) (erased (Term) t) (erased (Term) u) (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (SameTele es fs) p) ->
       (SameTele (Cons (Entry) (MkEntry s i t) es) (Cons (Entry) (MkEntry s i u) fs))))
  (UnifyC : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((Term) l) ((Term) r) ((UOut) out) -> Type
    enum
    (many UCSame : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) -> (UnifyC m ents rules (Ref x) (Ref x) (UOk rules)))
    (many UCBound : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) k) -> (UnifyC m ents rules (Bound k) (Bound k) (UOk rules)))
    (many UCBoundNeq : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) j) (erased (Nat) k) (erased (Neq j k) n) -> (UnifyC m ents rules (Bound j) (Bound k) (UFail)))
    (many UCUniv : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) -> (UnifyC m ents rules (Univ) (Univ) (UOk rules)))
    (many UCApp : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) h) (erased (Term) h2) (erased (List (Term)) as) (erased (List (Term)) as2) (erased (UOut) o1) (erased (UOut) out)
       (erased (SameLen as as2) sl) (erased (UnifyC m ents rules h h2 o1) p) (erased (AfterList m ents rules o1 as as2 out) q) -> (UnifyC m ents rules (App h as) (App h2 as2) out))
    (many UCAppArity : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) h) (erased (Term) h2) (erased (List (Term)) as) (erased (List (Term)) as2)
       (erased (ZipFail as as2) z) -> (UnifyC m ents rules (App h as) (App h2 as2) (UFail)))
    (many UCFn : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) lv) (erased (Term) lv2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2)
       (erased (List (Entry)) rs) (erased (List (Entry)) rs2) (erased (UOut) o1) (erased (UOut) o2) (erased (UOut) out)
       (erased (SameTele rs rs2) st1) (erased (SameTele ps ps2) st2) (erased (UnifyC m ents rules lv lv2 o1) p) (erased (AfterTele m ents rules o1 ps ps2 o2) q) (erased (AfterTele m ents rules o2 rs rs2 out) r) ->
       (UnifyC m ents rules (Fn lv ps rs) (Fn lv2 ps2 rs2) out))
    (many UCFnRets : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) lv) (erased (Term) lv2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2)
       (erased (List (Entry)) rs) (erased (List (Entry)) rs2) (erased (ZipTeleFail rs rs2) z) -> (UnifyC m ents rules (Fn lv ps rs) (Fn lv2 ps2 rs2) (UFail)))
    (many UCFnParams : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) lv) (erased (Term) lv2) (erased (List (Entry)) ps) (erased (List (Entry)) ps2)
       (erased (List (Entry)) rs) (erased (List (Entry)) rs2) (erased (SameTele rs rs2) st1) (erased (ZipTeleFail ps ps2) z) -> (UnifyC m ents rules (Fn lv ps rs) (Fn lv2 ps2 rs2) (UFail)))
    (many UCTyCtor : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (UOut) out)
       (erased (SameTele ps ps2) st) (erased (UnifyTeleC m ents rules ps ps2 out) p) -> (UnifyC m ents rules (TyCtor ps) (TyCtor ps2) out))
    (many UCTyCtorFail : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (ZipTeleFail ps ps2) z) ->
       (UnifyC m ents rules (TyCtor ps) (TyCtor ps2) (UFail)))
    (many UCValCtor : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (Term) ret) (erased (Term) ret2) (erased (UOut) o1) (erased (UOut) out)
       (erased (SameTele ps ps2) st) (erased (UnifyTeleC m ents rules ps ps2 o1) p) (erased (After m ents rules o1 ret ret2 out) q) -> (UnifyC m ents rules (ValCtor ps ret) (ValCtor ps2 ret2) out))
    (many UCValCtorFail : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Entry)) ps) (erased (List (Entry)) ps2) (erased (Term) ret) (erased (Term) ret2)
       (erased (ZipTeleFail ps ps2) z) -> (UnifyC m ents rules (ValCtor ps ret) (ValCtor ps2 ret2) (UFail)))
    (many UCMismatch : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (Nat) a) (erased (Nat) b)
       (erased (NonRef l) nl) (erased (NonRef r) nr) (erased (ShapeOf l a) sa) (erased (ShapeOf r b) sb) (erased (Neq a b) n) -> (UnifyC m ents rules l r (UFail)))
    (many UCCheckRef : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Side) s) (erased (Nat) x) (erased (Term) t) (erased (Term) l) (erased (Term) r)
       (erased (Sided s (Ref x) t l r) sd) (erased (NonRef t) nt) -> (UnifyC (Check) ents rules l r (UFail)))
    (many UCRigid : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Side) s) (erased (Nat) x) (erased (Term) t) (erased (Term) l) (erased (Term) r) (erased (Term) ty)
       (erased (Sided s (Ref x) t l r) sd) (erased (NonRef t) nt) (erased (EntOf ents x ty (KDecl)) e) -> (UnifyC (Force) ents rules l r (UFail)))
    (many UCOccurs : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Side) s) (erased (Nat) x) (erased (Term) t) (erased (Term) l) (erased (Term) r)
       (erased (Sided s (Ref x) t l r) sd) (erased (NonRef t) nt) (erased (Unassignable (Zero) x t) u) -> (UnifyC (Force) ents rules l r (UFail)))
    (many UCAssign : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Side) s) (erased (Nat) x) (erased (Term) t) (erased (Term) l) (erased (Term) r) (erased (Term) ty) (erased (Kind) k)
       (erased (Sided s (Ref x) t l r) sd) (erased (NonRef t) nt) (erased (EntOf ents x ty k) e) (erased (NotDecl k) nd) (erased (Assignable (Zero) x t) a) ->
       (UnifyC (Force) ents rules l r (UOk (Cons (Rule) (MkRule x t) rules))))
    (many UCCheckRefRef : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) (erased (Nat) y) (erased (Neq x y) n) -> (UnifyC (Check) ents rules (Ref x) (Ref y) (UFail)))
    (many UCRigidRigid : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) (erased (Nat) y) (erased (Term) tx) (erased (Term) ty)
       (erased (Neq x y) n) (erased (EntOf ents x tx (KDecl)) ex) (erased (EntOf ents y ty (KDecl)) ey) -> (UnifyC (Force) ents rules (Ref x) (Ref y) (UFail)))
    (many UCAlias : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) (erased (Nat) y) (erased (Term) tx) (erased (Kind) kx) (erased (Term) ty) (erased (Kind) ky)
       (erased (Nat) z) (erased (Term) tz) (erased (Nat) w) (erased (Term) tw) (erased (Term) tz2) (erased (Term) tw2) (erased (UOut) out)
       (erased (Neq x y) n) (erased (EntOf ents x tx kx) ex) (erased (EntOf ents y ty ky) ey) (erased (Orient x tx kx y ty ky z tz w tw) o)
       (erased (Canon (Cons (Rule) (MkRule z (Ref w)) rules) tz tz2) ctz) (erased (Canon (Cons (Rule) (MkRule z (Ref w)) rules) tw tw2) ctw)
       (erased (UnifyC (Force) ents (Cons (Rule) (MkRule z (Ref w)) rules) tz2 tw2 out) p) -> (UnifyC (Force) ents rules (Ref x) (Ref y) out)))
  (UnifyListC : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((List (Term)) as) ((List (Term)) bs) ((UOut) out) -> Type
    enum
    (many ULNil : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) -> (UnifyListC m ents rules (Nil (Term)) (Nil (Term)) (UOk rules)))
    (many ULCons : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) a) (erased (Term) b) (erased (Term) a2) (erased (Term) b2) (erased (List (Term)) as) (erased (List (Term)) bs)
       (erased (UOut) o1) (erased (UOut) out)
       (erased (Canon rules a a2) ca) (erased (Canon rules b b2) cb) (erased (UnifyC m ents rules a2 b2 o1) p) (erased (AfterList m ents rules o1 as bs out) q) ->
       (UnifyListC m ents rules (Cons (Term) a as) (Cons (Term) b bs) out)))
  (UnifyTeleC : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((List (Entry)) es) ((List (Entry)) fs) ((UOut) out) -> Type
    enum
    (many UTNil : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) -> (UnifyTeleC m ents rules (Nil (Entry)) (Nil (Entry)) (UOk rules)))
    (many UTCons : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Bool) s) (erased (Bool) i) (erased (Term) t) (erased (Term) u) (erased (Term) t2) (erased (Term) u2)
       (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (UOut) o1) (erased (UOut) out)
       (erased (Canon rules t t2) ct) (erased (Canon rules u u2) cu) (erased (UnifyC m ents rules t2 u2 o1) p) (erased (AfterTele m ents rules o1 es fs out) q) ->
       (UnifyTeleC m ents rules (Cons (Entry) (MkEntry s i t) es) (Cons (Entry) (MkEntry s i u) fs) out)))
  (After : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((UOut) o1) ((Term) t) ((Term) u) ((UOut) out) -> Type
    enum
    (many AFail : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) t) (erased (Term) u) -> (After m ents rules (UFail) t u (UFail)))
    (many AOk : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Rule)) rules1) (erased (Term) t) (erased (Term) u) (erased (Term) t2) (erased (Term) u2) (erased (UOut) out)
       (erased (Canon rules1 t t2) ct) (erased (Canon rules1 u u2) cu) (erased (UnifyC m ents rules1 t2 u2 out) p) -> (After m ents rules (UOk rules1) t u out)))
  (AfterList : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((UOut) o1) ((List (Term)) as) ((List (Term)) bs) ((UOut) out) -> Type
    enum
    (many ALFail : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Term)) as) (erased (List (Term)) bs) -> (AfterList m ents rules (UFail) as bs (UFail)))
    (many ALOk : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Rule)) rules1) (erased (List (Term)) as) (erased (List (Term)) bs) (erased (UOut) out)
       (erased (UnifyListC m ents rules1 as bs out) p) -> (AfterList m ents rules (UOk rules1) as bs out)))
  (AfterTele : ((Mode) m) ((List (Ent)) ents) ((List (Rule)) rules) ((UOut) o1) ((List (Entry)) es) ((List (Entry)) fs) ((UOut) out) -> Type
    enum
    (many ATFail : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Entry)) es) (erased (List (Entry)) fs) -> (AfterTele m ents rules (UFail) es fs (UFail)))
    (many ATOk : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Rule)) rules1) (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (UOut) out)
       (erased (UnifyTeleC m ents rules1 es fs out) p) -> (AfterTele m ents rules (UOk rules1) es fs out)))
  ; The derivation of the equations after an outcome: the rest under the table it left, or nothing.
  (Cont : ((Mode) m) ((List (Ent)) ents) ((UOut) o1) ((List (Eqn)) rest) ((UOut) out) -> Type
    enum
    (many ContOk : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules1) (erased (List (Eqn)) rest) (erased (UOut) out)
       (erased (Unify m ents rules1 rest out) p) -> (Cont m ents (UOk rules1) rest out))
    (many ContFail : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Eqn)) rest) -> (Cont m ents (UFail) rest (UFail)))))

; ---- From the walk to the derivation over the list of equations.
(def-fns _ $ erased zip-of-samelen : (erased (List (Term)) as) (erased (List (Term)) bs) (erased (List (Eqn)) rest) (subterm erased (SameLen as bs) sl) -> (erased (List (Eqn)) eqs) (erased (Zip as bs rest eqs) z)
  (match erased sl _
    ((SLNil) (values rest (ZipNil rest)))
    ((SLCons a b as2 bs2 p) (let (erased eqs) (erased z) (zip-of-samelen as2 bs2 rest p)) (values (Cons _ (MkEqn a b) eqs) (ZipCons a b as2 bs2 rest eqs z)))))

(def-fns _ $ erased zip-tele-of-same : (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (List (Eqn)) rest) (subterm erased (SameTele es fs) st) -> (erased (List (Eqn)) eqs) (erased (ZipTele es fs rest eqs) z)
  (match erased st _
    ((STNil) (values rest (ZTNil rest)))
    ((STCons s i t u es2 fs2 p) (let (erased eqs) (erased z) (zip-tele-of-same es2 fs2 rest p)) (values (Cons _ (MkEqn t u) eqs) (ZTCons s i t u es2 fs2 rest eqs z)))))

(def-fns _ $ erased zip-samelen : (erased (List (Term)) as) (erased (List (Term)) bs) (erased (List (Eqn)) rest) (erased (List (Eqn)) eqs) (subterm erased (Zip as bs rest eqs) z) -> (erased (SameLen as bs) sl)
  (match erased z _
    ((ZipNil r) (SLNil))
    ((ZipCons a b as2 bs2 r eqs2 p) (SLCons a b as2 bs2 (zip-samelen as2 bs2 rest eqs2 p)))))

(def-fns _ $ erased zip-tele-same : (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (List (Eqn)) rest) (erased (List (Eqn)) eqs) (subterm erased (ZipTele es fs rest eqs) z) -> (erased (SameTele es fs) st)
  (match erased z _
    ((ZTNil r) (STNil))
    ((ZTCons s i t u es2 fs2 r eqs2 p) (STCons s i t u es2 fs2 (zip-tele-same es2 fs2 rest eqs2 p)))))

(def-fns _
  (erased conv : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Term) l) (erased (Term) r) (erased (Term) l2) (erased (Term) r2) (erased (UOut) o1) (erased (List (Eqn)) rest) (erased (UOut) out)
      (subterm erased (UnifyC m ents rules l2 r2 o1) d) (erased (Canon rules l l2) cl) (erased (Canon rules r r2) cr) (erased (Cont m ents o1 rest out) k) -> (erased (Unify m ents rules (Cons (Eqn) (MkEqn l r) rest) out) u)
    (match erased d _
      ((UCSame a b c x) (match erased k _ ((ContOk a2 b2 d2 e2 g2 kk) (USame m ents rules l r rest x out cl cr kk))))
      ((UCBound a b c j) (match erased k _ ((ContOk a2 b2 d2 e2 g2 kk) (UBound m ents rules l r rest j out cl cr kk))))
      ((UCBoundNeq a b c j j2 n) (match erased k _ ((ContFail a2 b2 d2) (UBoundNeq m ents rules l r rest j j2 cl cr n))))
      ((UCUniv a b c) (match erased k _ ((ContOk a2 b2 d2 e2 g2 kk) (UUniv m ents rules l r rest out cl cr kk))))
      ((UCApp a b c h h2 as as2 o oo sl p q)
        (let (erased eqs) (erased z) (zip-of-samelen as as2 rest sl))
        (match erased (canon-canonical rules l l2 cl) _
          ((CnApp a3 h3 as3 ch cas)
            (match erased (canon-canonical rules r r2 cr) _
              ((CnApp a4 h4 as4 ch2 cas2)
                (UApp m ents rules l r rest h h2 as as2 eqs out cl cr z (conv m ents rules h h2 h h2 o eqs out p (canonical-fix rules h ch) (canonical-fix rules h2 ch2) (conv-after-list m ents rules o as as2 oo rest eqs out q z k))))))))
      ((UCAppArity a b c h h2 as as2 z) (match erased k _ ((ContFail a2 b2 d2) (UAppArity m ents rules l r rest h h2 as as2 cl cr z))))
      ((UCFn a b c lv lv2 ps ps2 rs rs2 o o2 oo st1 st2 p q rr)
        (let (erased e1) (erased z1) (zip-tele-of-same rs rs2 rest st1))
        (let (erased e2) (erased z2) (zip-tele-of-same ps ps2 e1 st2))
        (match erased (canon-canonical rules l l2 cl) _
          ((CnFn a3 l3 ps3 rs3 clv cps crs)
            (match erased (canon-canonical rules r r2 cr) _
              ((CnFn a4 l4 ps4 rs4 clv2 cps2 crs2)
                (UFn m ents rules l r rest lv lv2 ps ps2 rs rs2 e1 e2 out cl cr z1 z2
                  (conv m ents rules lv lv2 lv lv2 o e2 out p (canonical-fix rules lv clv) (canonical-fix rules lv2 clv2)
                    (conv-after-tele m ents rules o ps ps2 o2 e1 e2 out q z2 (conv-after-tele m ents rules o2 rs rs2 oo rest e1 out rr z1 k)))))))))
      ((UCFnRets a b c lv lv2 ps ps2 rs rs2 z) (match erased k _ ((ContFail a2 b2 d2) (UFnRets m ents rules l r rest lv lv2 ps ps2 rs rs2 cl cr z))))
      ((UCFnParams a b c lv lv2 ps ps2 rs rs2 st1 z) (match erased k _ ((ContFail a2 b2 d2) (UFnParams m ents rules l r rest lv lv2 ps ps2 rs rs2 cl cr z))))
      ((UCTyCtor a b c ps ps2 oo st p)
        (let (erased e1) (erased z) (zip-tele-of-same ps ps2 rest st))
        (UTyCtor m ents rules l r rest ps ps2 e1 out cl cr z (conv-tele m ents rules ps ps2 oo rest e1 out p z k)))
      ((UCTyCtorFail a b c ps ps2 z) (match erased k _ ((ContFail a2 b2 d2) (UTyCtorFail m ents rules l r rest ps ps2 cl cr z))))
      ((UCValCtor a b c ps ps2 ret ret2 o oo st p q)
        (let (erased e1) (erased z) (zip-tele-of-same ps ps2 (Cons _ (MkEqn ret ret2) rest) st))
        (UValCtor m ents rules l r rest ps ps2 ret ret2 e1 out cl cr z (conv-tele m ents rules ps ps2 o (Cons _ (MkEqn ret ret2) rest) e1 out p z (conv-after m ents rules o ret ret2 oo rest out q k))))
      ((UCValCtorFail a b c ps ps2 ret ret2 z) (match erased k _ ((ContFail a2 b2 d2) (UValCtorFail m ents rules l r rest ps ps2 ret ret2 cl cr z))))
      ((UCMismatch a b c l3 r3 sa0 sb0 nl nr sa sb n) (match erased k _ ((ContFail a2 b2 d2) (UMismatch m ents rules l r rest l2 r2 sa0 sb0 cl cr nl nr sa sb n))))
      ((UCCheckRef b c s x t l3 r3 sd nt) (match erased k _ ((ContFail a2 b2 d2) (UCheckRef ents rules l r rest s x t l2 r2 cl cr sd nt))))
      ((UCRigid b c s x t l3 r3 ty sd nt e) (match erased k _ ((ContFail a2 b2 d2) (URigid ents rules l r rest s x t l2 r2 ty cl cr sd nt e))))
      ((UCOccurs b c s x t l3 r3 sd nt un) (match erased k _ ((ContFail a2 b2 d2) (UOccurs ents rules l r rest s x t l2 r2 cl cr sd nt un))))
      ((UCAssign b c s x t l3 r3 ty kd sd nt e nd asg) (match erased k _ ((ContOk a2 b2 d2 e2 g2 kk) (UAssign ents rules l r rest s x t l2 r2 ty kd out cl cr sd nt e nd asg kk))))
      ((UCCheckRefRef b c x y n) (match erased k _ ((ContFail a2 b2 d2) (UCheckRefRef ents rules l r rest x y cl cr n))))
      ((UCRigidRigid b c x y tx ty n ex ey) (match erased k _ ((ContFail a2 b2 d2) (URigidRigid ents rules l r rest x y tx ty cl cr n ex ey))))
      ((UCAlias b c x y tx kx ty ky z tz w tw tz2 tw2 oo n ex ey o ctz ctw p)
        (UAlias ents rules l r rest x y tx ty kx ky z w tz tw out cl cr n ex ey o (conv (Force) ents (Cons _ (MkRule z (Ref w)) rules) tz tw tz2 tw2 oo rest out p ctz ctw k)))))
  (erased conv-list : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Term)) as) (erased (List (Term)) bs) (erased (UOut) o1) (erased (List (Eqn)) rest) (erased (List (Eqn)) eqs) (erased (UOut) out)
      (subterm erased (UnifyListC m ents rules as bs o1) d) (erased (Zip as bs rest eqs) z) (erased (Cont m ents o1 rest out) k) -> (erased (Unify m ents rules eqs out) u)
    (match erased d _
      ((ULNil a b c) (match erased z _ ((ZipNil r2) (match erased k _ ((ContOk a2 b2 d2 e2 g2 kk) kk)))))
      ((ULCons a b c a1 b1 a2 b2 as2 bs2 o oo ca cb p q)
        (match erased z _ ((ZipCons a3 b3 as3 bs3 r3 eqs2 z2) (conv m ents rules a1 b1 a2 b2 o eqs2 out p ca cb (conv-after-list m ents rules o as2 bs2 oo rest eqs2 out q z2 k)))))))
  (erased conv-tele : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (UOut) o1) (erased (List (Eqn)) rest) (erased (List (Eqn)) eqs) (erased (UOut) out)
      (subterm erased (UnifyTeleC m ents rules es fs o1) d) (erased (ZipTele es fs rest eqs) z) (erased (Cont m ents o1 rest out) k) -> (erased (Unify m ents rules eqs out) u)
    (match erased d _
      ((UTNil a b c) (match erased z _ ((ZTNil r2) (match erased k _ ((ContOk a2 b2 d2 e2 g2 kk) kk)))))
      ((UTCons a b c s i t u t2 u2 es2 fs2 o oo ct cu p q)
        (match erased z _ ((ZTCons s3 i3 t3 u3 es3 fs3 r3 eqs2 z2) (conv m ents rules t u t2 u2 o eqs2 out p ct cu (conv-after-tele m ents rules o es2 fs2 oo rest eqs2 out q z2 k)))))))
  (erased conv-after : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (UOut) o0) (erased (Term) t) (erased (Term) u) (erased (UOut) o1) (erased (List (Eqn)) rest) (erased (UOut) out)
      (subterm erased (After m ents rules o0 t u o1) d) (erased (Cont m ents o1 rest out) k) -> (erased (Cont m ents o0 (Cons (Eqn) (MkEqn t u) rest) out) c)
    (match erased d _
      ((AFail a b c t0 u0) (match erased k _ ((ContFail a2 b2 d2) (ContFail m ents (Cons _ (MkEqn t u) rest)))))
      ((AOk a b c rules1 t0 u0 t2 u2 oo ct cu p) (ContOk m ents rules1 (Cons _ (MkEqn t u) rest) out (conv m ents rules1 t u t2 u2 o1 rest out p ct cu k)))))
  (erased conv-after-list : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (UOut) o0) (erased (List (Term)) as) (erased (List (Term)) bs) (erased (UOut) o1) (erased (List (Eqn)) rest) (erased (List (Eqn)) eqs) (erased (UOut) out)
      (subterm erased (AfterList m ents rules o0 as bs o1) d) (erased (Zip as bs rest eqs) z) (erased (Cont m ents o1 rest out) k) -> (erased (Cont m ents o0 eqs out) c)
    (match erased d _
      ((ALFail a b c as0 bs0) (match erased k _ ((ContFail a2 b2 d2) (ContFail m ents eqs))))
      ((ALOk a b c rules1 as0 bs0 oo p) (ContOk m ents rules1 eqs out (conv-list m ents rules1 as bs o1 rest eqs out p z k)))))
  (erased conv-after-tele : (erased (Mode) m) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (UOut) o0) (erased (List (Entry)) es) (erased (List (Entry)) fs) (erased (UOut) o1) (erased (List (Eqn)) rest) (erased (List (Eqn)) eqs) (erased (UOut) out)
      (subterm erased (AfterTele m ents rules o0 es fs o1) d) (erased (ZipTele es fs rest eqs) z) (erased (Cont m ents o1 rest out) k) -> (erased (Cont m ents o0 eqs out) c)
    (match erased d _
      ((ATFail a b c es0 fs0) (match erased k _ ((ContFail a2 b2 d2) (ContFail m ents eqs))))
      ((ATOk a b c rules1 es0 fs0 oo p) (ContOk m ents rules1 eqs out (conv-tele m ents rules1 es fs o1 rest eqs out p z k))))))

; ---- The bound the walk lowers: at most [n] entries have no rule, and a mint for one that has none lowers
; it. A rule consed for such an entry leaves every other rule found.
(def-adts
  (FreeCount : ((List (Ent)) ents) ((List (Rule)) rules) ((Nat) n) -> Type
    enum
    (many FCNil : (erased (List (Rule)) rules) -> (FreeCount (Nil (Ent)) rules (Zero)))
    (many FCBound : (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (List (Ent)) rest) (erased (List (Rule)) rules) (erased (Term) r) (erased (Nat) n)
       (erased (RuleOf rules x r) p) (erased (FreeCount rest rules n) q) -> (FreeCount (Cons (Ent) (MkEnt x ty k) rest) rules n))
    (many FCFree : (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (List (Ent)) rest) (erased (List (Rule)) rules) (erased (Nat) n)
       (erased (FreeCount rest rules n) q) -> (FreeCount (Cons (Ent) (MkEnt x ty k) rest) rules (Succ n)))))

(def-fns _ $ many free-count : (subterm many (List (Ent)) ents) (many (List (Rule)) rules) -> (many (Nat) n) (erased (FreeCount ents rules n) p)
  (match many ents _
    ((Nil a) (values (Zero) (FCNil rules)))
    ((Cons a e rest)
      (match many e _
        ((MkEnt x ty k)
          (let (many n) (erased q) (free-count rest rules))
          (match many (rule-dec rules x) _
            ((RuleHit l y r p) (values n (FCBound x ty k rest rules r n p q)))
            ((RuleMiss l y p) (values (Succ n) (FCFree x ty k rest rules n q)))))))))

(def-fns _ $ erased rule-neq : (erased (List (Rule)) rules) (erased (Nat) y) (erased (Term) r) (erased (Nat) x) (subterm erased (RuleOf rules y r) p) (erased (NoRule rules x) q) -> (erased (Neq y x) n)
  (match erased p _
    ((RuleHere a b rest) (match erased q _ ((NoRuleCons c d e g n2 h) (neq-sym x y n2))))
    ((RuleThere a z b s rest n2 p2) (match erased q _ ((NoRuleCons c d e g n3 q2) (rule-neq rest y r x p2 q2))))))

(def-fns _ $ erased fc-cons : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) n) (erased (Nat) x) (erased (Term) t) (subterm erased (FreeCount ents rules n) fc) (erased (NoRule rules x) nr) ->
    (erased (FreeCount ents (Cons (Rule) (MkRule x t) rules) n) fc2)
  (match erased fc _
    ((FCNil a) (FCNil _))
    ((FCBound y ty k rest a r m p c) (FCBound y ty k rest _ r m (RuleThere y x r t rules (rule-neq rules y r x p nr) p) (fc-cons rest rules m x t c nr)))
    ((FCFree y ty k rest a m c) (FCFree y ty k rest _ m (fc-cons rest rules m x t c nr)))))

(def-fns _ $ erased assign-count : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) n) (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (Term) t)
    (erased (FreeCount ents rules n) fc) (subterm erased (EntOf ents x ty k) e) (erased (NoRule rules x) nr) ->
    (erased (Nat) m) (erased (Lt m n) lt) (erased (FreeCount ents (Cons (Rule) (MkRule x t) rules) m) fc2)
  (match erased e _
    ((EntHere a b c rest)
      (match erased fc _
        (absurd (FCBound x2 ty2 k2 rest2 a2 r m p c2) (rule-of-no-rule rules x r p nr))
        ((FCFree x2 ty2 k2 rest2 a2 m c2) (values m (lt-succ m) (FCBound x ty k rest _ t m (RuleHere x t rules) (fc-cons rest rules m x t c2 nr))))))
    ((EntThere a y b ty2 c k2 rest ne e2)
      (match erased fc _
        ((FCBound x2 ty3 k3 rest2 a2 r m p c2)
          (let (erased m2) (erased lt) (erased fc3) (assign-count rest rules m x ty k t c2 e2 nr))
          (values m2 lt (FCBound y ty2 k2 rest _ r m2 (RuleThere y x r t rules (rule-neq rules y r x p nr) p) fc3)))
        ((FCFree x2 ty3 k3 rest2 a2 m c2)
          (let (erased m2) (erased lt) (erased fc3) (assign-count rest rules m x ty k t c2 e2 nr))
          (values (Succ m2) (LtS m2 m lt) (FCFree y ty2 k2 rest _ m2 fc3)))))))

; ---- The table beside the rules: their ranking and their scope, kept through a unification mint by
; giving the new rule rank zero and every other rule one more; its canonical term has no ruled entry.
(def-adts
  (Table : ((List (Ent)) ents) ((List (Rule)) rules) -> Type
    enum
    (many MkTable : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (many (List (Nat)) ranks) (many (Nat) top) (erased (ValidFrom rules ranks rules ranks) v) (erased (AllLt ranks top) al)
       (erased (ScopedRules ents rules) sr) (erased (RulesPlain ents rules) rp) -> (Table ents rules)))
  (RulesPlain : ((List (Ent)) ents) ((List (Rule)) rules) -> Type
    enum
    (many RPNil : (erased (List (Ent)) ents) -> (RulesPlain ents (Nil (Rule))))
    (many RPCons : (erased (List (Ent)) ents) (erased (Nat) x) (erased (Term) t) (erased (List (Rule)) rest) (erased (Term) ty) (erased (Kind) k) (erased (EntOf ents x ty k) e) (erased (NotDecl k) nd)
       (erased (RulesPlain ents rest) q) -> (RulesPlain ents (Cons (Rule) (MkRule x t) rest))))
  (Shift : ((List (Nat)) ks) ((List (Nat)) ks2) -> Type
    enum
    (many ShNil : -> (Shift (Nil (Nat)) (Nil (Nat))))
    (many ShCons : (erased (Nat) k) (erased (List (Nat)) ks) (erased (List (Nat)) ks2) (erased (Shift ks ks2) p) -> (Shift (Cons (Nat) k ks) (Cons (Nat) (Succ k) ks2)))))

(def-fns _ $ many shift : (subterm many (List (Nat)) ks) -> (many (List (Nat)) ks2) (erased (Shift ks ks2) p)
  (match many ks _
    ((Nil a) (values (Nil _) (ShNil)))
    ((Cons a k rest) (let (many rest2) (erased p) (shift rest)) (values (Cons _ (Succ k) rest2) (ShCons k rest rest2 p)))))

(def-fns _ $ erased rule-rank-shift : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (List (Nat)) ranks2) (erased (Nat) z) (erased (Term) r) (erased (Nat) j)
    (subterm erased (RuleRank rules ranks z r j) p) (erased (Shift ranks ranks2) sh) -> (erased (RuleRank rules ranks2 z r (Succ j)) q)
  (match erased p _
    ((RRHere a b c rest ks) (match erased sh _ ((ShCons d e ks2 s2) (RRHere z r (Succ j) rest ks2))))
    ((RRThere a y b s c k2 rest ks n p2) (match erased sh _ ((ShCons d e ks2 s2) (RRThere z y r s (Succ j) (Succ k2) rest ks2 n (rule-rank-shift rest ks ks2 z r j p2 s2)))))))

(def-fns _ $ erased all-lt-shift : (erased (List (Nat)) ks) (erased (List (Nat)) ks2) (erased (Nat) top) (subterm erased (AllLt ks top) a) (erased (Shift ks ks2) sh) -> (erased (AllLt ks2 (Succ top)) b)
  (match erased a _
    ((ALNil c) (match erased sh _ ((ShNil) (ALNil (Succ top)))))
    ((ALCons k rest c lt q) (match erased sh _ ((ShCons d e ks3 s2) (ALCons (Succ k) ks3 (Succ top) (LtS k top lt) (all-lt-shift rest ks3 top q s2)))))))

(def-fns _
  (erased below-shift : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (List (Nat)) ranks2) (erased (Term) t) (erased (Nat) k) (erased (Nat) x) (erased (Term) s)
      (erased (NoRule rules x) nr) (erased (Shift ranks ranks2) sh) (subterm erased (Below rules ranks t k) b) -> (erased (Below (Cons (Rule) (MkRule x s) rules) (Cons (Nat) (Zero) ranks2) t (Succ k)) c)
    (match erased b _
      ((BlFree a c z d p)
        (match erased (nat-dec z x) _
          ((NDSame e) (BlRuled _ _ z (Succ k) s (Zero) (RRHere x s (Zero) rules ranks2) (LtZ k)))
          ((NDDiff e g n) (BlFree _ _ z (Succ k) (NoRuleCons z x s rules n p)))))
      ((BlRuled a c z d r j p lt) (BlRuled _ _ z (Succ k) r (Succ j) (RRThere z x r s (Succ j) (Zero) rules ranks2 (rule-neq rules z r x (rule-rank-of rules ranks z r j p) nr) (rule-rank-shift rules ranks ranks2 z r j p sh)) (LtS j k lt)))
      ((BlBound a c i d) (BlBound _ _ i (Succ k)))
      ((BlApp a c h as d p q) (BlApp _ _ h as (Succ k) (below-shift rules ranks ranks2 h k x s nr sh p) (below-shift-list rules ranks ranks2 as k x s nr sh q)))
      ((BlUniv a c d) (BlUniv _ _ (Succ k)))
      ((BlFn a c l ps rs d p q r) (BlFn _ _ l ps rs (Succ k) (below-shift rules ranks ranks2 l k x s nr sh p) (below-shift-tele rules ranks ranks2 ps k x s nr sh q) (below-shift-tele rules ranks ranks2 rs k x s nr sh r)))
      ((BlTyCtor a c ps d q) (BlTyCtor _ _ ps (Succ k) (below-shift-tele rules ranks ranks2 ps k x s nr sh q)))
      ((BlValCtor a c ps r d q p) (BlValCtor _ _ ps r (Succ k) (below-shift-tele rules ranks ranks2 ps k x s nr sh q) (below-shift rules ranks ranks2 r k x s nr sh p)))))
  (erased below-shift-list : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (List (Nat)) ranks2) (erased (List (Term)) ts) (erased (Nat) k) (erased (Nat) x) (erased (Term) s)
      (erased (NoRule rules x) nr) (erased (Shift ranks ranks2) sh) (subterm erased (BelowList rules ranks ts k) b) -> (erased (BelowList (Cons (Rule) (MkRule x s) rules) (Cons (Nat) (Zero) ranks2) ts (Succ k)) c)
    (match erased b _
      ((BlNil a c d) (BlNil _ _ (Succ k)))
      ((BlCons a c t ts2 d p q) (BlCons _ _ t ts2 (Succ k) (below-shift rules ranks ranks2 t k x s nr sh p) (below-shift-list rules ranks ranks2 ts2 k x s nr sh q)))))
  (erased below-shift-tele : (erased (List (Rule)) rules) (erased (List (Nat)) ranks) (erased (List (Nat)) ranks2) (erased (List (Entry)) es) (erased (Nat) k) (erased (Nat) x) (erased (Term) s)
      (erased (NoRule rules x) nr) (erased (Shift ranks ranks2) sh) (subterm erased (BelowTele rules ranks es k) b) -> (erased (BelowTele (Cons (Rule) (MkRule x s) rules) (Cons (Nat) (Zero) ranks2) es (Succ k)) c)
    (match erased b _
      ((BlTNil a c d) (BlTNil _ _ (Succ k)))
      ((BlTCons a c s0 i t es2 d p q) (BlTCons _ _ s0 i t es2 (Succ k) (below-shift rules ranks ranks2 t k x s nr sh p) (below-shift-tele rules ranks ranks2 es2 k x s nr sh q))))))

(def-fns _ $ erased valid-shift : (erased (List (Rule)) all) (erased (List (Nat)) ar) (erased (List (Nat)) ar2) (erased (List (Rule)) rs) (erased (List (Nat)) ks) (erased (List (Nat)) ks2) (erased (Nat) x) (erased (Term) s)
    (erased (NoRule all x) nr) (erased (Shift ar ar2) sha) (erased (Shift ks ks2) shk) (subterm erased (ValidFrom all ar rs ks) v) -> (erased (ValidFrom (Cons (Rule) (MkRule x s) all) (Cons (Nat) (Zero) ar2) rs ks2) w)
  (match erased v _
    ((VFNil a c) (match erased shk _ ((ShNil) (VFNil _ _))))
    ((VFCons a c y r k rs2 ks3 bl p) (match erased shk _ ((ShCons d e ks4 s2) (VFCons _ _ y r (Succ k) rs2 ks4 (below-shift all ar ar2 r k x s nr sha bl) (valid-shift all ar ar2 rs2 ks3 ks4 x s nr sha s2 p)))))))

; A canonical term the new entry does not occur in has no ruled entry under the new rule.
(def-fns _
  (erased below-zero : (erased (List (Rule)) rules) (erased (List (Nat)) ranks2) (erased (Nat) x) (erased (Term) s) (erased (Term) t) (erased (Nat) d)
      (erased (Assignable d x t) a) (subterm erased (Canonical rules t) c) -> (erased (Below (Cons (Rule) (MkRule x s) rules) ranks2 t (Zero)) b)
    (match erased c _
      ((CnRef e z p) (match erased a _ ((AsgRef d2 x2 z2 n) (BlFree _ _ z (Zero) (NoRuleCons z x s rules (neq-sym x z n) p)))))
      ((CnBound e k) (BlBound _ _ k (Zero)))
      ((CnApp e h as p q) (match erased a _ ((AsgApp d2 x2 h2 as2 pa qa) (BlApp _ _ h as (Zero) (below-zero rules ranks2 x s h d pa p) (below-zero-list rules ranks2 x s as d qa q)))))
      ((CnUniv e) (BlUniv _ _ (Zero)))
      ((CnFn e l ps rs p q r)
        (match erased a _ ((AsgFn d2 x2 l2 ps2 rs2 d1 d3 pa qa ra) (BlFn _ _ l ps rs (Zero) (below-zero rules ranks2 x s l d pa p) (below-zero-tele rules ranks2 x s ps d d1 qa q) (below-zero-tele rules ranks2 x s rs d1 d3 ra r)))))
      ((CnTyCtor e ps q) (match erased a _ ((AsgTyCtor d2 x2 ps2 d1 qa) (BlTyCtor _ _ ps (Zero) (below-zero-tele rules ranks2 x s ps d d1 qa q)))))
      ((CnValCtor e ps r q p) (match erased a _ ((AsgValCtor d2 x2 ps2 r2 d1 qa pa) (BlValCtor _ _ ps r (Zero) (below-zero-tele rules ranks2 x s ps d d1 qa q) (below-zero rules ranks2 x s r d1 pa p)))))))
  (erased below-zero-list : (erased (List (Rule)) rules) (erased (List (Nat)) ranks2) (erased (Nat) x) (erased (Term) s) (erased (List (Term)) ts) (erased (Nat) d)
      (erased (AssignableList d x ts) a) (subterm erased (CanonicalList rules ts) c) -> (erased (BelowList (Cons (Rule) (MkRule x s) rules) ranks2 ts (Zero)) b)
    (match erased c _
      ((CnNil e) (BlNil _ _ (Zero)))
      ((CnCons e t ts2 p q) (match erased a _ ((AsgCons d2 x2 t2 ts3 pa qa) (BlCons _ _ t ts2 (Zero) (below-zero rules ranks2 x s t d pa p) (below-zero-list rules ranks2 x s ts2 d qa q)))))))
  (erased below-zero-tele : (erased (List (Rule)) rules) (erased (List (Nat)) ranks2) (erased (Nat) x) (erased (Term) s) (erased (List (Entry)) es) (erased (Nat) d) (erased (Nat) out)
      (erased (AssignableTele d x es out) a) (subterm erased (CanonicalTele rules es) c) -> (erased (BelowTele (Cons (Rule) (MkRule x s) rules) ranks2 es (Zero)) b)
    (match erased c _
      ((CnTNil e) (BlTNil _ _ (Zero)))
      ((CnTCons e s0 i t es2 p q) (match erased a _ ((AsgTCons d2 x2 s1 i1 t2 es3 out2 pa qa) (BlTCons _ _ s0 i t es2 (Zero) (below-zero rules ranks2 x s t d pa p) (below-zero-tele rules ranks2 x s es2 (Succ d) out qa q))))))))

(def-fns _ $ many table-mint : (erased (List (Ent)) ents) (many (List (Rule)) rules) (many (Table ents rules) tb) (many (Nat) x) (many (Term) s) (erased (NoRule rules x) nr) (erased (Canonical rules s) cs)
    (erased (Assignable (Zero) x s) asg) (erased (Scoped ents s) ss) (erased (Term) ty) (erased (Kind) k) (erased (EntOf ents x ty k) e) (erased (NotDecl k) nd) -> (many (Table ents (Cons (Rule) (MkRule x s) rules)) tb2)
  (match many tb _
    ((MkTable a b ranks top v al sr rp)
      (let (many ranks2) (erased sh) (shift ranks))
      (MkTable _ _ (Cons _ (Zero) ranks2) (Succ top) (VFCons _ _ x s (Zero) rules ranks2 (below-zero rules (Cons _ (Zero) ranks2) x s s (Zero) asg cs) (valid-shift rules ranks ranks2 rules ranks ranks2 x s nr sh sh v))
        (ALCons (Zero) ranks2 (Succ top) (LtZ top) (all-lt-shift ranks ranks2 top al sh)) (SRCons _ x s rules ss sr) (RPCons _ x s rules ty k e nd rp)))))

; Canonicalization under a table.
(def-fns _ $ many canon-tb : (erased (List (Ent)) ents) (many (List (Rule)) rules) (many (Table ents rules) tb) (many (Term) t) -> (many (Term) u) (erased (Canon rules t u) p)
  (match many tb _ ((MkTable a b ranks top v al sr rp) (canon rules ranks v top t (below-all rules ranks top v al t)))))
(def-fns _ $ many canon-list-tb : (erased (List (Ent)) ents) (many (List (Rule)) rules) (many (Table ents rules) tb) (many (List (Term)) ts) -> (many (List (Term)) us) (erased (CanonList rules ts us) p)
  (match many tb _ ((MkTable a b ranks top v al sr rp) (canon-list rules ranks v top ts (below-all-list rules ranks top v al ts)))))
(def-fns _ $ many canon-tele-tb : (erased (List (Ent)) ents) (many (List (Rule)) rules) (many (Table ents rules) tb) (many (List (Entry)) es) -> (many (List (Entry)) fs) (erased (CanonTele rules es fs) p)
  (match many tb _ ((MkTable a b ranks top v al sr rp) (canon-tele rules ranks v top es (below-all-tele rules ranks top v al es)))))
(def-fns _ $ erased table-scoped : (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Table ents rules) tb) -> (erased (ScopedRules ents rules) sr)
  (match erased tb _ ((MkTable a b ranks top v al sr rp) sr)))

; ---- The walk. Each function answers the outcome with its derivation and a [Step]: the table unchanged,
; or a new table with the bound it lowered to, or no table. A third subterm argument, a phase, lets a
; function hand its own arguments to a helper (the second can only decrease when the first stays).
(def-adts
  (Step : ((Nat) n) ((List (Ent)) ents) ((List (Rule)) rules) ((UOut) o) -> Type
    enum
    (many StSame : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) -> (Step n ents rules (UOk rules)))
    (many StMint : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (many (List (Rule)) rules1) (many (Table ents rules1) tb1) (erased (Nat) n1) (erased (Lt n1 n) lt) (erased (FreeCount ents rules1 n1) fc) ->
       (Step n ents rules (UOk rules1)))
    (many StFail : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) -> (Step n ents rules (UFail))))
  (Phase : -> Type
    enum
    (many PInner : -> (Phase))
    (many POuter : (many (Phase) inner) -> (Phase)))
  (NonRefDec : ((Term) t) -> Type
    enum
    (many IsRef : (many (Nat) x) -> (NonRefDec (Ref x)))
    (many IsNonRef : (erased (Term) t) (erased (NonRef t) p) -> (NonRefDec t)))
  (Oriented : ((List (Ent)) ents) ((Nat) x) ((Term) tx) ((Kind) kx) ((Nat) y) ((Term) ty) ((Kind) ky) -> Type
    enum
    (many OrSome : (erased (List (Ent)) ents) (erased (Nat) x) (erased (Term) tx) (erased (Kind) kx) (erased (Nat) y) (erased (Term) ty) (erased (Kind) ky)
       (many (Nat) z) (many (Term) tz) (many (Nat) w) (many (Term) tw) (erased (Kind) kz) (erased (EntOf ents z tz kz) ez) (erased (NotDecl kz) nz) (erased (Orient x tx kx y ty ky z tz w tw) o) -> (Oriented ents x tx kx y ty ky))
    (many OrNone : (erased (List (Ent)) ents) (erased (Nat) x) (erased (Term) tx) (erased (Nat) y) (erased (Term) ty) -> (Oriented ents x tx (KDecl) y ty (KDecl)))))

(def-fns _ $ many step-seq : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (List (Rule)) rules1) (many (Step n ents rules (UOk rules1)) st1)
      (erased (Nat) n1) (erased (Lt n1 (Succ n)) le) (erased (UOut) o2) (many (Step n1 ents rules1 o2) st2) -> (many (Step n ents rules o2) st)
    (match many st2 _
      ((StSame a b c) st1)
      ((StMint a b c rules2 tb2 n2 lt2 fc2) (StMint _ _ _ rules2 tb2 n2 (lt-le-trans n2 n1 n lt2 le) fc2))
      ((StFail a b c) (StFail _ _ _))))

(def-fns _ $ many nonref-dec : (many (Term) t) -> (many (NonRefDec t) r)
  (match many t _
    ((Ref x) (IsRef x))
    ((Bound k) (IsNonRef _ (NRBound k)))
    ((App h as) (IsNonRef _ (NRApp h as)))
    ((Univ) (IsNonRef _ (NRUniv)))
    ((Fn l ps rs) (IsNonRef _ (NRFn l ps rs)))
    ((TyCtor ps) (IsNonRef _ (NRTyCtor ps)))
    ((ValCtor ps r) (IsNonRef _ (NRValCtor ps r)))))

(def-fns _ $ many orient-age : (erased (List (Ent)) ents) (many (Nat) x) (many (Term) tx) (many (Kind) kx) (erased (NotDecl kx) nx) (erased (EntOf ents x tx kx) ex)
      (many (Nat) y) (many (Term) ty) (many (Kind) ky) (erased (NotDecl ky) ny) (erased (EntOf ents y ty ky) ey) (erased (Neq x y) n) -> (many (Oriented ents x tx kx y ty ky) r)
    (match many (nat-cmp x y) _
      ((CLt a b c d lt) (OrSome _ _ _ _ _ _ _ y ty x tx ky ey ny (OrNewerR x tx kx y ty ky nx ny lt)))
      (absurd (CEq a b c) (neq-irrefl x n))
      ((CGt a b c d lt) (OrSome _ _ _ _ _ _ _ x tx y ty kx ex nx (OrNewerL x tx kx y ty ky nx ny lt)))))

(def-fns _ $ many orient-plain : (erased (List (Ent)) ents) (many (Nat) x) (many (Term) tx) (many (Kind) kx) (erased (NotDecl kx) nx) (erased (EntOf ents x tx kx) ex)
      (many (Nat) y) (many (Term) ty) (many (Kind) ky) (erased (EntOf ents y ty ky) ey) (erased (Neq x y) n) -> (many (Oriented ents x tx kx y ty ky) r)
    (match many ky _
      ((KDecl) (OrSome _ _ _ _ _ _ _ x tx y ty kx ex nx (OrRigidR x tx kx y ty nx)))
      ((KPlain) (orient-age ents x tx kx nx ex y ty (KPlain) (NDPlain) ey n))
      ((KLevel) (orient-age ents x tx kx nx ex y ty (KLevel) (NDLevel) ey n))))

(def-fns _ $ many orient : (erased (List (Ent)) ents) (many (Nat) x) (many (Term) tx) (many (Kind) kx) (erased (EntOf ents x tx kx) ex) (many (Nat) y) (many (Term) ty) (many (Kind) ky) (erased (EntOf ents y ty ky) ey)
      (erased (Neq x y) n) -> (many (Oriented ents x tx kx y ty ky) r)
    (match many kx _
      ((KDecl)
        (match many ky _
          ((KDecl) (OrNone _ x tx y ty))
          ((KPlain) (OrSome _ _ _ _ _ _ _ y ty x tx (KPlain) ey (NDPlain) (OrRigidL x tx y ty (KPlain) (NDPlain))))
          ((KLevel) (OrSome _ _ _ _ _ _ _ y ty x tx (KLevel) ey (NDLevel) (OrRigidL x tx y ty (KLevel) (NDLevel))))))
      ((KPlain) (orient-plain ents x tx (KPlain) (NDPlain) ex y ty ky ey n))
      ((KLevel) (orient-plain ents x tx (KLevel) (NDLevel) ex y ty ky ey n))))

; What an orientation says of the alias: the two are distinct and each is one of the two variables.
(def-fns _ $ erased orient-neq : (erased (Nat) x) (erased (Term) tx) (erased (Kind) kx) (erased (Nat) y) (erased (Term) ty) (erased (Kind) ky) (erased (Nat) z) (erased (Term) tz) (erased (Nat) w) (erased (Term) tw)
    (erased (Orient x tx kx y ty ky z tz w tw) o) (erased (Neq x y) n) -> (erased (Neq z w) m)
  (match erased o _
    ((OrRigidL a b c d e g) (neq-sym x y n))
    ((OrRigidR a b c d e g) n)
    ((OrNewerL a b c d e g h i lt) n)
    ((OrNewerR a b c d e g h i lt) (neq-sym x y n))))

(def-fns _ $ erased orient-free : (erased (List (Rule)) rules) (erased (Nat) x) (erased (Term) tx) (erased (Kind) kx) (erased (Nat) y) (erased (Term) ty) (erased (Kind) ky) (erased (Nat) z) (erased (Term) tz) (erased (Nat) w) (erased (Term) tw)
    (erased (Orient x tx kx y ty ky z tz w tw) o) (erased (NoRule rules x) nx) (erased (NoRule rules y) ny) -> (erased (NoRule rules z) nz) (erased (NoRule rules w) nw)
  (match erased o _
    ((OrRigidL a b c d e g) (values ny nx))
    ((OrRigidR a b c d e g) (values nx ny))
    ((OrNewerL a b c d e g h i lt) (values nx ny))
    ((OrNewerR a b c d e g h i lt) (values ny nx))))

(def-fns _ $ erased orient-has : (erased (List (Ent)) ents) (erased (Nat) x) (erased (Term) tx) (erased (Kind) kx) (erased (Nat) y) (erased (Term) ty) (erased (Kind) ky) (erased (Nat) z) (erased (Term) tz) (erased (Nat) w) (erased (Term) tw)
    (erased (Orient x tx kx y ty ky z tz w tw) o) (erased (HasEnt ents x) hx) (erased (HasEnt ents y) hy) -> (erased (HasEnt ents w) hw)
  (match erased o _
    ((OrRigidL a b c d e g) hx)
    ((OrRigidR a b c d e g) hy)
    ((OrNewerL a b c d e g h i lt) hy)
    ((OrNewerR a b c d e g h i lt) hx)))

(def-fns _ $ erased orient-scoped : (erased (List (Ent)) ents) (erased (Nat) x) (erased (Term) tx) (erased (Kind) kx) (erased (Nat) y) (erased (Term) ty) (erased (Kind) ky) (erased (Nat) z) (erased (Term) tz) (erased (Nat) w) (erased (Term) tw)
    (erased (Orient x tx kx y ty ky z tz w tw) o) (erased (Scoped ents tx) sx) (erased (Scoped ents ty) sy) -> (erased (Scoped ents tz) sz)
  (match erased o _
    ((OrRigidL a b c d e g) sy)
    ((OrRigidR a b c d e g) sx)
    ((OrNewerL a b c d e g h i lt) sx)
    ((OrNewerR a b c d e g h i lt) sy)))

(def-fns _ $ erased orient-scoped-w : (erased (List (Ent)) ents) (erased (Nat) x) (erased (Term) tx) (erased (Kind) kx) (erased (Nat) y) (erased (Term) ty) (erased (Kind) ky) (erased (Nat) z) (erased (Term) tz) (erased (Nat) w) (erased (Term) tw)
    (erased (Orient x tx kx y ty ky z tz w tw) o) (erased (Scoped ents tx) sx) (erased (Scoped ents ty) sy) -> (erased (Scoped ents tw) sw)
  (match erased o _
    ((OrRigidL a b c d e g) sx)
    ((OrRigidR a b c d e g) sy)
    ((OrNewerL a b c d e g h i lt) sy)
    ((OrNewerR a b c d e g h i lt) sx)))

; A variable against a term that is not one.
(def-fns _ $ many assign : (many (List (Ent)) ents) (many (List (Rule)) rules) (many (Table ents rules) tb) (erased (Nat) n) (erased (FreeCount ents rules n) fc) (many (Side) s) (many (Nat) x) (many (Term) t)
      (erased (Term) l) (erased (Term) r) (erased (Term) ty) (erased (Kind) k) (erased (Sided s (Ref x) t l r) sd) (erased (NonRef t) nt) (erased (EntOf ents x ty k) e) (erased (NotDecl k) nd)
      (erased (NoRule rules x) nx) (erased (Canonical rules t) ct) (erased (Scoped ents t) st) ->
      (erased (UOut) o) (many (Step n ents rules o) stp) (erased (UnifyC (Force) ents rules l r o) p)
    (match many (assign-dec (Zero) x t) _
      ((ADNo a2 b2 c2 un) (values (UFail) (StFail _ _ _) (UCOccurs ents rules s x t l r sd nt un)))
      ((ADYes a2 b2 c2 ok)
        (let (erased n1) (erased lt) (erased fc1) (assign-count ents rules n x ty k t fc e nx))
        (values (UOk (Cons _ (MkRule x t) rules)) (StMint _ _ _ (Cons _ (MkRule x t) rules) (table-mint ents rules tb x t nx ct ok st ty k e nd) n1 lt fc1) (UCAssign ents rules s x t l r ty k sd nt e nd ok)))))

(def-fns _ $ many unify-ref : (many (Mode) m) (many (List (Ent)) ents) (many (List (Rule)) rules) (many (Table ents rules) tb) (erased (Nat) n) (erased (FreeCount ents rules n) fc) (many (Side) s) (many (Nat) x) (many (Term) t)
      (erased (Term) l) (erased (Term) r) (erased (Sided s (Ref x) t l r) sd) (erased (NonRef t) nt) (erased (NoRule rules x) nx) (erased (HasEnt ents x) hx) (erased (Canonical rules t) ct) (erased (Scoped ents t) st) ->
      (erased (UOut) o) (many (Step n ents rules o) stp) (erased (UnifyC m ents rules l r o) p)
    (match many m _
      ((Check) (values (UFail) (StFail _ _ _) (UCCheckRef ents rules s x t l r sd nt)))
      ((Force)
        (match many (ent-dec ents x) _
          (absurd (EntMiss a b ne) (has-ent-no-ent ents x hx ne))
          ((EntHit a b ty k e)
            (match many k _
              ((KDecl) (values (UFail) (StFail _ _ _) (UCRigid ents rules s x t l r ty sd nt e)))
              ((KPlain) (assign ents rules tb n fc s x t l r ty (KPlain) sd nt e (NDPlain) nx ct st))
              ((KLevel) (assign ents rules tb n fc s x t l r ty (KLevel) sd nt e (NDLevel) nx ct st))))))))

; Two distinct variables in [Force] mode, up to the alias: what remains is to unify the types.
(def-adts $ AliasStep : ((Nat) n) ((List (Ent)) ents) ((List (Rule)) rules) ((Nat) x) ((Nat) y) -> Type
  enum
  (many AliasFail : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) (erased (Nat) y) (erased (UnifyC (Force) ents rules (Ref x) (Ref y) (UFail)) p) -> (AliasStep n ents rules x y))
  (many AliasMint : (erased (Nat) n) (erased (List (Ent)) ents) (erased (List (Rule)) rules) (erased (Nat) x) (erased (Nat) y)
     (many (Nat) z) (many (Term) tz) (many (Nat) w) (many (Term) tw) (many (Table ents (Cons (Rule) (MkRule z (Ref w)) rules)) tb1) (erased (Nat) n1) (erased (Lt n1 n) lt)
     (erased (FreeCount ents (Cons (Rule) (MkRule z (Ref w)) rules) n1) fc) (erased (Term) tx) (erased (Kind) kx) (erased (Term) ty) (erased (Kind) ky) (erased (Kind) kz)
     (erased (EntOf ents x tx kx) ex) (erased (EntOf ents y ty ky) ey) (erased (EntOf ents z tz kz) ez) (erased (NotDecl kz) nz) (erased (Orient x tx kx y ty ky z tz w tw) o) -> (AliasStep n ents rules x y)))

(def-fns _ $ many alias-step : (many (List (Ent)) ents) (many (List (Rule)) rules) (many (Table ents rules) tb) (erased (Nat) n) (erased (FreeCount ents rules n) fc) (many (Nat) x) (many (Nat) y) (erased (Neq x y) nq)
      (erased (NoRule rules x) nx) (erased (NoRule rules y) ny) (erased (HasEnt ents x) hx) (erased (HasEnt ents y) hy) -> (many (AliasStep n ents rules x y) r)
    (match many (ent-dec ents x) _
      (absurd (EntMiss a b ne) (has-ent-no-ent ents x hx ne))
      ((EntHit a b tx kx ex)
        (match many (ent-dec ents y) _
          (absurd (EntMiss a2 b2 ne) (has-ent-no-ent ents y hy ne))
          ((EntHit a2 b2 ty ky ey)
            (match many (orient ents x tx kx ex y ty ky ey nq) _
              ((OrNone a3 b3 c3 d3 e3) (AliasFail _ _ _ _ _ (UCRigidRigid ents rules x y tx ty nq ex ey)))
              ((OrSome a3 b3 c3 d3 e3 g3 h3 z tz w tw kz ez ndz o)
                (let (erased nz) (erased nw) (orient-free rules x tx kx y ty ky z tz w tw o nx ny))
                (let (erased n1) (erased lt) (erased fc1) (assign-count ents rules n z tz kz (Ref w) fc ez nz))
                (AliasMint _ _ _ _ _ z tz w tw
                  (table-mint ents rules tb z (Ref w) nz (CnRef rules w nw) (AsgRef (Zero) z w (orient-neq x tx kx y ty ky z tz w tw o nq)) (ScRef ents w (orient-has ents x tx kx y ty ky z tz w tw o hx hy)) tz kz ez ndz)
                  n1 lt fc1 tx kx ty ky kz ex ey ez ndz o))))))))

(def-fns _
  (many unify-canon : (many (Mode) m) (many (List (Ent)) ents) (erased (ScopedEnts ents ents) se) (many (List (Rule)) rules) (many (Table ents rules) tb) (subterm erased (Nat) n) (erased (FreeCount ents rules n) fc)
      (subterm many (Term) l) (many (Term) r) (erased (Canonical rules l) cl) (erased (Canonical rules r) cr) (erased (Scoped ents l) sl) (erased (Scoped ents r) sr) (subterm many (POuter (PInner)) is phase) ->
      (erased (UOut) o) (many (Step n ents rules o) st) (erased (UnifyC m ents rules l r o) p)
    (match many (nonref-dec l) _
      ((IsRef x)
        (match erased cl _
          ((CnRef a0 x0 nx)
            (match erased sl _
              ((ScRef a1 x1 hx)
                (match many (nonref-dec r) _
                  ((IsRef y)
                    (match erased cr _
                      ((CnRef a2 y0 ny)
                        (match erased sr _
                          ((ScRef a3 y1 hy)
                            (match many (nat-dec x y) _
                              ((NDSame z) (values (UOk rules) (StSame _ _ _) (UCSame m ents rules x)))
                              ((NDDiff z w nq)
                                (match many m _
                                  ((Check) (values (UFail) (StFail _ _ _) (UCCheckRefRef ents rules x y nq)))
                                  ((Force)
                                    (match many (alias-step ents rules tb n fc x y nq nx ny hx hy) _
                                      ((AliasFail a b c d e p) (values (UFail) (StFail _ _ _) p))
                                      ((AliasMint a b c d e z tz w tw tb1 n1 lt fc1 tx kx ty ky kz ex ey ez ndz o)
                                        (let (many tz2) (erased ctz) (canon-tb ents (Cons _ (MkRule z (Ref w)) rules) tb1 tz))
                                        (let (many tw2) (erased ctw) (canon-tb ents (Cons _ (MkRule z (Ref w)) rules) tb1 tw))
                                        (let (erased stz) (orient-scoped ents x tx kx y ty ky z tz w tw o (ent-of-scoped ents ents x tx kx se ex) (ent-of-scoped ents ents y ty ky se ey)))
                                        (let (erased stw) (orient-scoped-w ents x tx kx y ty ky z tz w tw o (ent-of-scoped ents ents x tx kx se ex) (ent-of-scoped ents ents y ty ky se ey)))
                                        (let (erased o2) (many st2) (erased q)
                                          (unify-canon m ents se (Cons _ (MkRule z (Ref w)) rules) tb1 (subterm (lt-subterm n1 n lt)) n1 fc1 tz2 tw2
                                            (canon-canonical _ tz tz2 ctz) (canon-canonical _ tw tw2 ctw) (canon-scoped ents _ tz tz2 (table-scoped ents _ tb1) stz ctz) (canon-scoped ents _ tw tw2 (table-scoped ents _ tb1) stw ctw) phase))
                                        (values o2 (step-seq n ents rules _ (StMint _ _ _ (Cons _ (MkRule z (Ref w)) rules) tb1 n1 lt fc1) n1 (lt-weaken n1 n lt) o2 st2)
                                          (UCAlias ents rules x y tx kx ty ky z tz w tw tz2 tw2 o2 nq ex ey o ctz ctw q)))))))))))))
                  ((IsNonRef tr0 nr) (unify-ref m ents rules tb n fc (SL) x r (Ref x) r (SidedL (Ref x) r) nr nx hx cr sr))))))))
      ((IsNonRef tl0 nl)
        (match many (nonref-dec r) _
          ((IsRef y) (match erased cr _ ((CnRef a2 y0 ny) (match erased sr _ ((ScRef a3 y1 hy) (unify-ref m ents rules tb n fc (SR) y l l (Ref y) (SidedR (Ref y) l) nl ny hy cl sl))))))
          ((IsNonRef tr0 nr)
            (let (many b) (erased sb) (shape-of r))
            (match many l _
              ((Ref x) (match erased nl _))
              ((Bound j)
                (match many (nat-dec (Succ (Zero)) b) _
                  ((NDDiff z w nq) (values (UFail) (StFail _ _ _) (UCMismatch m ents rules l r (Succ (Zero)) b nl nr (ShBound j) sb nq)))
                  ((NDSame z)
                    (match erased sb _
                      ((ShBound k0)
                        (match many r _
                          ((Bound k)
                            (match many (nat-dec j k) _
                              ((NDSame z2) (values (UOk rules) (StSame _ _ _) (UCBound m ents rules j)))
                              ((NDDiff z2 w2 nq) (values (UFail) (StFail _ _ _) (UCBoundNeq m ents rules j k nq)))))))))))
              ((App h as)
                (match many (nat-dec (Succ (Succ (Zero))) b) _
                  ((NDDiff z w nq) (values (UFail) (StFail _ _ _) (UCMismatch m ents rules l r (Succ (Succ (Zero))) b nl nr (ShApp h as) sb nq)))
                  ((NDSame z)
                    (match erased sb _
                      ((ShApp h0 as0)
                        (match many r _
                          ((App h2 as2)
                            (match erased cl _
                              ((CnApp a1 h1 as1 ch cas)
                                (match erased cr _
                                  ((CnApp a2 h3 as3 ch2 cas2)
                                    (match erased sl _
                                      ((ScApp a3 h4 as4 sh sas)
                                        (match erased sr _
                                          ((ScApp a4 h5 as5 sh2 sas2)
                                            (match many (zip-dec as as2 (Nil _)) _
                                              ((ZDFail a5 b5 c5 zf) (values (UFail) (StFail _ _ _) (UCAppArity m ents rules h h2 as as2 zf)))
                                              ((ZDOk a5 b5 c5 eqs z)
                                                (let (erased o1) (many st1) (erased p) (unify-canon m ents se rules tb n fc h h2 ch ch2 sh sh2 phase))
                                                (let (erased o2) (many st2) (erased q)
                                                  (after-list m ents se rules tb n fc _ l o1 st1 as as2 as as2 (canonical-fix-list rules as cas) (canonical-fix-list rules as2 cas2) (prove-subterm as l) sas sas2 (zip-samelen as as2 (Nil _) eqs z) (PInner)))
                                                (values o2 st2 (UCApp m ents rules h h2 as as2 o1 o2 (zip-samelen as as2 (Nil _) eqs z) p q)))))))))))))))))))
              ((Univ)
                (match many (nat-dec (Succ (Succ (Succ (Zero)))) b) _
                  ((NDDiff z w nq) (values (UFail) (StFail _ _ _) (UCMismatch m ents rules l r (Succ (Succ (Succ (Zero)))) b nl nr (ShUniv) sb nq)))
                  ((NDSame z) (match erased sb _ ((ShUniv) (match many r _ ((Univ) (values (UOk rules) (StSame _ _ _) (UCUniv m ents rules)))))))))
              ((Fn lv ps rs)
                (match many (nat-dec (Succ (Succ (Succ (Succ (Zero))))) b) _
                  ((NDDiff z w nq) (values (UFail) (StFail _ _ _) (UCMismatch m ents rules l r (Succ (Succ (Succ (Succ (Zero))))) b nl nr (ShFn lv ps rs) sb nq)))
                  ((NDSame z)
                    (match erased sb _
                      ((ShFn lv0 ps0 rs0)
                        (match many r _
                          ((Fn lv2 ps2 rs2)
                            (match erased cl _
                              ((CnFn a1 l1 p1 r1 clv cps crs)
                                (match erased cr _
                                  ((CnFn a2 l2 p2 r2 clv2 cps2 crs2)
                                    (match erased sl _
                                      ((ScFn a3 l3 p3 r3 slv sps srs)
                                        (match erased sr _
                                          ((ScFn a4 l4 p4 r4 slv2 sps2 srs2)
                                            (match many (zip-tele-dec rs rs2 (Nil _)) _
                                              ((ZTDFail a5 b5 c5 zf) (values (UFail) (StFail _ _ _) (UCFnRets m ents rules lv lv2 ps ps2 rs rs2 zf)))
                                              ((ZTDOk a5 b5 c5 e1 z1)
                                                (match many (zip-tele-dec ps ps2 (Nil _)) _
                                                  ((ZTDFail a6 b6 c6 zf) (values (UFail) (StFail _ _ _) (UCFnParams m ents rules lv lv2 ps ps2 rs rs2 (zip-tele-same rs rs2 (Nil _) e1 z1) zf)))
                                                  ((ZTDOk a6 b6 c6 e2 z2)
                                                    (let (erased o1) (many st1) (erased p) (unify-canon m ents se rules tb n fc lv lv2 clv clv2 slv slv2 phase))
                                                    (let (erased o2) (many st2) (erased q)
                                                      (after-tele m ents se rules tb n fc _ l o1 st1 ps ps2 ps ps2 (canonical-fix-tele rules ps cps) (canonical-fix-tele rules ps2 cps2) (prove-subterm ps l) sps sps2 (zip-tele-same ps ps2 (Nil _) e2 z2) (PInner)))
                                                    (let (erased o3) (many st3) (erased q2)
                                                      (after-tele m ents se rules tb n fc _ l o2 st2 rs rs2 rs rs2 (canonical-fix-tele rules rs crs) (canonical-fix-tele rules rs2 crs2) (prove-subterm rs l) srs srs2 (zip-tele-same rs rs2 (Nil _) e1 z1) (PInner)))
                                                    (values o3 st3 (UCFn m ents rules lv lv2 ps ps2 rs rs2 o1 o2 o3 (zip-tele-same rs rs2 (Nil _) e1 z1) (zip-tele-same ps ps2 (Nil _) e2 z2) p q q2)))))))))))))))))))))
              ((TyCtor ps)
                (match many (nat-dec (Succ (Succ (Succ (Succ (Succ (Zero)))))) b) _
                  ((NDDiff z w nq) (values (UFail) (StFail _ _ _) (UCMismatch m ents rules l r (Succ (Succ (Succ (Succ (Succ (Zero)))))) b nl nr (ShTyCtor ps) sb nq)))
                  ((NDSame z)
                    (match erased sb _
                      ((ShTyCtor ps0)
                        (match many r _
                          ((TyCtor ps2)
                            (match erased cl _
                              ((CnTyCtor a1 p1 cps)
                                (match erased cr _
                                  ((CnTyCtor a2 p2 cps2)
                                    (match erased sl _
                                      ((ScTyCtor a3 p3 sps)
                                        (match erased sr _
                                          ((ScTyCtor a4 p4 sps2)
                                            (match many (zip-tele-dec ps ps2 (Nil _)) _
                                              ((ZTDFail a5 b5 c5 zf) (values (UFail) (StFail _ _ _) (UCTyCtorFail m ents rules ps ps2 zf)))
                                              ((ZTDOk a5 b5 c5 e1 z1)
                                                (let (erased o1) (many st1) (erased p)
                                                  (unify-tele m ents se rules tb n fc ps ps2 ps ps2 (canonical-fix-tele rules ps cps) (canonical-fix-tele rules ps2 cps2) sps sps2 (zip-tele-same ps ps2 (Nil _) e1 z1) phase))
                                                (values o1 st1 (UCTyCtor m ents rules ps ps2 o1 (zip-tele-same ps ps2 (Nil _) e1 z1) p)))))))))))))))))))
              ((ValCtor ps ret)
                (match many (nat-dec (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))) b) _
                  ((NDDiff z w nq) (values (UFail) (StFail _ _ _) (UCMismatch m ents rules l r (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))) b nl nr (ShValCtor ps ret) sb nq)))
                  ((NDSame z)
                    (match erased sb _
                      ((ShValCtor ps0 ret0)
                        (match many r _
                          ((ValCtor ps2 ret2)
                            (match erased cl _
                              ((CnValCtor a1 p1 r1 cps cret)
                                (match erased cr _
                                  ((CnValCtor a2 p2 r2 cps2 cret2)
                                    (match erased sl _
                                      ((ScValCtor a3 p3 r3 sps sret)
                                        (match erased sr _
                                          ((ScValCtor a4 p4 r4 sps2 sret2)
                                            (match many (zip-tele-dec ps ps2 (Nil _)) _
                                              ((ZTDFail a5 b5 c5 zf) (values (UFail) (StFail _ _ _) (UCValCtorFail m ents rules ps ps2 ret ret2 zf)))
                                              ((ZTDOk a5 b5 c5 e1 z1)
                                                (let (erased o1) (many st1) (erased p)
                                                  (unify-tele m ents se rules tb n fc ps ps2 ps ps2 (canonical-fix-tele rules ps cps) (canonical-fix-tele rules ps2 cps2) sps sps2 (zip-tele-same ps ps2 (Nil _) e1 z1) phase))
                                                (let (erased o2) (many st2) (erased q)
                                                  (after m ents se rules tb n fc _ l o1 st1 ret ret2 (prove-subterm ret l) cret cret2 sret sret2 (PInner)))
                                                (values o2 st2 (UCValCtor m ents rules ps ps2 ret ret2 o1 o2 (zip-tele-same ps ps2 (Nil _) e1 z1) p q)))))))))))))))))))))))))
  ; the parts of an application, originals beside their canonical forms under the current table
  (many unify-list : (many (Mode) m) (many (List (Ent)) ents) (erased (ScopedEnts ents ents) se) (many (List (Rule)) rules) (many (Table ents rules) tb) (subterm erased (Nat) n) (erased (FreeCount ents rules n) fc)
      (many (List (Term)) as) (many (List (Term)) bs) (subterm many (List (Term)) as2) (many (List (Term)) bs2) (erased (CanonList rules as as2) ca) (erased (CanonList rules bs bs2) cb)
      (erased (ScopedList ents as) sa) (erased (ScopedList ents bs) sb) (erased (SameLen as bs) sl) (subterm many (POuter (PInner)) is phase) ->
      (erased (UOut) o) (many (Step n ents rules o) st) (erased (UnifyListC m ents rules as bs o) p)
    (match many as2 _
      ((Nil c) (match erased ca _ ((CanNil a) (match erased sl _ ((SLNil) (match erased cb _ ((CanNil a2) (values (UOk rules) (StSame _ _ _) (ULNil m ents rules)))))))))
      ((Cons c a2 rest2)
        (match erased ca _
          ((CanCons a0 a1 a3 as1 rest1 pa qa)
            (match erased sl _
              ((SLCons a4 b1 as4 bs1 sl2)
                (match erased cb _
                  ((CanCons b0 b3 b4 bs3 brest2 pb qb)
                    (match many as _
                      ((Cons c2 a rest)
                        (match many bs _
                          ((Cons c3 b brest)
                            (match many bs2 _
                              ((Cons c4 b2 brest2m)
                                (match erased sa _
                                  ((ScCons a5 a6 a7 sa1 sa2)
                                    (match erased sb _
                                      ((ScCons b5 b6 b7 sb1 sb2)
                                        (let (erased o1) (many st1) (erased p)
                                          (unify-canon m ents se rules tb n fc a2 b2 (canon-canonical rules a a2 pa) (canon-canonical rules b b2 pb)
                                            (canon-scoped ents rules a a2 (table-scoped ents rules tb) sa1 pa) (canon-scoped ents rules b b2 (table-scoped ents rules tb) sb1 pb) phase))
                                        (let (erased o2) (many st2) (erased q)
                                          (after-list m ents se rules tb n fc _ as2 o1 st1 rest brest rest2 brest2m qa qb (prove-subterm rest2 as2) sa2 sb2 sl2 (PInner)))
                                        (values o2 st2 (ULCons m ents rules a b a2 b2 rest brest o1 o2 pa pb p q)))))))))))))))))))))
  (many unify-tele : (many (Mode) m) (many (List (Ent)) ents) (erased (ScopedEnts ents ents) se) (many (List (Rule)) rules) (many (Table ents rules) tb) (subterm erased (Nat) n) (erased (FreeCount ents rules n) fc)
      (many (List (Entry)) es) (many (List (Entry)) fs) (subterm many (List (Entry)) es2) (many (List (Entry)) fs2) (erased (CanonTele rules es es2) ce) (erased (CanonTele rules fs fs2) cf)
      (erased (ScopedTele ents es) se2) (erased (ScopedTele ents fs) sf) (erased (SameTele es fs) st) (subterm many (POuter (PInner)) is phase) ->
      (erased (UOut) o) (many (Step n ents rules o) stp) (erased (UnifyTeleC m ents rules es fs o) p)
    (match many es2 _
      ((Nil c) (match erased ce _ ((CanTNil a) (match erased st _ ((STNil) (match erased cf _ ((CanTNil a2) (values (UOk rules) (StSame _ _ _) (UTNil m ents rules)))))))))
      ((Cons c e2 rest2)
        (match many e2 _
          ((MkEntry s i t2)
            (match erased ce _
              ((CanTCons a0 s0 i0 t0 t1 es1 rest1 pt qt)
                (match erased st _
                  ((STCons s3 i3 t3 u3 es3 fs3 st2)
                    (match erased cf _
                      ((CanTCons b0 s4 i4 u0 u1 fs4 frest2 pu qu)
                        (match many es _
                          ((Cons c2 e rest)
                            (match many e _
                              ((MkEntry s5 i5 t)
                                (match many fs _
                                  ((Cons c3 f frest)
                                    (match many f _
                                      ((MkEntry s6 i6 u)
                                        (match many fs2 _
                                          ((Cons c4 f2 frest2m)
                                            (match many f2 _
                                              ((MkEntry s7 i7 u2)
                                                (match erased se2 _
                                                  ((ScTCons a5 s8 i8 t8 es8 st1 sc2)
                                                    (match erased sf _
                                                      ((ScTCons b5 s9 i9 u9 fs9 su1 sd2)
                                                        (let (erased o1) (many stp1) (erased p)
                                                          (unify-canon m ents se rules tb n fc t2 u2 (canon-canonical rules t t2 pt) (canon-canonical rules u u2 pu)
                                                            (canon-scoped ents rules t t2 (table-scoped ents rules tb) st1 pt) (canon-scoped ents rules u u2 (table-scoped ents rules tb) su1 pu) phase))
                                                        (let (erased o2) (many stp2) (erased q)
                                                          (after-tele m ents se rules tb n fc _ es2 o1 stp1 rest frest rest2 frest2m qt qu (prove-subterm rest2 es2) sc2 sd2 st2 (PInner)))
                                                        (values o2 stp2 (UTCons m ents rules s i t u t2 u2 rest frest o1 o2 pt pu p q)))))))))))))))))))))))))))))
  ; After a step: nothing when it left no table; the parts as they are when it left the table alone; the
  ; parts read again through the new table when it minted, the bound being lower then.
  (many after : (many (Mode) m) (many (List (Ent)) ents) (erased (ScopedEnts ents ents) se) (many (List (Rule)) rules) (many (Table ents rules) tb) (subterm erased (Nat) n) (erased (FreeCount ents rules n) fc)
      (erased Type P) (subterm many P parent) (erased (UOut) o1) (many (Step n ents rules o1) st1) (many (Term) t) (many (Term) u) (erased (Subterm (Term) t P parent) sub)
      (erased (Canonical rules t) ct) (erased (Canonical rules u) cu) (erased (Scoped ents t) st) (erased (Scoped ents u) su) (subterm many (PInner) is phase) ->
      (erased (UOut) o) (many (Step n ents rules o) stp) (erased (After m ents rules o1 t u o) p)
    (match many st1 _
      ((StFail a b c) (values (UFail) (StFail _ _ _) (AFail m ents rules t u)))
      ((StSame a b c)
        (let (erased o) (many stp) (erased q) (unify-canon m ents se rules tb n fc (subterm sub) t u ct cu st su (POuter (PInner))))
        (values o stp (AOk m ents rules rules t u t u o (canonical-fix rules t ct) (canonical-fix rules u cu) q)))
      ((StMint a b c rules1 tb1 n1 lt fc1)
        (let (many t2) (erased c1) (canon-tb ents rules1 tb1 t))
        (let (many u2) (erased c2) (canon-tb ents rules1 tb1 u))
        (let (erased o) (many stp2) (erased q)
          (unify-canon m ents se rules1 tb1 (subterm (lt-subterm n1 n lt)) n1 fc1 t2 u2 (canon-canonical rules1 t t2 c1) (canon-canonical rules1 u u2 c2)
            (canon-scoped ents rules1 t t2 (table-scoped ents rules1 tb1) st c1) (canon-scoped ents rules1 u u2 (table-scoped ents rules1 tb1) su c2) (POuter (PInner))))
        (values o (step-seq n ents rules rules1 st1 n1 (lt-weaken n1 n lt) o stp2) (AOk m ents rules rules1 t u t2 u2 o c1 c2 q)))))
  (many after-list : (many (Mode) m) (many (List (Ent)) ents) (erased (ScopedEnts ents ents) se) (many (List (Rule)) rules) (many (Table ents rules) tb) (subterm erased (Nat) n) (erased (FreeCount ents rules n) fc)
      (erased Type P) (subterm many P parent) (erased (UOut) o1) (many (Step n ents rules o1) st1) (many (List (Term)) as) (many (List (Term)) bs) (many (List (Term)) as2) (many (List (Term)) bs2)
      (erased (CanonList rules as as2) ca) (erased (CanonList rules bs bs2) cb) (erased (Subterm (List (Term)) as2 P parent) sub) (erased (ScopedList ents as) sa) (erased (ScopedList ents bs) sb) (erased (SameLen as bs) sl)
      (subterm many (PInner) is phase) -> (erased (UOut) o) (many (Step n ents rules o) stp) (erased (AfterList m ents rules o1 as bs o) p)
    (match many st1 _
      ((StFail a b c) (values (UFail) (StFail _ _ _) (ALFail m ents rules as bs)))
      ((StSame a b c)
        (let (erased o) (many stp) (erased q) (unify-list m ents se rules tb n fc as bs (subterm sub) as2 bs2 ca cb sa sb sl (POuter (PInner))))
        (values o stp (ALOk m ents rules rules as bs o q)))
      ((StMint a b c rules1 tb1 n1 lt fc1)
        (let (many as3) (erased c1) (canon-list-tb ents rules1 tb1 as))
        (let (many bs3) (erased c2) (canon-list-tb ents rules1 tb1 bs))
        (let (erased o) (many stp2) (erased q) (unify-list m ents se rules1 tb1 (subterm (lt-subterm n1 n lt)) n1 fc1 as bs as3 bs3 c1 c2 sa sb sl (POuter (PInner))))
        (values o (step-seq n ents rules rules1 st1 n1 (lt-weaken n1 n lt) o stp2) (ALOk m ents rules rules1 as bs o q)))))
  (many after-tele : (many (Mode) m) (many (List (Ent)) ents) (erased (ScopedEnts ents ents) se) (many (List (Rule)) rules) (many (Table ents rules) tb) (subterm erased (Nat) n) (erased (FreeCount ents rules n) fc)
      (erased Type P) (subterm many P parent) (erased (UOut) o1) (many (Step n ents rules o1) st1) (many (List (Entry)) es) (many (List (Entry)) fs) (many (List (Entry)) es2) (many (List (Entry)) fs2)
      (erased (CanonTele rules es es2) ce) (erased (CanonTele rules fs fs2) cf) (erased (Subterm (List (Entry)) es2 P parent) sub) (erased (ScopedTele ents es) se2) (erased (ScopedTele ents fs) sf) (erased (SameTele es fs) st)
      (subterm many (PInner) is phase) -> (erased (UOut) o) (many (Step n ents rules o) stp) (erased (AfterTele m ents rules o1 es fs o) p)
    (match many st1 _
      ((StFail a b c) (values (UFail) (StFail _ _ _) (ATFail m ents rules es fs)))
      ((StSame a b c)
        (let (erased o) (many stp) (erased q) (unify-tele m ents se rules tb n fc es fs (subterm sub) es2 fs2 ce cf se2 sf st (POuter (PInner))))
        (values o stp (ATOk m ents rules rules es fs o q)))
      ((StMint a b c rules1 tb1 n1 lt fc1)
        (let (many es3) (erased c1) (canon-tele-tb ents rules1 tb1 es))
        (let (many fs3) (erased c2) (canon-tele-tb ents rules1 tb1 fs))
        (let (erased o) (many stp2) (erased q) (unify-tele m ents se rules1 tb1 (subterm (lt-subterm n1 n lt)) n1 fc1 es fs es3 fs3 c1 c2 se2 sf st (POuter (PInner))))
        (values o (step-seq n ents rules rules1 st1 n1 (lt-weaken n1 n lt) o stp2) (ATOk m ents rules rules1 es fs o q))))))

; ---- A list of equations as written: the entry point, deriving [Unify] through [conv]. The outcome's
; table comes with its ranking and scope when there is one.
(def-adts
  (ScopedEqs : ((List (Ent)) ents) ((List (Eqn)) eqs) -> Type
    enum
    (many SqNil : (erased (List (Ent)) ents) -> (ScopedEqs ents (Nil (Eqn))))
    (many SqCons : (erased (List (Ent)) ents) (erased (Term) l) (erased (Term) r) (erased (List (Eqn)) rest) (erased (Scoped ents l) p) (erased (Scoped ents r) q) (erased (ScopedEqs ents rest) s) ->
       (ScopedEqs ents (Cons (Eqn) (MkEqn l r) rest))))
  (OutTable : ((List (Ent)) ents) ((UOut) o) -> Type
    enum
    (many OTOk : (erased (List (Ent)) ents) (many (List (Rule)) rules) (many (Table ents rules) tb) -> (OutTable ents (UOk rules)))
    (many OTFail : (erased (List (Ent)) ents) -> (OutTable ents (UFail)))))

(def-fns _ $ many unify-eqs : (many (Mode) m) (many (List (Ent)) ents) (erased (ScopedEnts ents ents) se) (many (List (Rule)) rules) (many (Table ents rules) tb) (erased (Nat) n) (erased (FreeCount ents rules n) fc)
    (subterm many (List (Eqn)) eqs) (erased (ScopedEqs ents eqs) sq) -> (many (UOut) o) (many (OutTable ents o) ot) (erased (Unify m ents rules eqs o) p)
  (match many eqs _
    ((Nil a) (values (UOk rules) (OTOk _ rules tb) (UDone m ents rules)))
    ((Cons a eqn rest)
      (match many eqn _
        ((MkEqn l r)
          (match erased sq _
            ((SqCons b l0 r0 rest0 sl sr sq2)
              (let (many l2) (erased cl) (canon-tb ents rules tb l))
              (let (many r2) (erased cr) (canon-tb ents rules tb r))
              (let (erased o1) (many st1) (erased d)
                (unify-canon m ents se rules tb n fc l2 r2 (canon-canonical rules l l2 cl) (canon-canonical rules r r2 cr) (canon-scoped ents rules l l2 (table-scoped ents rules tb) sl cl) (canon-scoped ents rules r r2 (table-scoped ents rules tb) sr cr) (POuter (PInner))))
              (match many st1 _
                ((StFail b2 c2 d2) (values (UFail) (OTFail _) (conv m ents rules l r l2 r2 (UFail) rest (UFail) d cl cr (ContFail m ents rest))))
                ((StSame b2 c2 d2)
                  (let (many o) (many ot) (erased q) (unify-eqs m ents se rules tb n fc rest sq2))
                  (values o ot (conv m ents rules l r l2 r2 (UOk rules) rest o d cl cr (ContOk m ents rules rest o q))))
                ((StMint b2 c2 d2 rules1 tb1 n1 lt fc1)
                  (let (many o) (many ot) (erased q) (unify-eqs m ents se rules1 tb1 n1 fc1 rest sq2))
                  (values o ot (conv m ents rules l r l2 r2 (UOk rules1) rest o d cl cr (ContOk m ents rules1 rest o q))))))))))))
(MkUnit)
