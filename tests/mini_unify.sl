; needs: ../mini/base ../mini/term ../mini/canon ../mini/ctx ../mini/unify
; expect: (Cons (BTrue) (Cons (BFalse) (Cons (BFalse) (Cons (BFalse) (Cons (BTrue) (Cons (BTrue) (Cons (BTrue) (Nil))))))))
; Unification in mini/: over Nat's declaration (2 the type constructor, 3 Zero, 4 Succ) and two variables 5 and
; 6, in order: a variable takes an application; Zero against Succ is refused, both rigid; the occurs check;
; Check mode refuses two variables; Check mode accepts identical terms; Force aliases two variables; a variable
; with a rule is read through it. The helper reports a stuck answer, which none of these reach, as a failure.

(let (many nat) (App (Ref 2) (Nil _)))
(let (many ents)
  (Cons _ (MkEnt 6 nat (KPlain)) $ Cons _ (MkEnt 5 nat (KPlain)) $ Cons _ (MkEnt 4 (ValCtor (Cons _ (MkEntry (BFalse) (BFalse) nat) (Nil _)) nat) (KDecl))
    $ Cons _ (MkEnt 3 (ValCtor (Nil _) nat) (KDecl)) $ Cons _ (MkEnt 2 (TyCtor (Nil _)) (KDecl)) $ Nil _))

; Every entry is in scope: the evidence the unifier asks for.
(let (erased (HasEnt ents 6) h6) (HEHere _ _ _ _))
(let (erased (HasEnt ents 5) h5) (HEThere _ _ _ $ HEHere _ _ _ _))
(let (erased (HasEnt ents 4) h4) (HEThere _ _ _ $ HEThere _ _ _ $ HEHere _ _ _ _))
(let (erased (HasEnt ents 3) h3) (HEThere _ _ _ $ HEThere _ _ _ $ HEThere _ _ _ $ HEHere _ _ _ _))
(let (erased (HasEnt ents 2) h2) (HEThere _ _ _ $ HEThere _ _ _ $ HEThere _ _ _ $ HEThere _ _ _ $ HEHere _ _ _ _))
(let (erased s-nat) (ScApp ents (Ref 2) (Nil _) (ScRef _ 2 h2) (ScNil _)))
(let (erased (ScopedEnts ents ents) se)
  (SECons _ _ _ _ _ s-nat $ SECons _ _ _ _ _ s-nat $ SECons _ _ _ _ _ (ScValCtor _ _ _ (ScTCons _ _ _ _ _ s-nat (ScTNil _)) s-nat)
    $ SECons _ _ _ _ _ (ScValCtor _ _ _ (ScTNil _) s-nat) $ SECons _ _ _ _ _ (ScTyCtor _ _ (ScTNil _)) $ SENil _))
(let (many none) (Nil (Rule)))
(let (many tb0) (MkTable ents none (Nil _) (Zero) (VFNil _ _) (ALNil _) (SRNil _) (RPNil _)))

(def-fns _ $ many run : (many (Mode) m) (many (List (Rule)) rules) (many (Table ents rules) tb) (many (Term) l) (many (Term) r) (erased (Scoped ents l) sl) (erased (Scoped ents r) sr) ->
    (many (UOut) o) (many (OutTable ents o) ot)
  (let (many n) (erased fc) (free-count ents rules))
  (match many (unify-eqs m ents se rules tb n fc (Cons _ (MkEqn l r) (Nil _)) (SqCons _ _ _ _ sl sr (SqNil _))) _
    ((EqsStuck z0 z1 z2) (values (UFail) (OTFail _)))
    ((MkEqs y0 y1 y2 y3 o ot p) (values o ot))))

(def-fns _ $ many ok : (many (UOut) o) -> (many (Bool) b)
  (match many o _ ((UOk rs) (BTrue)) ((UFail) (BFalse))))

(let (many succ-m) (App (Ref 4) (Cons _ (Ref 6) (Nil _))))
(let (many succ-n) (App (Ref 4) (Cons _ (Ref 5) (Nil _))))
(let (erased s-succ-m) (ScApp ents _ _ (ScRef _ 4 h4) (ScCons _ _ _ (ScRef _ 6 h6) (ScNil _))))
(let (erased s-succ-n) (ScApp ents _ _ (ScRef _ 4 h4) (ScCons _ _ _ (ScRef _ 5 h5) (ScNil _))))
(let (erased s-zero) (ScApp ents _ _ (ScRef _ 3 h3) (ScNil _)))

(let (many o1) (many t1) (run (Force) none tb0 (Ref 5) succ-m (ScRef _ 5 h5) s-succ-m))
(let (many o2) (many t2) (run (Force) none tb0 (App (Ref 3) (Nil _)) succ-m s-zero s-succ-m))
(let (many o3) (many t3) (run (Force) none tb0 (Ref 5) succ-n (ScRef _ 5 h5) s-succ-n))
(let (many o4) (many t4) (run (Check) none tb0 (Ref 5) (Ref 6) (ScRef _ 5 h5) (ScRef _ 6 h6)))
(let (many o5) (many t5) (run (Check) none tb0 succ-n succ-n s-succ-n s-succ-n))
(let (many o6) (many t6) (run (Force) none tb0 (Ref 5) (Ref 6) (ScRef _ 5 h5) (ScRef _ 6 h6)))

; The alias lands on the newer variable, 6.
(let (many aliased)
  (match many o6 (((Bool) b))
    ((UFail) (BFalse))
    ((UOk rs)
      (match many rs (((Bool) b))
        ((Nil e) (BFalse))
        ((Cons e rule rest)
          (match many rule (((Bool) b))
            ((MkRule x t) (match many (nat-dec x 6) (((Bool) b)) ((NDSame f) (BTrue)) ((NDDiff f g n) (BFalse))))))))))
(comptime-match aliased (BTrue))

; With 6 ruled to be Succ 5 by the first run, 6 against Succ 5 is read through the rule and accepted in Check mode.
(let (many o7) (many t7) (run (Force) none tb0 (Ref 6) succ-n (ScRef _ 6 h6) s-succ-n))
(let (many r7)
  (match many t7 (((Bool) b))
    ((OTFail e) (BFalse))
    ((OTOk e rules tb)
      (let (many o) (many t) (run (Check) rules tb (Ref 6) succ-n (ScRef _ 6 h6) s-succ-n))
      (ok o))))

(Cons _ (ok o1) $ Cons _ (ok o2) $ Cons _ (ok o3) $ Cons _ (ok o4) $ Cons _ (ok o5) $ Cons _ (ok o6) $ Cons _ r7 $ Nil _)
