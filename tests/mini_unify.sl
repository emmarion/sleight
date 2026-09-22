; needs: ../mini/base ../mini/term ../mini/canon ../mini/ctx ../mini/unify
; expect: (Cons _ (BTrue) $ Cons _ (BFalse) $ Cons _ (BFalse) $ Cons _ (BFalse) $ Cons _ (BTrue) $ Cons _ (BTrue) $ Cons _ (BTrue) $ Nil _)
; Unification in mini/: over Nat's declaration (2 the type constructor, 3 Zero, 4 Succ) and two variables 5 and
; 6, in order: a variable takes an application; Zero against Succ is refused, both rigid; the occurs check;
; Check mode refuses two variables; Check mode accepts identical terms; Force aliases two variables; a variable
; with a rule is read through it.

(let ((many nat)) (TyApp (Ref 2) (Nil _) (Nil _)))
(let ((many succ-ps)) (Cons _ (MkEntry (BFalse) (BFalse) nat) (Nil _)))
(let ((many ents))
  (Cons _ (MkEnt 6 nat (KPlain)) $ Cons _ (MkEnt 5 nat (KPlain)) $ Cons _ (MkEnt 4 (TValCtor succ-ps nat) (KDecl))
    $ Cons _ (MkEnt 3 (TValCtor (Nil _) nat) (KDecl)) $ Cons _ (MkEnt 2 (TTyCtor (Nil _)) (KDecl)) $ Nil _))

; Every entry is in scope: the evidence the unifier asks for.
(let ((erased (HasEnt ents 6) h6)) (HEHere _ _ _ _))
(let ((erased (HasEnt ents 5) h5)) (HEThere _ _ _ $ HEHere _ _ _ _))
(let ((erased (HasEnt ents 4) h4)) (HEThere _ _ _ $ HEThere _ _ _ $ HEHere _ _ _ _))
(let ((erased (HasEnt ents 3) h3)) (HEThere _ _ _ $ HEThere _ _ _ $ HEThere _ _ _ $ HEHere _ _ _ _))
(let ((erased (HasEnt ents 2) h2)) (HEThere _ _ _ $ HEThere _ _ _ $ HEThere _ _ _ $ HEThere _ _ _ $ HEHere _ _ _ _))
(let ((erased s-nat)) (ScTyApp ents (Zero) (Ref 2) (Nil _) (Nil _) (Zero) (ScRef _ (Zero) 2 h2) (ScTNil _ (Zero)) (ScNil _ (Zero)) (LENil _ _)))
(let ((erased s-nat1)) (ScTyApp ents (Succ (Zero)) (Ref 2) (Nil _) (Nil _) (Succ (Zero)) (ScRef _ (Succ (Zero)) 2 h2) (ScTNil _ (Succ (Zero))) (ScNil _ (Succ (Zero))) (LENil _ _)))
(let ((erased s-succ-ps)) (ScTCons ents (Zero) (BFalse) (BFalse) nat (Nil _) (Succ (Zero)) s-nat (ScTNil _ (Succ (Zero)))))
(let ((erased (ScopedEnts ents ents) se))
  (SECons _ _ _ _ _ s-nat $ SECons _ _ _ _ _ s-nat $ SECons _ _ _ _ _ (ScValCtor _ (Zero) _ _ (Succ (Zero)) s-succ-ps s-nat1)
    $ SECons _ _ _ _ _ (ScValCtor _ (Zero) _ _ (Zero) (ScTNil _ (Zero)) s-nat) $ SECons _ _ _ _ _ (ScTyCtor _ (Zero) _ (Zero) (ScTNil _ (Zero))) $ SENil _))
(let ((many none)) (Nil (Rule)))
(let ((many tb0)) (MkTable ents none (Nil _) (Zero) (VFNil _ _) (ALNil _) (SRNil _) (RPNil _)))

(def-fns _ $ (many run : (many (Mode) m) (many (List (Rule)) rules) (many (Table ents rules) tb) (many (Term) l) (many (Term) r) (erased (Scoped ents (Zero) l) sl) (erased (Scoped ents (Zero) r) sr) ->
    (many (UOut) o) (many (OutTable ents o) ot))
  (let ((many n) (erased fc)) (free-count ents rules))
  (match many (unify-eqs m ents se rules tb n fc (Cons _ (MkEqn l r) (Nil _)) (SqCons _ _ _ _ sl sr (SqNil _))) _
    ((MkEqs y0 y1 y2 y3 o ot p) (values o ot))))

(def-fns _ $ (many ok : (many (UOut) o) -> (many (Bool) b))
  (match many o _ ((UOk rs) (BTrue)) ((UFail) (BFalse))))

(let ((many succ-m)) (ValApp (Ref 4) succ-ps nat (Cons _ (Ref 6) (Nil _))))
(let ((many succ-n)) (ValApp (Ref 4) succ-ps nat (Cons _ (Ref 5) (Nil _))))
(let ((many zero)) (ValApp (Ref 3) (Nil _) nat (Nil _)))
(let ((erased s-succ-m)) (ScValApp ents (Zero) _ _ _ _ (Succ (Zero)) (ScRef _ (Zero) 4 h4) s-succ-ps s-nat1 (ScCons _ (Zero) _ _ (ScRef _ (Zero) 6 h6) (ScNil _ (Zero))) (LECons _ _ _ _ _ _ (LENil _ _))))
(let ((erased s-succ-n)) (ScValApp ents (Zero) _ _ _ _ (Succ (Zero)) (ScRef _ (Zero) 4 h4) s-succ-ps s-nat1 (ScCons _ (Zero) _ _ (ScRef _ (Zero) 5 h5) (ScNil _ (Zero))) (LECons _ _ _ _ _ _ (LENil _ _))))
(let ((erased s-zero)) (ScValApp ents (Zero) _ _ _ _ (Zero) (ScRef _ (Zero) 3 h3) (ScTNil _ (Zero)) s-nat (ScNil _ (Zero)) (LENil _ _)))

(let ((many o1) (many t1)) (run (Force) none tb0 (Ref 5) succ-m (ScRef _ (Zero) 5 h5) s-succ-m))
(let ((many o2) (many t2)) (run (Force) none tb0 zero succ-m s-zero s-succ-m))
(let ((many o3) (many t3)) (run (Force) none tb0 (Ref 5) succ-n (ScRef _ (Zero) 5 h5) s-succ-n))
(let ((many o4) (many t4)) (run (Check) none tb0 (Ref 5) (Ref 6) (ScRef _ (Zero) 5 h5) (ScRef _ (Zero) 6 h6)))
(let ((many o5) (many t5)) (run (Check) none tb0 succ-n succ-n s-succ-n s-succ-n))
(let ((many o6) (many t6)) (run (Force) none tb0 (Ref 5) (Ref 6) (ScRef _ (Zero) 5 h5) (ScRef _ (Zero) 6 h6)))

; The alias lands on the newer variable, 6.
(let ((many aliased))
  (match many o6 (((Bool) b))
    ((UFail) (BFalse))
    ((UOk rs)
      (match many rs (((Bool) b))
        ((Nil e) (BFalse))
        ((Cons e rule rest)
          (match many rule (((Bool) b))
            ((MkRule x t) (match many (nat-dec x 6) (((Bool) b)) ((NDSame f) (BTrue)) ((NDDiff f g n) (BFalse))))))))))
(comptime-match many aliased (BTrue))

; With 6 ruled to be Succ 5 by the first run, 6 against Succ 5 is read through the rule and accepted in Check mode.
(let ((many o7) (many t7)) (run (Force) none tb0 (Ref 6) succ-n (ScRef _ (Zero) 6 h6) s-succ-n))
(let ((many r7))
  (match many t7 (((Bool) b))
    ((OTFail e) (BFalse))
    ((OTOk e rules tb)
      (let ((many o) (many t)) (run (Check) rules tb (Ref 6) succ-n (ScRef _ (Zero) 6 h6) s-succ-n))
      (ok o))))

(Cons _ (ok o1) $ Cons _ (ok o2) $ Cons _ (ok o3) $ Cons _ (ok o4) $ Cons _ (ok o5) $ Cons _ (ok o6) $ Cons _ r7 $ Nil _)
