; needs: ../mini/base ../mini/term ../mini/canon ../mini/ctx ../mini/unify
; expect: (Cons (BTrue) (Cons (BFalse) (Cons (BFalse) (Cons (BFalse) (Cons (BTrue) (Cons (BTrue) (Cons (BTrue) (Nil))))))))
; Unification in mini/: over Nat's declaration (2 the type constructor, 3 Zero, 4 Succ) and two variables 5 and
; 6, in order: a variable takes an application; Zero against Succ is refused, both rigid; the occurs check;
; Check mode refuses two variables; Check mode accepts identical terms; Force aliases two variables; a variable
; with a rule is read through it.

(let (many nat) (App (Ref 2) (Nil _)))
(let (many ents)
  (Cons _ (MkEnt 6 nat (KPlain)) $ Cons _ (MkEnt 5 nat (KPlain)) $ Cons _ (MkEnt 4 (ValCtor (Cons _ (MkEntry (BFalse) (BFalse) nat) (Nil _)) nat) (KDecl))
    $ Cons _ (MkEnt 3 (ValCtor (Nil _) nat) (KDecl)) $ Cons _ (MkEnt 2 (TyCtor (Nil _)) (KDecl)) $ Nil _))

(def-fns _ $ many succeeded : (erased (Mode) m) (erased (List (Ent)) es) (erased (List (Rule)) rules) (erased (List (Eqn)) eqs) (many (Unified m es rules eqs) u) -> (many (Bool) b)
  (match many u _
    ((UnifyStuck a b c d) (BFalse))
    ((MkUnified a b c d out p) (match many out _ ((UOk rs) (BTrue)) ((UFail) (BFalse))))))

(def-fns _ $ many eq1 : (many (Term) l) (many (Term) r) -> (many (List (Eqn)) eqs)
  (Cons _ (MkEqn l r) (Nil _)))

(let (many succ-m) (App (Ref 4) (Cons _ (Ref 6) (Nil _))))
(let (many succ-n) (App (Ref 4) (Cons _ (Ref 5) (Nil _))))
(let (many none) (Nil (Rule)))

(let (many r1) (succeeded _ _ _ _ $ unify 1000 (Force) ents none $ eq1 (Ref 5) succ-m))
(let (many r2) (succeeded _ _ _ _ $ unify 1000 (Force) ents none $ eq1 (App (Ref 3) (Nil _)) succ-m))
(let (many r3) (succeeded _ _ _ _ $ unify 1000 (Force) ents none $ eq1 (Ref 5) succ-n))
(let (many r4) (succeeded _ _ _ _ $ unify 1000 (Check) ents none $ eq1 (Ref 5) (Ref 6)))
(let (many r5) (succeeded _ _ _ _ $ unify 1000 (Check) ents none $ eq1 succ-n succ-n))
(let (many r6) (succeeded _ _ _ _ $ unify 1000 (Force) ents none $ eq1 (Ref 5) (Ref 6)))
(let (many r7) (succeeded _ _ _ _ $ unify 1000 (Force) ents (Cons _ (MkRule 6 succ-n) (Nil _)) $ eq1 (Ref 6) succ-n))

; The alias lands on the newer variable, 6.
(let (many u6) (unify 1000 (Force) ents none $ eq1 (Ref 5) (Ref 6)))
(let (many aliased)
  (match many u6 (((Bool) b))
    ((UnifyStuck a b c d) (BFalse))
    ((MkUnified a b c d out p)
      (match many out (((Bool) b))
        ((UFail) (BFalse))
        ((UOk rs)
          (match many rs (((Bool) b))
            ((Nil e) (BFalse))
            ((Cons e rule rest)
              (match many rule (((Bool) b))
                ((MkRule x t) (match many (nat-dec x 6) (((Bool) b)) ((NDSame f) (BTrue)) ((NDDiff f g n) (BFalse))))))))))))
(comptime-match aliased (BTrue))

(Cons _ r1 $ Cons _ r2 $ Cons _ r3 $ Cons _ r4 $ Cons _ r5 $ Cons _ r6 $ Cons _ r7 $ Nil _)
