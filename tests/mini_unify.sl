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

(def-fns _ $ many try : (many (Mode) m) (many (List (Rule)) rules) (many (Term) l) (many (Term) r) -> (many (UOut) o)
  (let (many n) (erased fc) (free-count ents rules))
  (let (many o) (erased p) (unify-eqs m ents rules n fc (Cons _ (MkEqn l r) (Nil _))))
  o)

(def-fns _ $ many succeeded : (many (UOut) o) -> (many (Bool) b)
  (match many o _ ((UOk rs) (BTrue)) ((UFail) (BFalse)) ((UStuck) (BFalse))))

(let (many succ-m) (App (Ref 4) (Cons _ (Ref 6) (Nil _))))
(let (many succ-n) (App (Ref 4) (Cons _ (Ref 5) (Nil _))))
(let (many none) (Nil (Rule)))

(let (many r1) (succeeded $ try (Force) none (Ref 5) succ-m))
(let (many r2) (succeeded $ try (Force) none (App (Ref 3) (Nil _)) succ-m))
(let (many r3) (succeeded $ try (Force) none (Ref 5) succ-n))
(let (many r4) (succeeded $ try (Check) none (Ref 5) (Ref 6)))
(let (many r5) (succeeded $ try (Check) none succ-n succ-n))
(let (many r6) (succeeded $ try (Force) none (Ref 5) (Ref 6)))
(let (many r7) (succeeded $ try (Force) (Cons _ (MkRule 6 succ-n) (Nil _)) (Ref 6) succ-n))

; The alias lands on the newer variable, 6.
(let (many u6) (try (Force) none (Ref 5) (Ref 6)))
(let (many aliased)
  (match many u6 (((Bool) b))
    ((UFail) (BFalse))
    ((UStuck) (BFalse))
    ((UOk rs)
      (match many rs (((Bool) b))
        ((Nil e) (BFalse))
        ((Cons e rule rest)
          (match many rule (((Bool) b))
            ((MkRule x t) (match many (nat-dec x 6) (((Bool) b)) ((NDSame f) (BTrue)) ((NDDiff f g n) (BFalse))))))))))
(comptime-match aliased (BTrue))

(Cons _ r1 $ Cons _ r2 $ Cons _ r3 $ Cons _ r4 $ Cons _ r5 $ Cons _ r6 $ Cons _ r7 $ Nil _)
