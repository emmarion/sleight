; needs: ../mini/base ../mini/term ../mini/canon ../mini/ctx ../mini/unify ../mini/core ../mini/eval ../mini/elab ../mini/elabfn ../mini/raw
; expect: (Cons (None) (Cons (Some (None)) (Cons (Some (None)) (Nil))))
; A program on which [elab-program] answers stuck, so that (if this session read the relations right) no
; derivation of [ElabProgram] exists for it: an open question for the owner, recorded, not resolved.
;   (def-adts (Nat () (Zero () (Nat)) (Succ (((Nat) pred)) (Nat))))
;   (def-lvl L)
;   (def-adts (T2 (((Type) P)) (C2 ((((valctor (((Nat) z)) (valctor (((Nat) n)) Type))) x3) ((Nat) z)) (T2 ((x3 z) (Zero))))))
;   (def-fns L (mk () (((tyctor ()) A)) Nat))
;   (let (A0) (mk))
;   (def-adts (T3 () (C3 (((A0) is w)) (T3))))
;   (def-fns L (outer ((((valctor (((tyctor ()) A)) Type)) x) (((T2 (x A0)) s) ((T3) s2)) (((Nat) r))
;     (match s (((Nat) r)) ((C2 x3p zp) (match s2 (((Nat) r2)) ((C3 wp) (Zero)))))))
;   (Zero)
; Entering C2 forces (x A0) = ((x3p zp) (Zero)); the heads are a variable against an application, so
; [UAssign] gives x the rule (x3p zp) with no check on their types, and then A0, whose type is the former
; (tyctor ()), gets the rule (Zero), whose type is not a former. Entering C3 then instantiates C3's fields
; under those rules: the is entry's term canonicalizes to ((Zero)), an application whose head's type is
; (Nat), and [MintTele]'s [TypeOfTerm] premise has no derivation for it. The two controls, the field as a
; type entry and the body without the forcing match, elaborate. The types of x and x3 are uninhabited (no
; declared constructor returns a former), so the branch is dead code; the session has not judged what the
; owner's design intends here.
(let (many tyc0) (l2 (k (KTyCtor)) (l0)))
(let (many x3-ty) (l3 (k (KValCtor)) (l1 (l2 nat (a "z"))) (l3 (k (KValCtor)) (l1 (l2 nat (a "n"))) (a "Type"))))
(let (many t2-decl)
  (l2 (k (KDefAdts))
    (l3 (a "T2") (l1 (l2 (a "Type") (a "P")))
      (l3 (a "C2") (l2 (l2 x3-ty (a "x3")) (l2 nat (a "z"))) (l2 (a "T2") (l2 (l2 (a "x3") (a "z")) zero))))))
(let (many mk-defn) (l3 (k (KDefFns)) (a "L") (l4 (a "mk") (l0) (l1 (l2 tyc0 (a "A"))) (a "Nat"))))
(let (many let-a0) (l3 (k (KLet)) (l1 (a "A0")) (l1 (a "mk"))))
(let (many t3-decl) (l2 (k (KDefAdts)) (l3 (a "T3") (l0) $ l3 (a "C3") (l1 (l3 (l1 (a "A0")) (k (KIs)) (a "w"))) (l1 (a "T3")))))
(let (many x-ty) (l3 (k (KValCtor)) (l1 (l2 tyc0 (a "A"))) (a "Type")))
(let (many inner) (l4 (k (KMatch)) (a "s2") (l1 (l2 nat (a "r2"))) (l2 (l2 (a "C3") (a "wp")) zero)))
(let (many outer-defn)
  (l3 (k (KDefFns)) (a "L")
    (l4 (a "outer") (l3 (l2 x-ty (a "x")) (l2 (l2 (a "T2") (l2 (a "x") (a "A0"))) (a "s")) (l2 (l1 (a "T3")) (a "s2"))) (l1 (l2 nat (a "r")))
      (l4 (k (KMatch)) (a "s") (l1 (l2 nat (a "r"))) (l2 (l3 (a "C2") (a "x3p") (a "zp")) inner)))))
(let (many prog) (Cons _ nat-decl $ Cons _ lvl-decl $ Cons _ t2-decl $ Cons _ mk-defn $ Cons _ let-a0 $ Cons _ t3-decl $ Cons _ outer-defn $ Cons _ zero $ Nil _))
(def-fns _ $ many shape : (many (List (Raw)) p) -> (many (Maybe (Maybe (Reason))) r)
  (match many (elab-program p) _
    ((ProgramStuck x) (None _))
    ((MkProgramDec x out q)
      (match many out _
        ((PErr r) (Some _ (Some _ r)))
        ((POk core ty) (Some _ (None _)))))))

; control 1: the field a type entry instead of an is entry
(let (many t3-ty-decl) (l2 (k (KDefAdts)) (l3 (a "T3") (l0) $ l3 (a "C3") (l1 (l2 (l1 (a "A0")) (a "w"))) (l1 (a "T3")))))
(let (many prog-ty) (Cons _ nat-decl $ Cons _ lvl-decl $ Cons _ t2-decl $ Cons _ mk-defn $ Cons _ let-a0 $ Cons _ t3-ty-decl $ Cons _ outer-defn $ Cons _ zero $ Nil _))
; control 2: no forcing, the inner match alone as the body
(let (many outer-plain)
  (l3 (k (KDefFns)) (a "L")
    (l4 (a "outer") (l3 (l2 x-ty (a "x")) (l2 (l2 (a "T2") (l2 (a "x") (a "A0"))) (a "s")) (l2 (l1 (a "T3")) (a "s2"))) (l1 (l2 nat (a "r"))) inner)))
(let (many prog-plain) (Cons _ nat-decl $ Cons _ lvl-decl $ Cons _ t2-decl $ Cons _ mk-defn $ Cons _ let-a0 $ Cons _ t3-decl $ Cons _ outer-plain $ Cons _ zero $ Nil _))
(Cons _ (shape prog) $ Cons _ (shape prog-ty) $ Cons _ (shape prog-plain) $ Nil _)
