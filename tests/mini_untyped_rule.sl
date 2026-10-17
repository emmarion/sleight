; needs: ../mini/base ../mini/term ../mini/canon ../mini/ctx ../mini/unify ../mini/core ../mini/eval ../mini/elab ../mini/elabfn ../mini/raw
; expect: (Cons _ (Some _ $ Some _ $ RBadReturn) $ Cons _ (Some _ $ Some _ $ RBadReturn) $ Cons _ (Some _ $ Some _ $ RBadReturn) $ Cons _ (Some _ $ None _) $ Cons _ (Some _ $ Some _ $ RBadReturn) $ Cons _ (Some _ $ None _) $ Nil _)
; A TValCtor former's return is an application of a type constructor other than the former's own binders
; (section 11, restored here at the owner's word). While the former accepted any type as its return,
; this program reached [type-of-term]'s stuck, so that (in one session's reading) no derivation of
; [ElabProgram] existed for it:
;   (def-adts (Nat () (Zero () (Nat)) (Succ (((Nat) pred)) (Nat))))
;   (def-lvl L)
;   (def-adts (T2 (((Type) P)) (C2 ((((valctor (((Nat) z)) (valctor (((Nat) n)) Type))) x3) ((Nat) z)) (T2 ((x3 z) (Zero))))))
;   (def-fns L (mk () (((tyctor ()) A)) Nat))
;   (let (A0) (mk))
;   (def-adts (T3 () (C3 (((A0) is w)) (T3))))
;   (def-fns L (outer ((((valctor (((tyctor ()) A)) Type)) x) (((T2 (x A0)) s) ((T3) s2)) (((Nat) r))
;     (match s (((Nat) r)) ((C2 x3p zp) (match s2 (((Nat) r2)) ((C3 wp) (Zero)))))))
;   (Zero)
; Entering C2 forced (x A0) = ((x3p zp) (Zero)); the heads being a variable against an application,
; [UAssign] gave x the rule (x3p zp) with no check on their types, and then A0, of the former type
; (tyctor ()), the rule (Zero), of type (Nat). Entering C3 then instantiated C3's fields under those rules,
; where the is entry's term canonicalizes to ((Zero)), an application whose head's type is no former, and
; [MintTele]'s [TypeOfTerm] premise has no derivation. The formers of x and x3 return Type, which item 80
; refuses, so the program and its two controls (the field a type entry; no forcing match) are now refused at
; the former. Two more controls: a former returning a declared type constructor, and one returning a type
; constructor bound by the enclosing telescope, both accepted; and one returning its own binder, refused.
(let ((many tyc0)) (l2 (k (KTyCtor)) (l0)))
(let ((many x3-ty)) (l3 (k (KValCtor)) (l1 (l2 nat (a "z"))) (l3 (k (KValCtor)) (l1 (l2 nat (a "n"))) (a "Type"))))
(let ((many t2-decl))
  (l2 (k (KDefAdts))
    (l3 (a "T2") (l1 (l2 (a "Type") (a "P")))
      (l3 (a "C2") (l2 (l2 x3-ty (a "x3")) (l2 nat (a "z"))) (l2 (a "T2") (l2 (l2 (a "x3") (a "z")) zero))))))
(let ((many mk-defn)) (l3 (k (KDefFns)) (a "L") (l4 (a "mk") (l0) (l1 (l2 tyc0 (a "A"))) (a "Nat"))))
(let ((many let-a0)) (l3 (k (KLet)) (l1 (a "A0")) (l1 (a "mk"))))
(let ((many t3-decl)) (l2 (k (KDefAdts)) (l3 (a "T3") (l0) $ l3 (a "C3") (l1 (l3 (l1 (a "A0")) (k (KIs)) (a "w"))) (l1 (a "T3")))))
(let ((many x-ty)) (l3 (k (KValCtor)) (l1 (l2 tyc0 (a "A"))) (a "Type")))
(let ((many inner)) (l4 (k (KMatch)) (a "s2") (l1 (l2 nat (a "r2"))) (l2 (l2 (a "C3") (a "wp")) zero)))
(let ((many outer-defn))
  (l3 (k (KDefFns)) (a "L")
    (l4 (a "outer") (l3 (l2 x-ty (a "x")) (l2 (l2 (a "T2") (l2 (a "x") (a "A0"))) (a "s")) (l2 (l1 (a "T3")) (a "s2"))) (l1 (l2 nat (a "r")))
      (l4 (k (KMatch)) (a "s") (l1 (l2 nat (a "r"))) (l2 (l3 (a "C2") (a "x3p") (a "zp")) inner)))))
(let ((many prog)) (Cons _ nat-decl $ Cons _ lvl-decl $ Cons _ t2-decl $ Cons _ mk-defn $ Cons _ let-a0 $ Cons _ t3-decl $ Cons _ outer-defn $ Cons _ zero $ Nil _))
(def-fns _ $ (many shape : (many (List (Sexp)) p) -> (many (Maybe (Maybe (Reason))) r))
  (let-match many (elab-program p) (MkProgramDec _ out _) ((ProgramStuck _) (None _)))
  (match many out _
    ((PErr r) (Some _ (Some _ r)))
    ((POk _ _) (Some _ (None _)))))

; control 1: the field a type entry instead of an is entry
(let ((many t3-ty-decl)) (l2 (k (KDefAdts)) (l3 (a "T3") (l0) $ l3 (a "C3") (l1 (l2 (l1 (a "A0")) (a "w"))) (l1 (a "T3")))))
(let ((many prog-ty)) (Cons _ nat-decl $ Cons _ lvl-decl $ Cons _ t2-decl $ Cons _ mk-defn $ Cons _ let-a0 $ Cons _ t3-ty-decl $ Cons _ outer-defn $ Cons _ zero $ Nil _))
; control 2: no forcing, the inner match alone as the body
(let ((many outer-plain))
  (l3 (k (KDefFns)) (a "L")
    (l4 (a "outer") (l3 (l2 x-ty (a "x")) (l2 (l2 (a "T2") (l2 (a "x") (a "A0"))) (a "s")) (l2 (l1 (a "T3")) (a "s2"))) (l1 (l2 nat (a "r"))) inner)))
(let ((many prog-plain)) (Cons _ nat-decl $ Cons _ lvl-decl $ Cons _ t2-decl $ Cons _ mk-defn $ Cons _ let-a0 $ Cons _ t3-decl $ Cons _ outer-plain $ Cons _ zero $ Nil _))
; control 3: a former returning a type constructor in scope, as a parameter's type
(let ((many ok-defn)) (l3 (k (KDefFns)) (a "L") (l4 (a "h") (l1 (l2 (l3 (k (KValCtor)) (l1 (l2 nat (a "n"))) (l1 (a "T4"))) (a "c"))) (l1 (l2 nat (a "r"))) zero)))
(let ((many t4-decl)) (l2 (k (KDefAdts)) (l3 (a "T4") (l0) $ l3 (a "C4") (l0) (l1 (a "T4")))))
(let ((many prog-ok)) (Cons _ nat-decl $ Cons _ lvl-decl $ Cons _ t4-decl $ Cons _ ok-defn $ Cons _ zero $ Nil _))
; control 5: a former returning a type constructor bound by the enclosing telescope
(let ((many nest-defn)) (l3 (k (KDefFns)) (a "L") (l4 (a "h") (l2 (l2 tyc0 (a "U")) (l2 (l3 (k (KValCtor)) (l1 (l2 nat (a "n"))) (l1 (a "U"))) (a "c"))) (l1 (l2 nat (a "r"))) zero)))
(let ((many prog-nest)) (Cons _ nat-decl $ Cons _ lvl-decl $ Cons _ nest-defn $ Cons _ zero $ Nil _))
; control 4: a former returning its own binder
(let ((many own-defn)) (l3 (k (KDefFns)) (a "L") (l4 (a "h") (l1 (l2 (l3 (k (KValCtor)) (l1 (l2 tyc0 (a "U"))) (l1 (a "U"))) (a "c"))) (l1 (l2 nat (a "r"))) zero)))
(let ((many prog-own)) (Cons _ nat-decl $ Cons _ lvl-decl $ Cons _ own-defn $ Cons _ zero $ Nil _))
(Cons _ (shape prog) $ Cons _ (shape prog-ty) $ Cons _ (shape prog-plain) $ Cons _ (shape prog-ok) $ Cons _ (shape prog-own) $ Cons _ (shape prog-nest) $ Nil _)
