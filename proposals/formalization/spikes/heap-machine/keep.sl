(def-adts
  ((Shape : ((Block) b1) ((Block) b2) -> Type)
    enum
    (many MkShape : (erased (Nat) tag) (erased (List (Word)) fs1 fs2) (erased (LenEq (Word) (Word) fs1 fs2) le)
       -> (Shape (MkBlock tag fs1) (MkBlock tag fs2)))))

(def-fns _ $ (erased leneq-refl : (subterm erased (List (Word)) xs) -> (erased (LenEq (Word) (Word) xs xs) p))
  (match erased xs _
    ((Nil _) (LENil _ _))
    ((Cons _ x rest) (LECons _ _ x x rest rest (leneq-refl rest)))))

(def-fns _ $ (erased leneq-trans : (erased (List (Word)) xs ys zs)
    (subterm erased (LenEq (Word) (Word) xs ys) p) (erased (LenEq (Word) (Word) ys zs) q) -> (erased (LenEq (Word) (Word) xs zs) r))
  (match erased p _
    ((LENil _ _) (let-match erased q (LENil _ _)) (LENil _ _))
    ((LECons _ _ x y xs1 ys1 p1)
      (let-match erased q (LECons _ _ _ z _ zs1 q1))
      (LECons _ _ x z xs1 zs1 (leneq-trans xs1 ys1 zs1 p1 q1)))))

(def-fns _ $ (erased setnth-leneq : (erased (List (Word)) xs) (erased (Nat) i) (erased (Word) y) (erased (List (Word)) ys)
    (subterm erased (SetNth (Word) xs i y ys) p) -> (erased (LenEq (Word) (Word) xs ys) q))
  (match erased p _
    ((SetHere _ x _ rest) (LECons _ _ x y rest rest (leneq-refl rest)))
    ((SetThere _ x rest j _ rest2 p1) (LECons _ _ x x rest rest2 (setnth-leneq rest j y rest2 p1)))))

(def-fns _ $ (erased shape-refl : (erased (Block) b) -> (erased (Shape b b) s))
  (let-match erased b (MkBlock tag fs))
  (MkShape tag fs fs (leneq-refl fs)))

(def-fns _ $ (erased shape-trans : (erased (Block) b1 b2 b3) (erased (Shape b1 b2) p) (erased (Shape b2 b3) q) -> (erased (Shape b1 b3) r))
  (let-match erased p (MkShape tag fs1 fs2 le1))
  (let-match erased q (MkShape _ _ fs3 le2))
  (MkShape tag fs1 fs3 (leneq-trans fs1 fs2 fs3 le1 le2)))

(def-fns _ $ (erased lookup-fresh-neq : (erased (Heap) h) (erased (Nat) x p) (erased (Block) b)
    (subterm erased (Lookup h x b) lk) (erased (Fresh h p) f) -> (erased (Neq x p) n))
  (match erased lk _
    ((LkHere _ _ rest) (let-match erased f (FreshCons _ _ _ _ n _)) (neq-sym p x n))
    ((LkThere _ c _ other rest _ lk1) (let-match erased f (FreshCons _ _ _ _ _ f1)) (lookup-fresh-neq rest x p b lk1 f1))))

(def-fns _ $ (erased update-fresh-back : (erased (Heap) h) (erased (Nat) a) (erased (Block) blk) (erased (Heap) h2) (erased (Nat) x)
    (subterm erased (Update h a blk h2) u) (erased (Fresh h2 x) f) -> (erased (Fresh h x) g))
  (match erased u _
    ((UpHere _ old _ rest) (let-match erased f (FreshCons _ _ _ _ n f1)) (FreshCons x a old rest n f1))
    ((UpThere _ c _ other rest rest2 _ u1)
      (let-match erased f (FreshCons _ _ _ _ n f1))
      (FreshCons x c other rest n (update-fresh-back rest a blk rest2 x u1 f1)))))

(def-fns _ $ (erased update-keeps : (erased (Heap) h) (erased (Nat) a) (erased (Block) old new) (erased (Heap) h2) (erased (Nat) x) (erased (Block) b)
    (subterm erased (Update h a new h2) u) (erased (Lookup h a old) la) (erased (Shape old new) sh) (erased (Lookup h x b) lx) ->
    (erased (Block) b2) (erased (Lookup h2 x b2) lk) (erased (Shape b b2) s))
  (match erased u _
    ((UpHere _ old0 _ rest)
      (let-match erased la (LkHere _ _ _) (absurd (LkThere _ _ _ _ _ n _) (neq-irrefl a n)))
      (match erased lx _
        ((LkHere _ _ _) (values new (LkHere a new rest) sh))
        ((LkThere _ _ _ _ _ n lx1) (values b (LkThere x a b new rest n lx1) (shape-refl b)))))
    ((UpThere _ c _ other rest rest2 nac u1)
      (let-match erased la (LkThere _ _ _ _ _ _ la1) (absurd (LkHere _ _ _) (neq-irrefl a nac)))
      (let-match erased lx (LkThere _ _ _ _ _ n lx1) ((LkHere _ _ _) (values b (LkHere c other rest2) (shape-refl b))))
      (let ((erased b2) (erased lk) (erased s)) (update-keeps rest a old new rest2 x b u1 la1 sh lx1))
      (values b2 (LkThere x c b2 other rest2 n lk) s))))

(def-fns _ $ (erased alloc-keeps : (erased (Heap) h) (erased (Nat) p) (erased (Block) blk) (erased (Heap) h2) (erased (Nat) x) (erased (Block) b)
    (erased (Alloc h p blk h2) al) (erased (Lookup h x b) lx) -> (erased (Lookup h2 x b) lk))
  (let-match erased al (MkAlloc _ _ _ f))
  (LkThere x p b blk h (lookup-fresh-neq h x p b lx f) lx))

(def-fns _ $ (erased alloc-fresh-back : (erased (Heap) h) (erased (Nat) p) (erased (Block) blk) (erased (Heap) h2) (erased (Nat) x)
    (erased (Alloc h p blk h2) al) (erased (Fresh h2 x) f) -> (erased (Fresh h x) g))
  (let-match erased al (MkAlloc _ _ _ _))
  (let-match erased f (FreshCons _ _ _ _ _ g))
  g)

(def-fns _ $ (erased patched-shape : (erased (Heap) h) (erased (List (Word)) env) (erased (Atom) a) (erased (Nat) i) (erased (Atom) b)
    (erased (Nat) p) (erased (Block) blk) (erased (Patched h env a i b p blk) pt) ->
    (erased (Block) old) (erased (Lookup h p old) lk) (erased (Shape old blk) s))
  (let-match erased pt (MkPatched _ _ _ _ _ _ w tag fs fs2 _ _ lk st))
  (values (MkBlock tag fs) lk (MkShape tag fs fs2 (setnth-leneq fs i w fs2 st))))

(def-fns _ $ (erased prim-grows : (erased (Heap) h) (erased (List (Word)) env) (erased (Instr) i) (erased (Label) l) (erased (Heap) h2) (erased (Word) w)
    (erased (Nat) x) (erased (Prim h env i l h2 w) d) (erased (Fresh h2 x) f) -> (erased (Fresh h x) g))
  (match erased d _
    ((PAtom _ _ _ _ _) f)
    ((PCon _ _ tag _ ws p _ _ al) (alloc-fresh-back h p (MkBlock tag ws) h2 x al f))
    ((PWrite _ _ _ _ _ p blk _ _ up) (update-fresh-back h p blk h2 x up f))
    ((PCopy _ _ _ _ _ _ blk q _ _ al) (alloc-fresh-back h q blk h2 x al f))
    ((PSameYes _ _ _ _ _ _ _) f)
    ((PSameNo _ _ _ _ _ _ _ _) f)))

(def-fns _ $ (erased prim-keeps : (erased (Heap) h) (erased (List (Word)) env) (erased (Instr) i) (erased (Label) l) (erased (Heap) h2) (erased (Word) w)
    (erased (Nat) x) (erased (Block) b) (erased (Prim h env i l h2 w) d) (erased (Lookup h x b) lx) ->
    (erased (Block) b2) (erased (Lookup h2 x b2) lk) (erased (Shape b b2) s))
  (let-match erased d (PWrite _ _ a j v p blk _ pt up)
    ((PAtom _ _ _ _ _) (values b lx (shape-refl b)))
    ((PCon _ _ tag _ ws p _ _ al) (values b (alloc-keeps h p (MkBlock tag ws) h2 x b al lx) (shape-refl b)))
    ((PCopy _ _ _ _ _ _ blk q _ _ al) (values b (alloc-keeps h q blk h2 x b al lx) (shape-refl b)))
    ((PSameYes _ _ _ _ _ _ _) (values b lx (shape-refl b)))
    ((PSameNo _ _ _ _ _ _ _ _) (values b lx (shape-refl b))))
  (let ((erased old) (erased la) (erased sh)) (patched-shape h env a j v p blk pt))
  (update-keeps h p old blk h2 x b up la sh lx))

(def-fns _ $ (erased prim-label-fresh : (erased (Heap) h) (erased (List (Word)) env) (erased (Instr) i) (erased (Nat) p) (erased (Heap) h2) (erased (Word) w)
    (erased (Prim h env i (LAddr p) h2 w) d) -> (erased (Fresh h p) f))
  (match erased d _
    ((PCon _ _ _ _ _ _ _ _ al) (let-match erased al (MkAlloc _ _ _ f)) f)
    ((PCopy _ _ _ _ _ _ _ _ _ _ al) (let-match erased al (MkAlloc _ _ _ f)) f)))

(def-fns _ $ (erased run-grows : (erased (List (Code)) fns) (erased (Heap) h) (erased (List (Word)) env) (erased (Code) c) (erased (Choices) ch)
    (erased (Heap) h2) (erased (Word) w) (erased (Nat) x)
    (subterm erased (Run fns h env c ch h2 w) d) (erased (Fresh h2 x) f) -> (erased (Fresh h x) g))
  (match erased d _
    ((RunDo _ _ _ i l _ _ p) (prim-grows h env i l h2 w x p f))
    ((RunLet _ _ _ rhs body ch1 h1 w1 ch2 _ _ p q)
      (run-grows fns h env rhs ch1 h1 w1 x p (run-grows fns h1 (Cons _ w1 env) body ch2 h2 w x q f)))
    ((RunMatch _ _ _ _ _ _ _ body _ env2 _ _ _ _ _ _ q) (run-grows fns h env2 body ch h2 w x q f))
    ((RunCall _ _ _ _ _ body ws _ _ _ _ _ q) (run-grows fns h ws body ch h2 w x q f))))

(def-fns _ $ (erased run-keeps : (erased (List (Code)) fns) (erased (Heap) h) (erased (List (Word)) env) (erased (Code) c) (erased (Choices) ch)
    (erased (Heap) h2) (erased (Word) w) (erased (Nat) x) (erased (Block) b)
    (subterm erased (Run fns h env c ch h2 w) d) (erased (Lookup h x b) lx) ->
    (erased (Block) b2) (erased (Lookup h2 x b2) lk) (erased (Shape b b2) s))
  (let-match erased d (RunLet _ _ _ rhs body ch1 h1 w1 ch2 _ _ p q)
    ((RunDo _ _ _ i l _ _ p) (prim-keeps h env i l h2 w x b p lx))
    ((RunMatch _ _ _ _ _ _ _ body _ env2 _ _ _ _ _ _ q) (run-keeps fns h env2 body ch h2 w x b q lx))
    ((RunCall _ _ _ _ _ body ws _ _ _ _ _ q) (run-keeps fns h ws body ch h2 w x b q lx)))
  (let ((erased b1) (erased lk1) (erased s1)) (run-keeps fns h env rhs ch1 h1 w1 x b p lx))
  (let ((erased b2) (erased lk2) (erased s2)) (run-keeps fns h1 (Cons _ w1 env) body ch2 h2 w x b1 q lk1))
  (values b2 lk2 (shape-trans b b1 b2 s1 s2)))

(def-fns _ $ (erased step-grows : (erased (List (Code)) fns) (erased (Heap) h) (erased (Control) c) (erased (Label) l) (erased (Heap) h2) (erased (Control) c2)
    (erased (Nat) x) (erased (Step fns h c l h2 c2) d) (erased (Fresh h2 x) f) -> (erased (Fresh h x) g))
  (match erased d _
    ((StDo _ _ env i _ _ _ w p) (prim-grows h env i l h2 w x p f))
    ((StLet _ _ _ _ _ _) f)
    ((StRet _ _ _ _ _ _) f)
    ((StMatch _ _ _ _ _ _ _ _ _ _ _ _ _ _) f)
    ((StCall _ _ _ _ _ _ _ _ _ _) f)))

(def-fns _ $ (erased steps-grows : (erased (List (Code)) fns) (erased (Heap) h) (erased (Control) c) (erased (List (Label)) ls) (erased (Heap) h2) (erased (Control) c2)
    (erased (Nat) x) (subterm erased (Steps fns h c ls h2 c2) d) (erased (Fresh h2 x) f) -> (erased (Fresh h x) g))
  (match erased d _
    ((StepsNil _ _ _) f)
    ((StepsCons _ _ _ l h1 c1 rest _ _ p q) (step-grows fns h c l h1 c1 x p (steps-grows fns h1 c1 rest h2 c2 x q f)))))

(def-fns _ $ (erased step-label-fresh : (erased (List (Code)) fns) (erased (Heap) h) (erased (Control) c) (erased (Nat) p) (erased (Heap) h2) (erased (Control) c2)
    (erased (Step fns h c (LAddr p) h2 c2) d) -> (erased (Fresh h p) f))
  (let-match erased d (StDo _ _ env i _ _ _ w q))
  (prim-label-fresh h env i p h2 w q))

(def-fns _ $ (erased never-reused : (erased (List (Code)) fns) (erased (Heap) h0) (erased (Control) c0) (erased (List (Label)) ls)
    (erased (Heap) h) (erased (Control) c) (erased (Nat) p) (erased (Heap) h2) (erased (Control) c2)
    (erased (Steps fns h0 c0 ls h c) before) (erased (Step fns h c (LAddr p) h2 c2) d) -> (erased (Fresh h0 p) f))
  (steps-grows fns h0 c0 ls h c p before (step-label-fresh fns h c p h2 c2 d)))

(def-fns _ $ (erased absurd alloc-not-live : (erased (Heap) h) (erased (Nat) p) (erased (Block) blk b) (erased (Heap) h2)
    (erased (Alloc h p blk h2) al) (erased (Lookup h p b) lk) -> (erased (False) f))
  (let-match erased al (MkAlloc _ _ _ fr))
  (neq-irrefl p (lookup-fresh-neq h p p b lk fr)))
