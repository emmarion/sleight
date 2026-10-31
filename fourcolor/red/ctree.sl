(def-adts $ (CtSel : ((Ctree) t) ((Col) e) ((Ctree) u) -> Type)
  enum
  (many SelN0 : (erased (Ctree) t1 t2 t3) -> (CtSel (CNode t1 t2 t3) (C0) (CEmpty)))
  (many SelN1 : (erased (Ctree) t1 t2 t3) -> (CtSel (CNode t1 t2 t3) (C1) t1))
  (many SelN2 : (erased (Ctree) t1 t2 t3) -> (CtSel (CNode t1 t2 t3) (C2) t2))
  (many SelN3 : (erased (Ctree) t1 t2 t3) -> (CtSel (CNode t1 t2 t3) (C3) t3))
  (many SelL : (erased (Ctree) lf) (erased (Col) e) -> (CtSel (CLeaf lf) e (CEmpty)))
  (many SelE : (erased (Col) e) -> (CtSel (CEmpty) e (CEmpty))))

(def-adts $ (CtRoot : ((Ctree) t) ((Nat) n) -> Type)
  enum
  (many RootL : (erased (Ctree) lf) (erased (Nat) n) (erased (CtRoot lf n) p) -> (CtRoot (CLeaf lf) (Succ n)))
  (many RootN : (erased (Ctree) t1 t2 t3) -> (CtRoot (CNode t1 t2 t3) (Zero)))
  (many RootE : -> (CtRoot (CEmpty) (Zero))))

; The multiplicity n of the trace et in t.
(def-adts $ (CtSub : ((Ctree) t) ((List (Col)) et) ((Nat) n) -> Type)
  enum
  (many SubNil : (erased (Ctree) t) (erased (Nat) n) (erased (CtRoot t n) p) -> (CtSub t (Nil (Col)) n))
  (many SubCons : (erased (Ctree) t u) (erased (Col) e) (erased (List (Col)) et) (erased (Nat) n) (erased (CtSel t e u) p)
      (erased (CtSub u et n) q) -> (CtSub t (Cons (Col) e et) n)))

(def-adts $ (CtMem : ((Ctree) t) ((List (Col)) et) -> Type)
  enum
  (many MkCtMem : (erased (Ctree) t) (erased (List (Col)) et) (erased (Nat) n) (erased (CtSub t et (Succ n)) p) -> (CtMem t et)))

; All leaves of t are at depth h.
(def-adts $ (CtH : ((Nat) h) ((Ctree) t) -> Type)
  enum
  (many HE : (erased (Nat) h) -> (CtH h (CEmpty)))
  (many HL : (erased (Ctree) lf) (erased (CtH (Zero) lf) p) -> (CtH (Zero) (CLeaf lf)))
  (many HN : (erased (Nat) h) (erased (Ctree) t1 t2 t3) (erased (CtH h t1) p1) (erased (CtH h t2) p2) (erased (CtH h t3) p3)
      -> (CtH (Succ h) (CNode t1 t2 t3))))

(def-fns _ $ (many sel-node : (many (Ctree) t1 t2 t3) (many (Col) e) -> (many (Ctree) u) (erased (CtSel (CNode t1 t2 t3) e u) s))
  (match many e _
    ((C0) (values (CEmpty) (SelN0 t1 t2 t3)))
    ((C1) (values t1 (SelN1 t1 t2 t3)))
    ((C2) (values t2 (SelN2 t1 t2 t3)))
    ((C3) (values t3 (SelN3 t1 t2 t3)))))

(def-fns _ $ (many sel-exists : (many (Ctree) t) (many (Col) e) -> (many (Ctree) u) (erased (CtSel t e u) s))
  (match many t _
    ((CNode t1 t2 t3) (sel-node t1 t2 t3 e))
    ((CLeaf lf) (values (CEmpty) (SelL lf e)))
    ((CEmpty) (values (CEmpty) (SelE e)))))

(def-fns _ $ (erased sel-fn : (erased (Ctree) t u v) (erased (Col) e) (erased (CtSel t e u) p) (erased (CtSel t e v) q) ->
    (erased (Eq (Ctree) u v) r))
  (match erased p _
    ((SelN0 _ _ _) (let-match erased q (SelN0 _ _ _)) (Refl _ u))
    ((SelN1 _ _ _) (let-match erased q (SelN1 _ _ _)) (Refl _ u))
    ((SelN2 _ _ _) (let-match erased q (SelN2 _ _ _)) (Refl _ u))
    ((SelN3 _ _ _) (let-match erased q (SelN3 _ _ _)) (Refl _ u))
    ((SelL _ _) (let-match erased q (SelL _ _)) (Refl _ u))
    ((SelE _) (let-match erased q (SelE _)) (Refl _ u))))

(def-fns _ $ (many root-exists : (subterm many (Ctree) t) -> (many (Nat) n) (erased (CtRoot t n) r))
  (let-match many t (CLeaf lf) ((CNode t1 t2 t3) (values (Zero) (RootN t1 t2 t3))) ((CEmpty) (values (Zero) (RootE))))
  (let ((many k) (erased r)) (notail $ root-exists lf))
  (values (Succ k) (RootL lf k r)))

(def-fns _ $ (erased root-fn : (erased (Ctree) t) (erased (Nat) n m) (subterm erased (CtRoot t n) p) (erased (CtRoot t m) q) ->
    (erased (Eq (Nat) n m) r))
  (match erased p _
    ((RootL lf k p1) (let-match erased q (RootL _ j q1)) (eq-cong-succ k j (root-fn lf k j p1 q1)))
    ((RootN _ _ _) (let-match erased q (RootN _ _ _)) (Refl _ n))
    ((RootE) (let-match erased q (RootE)) (Refl _ n))))

(def-fns _ $ (many sub-exists : (many (Ctree) t) (subterm many (List (Col)) et) -> (many (Nat) n) (erased (CtSub t et n) s))
  (match many et _
    ((Nil _) (let ((many n) (erased r)) (root-exists t)) (values n (SubNil t n r)))
    ((Cons _ e et1)
      (let ((many u) (erased sl)) (sel-exists t e))
      (let ((many n) (erased s)) (tail $ sub-exists u et1))
      (values n (SubCons t u e et1 n sl s)))))

(def-fns _ $ (erased sub-fn : (erased (Ctree) t) (erased (List (Col)) et) (erased (Nat) n m) (subterm erased (CtSub t et n) p)
    (erased (CtSub t et m) q) -> (erased (Eq (Nat) n m) r))
  (match erased p _
    ((SubNil _ _ r1) (let-match erased q (SubNil _ _ r2)) (root-fn t n m r1 r2))
    ((SubCons _ u e et1 _ s1 p1)
      (let-match erased q (SubCons _ v _ _ _ s2 q1))
      (let-match erased (sel-fn t u v e s1 s2) (Refl _ _))
      (sub-fn u et1 n m p1 q1))))

(def-fns _ $ (erased sub-sel : (erased (Ctree) t u) (erased (Col) e) (erased (List (Col)) et) (erased (Nat) n)
    (erased (CtSub t (Cons (Col) e et) n) p) (erased (CtSel t e u) s) -> (erased (CtSub u et n) q))
  (let-match erased p (SubCons _ v _ _ _ s1 q))
  (let-match erased (sel-fn t u v e s s1) (Refl _ _))
  q)

(def-fns _ $ (erased absurd sub-empty : (erased (List (Col)) et) (erased (Nat) n) (subterm erased (CtSub (CEmpty) et (Succ n)) s) ->
    (erased (False) f))
  (match erased s _
    (absurd (SubNil _ _ r) r)
    (absurd (SubCons _ _ _ et1 _ sl s1) (let-match erased sl (SelE _)) (sub-empty et1 n s1))))

(def-fns _ $ (erased mem-cons : (erased (Ctree) t u) (erased (Col) e) (erased (List (Col)) et) (erased (CtSel t e u) s)
    (erased (CtMem u et) m) -> (erased (CtMem t (Cons (Col) e et)) r))
  (let-match erased m (MkCtMem _ _ n p))
  (MkCtMem t (Cons _ e et) n (SubCons t u e et (Succ n) s p)))

(def-fns _ $ (erased mem-sel : (erased (Ctree) t u) (erased (Col) e) (erased (List (Col)) et) (erased (CtMem t (Cons (Col) e et)) m)
    (erased (CtSel t e u) s) -> (erased (CtMem u et) r))
  (let-match erased m (MkCtMem _ _ n p))
  (MkCtMem u et n (sub-sel t u e et (Succ n) p s)))

(def-adts $ (CtCons : ((Ctree) t1) ((Ctree) t2) ((Ctree) t3) ((Ctree) t) -> Type)
  enum
  (many CCEmpty : -> (CtCons (CEmpty) (CEmpty) (CEmpty) (CEmpty)))
  (many CCNode : (erased (Ctree) t1 t2 t3) -> (CtCons t1 t2 t3 (CNode t1 t2 t3))))

(def-fns _ $ (many ctree-cons : (many (Ctree) t1 t2 t3) -> (many (Ctree) t) (erased (CtCons t1 t2 t3 t) p))
  (let-match many t1 (CEmpty) (else (values (CNode t1 t2 t3) (CCNode t1 t2 t3))))
  (let-match many t2 (CEmpty) (else (values (CNode t1 t2 t3) (CCNode t1 t2 t3))))
  (let-match many t3 (CEmpty) (else (values (CNode t1 t2 t3) (CCNode t1 t2 t3))))
  (values (CEmpty) (CCEmpty)))

(def-fns _ $ (erased cons-sel : (erased (Ctree) t1 t2 t3 t u) (erased (Col) e) (erased (CtCons t1 t2 t3 t) c)
    (erased (CtSel t e u) s) -> (erased (CtSel (CNode t1 t2 t3) e u) r))
  (let-match erased c (CCEmpty)
    ((CCNode _ _ _) s))
  (let-match erased s (SelE _))
  (let ((erased _) (erased r)) (sel-node (CEmpty) (CEmpty) (CEmpty) e))
  (match erased r _
    ((SelN0 _ _ _) r) ((SelN1 _ _ _) r) ((SelN2 _ _ _) r) ((SelN3 _ _ _) r)))

(def-fns _ $ (erased cons-sel-back : (erased (Ctree) t1 t2 t3 t u) (erased (Col) e) (erased (CtCons t1 t2 t3 t) c)
    (erased (CtSel (CNode t1 t2 t3) e u) s) -> (erased (CtSel t e u) r))
  (let-match erased c (CCEmpty)
    ((CCNode _ _ _) s))
  (match erased s _
    ((SelN0 _ _ _) (SelE e)) ((SelN1 _ _ _) (SelE e)) ((SelN2 _ _ _) (SelE e)) ((SelN3 _ _ _) (SelE e))))

(def-fns _ $ (erased cons-root : (erased (Ctree) t1 t2 t3 t) (erased (CtCons t1 t2 t3 t) c) -> (erased (CtRoot t (Zero)) r))
  (match erased c _ ((CCNode _ _ _) (RootN t1 t2 t3)) ((CCEmpty) (RootE))))

(def-fns _ $ (erased cons-h : (erased (Nat) h) (erased (Ctree) t1 t2 t3 t) (erased (CtCons t1 t2 t3 t) c)
    (erased (CtH h t1) p1) (erased (CtH h t2) p2) (erased (CtH h t3) p3) -> (erased (CtH (Succ h) t) r))
  (match erased c _ ((CCNode _ _ _) (HN h t1 t2 t3 p1 p2 p3)) ((CCEmpty) (HE (Succ h)))))

(def-fns _ $ (erased cons-mem : (erased (Ctree) t1 t2 t3 t) (erased (List (Col)) et) (erased (CtCons t1 t2 t3 t) c)
    (erased (CtMem t et) m) -> (erased (Col) e) (erased (List (Col)) et1) (erased (Eq (List (Col)) et (Cons (Col) e et1)) q)
    (erased (Ctree) u) (erased (CtSel (CNode t1 t2 t3) e u) s) (erased (CtMem u et1) r))
  (let-match erased m (MkCtMem _ _ n p))
  (let-match erased p (SubCons _ u e et1 _ s1 p1)
    (absurd (SubNil _ _ rt) (root-fn t (Succ n) (Zero) rt (cons-root t1 t2 t3 t c))))
  (values e et1 (Refl _ et) u (cons-sel t1 t2 t3 t u e c s1) (MkCtMem u et1 n p1)))

(def-fns _ $ (erased empty-sub : (subterm erased (List (Col)) et) -> (erased (CtSub (CEmpty) et (Zero)) s))
  (match erased et _
    ((Nil _) (SubNil (CEmpty) (Zero) (RootE)))
    ((Cons _ e et1) (SubCons (CEmpty) (CEmpty) e et1 (Zero) (SelE e) (empty-sub et1)))))

(def-fns _ $ (erased leaf-mem : (erased (Ctree) lf) -> (erased (CtMem (CLeaf lf) (Nil (Col))) m))
  (let ((erased k) (erased r)) (root-exists lf))
  (MkCtMem (CLeaf lf) (Nil _) k (SubNil _ _ (RootL lf k r))))

(def-fns _ $ (erased sel-h : (erased (Nat) h) (erased (Ctree) t1 t2 t3 u) (erased (Col) e) (erased (CtH (Succ h) (CNode t1 t2 t3)) k)
    (erased (CtSel (CNode t1 t2 t3) e u) s) -> (erased (CtH h u) r))
  (let-match erased k (HN _ _ _ _ k1 k2 k3))
  (match erased s _ ((SelN0 _ _ _) (HE h)) ((SelN1 _ _ _) k1) ((SelN2 _ _ _) k2) ((SelN3 _ _ _) k3)))

(def-adts $ (CtOr : ((Ctree) tl) ((Ctree) tr) ((Ctree) t) -> Type)
  enum
  (many OrEL : (erased (Ctree) t) -> (CtOr (CEmpty) t t))
  (many OrER : (erased (Ctree) t) -> (CtOr t (CEmpty) t))
  (many OrLL : (erased (Ctree) a b) -> (CtOr (CLeaf a) (CLeaf b) (CLeaf (CEmpty))))
  (many OrNN : (erased (Ctree) l1 l2 l3 r1 r2 r3 u1 u2 u3 t) (erased (CtOr l1 r1 u1) o1) (erased (CtOr l2 r2 u2) o2)
      (erased (CtOr l3 r3 u3) o3) (erased (CtCons u1 u2 u3 t) c) -> (CtOr (CNode l1 l2 l3) (CNode r1 r2 r3) t)))

(def-fns _ $ (many ctree-union : (erased (Nat) h) (many (Ctree) tl) (subterm many (Ctree) tr) (erased (CtH h tl) hl) (erased (CtH h tr) hr) ->
    (many (Ctree) t) (erased (CtOr tl tr t) o) (erased (CtH h t) ht))
  (match many tr _
    ((CEmpty) (values tl (OrER tl) hl))
    ((CLeaf b)
      (let-match erased hr (HL _ _))
      (match many tl _
        ((CEmpty) (values tr (OrEL tr) hr))
        ((CLeaf a) (values simple-leaf (OrLL a b) (HL (CEmpty) (HE (Zero)))))
        (absurd (CNode _ _ _) hl)))
    ((CNode r1 r2 r3)
      (let-match erased hr (HN h1 _ _ _ q1 q2 q3))
      (let-match many tl (CNode l1 l2 l3)
        ((CEmpty) (values tr (OrEL tr) hr))
        (absurd (CLeaf _) hl))
      (let-match erased hl (HN _ _ _ _ p1 p2 p3))
      (let ((many u1) (erased o1) (erased k1)) (notail $ ctree-union h1 l1 r1 p1 q1))
      (let ((many u2) (erased o2) (erased k2)) (notail $ ctree-union h1 l2 r2 p2 q2))
      (let ((many u3) (erased o3) (erased k3)) (notail $ ctree-union h1 l3 r3 p3 q3))
      (let ((many t) (erased c)) (ctree-cons u1 u2 u3))
      (values t (OrNN l1 l2 l3 r1 r2 r3 u1 u2 u3 t o1 o2 o3 c) (cons-h h1 u1 u2 u3 t c k1 k2 k3)))))

(def-fns _ $ (erased or-lift : (erased (Ctree) tl tr l r) (erased (Col) e) (erased (List (Col)) et) (erased (CtSel tl e l) sl)
    (erased (CtSel tr e r) sr) (erased (Or (CtMem l et) (CtMem r et)) o) ->
    (erased (Or (CtMem tl (Cons (Col) e et)) (CtMem tr (Cons (Col) e et))) res))
  (match erased o _
    ((InL _ _ m) (InL _ _ (mem-cons tl l e et sl m)))
    ((InR _ _ m) (InR _ _ (mem-cons tr r e et sr m)))))

(def-fns _ $ (erased or-mem : (erased (Ctree) tl tr t) (subterm erased (List (Col)) et) (erased (CtOr tl tr t) o) (erased (CtMem t et) m)
    -> (erased (Or (CtMem tl et) (CtMem tr et)) r))
  (match erased o _
    ((OrEL _) (InR _ _ m))
    ((OrER _) (InL _ _ m))
    ((OrLL a _)
      (let-match erased m (MkCtMem _ _ n s))
      (let-match erased s (SubNil _ _ _) (absurd (SubCons _ _ _ et1 _ sl s1) (let-match erased sl (SelL _ _)) (sub-empty et1 n s1)))
      (InL _ _ (leaf-mem a)))
    ((OrNN l1 l2 l3 r1 r2 r3 u1 u2 u3 _ o1 o2 o3 c)
      (let ((erased e) (erased et1) (erased q) (erased _) (erased s) (erased m1)) (cons-mem u1 u2 u3 t et c m))
      (let-match erased q (Refl _ _))
      (match erased s _
        (absurd (SelN0 _ _ _) (let-match erased m1 (MkCtMem _ _ n p)) (sub-empty et1 n p))
        ((SelN1 _ _ _) (or-lift (CNode l1 l2 l3) (CNode r1 r2 r3) l1 r1 e et1 (SelN1 l1 l2 l3) (SelN1 r1 r2 r3) (or-mem l1 r1 u1 et1 o1 m1)))
        ((SelN2 _ _ _) (or-lift (CNode l1 l2 l3) (CNode r1 r2 r3) l2 r2 e et1 (SelN2 l1 l2 l3) (SelN2 r1 r2 r3) (or-mem l2 r2 u2 et1 o2 m1)))
        ((SelN3 _ _ _) (or-lift (CNode l1 l2 l3) (CNode r1 r2 r3) l3 r3 e et1 (SelN3 l1 l2 l3) (SelN3 r1 r2 r3) (or-mem l3 r3 u3 et1 o3 m1)))))))

; t2 holds the traces whose image under g is in t.
(def-adts $ (CtPerm : ((Perm) g) ((Ctree) t) ((Ctree) t2) -> Type)
  enum
  (many CPE : (erased (Perm) g) -> (CtPerm g (CEmpty) (CEmpty)))
  (many CPL : (erased (Perm) g) (erased (Ctree) lf) -> (CtPerm g (CLeaf lf) (CLeaf lf)))
  (many CPN : (erased (Col) g1 g2 g3) (erased (Ctree) t1 t2 t3 u1 u2 u3 a1 a2 a3 t)
      (erased (CtSel (CNode t1 t2 t3) g1 u1) s1) (erased (CtSel (CNode t1 t2 t3) g2 u2) s2) (erased (CtSel (CNode t1 t2 t3) g3 u3) s3)
      (erased (CtPerm (MkPerm g1 g2 g3) u1 a1) p1) (erased (CtPerm (MkPerm g1 g2 g3) u2 a2) p2)
      (erased (CtPerm (MkPerm g1 g2 g3) u3 a3) p3) (erased (CtCons a1 a2 a3 t) c) -> (CtPerm (MkPerm g1 g2 g3) (CNode t1 t2 t3) t)))

(def-adts $ (RotDir : ((Bool) left) ((Perm) g) -> Type)
  enum
  (many RDL : -> (RotDir (BTrue) p312))
  (many RDR : -> (RotDir (BFalse) p231)))

(def-fns _ $ (many ctree-rot : (many (Bool) left) (erased (Perm) g) (erased (RotDir left g) d) (subterm many (Ctree) t) ->
    (many (Ctree) r) (erased (CtPerm g t r) p))
  (let-match many t (CNode t1 t2 t3)
    ((CEmpty) (values t (CPE g)))
    ((CLeaf lf) (values t (CPL g lf))))
  (let ((many a1) (erased p1)) (notail $ ctree-rot left g d t1))
  (let ((many a2) (erased p2)) (notail $ ctree-rot left g d t2))
  (let ((many a3) (erased p3)) (notail $ ctree-rot left g d t3))
  (match many left _
    ((BTrue) (let-match erased d (RDL)) (let ((many r) (erased c)) (ctree-cons a3 a1 a2))
      (values r (CPN (C3) (C1) (C2) t1 t2 t3 t3 t1 t2 a3 a1 a2 r (SelN3 t1 t2 t3) (SelN1 t1 t2 t3) (SelN2 t1 t2 t3) p3 p1 p2 c)))
    ((BFalse) (let-match erased d (RDR)) (let ((many r) (erased c)) (ctree-cons a2 a3 a1))
      (values r (CPN (C2) (C3) (C1) t1 t2 t3 t2 t3 t1 a2 a3 a1 r (SelN2 t1 t2 t3) (SelN3 t1 t2 t3) (SelN1 t1 t2 t3) p2 p3 p1 c)))))

(def-fns _ $ (erased perm-h : (erased (Perm) g) (erased (Nat) h) (erased (Ctree) t tp) (subterm erased (CtPerm g t tp) p) (erased (CtH h t) k) ->
    (erased (CtH h tp) r))
  (let-match erased p (CPN g1 g2 g3 t1 t2 t3 u1 u2 u3 a1 a2 a3 _ s1 s2 s3 p1 p2 p3 c)
    ((CPE _) k)
    ((CPL _ _) k))
  (let-match erased k (HN h1 _ _ _ _ _ _))
  (cons-h h1 a1 a2 a3 tp c (perm-h g h1 u1 a1 p1 (sel-h h1 t1 t2 t3 u1 g1 k s1)) (perm-h g h1 u2 a2 p2 (sel-h h1 t1 t2 t3 u2 g2 k s2))
    (perm-h g h1 u3 a3 p3 (sel-h h1 t1 t2 t3 u3 g3 k s3))))

(def-adts $ (PermMem : ((Perm) g) ((Ctree) t) ((List (Col)) et) -> Type)
  enum
  (many MkPermMem : (erased (Perm) g) (erased (Ctree) t) (erased (List (Col)) et et2) (erased (PermT g et et2) p)
      (erased (CtMem t et2) m) -> (PermMem g t et)))

(def-fns _ $ (erased absurd mem-empty : (erased (List (Col)) et) (erased (CtMem (CEmpty) et) m) -> (erased (False) f))
  (let-match erased m (MkCtMem _ _ n s))
  (sub-empty et n s))

(def-fns _ $ (erased leaf-mem-nil : (erased (Ctree) lf) (erased (List (Col)) et) (erased (CtMem (CLeaf lf) et) m) ->
    (erased (Eq (List (Col)) et (Nil (Col))) q))
  (let-match erased m (MkCtMem _ _ n s))
  (let-match erased s (SubNil _ _ _) (absurd (SubCons _ _ _ et1 _ sl s1) (let-match erased sl (SelL _ _)) (sub-empty et1 n s1)))
  (Refl _ et))

(def-fns _ $ (erased pm-lift : (erased (Perm) g) (erased (Ctree) t u) (erased (Col) e e2) (erased (List (Col)) et) (erased (PermC g e e2) pc)
    (erased (CtSel t e2 u) s) (erased (PermMem g u et) pm) -> (erased (PermMem g t (Cons (Col) e et)) r))
  (let-match erased pm (MkPermMem _ _ _ et2 p m))
  (MkPermMem g t (Cons _ e et) (Cons _ e2 et2) (PTCons g e e2 et et2 pc p) (mem-cons t u e2 et2 s m)))

(def-fns _ $ (erased perm-mem : (erased (Perm) g) (erased (Ctree) t tp) (subterm erased (List (Col)) et) (erased (CtPerm g t tp) p)
    (erased (CtMem tp et) m) -> (erased (PermMem g t et) r))
  (match erased p _
    (absurd (CPE _) (mem-empty et m))
    ((CPL _ lf) (let-match erased (leaf-mem-nil lf et m) (Refl _ _)) (MkPermMem g t et et (PTNil g) m))
    ((CPN g1 g2 g3 _ _ _ u1 u2 u3 a1 a2 a3 _ s1 s2 s3 p1 p2 p3 c)
      (let ((erased e) (erased et1) (erased q) (erased _) (erased s) (erased m1)) (cons-mem a1 a2 a3 tp et c m))
      (let-match erased q (Refl _ _))
      (match erased s _
        (absurd (SelN0 _ _ _) (mem-empty et1 m1))
        ((SelN1 _ _ _) (pm-lift g t u1 e g1 et1 (PC1 g1 g2 g3) s1 (perm-mem g u1 a1 et1 p1 m1)))
        ((SelN2 _ _ _) (pm-lift g t u2 e g2 et1 (PC2 g1 g2 g3) s2 (perm-mem g u2 a2 et1 p2 m1)))
        ((SelN3 _ _ _) (pm-lift g t u3 e g3 et1 (PC3 g1 g2 g3) s3 (perm-mem g u3 a3 et1 p3 m1)))))))

; t holds the union of the left rotation of tl and the right rotation of tr.
(def-adts $ (CtRLR : ((Ctree) tl) ((Ctree) tr) ((Ctree) t) -> Type)
  enum
  (many RLN : (erased (Ctree) l1 l2 l3 r1 r2 r3 u1 u2 u3 t) (erased (CtRLR l3 r2 u1) o1) (erased (CtRLR l1 r3 u2) o2)
      (erased (CtRLR l2 r1 u3) o3) (erased (CtCons u1 u2 u3 t) c) -> (CtRLR (CNode l1 l2 l3) (CNode r1 r2 r3) t))
  (many RLLL : (erased (Ctree) a b) -> (CtRLR (CLeaf a) (CLeaf b) (CLeaf (CEmpty))))
  (many RLU : (erased (Ctree) tl tr a b t) (erased (CtPerm p312 tl a) pa) (erased (CtPerm p231 tr b) pb) (erased (CtOr a b t) o)
      -> (CtRLR tl tr t)))

(def-fns _ $ (many ctree-union-rot : (erased (Nat) h) (many (Ctree) tl tr) (erased (CtH h tl) hl) (erased (CtH h tr) hr) ->
    (many (Ctree) t) (erased (CtRLR tl tr t) o) (erased (CtH h t) ht))
  (let ((many a) (erased pa)) (ctree-rot (BTrue) p312 (RDL) tl))
  (let ((many b) (erased pb)) (ctree-rot (BFalse) p231 (RDR) tr))
  (let ((many t) (erased o) (erased ht)) (ctree-union h a b (perm-h p312 h tl a pa hl) (perm-h p231 h tr b pb hr)))
  (values t (RLU tl tr a b t pa pb o) ht))

(def-fns _ $ (many ctree-union-rotlr : (erased (Nat) h) (many (Ctree) tl) (subterm many (Ctree) tr) (erased (CtH h tl) hl) (erased (CtH h tr) hr) ->
    (many (Ctree) t) (erased (CtRLR tl tr t) o) (erased (CtH h t) ht))
  (match many tr _
    ((CLeaf b)
      (let-match erased hr (HL _ _))
      (match many tl _ ((CLeaf a) (values simple-leaf (RLLL a b) (HL (CEmpty) (HE (Zero))))) (else (ctree-union-rot h tl tr hl hr))))
    ((CEmpty) (ctree-union-rot h tl tr hl hr))
    ((CNode r1 r2 r3)
      (let-match many tl (CNode l1 l2 l3) (else (ctree-union-rot h tl tr hl hr)))
      (let-match erased hl (HN h1 _ _ _ p1 p2 p3))
      (let-match erased hr (HN _ _ _ _ q1 q2 q3))
      (let ((many u1) (erased o1) (erased k1)) (notail $ ctree-union-rotlr h1 l3 r2 p3 q2))
      (let ((many u2) (erased o2) (erased k2)) (notail $ ctree-union-rotlr h1 l1 r3 p1 q3))
      (let ((many u3) (erased o3) (erased k3)) (notail $ ctree-union-rotlr h1 l2 r1 p2 q1))
      (let ((many t) (erased c)) (ctree-cons u1 u2 u3))
      (values t (RLN l1 l2 l3 r1 r2 r3 u1 u2 u3 t o1 o2 o3 c) (cons-h h1 u1 u2 u3 t c k1 k2 k3)))))

(def-fns _ $ (erased rlr-lift : (erased (Ctree) tl tr l r) (erased (Col) e el er) (erased (List (Col)) et)
    (erased (PermC p312 e el) pl) (erased (CtSel tl el l) sl) (erased (PermC p231 e er) pr) (erased (CtSel tr er r) sr)
    (erased (Or (PermMem p312 l et) (PermMem p231 r et)) o) ->
    (erased (Or (PermMem p312 tl (Cons (Col) e et)) (PermMem p231 tr (Cons (Col) e et))) res))
  (match erased o _
    ((InL _ _ m) (InL _ _ (pm-lift p312 tl l e el et pl sl m)))
    ((InR _ _ m) (InR _ _ (pm-lift p231 tr r e er et pr sr m)))))

(def-fns _ $ (erased rlr-mem : (erased (Ctree) tl tr t) (subterm erased (List (Col)) et) (erased (CtRLR tl tr t) o) (erased (CtMem t et) m)
    -> (erased (Or (PermMem p312 tl et) (PermMem p231 tr et)) r))
  (match erased o _
    ((RLLL a _)
      (let-match erased (leaf-mem-nil (CEmpty) et m) (Refl _ _))
      (InL _ _ (MkPermMem p312 tl et et (PTNil p312) (leaf-mem a))))
    ((RLU _ _ a b _ pa pb o1)
      (match erased (or-mem a b t et o1 m) _
        ((InL _ _ ma) (InL _ _ (perm-mem p312 tl a et pa ma)))
        ((InR _ _ mb) (InR _ _ (perm-mem p231 tr b et pb mb)))))
    ((RLN l1 l2 l3 r1 r2 r3 u1 u2 u3 _ o1 o2 o3 c)
      (let ((erased e) (erased et1) (erased q) (erased _) (erased s) (erased m1)) (cons-mem u1 u2 u3 t et c m))
      (let-match erased q (Refl _ _))
      (match erased s _
        (absurd (SelN0 _ _ _) (mem-empty et1 m1))
        ((SelN1 _ _ _) (rlr-lift tl tr l3 r2 e (C3) (C2) et1 (PC1 (C3) (C1) (C2)) (SelN3 l1 l2 l3) (PC1 (C2) (C3) (C1)) (SelN2 r1 r2 r3)
          (rlr-mem l3 r2 u1 et1 o1 m1)))
        ((SelN2 _ _ _) (rlr-lift tl tr l1 r3 e (C1) (C3) et1 (PC2 (C3) (C1) (C2)) (SelN1 l1 l2 l3) (PC2 (C2) (C3) (C1)) (SelN3 r1 r2 r3)
          (rlr-mem l1 r3 u2 et1 o2 m1)))
        ((SelN3 _ _ _) (rlr-lift tl tr l2 r1 e (C2) (C1) et1 (PC3 (C3) (C1) (C2)) (SelN2 l1 l2 l3) (PC3 (C2) (C3) (C1)) (SelN1 r1 r2 r3)
          (rlr-mem l2 r1 u3 et1 o3 m1)))))))

(def-adts $ (CtDisj : ((Ctree) tl) ((Ctree) tr) -> Type)
  enum
  (many DjN : (erased (Ctree) l1 l2 l3 r1 r2 r3) (erased (CtDisj l1 r1) d1) (erased (CtDisj l2 r2) d2) (erased (CtDisj l3 r3) d3)
      -> (CtDisj (CNode l1 l2 l3) (CNode r1 r2 r3)))
  (many DjEL : (erased (Ctree) t) -> (CtDisj (CEmpty) t))
  (many DjER : (erased (Ctree) t) -> (CtDisj t (CEmpty)))
  (many DjLN : (erased (Ctree) a r1 r2 r3) -> (CtDisj (CLeaf a) (CNode r1 r2 r3)))
  (many DjNL : (erased (Ctree) l1 l2 l3 a) -> (CtDisj (CNode l1 l2 l3) (CLeaf a))))

(def-adts $ (Both : ((Ctree) tl) ((Ctree) tr) -> Type)
  enum
  (many MkBoth : (erased (Ctree) tl tr) (erased (List (Col)) et) (erased (CtMem tl et) ml) (erased (CtMem tr et) mr) -> (Both tl tr)))

(def-adts $ (DisjRes : ((Ctree) tl) ((Ctree) tr) -> Type)
  enum
  (many DjYes : (erased (Ctree) tl tr) (erased (CtDisj tl tr) d) -> (DisjRes tl tr))
  (many DjNo : (erased (Ctree) tl tr) (erased (Both tl tr) b) -> (DisjRes tl tr)))

(def-fns _ $ (erased both-lift : (erased (Ctree) tl tr l r) (erased (Col) e) (erased (CtSel tl e l) sl) (erased (CtSel tr e r) sr)
    (erased (Both l r) b) -> (erased (Both tl tr) res))
  (let-match erased b (MkBoth _ _ et ml mr))
  (MkBoth tl tr (Cons _ e et) (mem-cons tl l e et sl ml) (mem-cons tr r e et sr mr)))

(def-fns _ $ (many ctree-disjoint : (many (Ctree) tl) (subterm many (Ctree) tr) -> (many (DisjRes tl tr) b))
  (match many tr _
    ((CEmpty) (DjYes tl tr (DjER tl)))
    ((CLeaf a)
      (match many tl _
        ((CLeaf b) (DjNo tl tr (MkBoth tl tr (Nil _) (leaf-mem b) (leaf-mem a))))
        ((CEmpty) (DjYes tl tr (DjEL tr)))
        ((CNode l1 l2 l3) (DjYes tl tr (DjNL l1 l2 l3 a)))))
    ((CNode r1 r2 r3)
      (let-match many tl (CNode l1 l2 l3)
        ((CEmpty) (DjYes tl tr (DjEL tr)))
        ((CLeaf b) (DjYes tl tr (DjLN b r1 r2 r3))))
      (let-match many (notail $ ctree-disjoint l1 r1) (DjYes _ _ d1)
        ((DjNo _ _ b) (DjNo tl tr (both-lift tl tr l1 r1 (C1) (SelN1 l1 l2 l3) (SelN1 r1 r2 r3) b))))
      (let-match many (notail $ ctree-disjoint l2 r2) (DjYes _ _ d2)
        ((DjNo _ _ b) (DjNo tl tr (both-lift tl tr l2 r2 (C2) (SelN2 l1 l2 l3) (SelN2 r1 r2 r3) b))))
      (let-match many (notail $ ctree-disjoint l3 r3) (DjYes _ _ d3)
        ((DjNo _ _ b) (DjNo tl tr (both-lift tl tr l3 r3 (C3) (SelN3 l1 l2 l3) (SelN3 r1 r2 r3) b))))
      (DjYes tl tr (DjN l1 l2 l3 r1 r2 r3 d1 d2 d3)))))

(def-fns _ $ (erased absurd disj-mem : (erased (Ctree) tl tr) (subterm erased (List (Col)) et) (erased (CtDisj tl tr) d)
    (erased (CtMem tl et) ml) (erased (CtMem tr et) mr) -> (erased (False) f))
  (match erased d _
    (absurd (DjEL _) (mem-empty et ml))
    (absurd (DjER _) (mem-empty et mr))
    (absurd (DjLN a _ _ _)
      (let-match erased (leaf-mem-nil a et ml) (Refl _ _))
      (let-match erased mr (MkCtMem _ _ _ s))
      (let-match erased s (SubNil _ _ rt))
      rt)
    (absurd (DjNL _ _ _ a)
      (let-match erased (leaf-mem-nil a et mr) (Refl _ _))
      (let-match erased ml (MkCtMem _ _ _ s))
      (let-match erased s (SubNil _ _ rt))
      rt)
    (absurd (DjN l1 l2 l3 r1 r2 r3 d1 d2 d3)
      (let ((erased e) (erased et1) (erased q) (erased _) (erased s) (erased m1)) (cons-mem l1 l2 l3 tl et (CCNode l1 l2 l3) ml))
      (let-match erased q (Refl _ _))
      (match erased s _
        (absurd (SelN0 _ _ _) (mem-empty et1 m1))
        (absurd (SelN1 _ _ _) (disj-mem l1 r1 et1 d1 m1 (mem-sel tr r1 e et1 mr (SelN1 r1 r2 r3))))
        (absurd (SelN2 _ _ _) (disj-mem l2 r2 et1 d2 m1 (mem-sel tr r2 e et1 mr (SelN2 r1 r2 r3))))
        (absurd (SelN3 _ _ _) (disj-mem l3 r3 et1 d3 m1 (mem-sel tr r3 e et1 mr (SelN3 r1 r2 r3))))))))

