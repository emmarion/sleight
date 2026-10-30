(def-adts $ (Col : -> Type)
  enum
  (many C0 : -> (Col))
  (many C1 : -> (Col))
  (many C2 : -> (Col))
  (many C3 : -> (Col)))

(def-adts $ (Perm : -> Type)
  enum
  (many MkPerm : (many (Col) p1 p2 p3) -> (Perm)))

(def-adts $ (Step : -> Type)
  enum
  (many SR : (many (Nat) n) -> (Step))
  (many SRr : -> (Step))
  (many SY : -> (Step))
  (many SH : -> (Step))
  (many SU : -> (Step))
  (many SK : -> (Step))
  (many SA : -> (Step)))

(def-adts $ (Config : -> Type)
  enum
  (many MkConfig : (many (Bool) sym) (many (List (Nat)) contract) (many (List (Step)) prog) -> (Config)))

(def-adts $ (Ctree : -> Type)
  enum
  (many CNode : (many (Ctree) t1 t2 t3) -> (Ctree))
  (many CLeaf : (many (Ctree) lf) -> (Ctree))
  (many CEmpty : -> (Ctree)))

(def-adts $ (Gsym : -> Type)
  enum
  (many GPush : -> (Gsym))
  (many GSkip : -> (Gsym))
  (many GPop0 : -> (Gsym))
  (many GPop1 : -> (Gsym)))

(def-adts $ (Gtree : -> Type)
  enum
  (many GNode : (many (Gtree) t0 t1 t2 t3) -> (Gtree))
  (many GL0 : -> (Gtree))
  (many GL1 : -> (Gtree))
  (many GL2 : -> (Gtree))
  (many GL3 : -> (Gtree))
  (many GL01 : -> (Gtree))
  (many GL12 : -> (Gtree))
  (many GL13 : -> (Gtree))
  (many GL23 : -> (Gtree))
  (many GEmpty : -> (Gtree)))

(def-adts $ (Bstack : -> Type)
  enum
  (many BS0 : -> (Bstack))
  (many BP0 : (many (Bstack) bs) -> (Bstack))
  (many BP1 : (many (Bstack) bs) -> (Bstack)))

(def-adts $ (Rx : (Type T) -> Type)
  enum
  (many MkRx : (erased Type T) (many (Bstack) bs) (many T t) -> (Rx T)))

(def-adts $ (Kr : -> Type)
  enum
  (many KDone : (many (Ctree) ctu) (many (Gtree) gtr gtu) -> (Kr))
  (many KGo : (many (Ctree) ctu ctr) (many (Gtree) gtu) -> (Kr)))

(def-adts $ (CtrStep : -> Type)
  enum
  (many CStop : (many (Maybe (List (Step))) r) -> (CtrStep))
  (many CGo : (many (List (Bool)) mr mc) (many (List (Step)) pre) -> (CtrStep)))

(def-fns _ $ (many bif : (erased Type A) (many (Bool) b) (many A x y) -> (many A r))
  (match many b _ ((BTrue) x) ((BFalse) y)))

(def-fns _ $ (many orb : (many (Bool) a b) -> (many (Bool) c))
  (bif _ a (BTrue) b))

(def-fns _ $ (many andb : (many (Bool) a b) -> (many (Bool) c))
  (bif _ a b (BFalse)))

(def-fns _ $ (many negb : (many (Bool) a) -> (many (Bool) c))
  (bif _ a (BFalse) (BTrue)))

(def-fns _ $ (many nat-eqb : (many (Nat) a b) -> (many (Bool) c))
  (match many (nat-eq a b) _ ((Equal _ _ _) (BTrue)) ((Unequal _ _ _ _ _) (BFalse))))

(def-fns _ $ (many nat-ltb : (many (Nat) a b) -> (many (Bool) c))
  (match many (nat-cmp a b) _ ((CLt _ _ _ _ _) (BTrue)) (else (BFalse))))

(def-fns _ $ (many monus : (subterm many (Nat) a) (many (Nat) b) -> (many (Nat) r))
  (let-match many b (Succ b1) ((Zero) a))
  (let-match many a (Succ a1) ((Zero) 0))
  (tail $ monus a1 b1))

(def-fns _ $ (many mem-nat : (many (Nat) x) (subterm many (List (Nat)) xs) -> (many (Bool) b))
  (let-match many xs (Cons _ y rest) ((Nil _) (BFalse)))
  (match many (nat-eqb x y) _ ((BTrue) (BTrue)) ((BFalse) (tail $ mem-nat x rest))))

(def-fns _ $ (many nilp : (erased Type A) (many (List A) xs) -> (many (Bool) b))
  (match many xs _ ((Nil _) (BTrue)) (else (BFalse))))

(def-fns _ $ (many size : (erased Type A) (subterm many (List A) xs) -> (many (Nat) n))
  (let-match many xs (Cons _ _ rest) ((Nil _) 0))
  (Succ $ notail $ size _ rest))

(def-fns _ $ (many cat : (erased Type A) (subterm many (List A) xs) (many (List A) ys) -> (many (List A) zs))
  (let-match many xs (Cons _ x rest) ((Nil _) ys))
  (Cons _ x $ notail $ cat _ rest ys))

(def-fns _ $ (many rev-onto : (erased Type A) (subterm many (List A) xs) (many (List A) acc) -> (many (List A) zs))
  (let-match many xs (Cons _ x rest) ((Nil _) acc))
  (tail $ rev-onto _ rest (Cons _ x acc)))

(def-fns _ $ (many take : (erased Type A) (subterm many (Nat) n) (many (List A) xs) -> (many (List A) ys))
  (let-match many n (Succ n1) ((Zero) (Nil _)))
  (let-match many xs (Cons _ x rest) ((Nil _) (Nil _)))
  (Cons _ x $ notail $ take _ n1 rest))

(def-fns _ $ (many drop : (erased Type A) (subterm many (Nat) n) (many (List A) xs) -> (many (List A) ys))
  (let-match many n (Succ n1) ((Zero) xs))
  (let-match many xs (Cons _ _ rest) ((Nil _) (Nil _)))
  (tail $ drop _ n1 rest))

(def-fns _ $ (many rot : (erased Type A) (many (Nat) n) (many (List A) xs) -> (many (List A) ys))
  (cat _ (drop _ n xs) (take _ n xs)))

(def-fns _ $ (many rotr : (erased Type A) (many (Nat) n) (many (List A) xs) -> (many (List A) ys))
  (rot _ (monus (size _ xs) n) xs))

(def-fns _ $ (many nseq : (erased Type A) (subterm many (Nat) n) (many A x) -> (many (List A) ys))
  (let-match many n (Succ n1) ((Zero) (Nil _)))
  (Cons _ x $ notail $ nseq _ n1 x))

(def-fns _ $ (many count-b : (many (Bool) b) (subterm many (List (Bool)) bs) -> (many (Nat) n))
  (let-match many bs (Cons _ x rest) ((Nil _) 0))
  (let ((many k)) (notail $ count-b b rest))
  (bif _ (orb (andb b x) (negb (orb b x))) (Succ k) k))

(def-fns _ $ (many mask : (erased Type A) (subterm many (List (Bool)) m) (many (List A) xs) -> (many (List A) ys))
  (let-match many m (Cons _ b m1) ((Nil _) (Nil _)))
  (let-match many xs (Cons _ x rest) ((Nil _) (Nil _)))
  (let ((many ys)) (notail $ mask _ m1 rest))
  (bif _ b (Cons _ x ys) ys))

(def-fns _ $ (many addc : (many (Col) a b) -> (many (Col) c))
  (match many a _
    ((C0) b)
    ((C1) (match many b _ ((C0) (C1)) ((C1) (C0)) ((C2) (C3)) ((C3) (C2))))
    ((C2) (match many b _ ((C0) (C2)) ((C1) (C3)) ((C2) (C0)) ((C3) (C1))))
    ((C3) (match many b _ ((C0) (C3)) ((C1) (C2)) ((C2) (C1)) ((C3) (C0))))))

(def-fns _ $ (many col-eq : (many (Col) a b) -> (many (Bool) r))
  (match many (addc a b) _ ((C0) (BTrue)) (else (BFalse))))

(def-fns _ $ (many permc : (many (Perm) g) (many (Col) c) -> (many (Col) d))
  (let-match many g (MkPerm p1 p2 p3))
  (match many c _ ((C0) (C0)) ((C1) p1) ((C2) p2) ((C3) p3)))

(let ((many p123)) (MkPerm (C1) (C2) (C3)))
(let ((many p132)) (MkPerm (C1) (C3) (C2)))
(let ((many p231)) (MkPerm (C2) (C3) (C1)))
(let ((many p312)) (MkPerm (C3) (C1) (C2)))

(def-fns _ $ (many perm-comp : (many (Perm) g h) -> (many (Perm) gh))
  (let-match many h (MkPerm h1 h2 h3))
  (MkPerm (permc g h1) (permc g h2) (permc g h3)))

(def-fns _ $ (many edge-rot : (many (Col) c) -> (many (Perm) g))
  (match many c _ ((C2) p312) ((C3) p231) (else p123)))

(def-fns _ $ (many cc : (many (Col) c) (many (List (Col)) et) -> (many (List (Col)) r))
  (Cons _ c $ Cons _ c et))

(def-fns _ $ (many ct-empty : (many (Ctree) t) -> (many (Bool) b))
  (match many t _ ((CEmpty) (BTrue)) (else (BFalse))))

(def-fns _ $ (many ct-leaf : (many (Ctree) t) -> (many (Bool) b))
  (match many t _ ((CLeaf _) (BTrue)) (else (BFalse))))

(def-fns _ $ (many ct-cons : (many (Ctree) t1 t2 t3) -> (many (Ctree) t))
  (bif _ (andb (ct-empty t1) $ andb (ct-empty t2) (ct-empty t3)) (CEmpty) (CNode t1 t2 t3)))

(let ((many simple-leaf)) (CLeaf (CEmpty)))

(def-fns _ $ (many ct-cons-e : (many (Col) c) (many (Ctree) t) -> (many (Ctree) r))
  (match many c _
    ((C0) (CEmpty))
    ((C1) (ct-cons t (CEmpty) (CEmpty)))
    ((C2) (ct-cons (CEmpty) t (CEmpty)))
    ((C3) (ct-cons (CEmpty) (CEmpty) t))))

(def-fns _ $ (many ct-union : (many (Ctree) tl) (subterm many (Ctree) tr) -> (many (Ctree) t))
  (let-match many tr (CNode r1 r2 r3) ((CEmpty) tl) ((CLeaf _) (bif _ (ct-empty tl) tr simple-leaf)))
  (let-match many tl (CNode l1 l2 l3) ((CEmpty) tr) ((CLeaf _) simple-leaf))
  (ct-cons (notail $ ct-union l1 r1) (notail $ ct-union l2 r2) (notail $ ct-union l3 r3)))

(def-fns _ $ (many ct-rot : (many (Bool) left) (subterm many (Ctree) t) -> (many (Ctree) r))
  (let-match many t (CNode t1 t2 t3) (else t))
  (let ((many a1) (many a2) (many a3)) (values (notail $ ct-rot left t1) (notail $ ct-rot left t2) (notail $ ct-rot left t3)))
  (bif _ left (ct-cons a3 a1 a2) (ct-cons a2 a3 a1)))

(def-fns _ $ (many ct-cons-rot : (many (Ctree) t) -> (many (Ctree) r))
  (ct-cons t (ct-rot (BTrue) t) (ct-rot (BFalse) t)))

(def-fns _ $ (many ct-union-rot : (many (Ctree) tl tr) -> (many (Ctree) t))
  (ct-union (ct-rot (BTrue) tl) (ct-rot (BFalse) tr)))

(def-fns _ $ (many ct-union-rotlr : (many (Ctree) tl) (subterm many (Ctree) tr) -> (many (Ctree) t))
  (let-match many tr (CNode r1 r2 r3)
    ((CLeaf _) (bif _ (ct-leaf tl) simple-leaf (ct-union-rot tl tr)))
    ((CEmpty) (ct-union-rot tl tr)))
  (let-match many tl (CNode l1 l2 l3) (else (ct-union-rot tl tr)))
  (ct-cons (notail $ ct-union-rotlr l3 r2) (notail $ ct-union-rotlr l1 r3) (notail $ ct-union-rotlr l2 r1)))

(def-fns _ $ (many ct-disjoint : (many (Ctree) tl) (subterm many (Ctree) tr) -> (many (Bool) b))
  (let-match many tr (CNode r1 r2 r3) ((CLeaf _) (negb (ct-leaf tl))) ((CEmpty) (BTrue)))
  (let-match many tl (CNode l1 l2 l3) (else (BTrue)))
  (let-match many (notail $ ct-disjoint l1 r1) (BTrue) ((BFalse) (BFalse)))
  (let-match many (notail $ ct-disjoint l2 r2) (BTrue) ((BFalse) (BFalse)))
  (tail $ ct-disjoint l3 r3))

(def-fns _ $ (many cfcbr2 : (many (Perm) g) (subterm many (List (Col)) et) -> (many (Ctree) t))
  (let-match many et (Cons _ e rest) ((Nil _) simple-leaf))
  (ct-cons-e (permc g e) $ notail $ cfcbr2 g rest))

(def-fns _ $ (many cfcbr1 : (many (Perm) g) (subterm many (List (Col)) et) -> (many (Ctree) t))
  (let-match many et (Cons _ e rest) ((Nil _) simple-leaf))
  (match many (permc g e) _
    ((C0) (CEmpty))
    ((C1) (ct-cons-e (C1) $ notail $ cfcbr1 g rest))
    ((C2) (ct-cons-e (C2) $ cfcbr2 g rest))
    ((C3) (ct-cons-e (C2) $ cfcbr2 (perm-comp p132 g) rest))))

(def-fns _ $ (many cpbranch : (many (List (Col)) et) -> (many (Ctree) t))
  (let-match many et (Cons _ _ r1) ((Nil _) (CEmpty)))
  (let-match many r1 (Cons _ e r2) ((Nil _) (CEmpty)))
  (match many e _ ((C0) (CEmpty)) (else (cfcbr1 (edge-rot e) r2))))

(def-fns _ $ (many cpcol : (subterm many (List (Step)) cp) (many (List (Col)) et) -> (many (Ctree) t))
  (let-match many cp (Cons _ s rest) ((Nil _) (cpbranch et)))
  (match many s _
    ((SR n) (tail $ cpcol rest (rot _ n et)))
    ((SRr) (match many (nat-ltb 1 (size _ et)) _ ((BTrue) (tail $ cpcol rest (rotr _ 1 et))) ((BFalse) (CEmpty))))
    ((SU) (ct-union (notail $ cpcol rest (cc (C1) et)) $ ct-union (notail $ cpcol rest (cc (C2) et)) (notail $ cpcol rest (cc (C3) et))))
    ((SY)
      (let-match many et (Cons _ e1 r1) ((Nil _) (CEmpty)))
      (let ((many e2) (many e3)) (values (permc p231 e1) (permc p312 e1)))
      (ct-union (notail $ cpcol rest (Cons _ e2 $ Cons _ e3 r1)) (notail $ cpcol rest (Cons _ e3 $ Cons _ e2 r1))))
    (else
      (let-match many et (Cons _ e1 r1) ((Nil _) (CEmpty)))
      (let-match many r1 (Cons _ e2 r2) ((Nil _) (CEmpty)))
      (let ((many same)) (col-eq e1 e2))
      (match many s _
        ((SK) (match many same _ ((BTrue) (CEmpty)) ((BFalse) (tail $ cpcol rest (Cons _ (addc e1 e2) r2)))))
        ((SH)
          (match many same _
            ((BTrue) (ct-union (notail $ cpcol rest (cc (permc p231 e1) r2)) (notail $ cpcol rest (cc (permc p312 e1) r2))))
            ((BFalse) (tail $ cpcol rest (Cons _ e2 $ Cons _ e1 r2)))))
        (else
          (let ((many (List (Col)) next)) (match many r2 _ ((Nil _) et) (else r2)))
          (match many same _ ((BTrue) (tail $ cpcol rest next)) ((BFalse) (CEmpty))))))))

(def-fns _ $ (many cpcolor0 : (subterm many (List (Step)) cp) -> (many (Ctree) t))
  (let-match many cp (Cons _ s rest) ((Nil _) (cpcol cp (cc (C1) (Nil _)))))
  (match many s _
    ((SR _) (tail $ cpcolor0 rest))
    ((SY) (cpcol rest (Cons _ (C1) $ Cons _ (C2) $ Cons _ (C3) $ Nil _)))
    ((SU) (ct-union (cpcol rest (cc (C1) $ cc (C2) $ Nil _)) (cpcol rest (cc (C1) $ cc (C1) $ Nil _))))
    (else (cpcol cp (cc (C1) (Nil _))))))

(def-fns _ $ (many cpcolor : (many (List (Step)) cp) -> (many (Ctree) t))
  (ct-cons-rot (cpcolor0 (rev-onto _ cp (Nil _)))))

(def-fns _ $ (many gsel : (erased Type A) (many (Gsym) s) (many A x0 x1 x2 x3) -> (many A r))
  (match many s _ ((GPush) x0) ((GSkip) x1) ((GPop0) x2) ((GPop1) x3)))

(def-fns _ $ (many spick : (erased Type A) (many (Bstack) bs) (many A x y z) -> (many A r))
  (match many bs _ ((BS0) x) ((BP0 _) y) ((BP1 _) z)))

(def-fns _ $ (many leaf-has : (many (Gtree) t) (many (Gsym) s) -> (many (Bool) b))
  (let ((many T) (many F)) (values (BTrue) (BFalse)))
  (match many t _
    ((GL0) (gsel _ s T F F F))
    ((GL1) (gsel _ s F T F F))
    ((GL2) (gsel _ s F F T F))
    ((GL3) (gsel _ s F F F T))
    ((GL01) (gsel _ s T T F F))
    ((GL12) (gsel _ s F T T F))
    ((GL13) (gsel _ s F T F T))
    ((GL23) (gsel _ s F F T T))
    (else F)))

(def-fns _ $ (many gt-empty : (many (Gtree) t) -> (many (Bool) b))
  (match many t _ ((GEmpty) (BTrue)) (else (BFalse))))

(def-fns _ $ (many rcons-if : (erased Type T) (many (Bool) empty) (many (Bstack) bs) (many T t) (many (List (Rx T)) r) -> (many (List (Rx T)) r2))
  (bif _ empty r (Cons _ (MkRx _ bs t) r)))

(def-fns _ $ (many rpop : (erased Type T) (many (Bool) e2 e3) (many (Bstack) bs) (many T t2 t3) (many (List (Rx T)) r2 r3) ->
    (many (List (Rx T)) a2 a3))
  (match many bs _
    ((BS0) (values r2 r3))
    ((BP0 b) (values (rcons-if _ e2 b t2 r2) (rcons-if _ e3 b t3 r3)))
    ((BP1 b) (values (rcons-if _ e3 b t3 r2) (rcons-if _ e2 b t2 r3)))))

(def-fns _ $ (many ctr-split : (many (List (Rx (Gtree))) r1 r2 r3) (subterm many (List (Rx (Gtree))) r) ->
    (many (List (Rx (Gtree))) s1 s2 s3))
  (let-match many r (Cons _ x rest) ((Nil _) (values r1 r2 r3)))
  (let-match many x (MkRx _ bs t))
  (let-match many t (GNode t0 t1 t2 t3) (else (tail $ ctr-split r1 r2 r3 rest)))
  (let ((many a2) (many a3)) (rpop _ (gt-empty t2) (gt-empty t3) bs t2 t3 r2 r3))
  (let ((many e0)) (gt-empty t0))
  (tail $ ctr-split (rcons-if _ (gt-empty t1) bs t1 r1) (rcons-if _ e0 (BP0 bs) t0 a2) (rcons-if _ e0 (BP1 bs) t0 a3) rest))

(def-fns _ $ (many decr-if : (many (Bool) b) (many (Ctree) lf) -> (many (Ctree) r))
  (let-match many b (BTrue) ((BFalse) lf))
  (match many lf _ ((CLeaf l) l) (else lf)))

(def-fns _ $ (many ctr-decr : (many (Ctree) lf1 lf2 lf3) (subterm many (List (Rx (Gtree))) r) -> (many (Ctree) m1 m2 m3))
  (let-match many r (Cons _ x rest) ((Nil _) (values lf1 lf2 lf3)))
  (let-match many x (MkRx _ bs t))
  (let ((many push) (many pop0) (many pop1)) (values (leaf-has t (GPush)) (leaf-has t (GPop0)) (leaf-has t (GPop1))))
  (tail $ ctr-decr (decr-if (leaf-has t (GSkip)) lf1)
    (decr-if push $ decr-if (spick _ bs (BFalse) pop0 pop1) lf2)
    (decr-if push $ decr-if (spick _ bs (BFalse) pop1 pop0) lf3) rest))

(def-fns _ $ (many if-e : (many (Ctree) lf lf2) -> (many (Ctree) r))
  (bif _ (ct-empty lf2) lf (CEmpty)))

(def-fns _ $ (many ctree-restrict : (subterm many (Nat) h) (many (Ctree) t) (many (List (Rx (Gtree))) r) -> (many (Ctree) keep gone))
  (let-match many r (Cons _ _ _) ((Nil _) (values t (CEmpty))))
  (let-match many t (CNode t1 t2 t3) (else (values (CEmpty) (CEmpty))))
  (match many h _
    ((Succ h1)
      (let ((many r1) (many r2) (many r3)) (ctr-split (Nil _) (Nil _) (Nil _) r))
      (let ((many a1) (many b1)) (notail $ ctree-restrict h1 t1 r1))
      (let ((many a2) (many b2)) (notail $ ctree-restrict h1 t2 r2))
      (let ((many a3) (many b3)) (notail $ ctree-restrict h1 t3 r3))
      (values (ct-cons a1 a2 a3) (ct-cons b1 b2 b3)))
    ((Zero)
      (let ((many l1) (many l2) (many l3)) (ctr-decr t1 t2 t3 r))
      (values (ct-cons l1 l2 l3) (ct-cons (if-e t1 l1) (if-e t2 l2) (if-e t3 l3))))))

(def-fns _ $ (many gtr-split : (many (List (Rx (Ctree))) r0 r1 r2 r3) (subterm many (List (Rx (Ctree))) r) ->
    (many (List (Rx (Ctree))) s0 s1 s2 s3))
  (let-match many r (Cons _ x rest) ((Nil _) (values r0 r1 r2 r3)))
  (let-match many x (MkRx _ bs t))
  (let-match many t (CNode t1 t2 t3) (else (tail $ gtr-split r0 r1 r2 r3 rest)))
  (let ((many e2) (many e3)) (values (ct-empty t2) (ct-empty t3)))
  (let ((many a2) (many a3)) (rpop _ e2 e3 bs t2 t3 r2 r3))
  (tail $ gtr-split (rcons-if _ e2 (BP0 bs) t2 (rcons-if _ e3 (BP1 bs) t3 r0)) (rcons-if _ (ct-empty t1) bs t1 r1) a2 a3 rest))

(def-fns _ $ (many sym-hit : (many (Gsym) s) (many (Bstack) bs) (many (Ctree) t) -> (many (Bool) b))
  (let-match many t (CNode t1 t2 t3) (else (BFalse)))
  (let ((many l2) (many l3)) (values (ct-leaf t2) (ct-leaf t3)))
  (gsel _ s (orb l2 l3) (ct-leaf t1) (spick _ bs (BFalse) l2 l3) (spick _ bs (BFalse) l3 l2)))

(def-fns _ $ (many gtr-match : (many (Gsym) s) (subterm many (List (Rx (Ctree))) r) -> (many (Bool) b))
  (let-match many r (Cons _ x rest) ((Nil _) (BFalse)))
  (let-match many x (MkRx _ bs t))
  (match many (sym-hit s bs t) _ ((BTrue) (BTrue)) ((BFalse) (tail $ gtr-match s rest))))

(def-fns _ $ (many gsplit1 : (many (Bool) b) (many (Gtree) t) -> (many (Gtree) hit miss))
  (match many b _ ((BTrue) (values t (GEmpty))) ((BFalse) (values (GEmpty) t))))

(def-fns _ $ (many gsplit2 : (many (Bool) ba bb) (many (Gtree) t la lb) -> (many (Gtree) hit miss))
  (match many ba _
    ((BTrue) (match many bb _ ((BTrue) (values t (GEmpty))) ((BFalse) (values la lb))))
    ((BFalse) (match many bb _ ((BTrue) (values lb la)) ((BFalse) (values (GEmpty) t))))))

(def-fns _ $ (many gt-empty4 : (many (Gtree) a0 a1 a2 a3) -> (many (Bool) b))
  (andb (gt-empty a0) $ andb (gt-empty a1) $ andb (gt-empty a2) (gt-empty a3)))

(def-fns _ $ (many gleaf-restrict : (many (Gtree) t) (many (List (Rx (Ctree))) r) -> (many (Gtree) hit miss))
  (match many t _
    ((GL0) (gsplit1 (gtr-match (GPush) r) t))
    ((GL1) (gsplit1 (gtr-match (GSkip) r) t))
    ((GL2) (gsplit1 (gtr-match (GPop0) r) t))
    ((GL3) (gsplit1 (gtr-match (GPop1) r) t))
    ((GL01) (gsplit2 (gtr-match (GPush) r) (gtr-match (GSkip) r) t (GL0) (GL1)))
    ((GL12) (gsplit2 (gtr-match (GSkip) r) (gtr-match (GPop0) r) t (GL1) (GL2)))
    ((GL13) (gsplit2 (gtr-match (GSkip) r) (gtr-match (GPop1) r) t (GL1) (GL3)))
    ((GL23) (gsplit2 (gtr-match (GPop0) r) (gtr-match (GPop1) r) t (GL2) (GL3)))
    (else (values (GEmpty) (GEmpty)))))

(def-fns _ $ (many gtree-restrict : (subterm many (Gtree) t) (many (List (Rx (Ctree))) r) -> (many (Gtree) hit miss))
  (let-match many r (Cons _ _ _) ((Nil _) (values (GEmpty) t)))
  (let-match many t (GNode t0 t1 t2 t3) (else (gleaf-restrict t r)))
  (let ((many r0) (many r1) (many r2) (many r3)) (gtr-split (Nil _) (Nil _) (Nil _) (Nil _) r))
  (let ((many a0) (many b0)) (notail $ gtree-restrict t0 r0))
  (let ((many a1) (many b1)) (notail $ gtree-restrict t1 r1))
  (let ((many a2) (many b2)) (notail $ gtree-restrict t2 r2))
  (let ((many a3) (many b3)) (notail $ gtree-restrict t3 r3))
  (let-match many (gt-empty4 a0 a1 a2 a3) (BFalse) ((BTrue) (values (GEmpty) t)))
  (let-match many (gt-empty4 b0 b1 b2 b3) (BFalse) ((BTrue) (values t (GEmpty))))
  (values (GNode a0 a1 a2 a3) (GNode b0 b1 b2 b3)))

(def-fns _ $ (many ktc-step : (many (Nat) h) (many (Ctree) ctu) (many (Gtree) gtr gtu) -> (many (Kr) k))
  (let-match many (orb (ct-empty ctu) (gt-empty gtr)) (BFalse) ((BTrue) (KDone ctu gtr gtu)))
  (let-match many (gt-empty gtu) (BFalse) ((BTrue) (KDone (CEmpty) (GEmpty) (GEmpty))))
  (let ((many keep) (many gone)) (ctree-restrict h ctu (Cons _ (MkRx _ (BS0) gtr) $ Nil _)))
  (KGo keep (ct-union-rotlr gone gone) gtu))

(def-fns _ $ (many ktc : (subterm many (Nat) d) (many (Nat) h) (many (Ctree) ctu ctr) (many (Gtree) gtu) ->
    (many (Ctree) ctu2) (many (Gtree) gtr2 gtu2))
  (let-match many d (Succ d1)
    ((Zero)
      (let ((many hit) (many miss)) (gtree-restrict gtu (Cons _ (MkRx _ (BS0) ctr) $ Nil _)))
      (values ctu hit miss)))
  (let ((many c1) (many g1) (many u1)) (notail $ ktc d1 h ctu ctr gtu))
  (let ((many (Ctree) c2) (many (Gtree) g2) (many (Gtree) u2))
    (match many (ktc-step h c1 g1 u1) _
      ((KDone a b c) (values a b c))
      ((KGo a b c) (notail $ ktc d1 h a b c))))
  (match many (ktc-step h c2 g2 u2) _
    ((KDone a b c) (values a b c))
    ((KGo a b c) (tail $ ktc d1 h a b c))))

(def-fns _ $ (many dyck-iter : (subterm many (Nat) n) (subterm many (Nat) k) (many (Ctree) t) -> (many (Ctree) r))
  (let-match many k (Succ k1) ((Zero) t))
  (let ((many x)) (notail $ dyck-iter n k1 t))
  (match many n _
    ((Zero) (CLeaf x))
    ((Succ n1) (tail $ dyck-iter n1 (Succ k) x))))

(def-fns _ $ (many add-dyck : (many (Nat) m n) (many (Ctree) t) -> (many (Ctree) r))
  (match many n _
    ((Zero) (CLeaf t))
    ((Succ n1) (dyck-iter n1 (Succ m) t))))

(let ((erased CP)) (Pair (Ctree) (Ctree)))
(let ((erased GP)) (Pair (Gtree) (Gtree)))

(def-fns _ $ (many leaf-table-from : (many (Ctree) lf) (many (Nat) n) (subterm many (Nat) h) -> (many (List CP) tab))
  (let-match many h (Succ h1) ((Zero) (Nil _)))
  (let ((many top)) (MkPair _ _ lf lf))
  (let-match many h1 (Succ h2) ((Zero) (Cons _ top $ Nil _)))
  (Cons _ top $ Cons _ (MkPair _ _ (CEmpty) lf) $ notail $ leaf-table-from (add-dyck 2 n lf) (Succ n) h2))

(def-fns _ $ (many merge-line : (many CP x) (subterm many (List CP) ys) -> (many (List CP) zs))
  (let-match many ys (Cons _ y rest) ((Nil _) (Nil _)))
  (let-match many x (MkPair _ _ t0 t1))
  (let-match many y (MkPair _ _ t2 t3))
  (Cons _ (MkPair _ _ (ct-cons t1 t2 t3) (ct-cons t0 t3 t2)) $ notail $ merge-line y rest))

(def-fns _ $ (many merge-iter : (subterm many (Nat) n) (many (List CP) tab) -> (many (List CP) r))
  (let-match many n (Succ n1) ((Zero) tab))
  (let ((many (List CP) next)) (match many tab _ ((Cons _ line rest) (merge-line line rest)) ((Nil _) tab)))
  (tail $ merge-iter n1 next))

(def-fns _ $ (many prune : (many (Col) c) (subterm many (Ctree) t) -> (many (Ctree) r))
  (let-match many t (CNode t1 t2 t3) (else t))
  (match many c _
    ((C1) (ct-cons (notail $ prune c t1) t2 (CEmpty)))
    ((C2) (ct-cons (CEmpty) (notail $ prune c t2) t3))
    (else (ct-cons t1 (CEmpty) (notail $ prune c t3)))))

(def-fns _ $ (many ctree-init : (many (Nat) h) -> (many (Ctree) t))
  (let ((many tab)) (merge-iter (monus h 1) $ Cons _ (MkPair _ _ (CEmpty) simple-leaf) $ leaf-table-from simple-leaf 0 h))
  (let-match many tab (Cons _ x rest) ((Nil _) (CEmpty)))
  (let-match many rest (Cons _ y _) ((Nil _) (CEmpty)))
  (let-match many x (MkPair _ _ _ t1))
  (let-match many y (MkPair _ _ t2 t3))
  (ct-cons (prune (C1) t1) (prune (C2) t2) (prune (C3) t3)))

(let ((many gp-empty)) (MkPair _ _ (GEmpty) (GEmpty)))

(def-fns _ $ (many gt-merge : (many GP p0 p1 p2) -> (many GP r))
  (let-match many p0 (MkPair _ _ t0 u0))
  (let-match many p1 (MkPair _ _ t1 u1))
  (let-match many p2 (MkPair _ _ t2 t3))
  (MkPair _ _ (GNode t0 u1 t2 t3) (GNode u0 t1 t3 t2)))

(def-fns _ $ (many gt-merge-line : (many GP p0 p1 p2) (many (List GP) lpt) (subterm many (Nat) d) -> (many (List GP) r))
  (let ((many (List GP) rest))
    (match many d _
      ((Zero) (Nil _))
      ((Succ d1)
        (match many lpt _
          ((Nil _) (Cons _ (gt-merge gp-empty p0 p1) $ Cons _ (gt-merge gp-empty gp-empty p0) $ Nil _))
          ((Cons _ p lpt1) (notail $ gt-merge-line p p0 p1 lpt1 d1))))))
  (Cons _ (gt-merge p0 p1 p2) rest))

(def-fns _ $ (many gtree-init-table : (many (Nat) d) (subterm many (Nat) h) -> (many (List GP) tab))
  (let-match many h (Succ h1)
    ((Zero) (Cons _ (MkPair _ _ (GL01) (GL0)) $ Cons _ (MkPair _ _ (GL13) (GL12)) $ Cons _ (MkPair _ _ (GL23) (GL23)) $ Nil _)))
  (let ((many tab)) (notail $ gtree-init-table (Succ d) h1))
  (let-match many tab (Cons _ p1 r1) ((Nil _) tab))
  (let-match many r1 (Cons _ p0 lpt) ((Nil _) tab))
  (gt-merge-line p0 p1 gp-empty lpt d))

(def-fns _ $ (many gtree-init : (many (Nat) h) -> (many (Gtree) t))
  (let-match many h (Succ h1) ((Zero) (GEmpty)))
  (let-match many (gtree-init-table 0 h1) (Cons _ p _) ((Nil _) (GEmpty)))
  (let-match many p (MkPair _ _ t _))
  t)

(def-fns _ $ (many cprsize : (subterm many (List (Step)) cp) -> (many (Nat) n))
  (let-match many cp (Cons _ s rest) ((Nil _) 2))
  (let ((many k)) (notail $ cprsize rest))
  (match many s _
    ((SY) (Succ k))
    ((SU) (Succ $ Succ k))
    ((SK) (Succ $ monus k 2))
    ((SA) (bif _ (nat-ltb 2 k) (monus k 2) k))
    (else k)))

(def-fns _ $ (many kempe-tree : (many (List (Step)) cp) -> (many (Ctree) t))
  (let-match many (cprsize cp) (Succ n1) ((Zero) (CEmpty)))
  (let-match many n1 (Succ h) ((Zero) (CEmpty)))
  (let ((many ct) (many _) (many _)) (ktc (Succ $ Succ h) h (ctree-init (Succ h)) (cpcolor cp) (gtree-init (Succ h))))
  ct)

(def-fns _ $ (many cpksize : (subterm many (List (Step)) cp) -> (many (Nat) n))
  (let-match many cp (Cons _ s rest) ((Nil _) 0))
  (let ((many k)) (notail $ cpksize rest))
  (match many s _ ((SH) (Succ k)) (else k)))

(def-fns _ $ (many ctrmsize : (subterm many (List (Step)) cp) -> (many (Nat) n))
  (let-match many cp (Cons _ s rest) ((Nil _) 0))
  (let ((many k)) (notail $ ctrmsize rest))
  (match many s _
    ((SR _) k)
    ((SY) (bif _ (nilp _ rest) 0 (Succ k)))
    ((SH) (Succ $ Succ $ Succ k))
    (else 0)))

(def-fns _ $ (many ctrmask : (many (List (Nat)) cci) (many (Nat) i) (subterm many (Nat) n) -> (many (List (Bool)) m))
  (let-match many n (Succ n1) ((Zero) (Nil _)))
  (Cons _ (mem-nat i cci) $ notail $ ctrmask cci (Succ i) n1))

(def-fns _ $ (many nsp : (many (Bool) b x y) -> (many (Bool) r))
  (bif _ b (orb x y) (andb x y)))

(def-fns _ $ (many one-step : (many (Bool) none) (many (Step) s) -> (many (List (Step)) r))
  (bif _ none (Nil _) (Cons _ s $ Nil _)))

(def-fns _ $ (many ctr-step : (many (Step) s) (many (List (Step)) rest) (many (List (Bool)) mr mc) -> (many (CtrStep) r))
  (let ((many fail)) (CStop $ None _))
  (match many s _
    ((SR i)
      (let ((many mr1)) (rotr _ i mr))
      (CGo mr1 mc $ Cons _ (SR $ count-b (BFalse) $ take _ i mr1) $ Nil _))
    ((SY)
      (let-match many mr (Cons _ b1 mr1) ((Nil _) fail))
      (let-match many mr1 (Cons _ b2 mr2) ((Nil _) fail))
      (match many rest _
        ((Nil _)
          (let-match many mr2 (Cons _ b3 _) ((Nil _) fail))
          (bif _ (nsp b1 b2 b3) fail (CStop $ Some _ $ one-step (orb b1 $ orb b2 b3) (SY))))
        (else
          (let-match many mc (Cons _ b3 mc1) ((Nil _) fail))
          (bif _ (nsp b1 b2 b3) fail (CGo (Cons _ b3 mr2) mc1 $ one-step (orb b1 b2) (bif _ b3 (SU) (SY)))))))
    ((SH)
      (let-match many mr (Cons _ b1 mr1) ((Nil _) fail))
      (let-match many mr1 (Cons _ b2 mr2) ((Nil _) fail))
      (let-match many mc (Cons _ b3 mc1) ((Nil _) fail))
      (let-match many mc1 (Cons _ b4 mc2) ((Nil _) fail))
      (let-match many mc2 (Cons _ b5 mc3) ((Nil _) fail))
      (let ((many pre))
        (bif _ b3 (Nil _) $ one-step (BFalse) $
          bif _ b1 (bif _ b2 (SA) (SK)) $
          bif _ b2 (SK) $
          bif _ b4 (bif _ b5 (SU) (SY)) $
          bif _ b5 (SY) (SH)))
      (let ((many skip)) (bif _ b1 (andb (negb b2) b5) (andb b2 b4)))
      (bif _ (orb (nsp b3 b1 b4) (nsp b3 b2 b5)) fail $
        bif _ (andb b1 $ andb b2 $ nat-eqb 0 $ count-b (BFalse) mr2) fail $
        CGo (Cons _ b4 $ Cons _ b5 mr2) mc3 (bif _ skip (Nil _) pre)))
    (else fail)))

(def-fns _ $ (many cfctr : (many (List (Bool)) mr mc) (subterm many (List (Step)) cp) -> (many (Maybe (List (Step))) r))
  (let-match many cp (Cons _ s rest) ((Nil _) (None _)))
  (let-match many (ctr-step s rest mr mc) (CGo mr1 mc1 pre) ((CStop r) r))
  (let-match many (notail $ cfctr mr1 mc1 rest) (Some _ cpc) ((None _) (None _)))
  (Some _ $ cat _ pre cpc))

(def-fns _ $ (many ctrband : (many (List (Bool)) cm) (subterm many (List (Step)) cp) -> (many (List (Bool)) mr mk))
  (let ((many F)) (BFalse))
  (let-match many cp (Cons _ s rest) ((Nil _) (values (Nil _) (Nil _))))
  (match many s _
    ((SR n)
      (let ((many mr) (many mk)) (notail $ ctrband cm rest))
      (values (rot _ n mr) mk))
    ((SY)
      (let-match many rest (Cons _ _ _) ((Nil _) (values (Cons _ F $ Cons _ F $ Cons _ F $ Nil _) (Nil _))))
      (let-match many cm (Cons _ b1 cm1) ((Nil _) (values (Nil _) (Nil _))))
      (let ((many mr) (many mk)) (notail $ ctrband cm1 rest))
      (let-match many mr (Cons _ a0 mr1) ((Nil _) (values (Nil _) (Nil _))))
      (let-match many mr1 (Cons _ a1 mr2) ((Nil _) (values (Nil _) (Nil _))))
      (values (Cons _ (orb b1 a0) $ Cons _ F $ Cons _ (orb b1 a1) mr2) mk))
    ((SH)
      (let-match many cm (Cons _ b1 cm1) ((Nil _) (values (Nil _) (Nil _))))
      (let-match many cm1 (Cons _ b0 cm2) ((Nil _) (values (Nil _) (Nil _))))
      (let-match many cm2 (Cons _ b2 cm3) ((Nil _) (values (Nil _) (Nil _))))
      (let ((many mr) (many mk)) (notail $ ctrband cm3 rest))
      (let-match many mr (Cons _ a0 mr1) ((Nil _) (values (Nil _) (Nil _))))
      (let-match many mr1 (Cons _ a1 mr2) ((Nil _) (values (Nil _) (Nil _))))
      (let-match many mr2 (Cons _ a2 mr3) ((Nil _) (values (Nil _) (Nil _))))
      (values (Cons _ (orb b0 a0) $ Cons _ b1 $ Cons _ (orb b2 a2) mr3) (Cons _ (orb b0 $ orb b1 $ orb b2 a1) mk)))
    (else (values (Nil _) (Nil _)))))

(def-fns _ $ (many cpadj : (many (List (Bool)) mr mk) (subterm many (List (Step)) cp) -> (many (List (Bool)) mr2 mk2))
  (let-match many cp (Cons _ s rest)
    ((Nil _)
      (let-match many mr (Cons _ b0 r1) ((Nil _) (values mr mk)))
      (let-match many r1 (Cons _ b1 r2) ((Nil _) (values mr mk)))
      (let-match many r2 (Nil _) (else (values mr mk)))
      (let-match many mk (Nil _) (else (values mr mk)))
      (values (Cons _ b1 $ Cons _ b0 $ Nil _) (Nil _))))
  (match many s _
    ((SR n)
      (let ((many a) (many b)) (notail $ cpadj (rotr _ n mr) mk rest))
      (values (rot _ n a) b))
    ((SY)
      (let-match many mr (Cons _ b0 r1) ((Nil _) (values mr mk)))
      (let-match many r1 (Cons _ b1 r2) ((Nil _) (values mr mk)))
      (let-match many r2 (Cons _ b2 r3) ((Nil _) (values mr mk)))
      (let ((many a) (many mk1)) (notail $ cpadj (Cons _ b0 $ Cons _ b2 r3) mk rest))
      (let-match many a (Cons _ a0 s1) ((Nil _) (values mr mk)))
      (let-match many s1 (Cons _ a2 s2) ((Nil _) (values mr mk)))
      (values (Cons _ (orb a0 b1) $ Cons _ (orb b0 b2) $ Cons _ (orb a2 b1) s2) mk1))
    ((SH)
      (let-match many mr (Cons _ b0 r1) ((Nil _) (values mr mk)))
      (let-match many r1 (Cons _ b1 r2) ((Nil _) (values mr mk)))
      (let-match many mk (Cons _ c1 k1) ((Nil _) (values mr mk)))
      (let ((many a) (many mk1)) (notail $ cpadj (Cons _ b0 $ Cons _ c1 r2) k1 rest))
      (let-match many a (Cons _ a0 s1) ((Nil _) (values mr mk)))
      (let-match many s1 (Cons _ a1 s2) ((Nil _) (values mr mk)))
      (let ((many (Bool) hd)) (match many r2 _ ((Cons _ x _) x) ((Nil _) b0)))
      (let ((many (List (Bool)) tl)) (match many s2 _ ((Cons _ a2 s3) (Cons _ (orb a2 b1) s3)) ((Nil _) s2)))
      (values (Cons _ (orb a0 b1) $ Cons _ (orb b0 $ orb c1 hd) tl) (Cons _ (orb a1 b1) mk1)))
    (else (values mr mk))))

(def-fns _ $ (many cptriad : (many (List (Bool)) mrc mkc) (many (List (Step)) cp) (subterm many (Nat) i) -> (many (Bool) b))
  (let-match many i (Succ i1) ((Zero) (BFalse)))
  (let ((many mrt) (many mkt)) (cpadj (nseq _ (cprsize cp) (BFalse)) (ctrmask (Cons _ i1 $ Nil _) 0 (cpksize cp)) cp))
  (let ((many mct)) (cat _ (mask _ mrc mrt) (mask _ mkc mkt)))
  (match many (andb (nat-ltb 0 $ count-b (BFalse) mct) (nat-ltb 2 $ count-b (BTrue) mct)) _
    ((BTrue) (BTrue))
    ((BFalse) (tail $ cptriad mrc mkc cp i1))))

(def-fns _ $ (many valid-ctrm : (many (List (Bool)) cm) (many (List (Step)) cp) -> (many (Bool) b))
  (let ((many n)) (count-b (BTrue) cm))
  (let-match many (nat-eqb n 4) (BTrue) ((BFalse) (andb (nat-ltb 0 n) (nat-ltb n 4))))
  (let ((many mr) (many mk)) (ctrband cm cp))
  (cptriad mr mk cp (cpksize cp)))

(def-fns _ $ (many contract-ctree : (many (Config) cf) -> (many (Maybe (Ctree)) r))
  (let-match many cf (MkConfig _ cci cp))
  (let ((many cm)) (ctrmask cci 0 (ctrmsize cp)))
  (let-match many (cfctr (nseq _ (cprsize cp) (BFalse)) cm cp) (Some _ cpc) ((None _) (None _)))
  (let-match many (valid-ctrm cm cp) (BTrue) ((BFalse) (None _)))
  (Some _ $ cpcolor cpc))

(def-fns _ $ (many check-reducible : (many (Config) cf) -> (many (Bool) b))
  (let-match many cf (MkConfig _ _ cp))
  (match many (contract-ctree cf) _
    ((Some _ ct) (ct-disjoint (kempe-tree cp) ct))
    ((None _) (BFalse))))

(def-fns _ $ (many check-all : (subterm many (List (Config)) cfs) -> (many (Bool) b))
  (let-match many cfs (Cons _ cf rest) ((Nil _) (BTrue)))
  (match many (check-reducible cf) _ ((BTrue) (tail $ check-all rest)) ((BFalse) (BFalse))))
