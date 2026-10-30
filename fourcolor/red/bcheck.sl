; The Birkhoff check of birkhoff.v, certified, and the part of Birkhoff_valid that rests on it alone. Load after ccheck.sl.

; After ctree_of_ttail of ctree.v: t holds the one trace et, which has no Color0.
(def-adts $ (TT : ((List (Col)) et) ((Ctree) t) -> Type)
  enum
  (many TTNil : -> (TT (Nil (Col)) (CLeaf (CEmpty))))
  (many TT1 : (erased (List (Col)) et) (erased (Ctree) t) (erased (TT et t) p) -> (TT (Cons (Col) (C1) et) (CNode t (CEmpty) (CEmpty))))
  (many TT2 : (erased (List (Col)) et) (erased (Ctree) t) (erased (TT et t) p) -> (TT (Cons (Col) (C2) et) (CNode (CEmpty) t (CEmpty))))
  (many TT3 : (erased (List (Col)) et) (erased (Ctree) t) (erased (TT et t) p) -> (TT (Cons (Col) (C3) et) (CNode (CEmpty) (CEmpty) t))))

(def-adts $ (TTD : ((List (Col)) et) -> Type)
  enum
  (many TTYes : (erased (List (Col)) et) (many (Ctree) t) (erased (TT et t) p) -> (TTD et))
  (many TTNo : (erased (List (Col)) et) -> (TTD et)))

(def-fns _ $ (many ttail-c : (subterm many (List (Col)) et) -> (many (TTD et) r))
  (let-match many et (Cons _ c et1) ((Nil _) (TTYes et (CLeaf (CEmpty)) (TTNil))))
  (let-match many (notail $ ttail-c et1) (TTYes _ t p) ((TTNo _) (TTNo et)))
  (match many c _
    ((C0) (TTNo et))
    ((C1) (TTYes et (CNode t (CEmpty) (CEmpty)) (TT1 et1 t p)))
    ((C2) (TTYes et (CNode (CEmpty) t (CEmpty)) (TT2 et1 t p)))
    ((C3) (TTYes et (CNode (CEmpty) (CEmpty) t) (TT3 et1 t p)))))

; The one trace of t, after the reversed prefix pre, has a completion satisfying P (one direction of ctree_of_ttail_mem).
(def-fns _ $ (erased tt-allp : (erased Pred P) (erased (List (Col)) et pre full ct) (erased (Ctree) t) (subterm erased (TT et t) p)
    (erased (RevApp (Col) pre et full) ra) (erased (Ctr (C0) full ct) c) (erased (Holds P ct) h) -> (erased (CtAllP P t pre) r))
  (match erased p _
    ((TTNil) (CAPL P (CEmpty) pre full ct ra c h))
    ((TT1 et1 t1 p1)
      (CAPN P t1 (CEmpty) (CEmpty) pre (tt-allp P et1 (Cons _ (C1) pre) full ct t1 p1 (RACons (Col) (C1) pre et1 full ra) c h)
        (CAPE P (Cons _ (C2) pre)) (CAPE P (Cons _ (C3) pre))))
    ((TT2 et1 t1 p1)
      (CAPN P (CEmpty) t1 (CEmpty) pre (CAPE P (Cons _ (C1) pre))
        (tt-allp P et1 (Cons _ (C2) pre) full ct t1 p1 (RACons (Col) (C2) pre et1 full ra) c h) (CAPE P (Cons _ (C3) pre))))
    ((TT3 et1 t1 p1)
      (CAPN P (CEmpty) (CEmpty) t1 pre (CAPE P (Cons _ (C1) pre)) (CAPE P (Cons _ (C2) pre))
        (tt-allp P et1 (Cons _ (C3) pre) full ct t1 p1 (RACons (Col) (C3) pre et1 full ra) c h)))))

(def-fns _ $ (many addk-c : (many (Col) a b) -> (many (Col) c) (erased (AddK a b c) p))
  (match many a _
    ((C0) (values b (AZL b)))
    ((C1) (match many b _ ((C0) (values a (AZR a))) ((C1) (values (C0) (ASame a))) ((C2) (values (C3) (AThird a b (C3) (T123))))
      ((C3) (values (C2) (AThird a b (C2) (T132))))))
    ((C2) (match many b _ ((C0) (values a (AZR a))) ((C1) (values (C3) (AThird a b (C3) (T213)))) ((C2) (values (C0) (ASame a)))
      ((C3) (values (C1) (AThird a b (C1) (T231))))))
    ((C3) (match many b _ ((C0) (values a (AZR a))) ((C1) (values (C2) (AThird a b (C2) (T312)))) ((C2) (values (C1) (AThird a b (C1) (T321))))
      ((C3) (values (C0) (ASame a)))))))

(def-fns _ $ (many ctr-c : (many (Col) s) (subterm many (List (Col)) et) -> (many (List (Col)) ct) (erased (Ctr s et ct) c))
  (let-match many et (Cons _ e et1) ((Nil _) (values (Cons _ s (Nil _)) (CtrNil s))))
  (let ((many s2) (erased a)) (addk-c s e))
  (let ((many ct) (erased c)) (notail $ ctr-c s2 et1))
  (values (Cons _ e ct) (CtrCons s e s2 et1 ct a c)))

(def-fns _ $ (many coleq-c : (many (Col) a b) -> (many (Chk (Eq (Col) a b)) r))
  (match many a _
    ((C0) (match many b _ ((C0) (CkY _ (Refl _ a))) (else (CkN _))))
    ((C1) (match many b _ ((C1) (CkY _ (Refl _ a))) (else (CkN _))))
    ((C2) (match many b _ ((C2) (CkY _ (Refl _ a))) (else (CkN _))))
    ((C3) (match many b _ ((C3) (CkY _ (Refl _ a))) (else (CkN _))))))

(def-fns _ $ (many cleq-c : (subterm many (List (Col)) xs) (many (List (Col)) ys) -> (many (Chk (Eq (List (Col)) xs ys)) r))
  (let-match many xs (Cons _ x xs1) ((Nil _) (match many ys _ ((Nil _) (CkY _ (Refl _ xs))) (else (CkN _)))))
  (let-match many ys (Cons _ y ys1) ((Nil _) (CkN _)))
  (let-match many (coleq-c x y) (CkY _ q1) ((CkN _) (CkN _)))
  (let-match many (notail $ cleq-c xs1 ys1) (CkY _ q) ((CkN _) (CkN _)))
  (let-match erased q1 (Refl _ _))
  (let-match erased q (Refl _ _))
  (CkY _ (Refl _ xs)))

(def-fns _ $ (many belast-c : (erased Type A) (subterm many (List A) xs) -> (many (List A) ys))
  (let-match many xs (Cons _ x xs1) ((Nil _) xs))
  (let-match many xs1 (Cons _ _ _) ((Nil _) xs1))
  (Cons _ x (notail $ belast-c _ xs1)))

(def-adts $ (PickD : ((Ctree) t) -> Type)
  enum
  (many PkYes : (erased (Ctree) t) (many (List (Col)) p) (erased (CtMem t p) m) -> (PickD t))
  (many PkNo : (erased (Ctree) t) -> (PickD t)))

; After ctree_pick_rev_rec of birkhoff.v: a trace p of t, after the reversed prefix acc whose sum is e, such that the even
; normal form of e :: rev p without its last entry is in ctu1.
(def-fns _ $ (many pick-c : (many (Ctree) ctu1) (subterm many (Ctree) t) (many (List (Col)) acc) (many (Col) e) -> (many (PickD t) r))
  (match many t _
    ((CLeaf lf)
      (let ((many et2) (erased _)) (etrace-c (belast-c _ (Cons _ e acc))))
      (let ((many k) (erased _)) (sub-exists ctu1 et2))
      (let-match many k (Succ _) ((Zero) (PkNo t)))
      (PkYes t (Nil _) (leaf-mem lf)))
    ((CNode t1 t2 t3)
      (let ((many e1) (erased _)) (addk-c e (C1)))
      (let-match many (notail $ pick-c ctu1 t1 (Cons _ (C1) acc) e1) (PkNo _)
        ((PkYes _ p m) (PkYes t (Cons _ (C1) p) (mem-cons t t1 (C1) p (SelN1 t1 t2 t3) m))))
      (let ((many e2) (erased _)) (addk-c e (C2)))
      (let-match many (notail $ pick-c ctu1 t2 (Cons _ (C2) acc) e2) (PkNo _)
        ((PkYes _ p m) (PkYes t (Cons _ (C2) p) (mem-cons t t2 (C2) p (SelN2 t1 t2 t3) m))))
      (let ((many e3) (erased _)) (addk-c e (C3)))
      (let-match many (notail $ pick-c ctu1 t3 (Cons _ (C3) acc) e3) (PkNo _)
        ((PkYes _ p m) (PkYes t (Cons _ (C3) p) (mem-cons t t3 (C3) p (SelN3 t1 t2 t3) m))))
      (PkNo t))
    ((CEmpty) (PkNo t))))

; Gonthier's cpcard, for cubic programs: the number of darts of the map.
(def-adts $ (Cpcard : ((List (Step)) cp) ((Nat) k) -> Type)
  enum
  (many CcNil : -> (Cpcard (Nil (Step)) (Succ (Succ (Zero)))))
  (many CcR : (erased (Nat) j k) (erased (List (Step)) cp) (erased (Cpcard cp k) c) -> (Cpcard (Cons (Step) (SR j) cp) k))
  (many CcU : (erased (Nat) k) (erased (List (Step)) cp) (erased (Cpcard cp k) c) -> (Cpcard (Cons (Step) (SU) cp) (Succ (Succ k))))
  (many CcY : (erased (Nat) k) (erased (List (Step)) cp) (erased (Cpcard cp k) c) -> (Cpcard (Cons (Step) (SY) cp) (Succ (Succ (Succ (Succ k))))))
  (many CcH : (erased (Nat) k) (erased (List (Step)) cp) (erased (Cpcard cp k) c)
      -> (Cpcard (Cons (Step) (SH) cp) (Succ (Succ (Succ (Succ (Succ (Succ k)))))))))

; Birkhoff_check1 of birkhoff.v for ring size h + 2 and kernel size m, with t the tree cpcolor-c computes for cp.
(def-adts $ (BkProg : ((Nat) h) ((Nat) m) ((List (Step)) cp) ((Ctree) t) -> Type)
  enum
  (many MkBkProg : (erased (Nat) h m) (erased (List (Step)) cp) (erased (Ctree) t) (erased (Nat) k x y b) (erased (CubicProg cp) cq)
      (erased (NoA cp) na) (erased (Cprsize cp (Succ (Succ h))) cs) (erased (Cpcard cp k) cc) (erased (Mul 6 m x) mx) (erased (Mul 4 (Succ h) y) my)
      (erased (Add x y b) xy) (erased (Lt (Succ k) b) lt) (erased (CtH (Succ h) t) ht) (erased (CtRing cp t (Nil (Col))) rt)
      (erased (CpComp cp t) cm) -> (BkProg h m cp t)))

(def-adts $ (BkBasis : ((Nat) h) ((Nat) m) ((List (List (Step))) cps) ((List (Ctree)) ts) -> Type)
  enum
  (many BBNil : (erased (Nat) h m) -> (BkBasis h m (Nil (List (Step))) (Nil (Ctree))))
  (many BBCons : (erased (Nat) h m) (erased (List (Step)) cp) (erased (Ctree) t) (erased (List (List (Step))) cps) (erased (List (Ctree)) ts)
      (erased (BkProg h m cp t) p) (erased (BkBasis h m cps ts) q) -> (BkBasis h m (Cons (List (Step)) cp cps) (Cons (Ctree) t ts))))

(def-fns _ $ (many cubic-c : (subterm many (List (Step)) cp) -> (many (Chk (CubicProg cp)) r))
  (let-match many cp (Cons _ s cp1) ((Nil _) (CkY _ (CubNil))))
  (let-match many (notail $ cubic-c cp1) (CkY _ q) ((CkN _) (CkN _)))
  (match many s _ ((SR j) (CkY _ (CubR j cp1 q))) ((SY) (CkY _ (CubY cp1 q))) ((SH) (CkY _ (CubH cp1 q))) ((SU) (CkY _ (CubU cp1 q)))
    (else (CkN _))))

(def-fns _ $ (erased cubic-noa : (erased (List (Step)) cp) (subterm erased (CubicProg cp) cq) -> (erased (NoA cp) na))
  (match erased cq _
    ((CubNil) (NoANil))
    ((CubR j cp1 q) (NoAR j cp1 (cubic-noa cp1 q)))
    ((CubY cp1 q) (NoAY cp1 (cubic-noa cp1 q)))
    ((CubH cp1 q) (NoAH cp1 (cubic-noa cp1 q)))
    ((CubU cp1 q) (NoAU cp1 (cubic-noa cp1 q)))))

(def-fns _ $ (many cpcard-c : (subterm many (List (Step)) cp) (erased (CubicProg cp) cq) -> (many (Nat) k) (erased (Cpcard cp k) c))
  (let-match many cp (Cons _ s cp1) ((Nil _) (values (Succ $ Succ $ Zero) (CcNil))))
  (match many s _
    ((SR j) (let-match erased cq (CubR _ _ q)) (let ((many k) (erased c)) (tail $ cpcard-c cp1 q)) (values k (CcR j k cp1 c)))
    ((SY) (let-match erased cq (CubY _ q)) (let ((many k) (erased c)) (notail $ cpcard-c cp1 q)) (values (Succ $ Succ $ Succ $ Succ k) (CcY k cp1 c)))
    ((SH) (let-match erased cq (CubH _ q)) (let ((many k) (erased c)) (notail $ cpcard-c cp1 q))
      (values (Succ $ Succ $ Succ $ Succ $ Succ $ Succ k) (CcH k cp1 c)))
    ((SU) (let-match erased cq (CubU _ q)) (let ((many k) (erased c)) (notail $ cpcard-c cp1 q)) (values (Succ $ Succ k) (CcU k cp1 c)))
    (absurd (SRr) cq)
    (absurd (SK) cq)
    (absurd (SA) cq)))

(def-fns _ $ (many cprsize-cub : (subterm many (List (Step)) cp) (erased (CubicProg cp) cq) -> (many (Nat) k) (erased (Cprsize cp k) c))
  (let-match many cp (Cons _ s cp1) ((Nil _) (values (Succ $ Succ $ Zero) (CsNil))))
  (match many s _
    ((SR j) (let-match erased cq (CubR _ _ q)) (let ((many k) (erased c)) (tail $ cprsize-cub cp1 q)) (values k (CsR j k cp1 c)))
    ((SY) (let-match erased cq (CubY _ q)) (let ((many k) (erased c)) (notail $ cprsize-cub cp1 q)) (values (Succ k) (CsY k cp1 c)))
    ((SH) (let-match erased cq (CubH _ q)) (let ((many k) (erased c)) (tail $ cprsize-cub cp1 q)) (values k (CsH k cp1 c)))
    ((SU) (let-match erased cq (CubU _ q)) (let ((many k) (erased c)) (notail $ cprsize-cub cp1 q)) (values (Succ $ Succ k) (CsU k cp1 c)))
    (absurd (SRr) cq)
    (absurd (SK) cq)
    (absurd (SA) cq)))

(def-adts $ (BkPD : ((Nat) h) ((Nat) m) ((List (Step)) cp) -> Type)
  enum
  (many BPYes : (erased (Nat) h m) (erased (List (Step)) cp) (many (Ctree) t) (erased (BkProg h m cp t) p) -> (BkPD h m cp))
  (many BPNo : (erased (Nat) h m) (erased (List (Step)) cp) -> (BkPD h m cp)))

(def-fns _ $ (many bkprog-c : (many (Nat) h m) (many (List (Step)) cp) -> (many (BkPD h m cp) r))
  (let-match many (cubic-c cp) (CkY _ cq) ((CkN _) (BPNo h m cp)))
  (let ((erased na)) (cubic-noa cp cq))
  (let ((many r) (erased cs)) (cprsize-cub cp cq))
  (let-match many (nat-eq r (Succ $ Succ h)) (Equal _ _ _) (else (BPNo h m cp)))
  (let ((many k) (erased cc)) (cpcard-c cp cq))
  (let ((many x) (erased mx)) (mul 6 m))
  (let ((many y) (erased my)) (mul 4 (Succ h)))
  (let ((many b) (erased xy)) (add x y))
  (let-match many (lt-dec (Succ k) b) (Yes _ _ _ _ lt) (else (BPNo h m cp)))
  (let ((many t) (erased ht) (erased rt) (erased cm)) (cpcolor-c h cp cs na))
  (BPYes h m cp t (MkBkProg h m cp t k x y b cq na cs cc mx my xy lt ht rt cm)))

(def-adts $ (BBD : ((Nat) h) ((Nat) m) ((List (List (Step))) cps) -> Type)
  enum
  (many BBYes : (erased (Nat) h m) (erased (List (List (Step))) cps) (many (List (Ctree)) ts) (erased (BkBasis h m cps ts) p) -> (BBD h m cps))
  (many BBNo : (erased (Nat) h m) (erased (List (List (Step))) cps) -> (BBD h m cps)))

(def-fns _ $ (many bkbasis-c : (many (Nat) h m) (subterm many (List (List (Step))) cps) -> (many (BBD h m cps) r))
  (let-match many cps (Cons _ cp rest) ((Nil _) (BBYes h m cps (Nil _) (BBNil h m))))
  (let-match many (bkprog-c h m cp) (BPYes _ _ _ t p) ((BPNo _ _ _) (BBNo h m cps)))
  (let-match many (notail $ bkbasis-c h m rest) (BBYes _ _ _ ts q) ((BBNo _ _ _) (BBNo h m cps)))
  (BBYes h m cps (Cons _ t ts) (BBCons h m cp t rest ts p q)))

; Some tree of ts is disjoint from ct (check_basis of birkhoff.v).
(def-adts $ (BDisj : ((List (Ctree)) ts) ((Ctree) ct) -> Type)
  enum
  (many MkBDisj : (erased (List (Ctree)) ts) (erased (Ctree) ct t) (erased (Elem (Ctree) t ts) el) (erased (CtDisj ct t) dj) -> (BDisj ts ct)))

(def-fns _ $ (many bdisj-c : (many (Ctree) ct) (subterm many (List (Ctree)) ts) -> (many (Chk (BDisj ts ct)) r))
  (let-match many ts (Cons _ t rest) ((Nil _) (CkN _)))
  (let-match many (ctree-disjoint ct t) (DjNo _ _ _) ((DjYes _ _ dj) (CkY _ (MkBDisj ts ct t (ElHere _ t rest) dj))))
  (let-match many (notail $ bdisj-c ct rest) (CkY _ b) ((CkN _) (CkN _)))
  (let-match erased b (MkBDisj _ _ t2 el dj))
  (CkY _ (MkBDisj ts ct t2 (ElThere _ t2 t rest el) dj)))

; One side of do_Birkhoff_check2 of birkhoff.v: from the trace a, the Kempe closure of ctu and gtu with the even normal form of
; a removed reaches ctu3, gtu3 and no chromograms left to remove.
(def-adts $ (SRun : ((Nat) h) ((List (Col)) a) ((Ctree) ctu) ((Gtree) gtu) ((Ctree) ctu3) ((Gtree) gtu3) -> Type)
  enum
  (many MkSRun : (erased (Nat) h) (erased (List (Col)) a etr) (erased (Ctree) ctu ctr ctu3) (erased (Gtree) gtu gtu3) (erased (ETrace a etr) et)
      (erased (TT etr ctr) tt) (erased (KR h ctu ctr gtu ctu3 (GEmpty) gtu3) kr) -> (SRun h a ctu gtu ctu3 gtu3)))

(def-adts $ (SideD : ((Nat) h) ((List (Ctree)) ts) ((List (Col)) a) ((Ctree) ctu) ((Gtree) gtu) -> Type)
  enum
  (many SdGo : (erased (Nat) h) (erased (List (Ctree)) ts) (erased (List (Col)) a) (erased (Ctree) ctu) (erased (Gtree) gtu) (many (Ctree) ctu3)
      (many (Gtree) gtu3) (erased (SRun h a ctu gtu ctu3 gtu3) run) (erased (CtH (Succ h) ctu3) hc3) (many (Chk (BDisj ts ctu3)) bd)
      -> (SideD h ts a ctu gtu))
  (many SdNo : (erased (Nat) h) (erased (List (Ctree)) ts) (erased (List (Col)) a) (erased (Ctree) ctu) (erased (Gtree) gtu) -> (SideD h ts a ctu gtu)))

(def-fns _ $ (many side-c : (many (Nat) h) (many (List (Ctree)) ts) (many (List (Col)) a) (many (Ctree) ctu) (many (Gtree) gtu) (erased (CtH (Succ h) ctu) hc)
    -> (many (SideD h ts a ctu gtu) r))
  (let ((many etr) (erased et)) (etrace-c a))
  (let-match many (ttail-c etr) (TTYes _ ctr tt) ((TTNo _) (SdNo h ts a ctu gtu)))
  (let ((many ctu3) (many gtr3) (many gtu3) (erased kr) (erased hc3)) (ktc-c ctu ctr gtu (Succ h) h ctu ctr gtu (KRBase h ctu ctr gtu) (CRBase h ctu ctr gtu) hc))
  (let-match many gtr3 (GEmpty) (else (SdNo h ts a ctu gtu)))
  (SdGo h ts a ctu gtu ctu3 gtu3 (MkSRun h a etr ctu ctr ctu3 gtu gtu3 et tt kr) hc3 (bdisj-c ctu3 ts)))

; Birkhoff_check2 of birkhoff.v for ring size h + 2 and the basis trees ts, as a certificate: BK for the call with ctu1, gtu1,
; n, ctu2 and gtu2, and BKS for one side of it, with the other side's trees cto and gto.
(def-adts
  ((BK : ((Nat) h) ((List (Ctree)) ts) ((Ctree) ctu1) ((Gtree) gtu1) ((Nat) n) ((Ctree) ctu2) ((Gtree) gtu2) -> Type)
    enum
    (many MkBK : (erased (Nat) h) (erased (List (Ctree)) ts) (erased (Ctree) ctu1) (erased (Gtree) gtu1) (erased (Nat) n) (erased (Ctree) ctu2)
        (erased (Gtree) gtu2) (erased (List (Col)) a1 c1 p c2) (erased (Ctr (C0) a1 c1) cr1) (erased (Ctr (C0) p c2) cr2)
        (erased (RevApp (Col) c2 (Nil (Col)) c1) rv) (erased (BKS h ts a1 ctu1 gtu1 ctu2 gtu2 n) s1) (erased (BKS h ts p ctu2 gtu2 ctu1 gtu1 n) s2)
        -> (BK h ts ctu1 gtu1 (Succ n) ctu2 gtu2)))
  ((BKS : ((Nat) h) ((List (Ctree)) ts) ((List (Col)) a) ((Ctree) ctu) ((Gtree) gtu) ((Ctree) cto) ((Gtree) gto) ((Nat) n) -> Type)
    enum
    (many BKSBasis : (erased (Nat) h) (erased (List (Ctree)) ts) (erased (List (Col)) a) (erased (Ctree) ctu) (erased (Gtree) gtu) (erased (Ctree) cto)
        (erased (Gtree) gto) (erased (Nat) n) (erased (Ctree) ctu3) (erased (Gtree) gtu3) (erased (SRun h a ctu gtu ctu3 gtu3) run)
        (erased (BDisj ts ctu3) bd) -> (BKS h ts a ctu gtu cto gto n))
    (many BKSRec : (erased (Nat) h) (erased (List (Ctree)) ts) (erased (List (Col)) a) (erased (Ctree) ctu) (erased (Gtree) gtu) (erased (Ctree) cto)
        (erased (Gtree) gto) (erased (Nat) n) (erased (Ctree) ctu3) (erased (Gtree) gtu3) (erased (SRun h a ctu gtu ctu3 gtu3) run)
        (erased (BK h ts cto gto n ctu3 gtu3) bk) -> (BKS h ts a ctu gtu cto gto n))))

(def-fns _ $ (many bk2-c : (many (Nat) h) (many (List (Ctree)) ts) (subterm many (Nat) n) (many (Ctree) ctu1) (many (Gtree) gtu1) (many (Ctree) ctu2)
    (many (Gtree) gtu2) (erased (CtH (Succ h) ctu1) hc1) (erased (CtH (Succ h) ctu2) hc2) -> (many (Chk (BK h ts ctu1 gtu1 n ctu2 gtu2)) r))
  (let-match many n (Succ n1) ((Zero) (CkN _)))
  (let-match many (pick-c ctu1 ctu2 (Nil _) (C0)) (PkYes _ p _) ((PkNo _) (CkN _)))
  (let ((many c2) (erased cr2)) (ctr-c (C0) p))
  (let ((many c1) (erased rv)) (rev-onto-c _ c2 (Nil _)))
  (let ((many a1)) (belast-c _ c1))
  (let ((many c1b) (erased cr1)) (ctr-c (C0) a1))
  (let-match many (cleq-c c1b c1) (CkY _ q) ((CkN _) (CkN _)))
  (let-match erased q (Refl _ _))
  (let ((many (Chk (BKS h ts a1 ctu1 gtu1 ctu2 gtu2 n1)) k1))
    (match many (side-c h ts a1 ctu1 gtu1 hc1) _
      ((SdNo _ _ _ _ _) (CkN _))
      ((SdGo _ _ _ _ _ ctu3 gtu3 run hc3 bd)
        (let-match many bd (CkN _) ((CkY _ b) (CkY _ (BKSBasis h ts a1 ctu1 gtu1 ctu2 gtu2 n1 ctu3 gtu3 run b))))
        (let-match many (notail $ bk2-c h ts n1 ctu2 gtu2 ctu3 gtu3 hc2 hc3) (CkY _ b) ((CkN _) (CkN _)))
        (CkY _ (BKSRec h ts a1 ctu1 gtu1 ctu2 gtu2 n1 ctu3 gtu3 run b)))))
  (let-match many k1 (CkY _ s1) ((CkN _) (CkN _)))
  (let ((many (Chk (BKS h ts p ctu2 gtu2 ctu1 gtu1 n1)) k2))
    (match many (side-c h ts p ctu2 gtu2 hc2) _
      ((SdNo _ _ _ _ _) (CkN _))
      ((SdGo _ _ _ _ _ ctu3 gtu3 run hc3 bd)
        (let-match many bd (CkN _) ((CkY _ b) (CkY _ (BKSBasis h ts p ctu2 gtu2 ctu1 gtu1 n1 ctu3 gtu3 run b))))
        (let-match many (notail $ bk2-c h ts n1 ctu1 gtu1 ctu3 gtu3 hc1 hc3) (CkY _ b) ((CkN _) (CkN _)))
        (CkY _ (BKSRec h ts p ctu2 gtu2 ctu1 gtu1 n1 ctu3 gtu3 run b)))))
  (let-match many k2 (CkY _ s2) ((CkN _) (CkN _)))
  (CkY _ (MkBK h ts ctu1 gtu1 n1 ctu2 gtu2 a1 c1 p c2 cr1 cr2 rv s1 s2)))

; Birkhoff_check of birkhoff.v for ring size h + 2 and kernel size m: the basis programs cps, whose trees are ts, and the
; certificate of a run of Birkhoff_check2 from the initial trees ctu and gtu.
(def-adts $ (BirkhoffCheck : ((Nat) h) ((Nat) m) -> Type)
  enum
  (many MkBirkhoffCheck : (erased (Nat) h m n) (erased (List (List (Step))) cps) (erased (List (Ctree)) ts) (erased (Ctree) ctu) (erased (Gtree) gtu)
      (erased (CEv ctu (ESStart)) ce) (erased (GE ctu (Cons RS (MkRx (GSet) (BS0) (GSG gtu)) (Nil RS)) (ESStart) (Succ h)) ge)
      (erased (GCov (GSG gtu) (Zero) (BFalse) (Succ h)) gc) (erased (BkBasis h m cps ts) bb) (erased (BK h ts ctu gtu n ctu gtu) bk)
      -> (BirkhoffCheck h m)))

(def-fns _ $ (many birkhoff-check-c : (many (Nat) h m n) (many (List (List (Step))) cps) -> (many (Chk (BirkhoffCheck h m)) r))
  (let-match many (bkbasis-c h m cps) (BBYes _ _ _ ts bb) ((BBNo _ _ _) (CkN _)))
  (let ((many i) (many _)) (init-for h (Nil _)))
  (let-match many i (IFYes _ ctu gtu ce ge gc hc))
  (let-match many (bk2-c h ts n ctu gtu ctu gtu hc hc) (CkY _ bk) ((CkN _) (CkN _)))
  (CkY _ (MkBirkhoffCheck h m n cps ts ctu gtu ce ge gc bb bk)))

; The traces that a colour permutation sends into NT.
(def-adts $ (PermIn : ((PredC) NT) ((List (Col)) ct) -> Type)
  enum
  (many MkPermIn : (erased Pred NT) (erased (List (Col)) ct ct2) (erased (Perm) g) (erased (IsPerm g) ip) (erased (PermT g ct ct2) pt)
      (erased (Holds NT ct2) h) -> (PermIn NT ct)))

; The completion of the even normal form of a trace whose completion c is in NT is sent into NT by a colour permutation.
(def-fns _ $ (erased etrace-permin : (erased Pred NT) (erased (List (Col)) a etr c ct) (erased (ETrace a etr) et) (erased (Ctr (C0) a c) cr)
    (erased (Ctr (C0) etr ct) cr2) (erased (Holds NT c) nt) -> (erased (Holds (MkPred (PredC) NT PermIn) ct) r))
  (match erased et _
    ((ETrEven _ _)
      (let-match erased (ctr-fn (C0) a c ct cr cr2) (Refl _ _))
      (MkHolds (PredC) NT PermIn ct (MkPermIn NT ct ct p123 (IP123) (tail-id ct) nt)))
    ((ETrOdd _ _ _ q)
      (MkHolds (PredC) NT PermIn ct (MkPermIn NT ct c p132 (IP132)
        (permt-invert p132 p132 c ct (PI132) (perm-ctr p132 (IP132) (C0) (C0) a etr c ct q (PC0 p132) cr cr2)) nt)))))

; A side of the check run from a valid state, with its trace a completed outside T, ends in a valid state.
(def-fns _ $ (erased srun-kv : (erased Pred NT) (erased (Nat) h) (erased (List (Col)) a c) (erased (Ctree) ctu ctu3) (erased (Gtree) gtu gtu3)
    (erased (Ctr (C0) a c) cr) (erased (Holds NT c) nt) (erased (SRun h a ctu gtu ctu3 gtu3) run)
    (erased (KV (MkPred (PredC) NT PermIn) h ctu (GEmpty) gtu) kv) -> (erased (KV (MkPred (PredC) NT PermIn) h ctu3 (GEmpty) gtu3) r))
  (let-match erased run (MkSRun _ _ etr _ ctr _ _ _ et tt kr))
  (let ((erased ct) (erased cr2)) (ctr-exists (C0) etr))
  (let ((erased Q)) (MkPred (PredC) NT PermIn))
  (kr-kv Q h ctu ctr gtu kv (CKBase Q h ctr (tt-allp Q etr (Nil _) etr ct ctr tt (RANil (Col) etr) cr2 (etrace-permin NT a etr c ct et cr cr2 nt)))
    ctu3 (GEmpty) gtu3 kr))

; One side of a ring in Birkhoff_valid of birkhoff.v, by functions at level L: T is a Kempe-closed set of complete traces
; (there, the ring traces of the map on one side of the ring), NT holds the traces not in T, and every basis tree for ring
; size h + 2 and kernel size m, the trees ts, holds the even normal form of a trace whose completion is in T (chkbP).
(def-adts $ (BSide : ((Level) L) ((Nat) h m) ((List (Ctree)) ts) ((PredC) T NT) -> Type)
  enum
  (many MkBSide : (erased (Level) L) (erased (Nat) h m) (erased (List (Ctree)) ts) (erased Pred T NT) (erased Rel R) (erased (KClosed L T R) cl)
      (erased (Fn L (erased (List (Col)) ct) -> (erased (Or (Holds T ct) (Holds NT ct)) r)) dec)
      (erased (Fn L (erased (List (Col)) ct) (erased (Holds T ct) p) (erased (Holds NT ct) q) -> (erased (False) f)) ref)
      (erased (Fn L (erased (Ctree) t) (erased (Elem (Ctree) t ts) el) -> (erased (List (Col)) et et2 ct)
          (erased (Length (Col) et (Succ h)) len) (erased (ETrace et et2) e) (erased (CtMem t et2) mt) (erased (Ctr (C0) et ct) cr)
          (erased (Holds T ct) p)) hit)
      -> (BSide L h m ts T NT)))

; No trace c1 is in T1 with its reverse in T2, and the other way round (colorable_from_ring and noncolG in Birkhoff_valid).
(def-adts $ (BGlue : ((Level) L) ((PredC) T1 T2) -> Type)
  enum
  (many MkBGlue : (erased (Level) L) (erased Pred T1 T2)
      (erased (Fn L (erased (List (Col)) c1 c2) (erased (RevApp (Col) c2 (Nil (Col)) c1) rv) (erased (Holds T1 c1) p) (erased (Holds T2 c2) q)
          -> (erased (False) f)) g12)
      (erased (Fn L (erased (List (Col)) c1 c2) (erased (RevApp (Col) c2 (Nil (Col)) c1) rv) (erased (Holds T2 c1) p) (erased (Holds T1 c2) q)
          -> (erased (False) f)) g21)
      -> (BGlue L T1 T2)))

; The part of Birkhoff_valid of birkhoff.v that rests on the check: a successful Birkhoff check, given by the fields of a
; BirkhoffCheck, leaves no two sides as above for its basis trees ts.
(def-fns _ $ (erased birkhoff-check-sound : (erased (Level) L) -> (erased (Level) N)
    (erased (Fn N (erased (Nat) h m n) (erased (List (Ctree)) ts) (erased (Ctree) ctu) (erased (Gtree) gtu) (erased (CEv ctu (ESStart)) ce)
        (erased (GE ctu (Cons RS (MkRx (GSet) (BS0) (GSG gtu)) (Nil RS)) (ESStart) (Succ h)) ge) (erased (GCov (GSG gtu) (Zero) (BFalse) (Succ h)) gc)
        (erased (BK h ts ctu gtu n ctu gtu) bk) (erased Pred T1 NT1 T2 NT2) (erased (BSide L h m ts T1 NT1) s1) (erased (BSide L h m ts T2 NT2) s2)
        (erased (BGlue L T1 T2) g) -> (erased (False) f)) f))
  (let ((erased M) (erased walk)) (kcc-coclosure L))
  (def-fns _
    ((erased bk-sound : (erased (Nat) h m) (erased (List (Ctree)) ts)
        (erased Pred T1 NT1 T2 NT2) (erased (BSide L h m ts T1 NT1) s1) (erased (BSide L h m ts T2 NT2) s2) (erased (BGlue L T1 T2) g)
        (erased (Ctree) ctu1 ctu2) (erased (Gtree) gtu1 gtu2) (erased (Nat) n) (subterm erased (BK h ts ctu1 gtu1 n ctu2 gtu2) bk)
        (erased (KV (MkPred (PredC) NT1 PermIn) h ctu1 (GEmpty) gtu1) kv1) (erased (KV (MkPred (PredC) NT2 PermIn) h ctu2 (GEmpty) gtu2) kv2)
        -> (erased (False) f))
      (let-match erased bk (MkBK _ _ _ _ n1 _ _ a1 c1 p c2 cr1 cr2 rv bs1 bs2))
      (let-match erased s1 (MkBSide _ _ _ _ _ _ R1 cl1 dec1 ref1 hit1))
      (let-match erased s2 (MkBSide _ _ _ _ _ _ R2 cl2 dec2 ref2 hit2))
      (let-match erased g (MkBGlue _ _ _ g12 g21))
      (match erased (dec1 c1) _
        ((InR _ _ nt1) (bks-sound h m ts T1 NT1 T2 NT2 s1 s2 (MkBGlue L T2 T1 g21 g12) a1 c1 cr1 nt1 ctu1 ctu2 gtu1 gtu2 n1 bs1 kv1 kv2))
        ((InL _ _ t1)
          (match erased (dec2 c2) _
            ((InL _ _ t2) (g12 c1 c2 rv t1 t2))
            ((InR _ _ nt2) (bks-sound h m ts T2 NT2 T1 NT1 s2 s1 g p c2 cr2 nt2 ctu2 ctu1 gtu2 gtu1 n1 bs2 kv2 kv1))))))
    ((erased bks-sound : (erased (Nat) h m) (erased (List (Ctree)) ts)
        (erased Pred T NT To NTo) (erased (BSide L h m ts T NT) s) (erased (BSide L h m ts To NTo) so) (erased (BGlue L To T) g)
        (erased (List (Col)) a c) (erased (Ctr (C0) a c) cr) (erased (Holds NT c) nt) (erased (Ctree) ctu cto) (erased (Gtree) gtu gto) (erased (Nat) n)
        (subterm erased (BKS h ts a ctu gtu cto gto n) bks) (erased (KV (MkPred (PredC) NT PermIn) h ctu (GEmpty) gtu) kv)
        (erased (KV (MkPred (PredC) NTo PermIn) h cto (GEmpty) gto) kvo) -> (erased (False) f))
      (let ((erased Q)) (MkPred (PredC) NT PermIn))
      (match erased bks _
        ((BKSBasis _ _ _ _ _ _ _ _ ctu3 gtu3 run bd)
          (let ((erased kv3)) (srun-kv NT h a c ctu ctu3 gtu gtu3 cr nt run kv))
          (let-match erased bd (MkBDisj _ _ t el dj))
          (let-match erased s (MkBSide _ _ _ _ _ _ R cl dec ref hit))
          (let ((erased et) (erased et2) (erased ct) (erased len) (erased e) (erased mt) (erased cr1) (erased tc)) (hit t el))
          (let ((erased k) (erased sb)) (sub-exists ctu3 et2))
          (let-match erased k (Zero) (absurd (Succ k1) (disj-mem ctu3 t et2 dj (MkCtMem ctu3 et2 k1 sb) mt)))
          (let ((erased kc)) (kempe-treeP-c Q h ctu3 (MkKSound Q h ctu3 (GEmpty) gtu3 kv3) et et2 ct len e sb cr1))
          (let ((erased ct2) (erased hq) (erased ht)) (walk Q T R cl ct kc tc))
          (let-match erased hq (MkHolds _ _ _ _ pin))
          (let-match erased pin (MkPermIn _ _ ct3 g3 ip pt hn))
          (let-match erased cl (MkKClosed _ _ _ cpf _ _))
          (ref ct3 (cpf ct2 ct3 g3 ip pt ht) hn))
        ((BKSRec _ _ _ _ _ _ _ _ ctu3 gtu3 run bk)
          (bk-sound h m ts To NTo T NT so s g cto ctu3 gto gtu3 n bk kvo (srun-kv NT h a c ctu ctu3 gtu gtu3 cr nt run kv))))))
  (def-fns _ $ (erased bc-sound : (erased (Nat) h m n) (erased (List (Ctree)) ts) (erased (Ctree) ctu) (erased (Gtree) gtu) (erased (CEv ctu (ESStart)) ce)
      (erased (GE ctu (Cons RS (MkRx (GSet) (BS0) (GSG gtu)) (Nil RS)) (ESStart) (Succ h)) ge) (erased (GCov (GSG gtu) (Zero) (BFalse) (Succ h)) gc)
      (erased (BK h ts ctu gtu n ctu gtu) bk) (erased Pred T1 NT1 T2 NT2) (erased (BSide L h m ts T1 NT1) s1) (erased (BSide L h m ts T2 NT2) s2)
      (erased (BGlue L T1 T2) g) -> (erased (False) f))
    (bk-sound h m ts T1 NT1 T2 NT2 s1 s2 g ctu ctu gtu gtu n bk (KVBase (MkPred (PredC) NT1 PermIn) h ctu gtu ce ge gc)
      (KVBase (MkPred (PredC) NT2 PermIn) h ctu gtu ce ge gc)))
  (values (level-of bc-sound) bc-sound))

; Birkhoff2 to Birkhoff5 of birkhoff.v, which bgoal.sl proves.
(def-adts $ (BirkhoffChecks : -> Type)
  enum
  (many MkBirkhoffChecks : (erased (BirkhoffCheck (Zero) (Zero)) b2) (erased (BirkhoffCheck (Succ (Zero)) (Zero)) b3)
      (erased (BirkhoffCheck (Succ (Succ (Zero))) (Zero)) b4) (erased (BirkhoffCheck (Succ (Succ (Succ (Zero)))) (Succ (Zero))) b5)
      -> (BirkhoffChecks)))
