; Runtime checkers that certify the base certificates of kempe.sl for given initial trees, in place of proving them
; of ctree-init and gtree-init.

(def-fns _ $ (many pick4-c : (erased Type A) (many (Gsym) s) (many A x0 x1 x2 x3) -> (many A x) (erased (Pick4 A s x0 x1 x2 x3 x) p))
  (match many s _
    ((GPush) (values x0 (PkPush A x0 x1 x2 x3)))
    ((GSkip) (values x1 (PkSkip A x0 x1 x2 x3)))
    ((GPop0) (values x2 (PkPop0 A x0 x1 x2 x3)))
    ((GPop1) (values x3 (PkPop1 A x0 x1 x2 x3)))))

(def-fns _ $ (many gsel-c : (many (GSet) gs) (many (Gsym) s) -> (many (GSet) gs2) (erased (GSel gs s gs2) p))
  (let-match many gs (GSG g) ((GSOne) (values (GSG (GEmpty)) (GSelOne s))))
  (match many (gtree-kind g) _
    ((GKNode _ u0 u1 u2 u3 eq)
      (let-match erased eq (Refl _ _))
      (let-match many g (GNode t0 t1 t2 t3))
      (let ((many u) (erased pk)) (pick4-c (Gtree) s t0 t1 t2 t3))
      (values (GSG u) (GSelN t0 t1 t2 t3 u s pk)))
    ((GKLeaf _ q l)
      (let ((many b0) (many b1) (many b2) (many b3) (erased gb)) (gbits-c g))
      (let-match erased gb (GBLeaf _ _ l2) (absurd (GBNode _ _ _ _) l))
      (let-match erased (leafset-fn g q (MkBits b0 b1 b2 b3) l l2) (Refl _ _))
      (let ((many b) (erased pk)) (pick4-c (Bool) s b0 b1 b2 b3))
      (match many b _
        ((BTrue) (values (GSOne) (GSelL g b0 b1 b2 b3 b s (GSOne) l pk (BSetT))))
        ((BFalse) (values (GSG (GEmpty)) (GSelL g b0 b1 b2 b3 b s (GSG (GEmpty)) l pk (BSetF))))))))

(def-fns _ $ (many not-c : (many (Bool) b) -> (many (Bool) c) (erased (Not b c) n))
  (match many b _ ((BTrue) (values (BFalse) (NotT))) ((BFalse) (values (BTrue) (NotF)))))

(def-adts $ (GCovRes : ((GSet) gs) ((Nat) d) ((Bool) b) ((Nat) n) -> Type)
  enum
  (many GCYes : (erased (GSet) gs) (erased (Nat) d) (erased (Bool) b) (erased (Nat) n) (erased (GCov gs d b n) c) -> (GCovRes gs d b n))
  (many GCNo : (erased (GSet) gs) (erased (Nat) d) (erased (Bool) b) (erased (Nat) n) -> (GCovRes gs d b n)))

(def-fns _ $ (many gcov-end : (many (GSet) gs) (many (Nat) d) (many (Bool) b) -> (many (GCovRes gs d b (Zero)) r))
  (let ((many no)) (GCNo gs d b (Zero)))
  (match many d _
    ((Zero)
      (match many b _
        ((BTrue) (match many gs _ ((GSOne) (GCYes gs d b (Zero) (GCNilOk gs d b (GBEnd0) (GROne)))) (else no)))
        ((BFalse) (GCYes gs d b (Zero) (GCNilBad gs d b (EB0))))))
    ((Succ d1)
      (match many d1 _
        ((Zero) (match many gs _ ((GSOne) (GCYes gs d b (Zero) (GCNilOk gs d b (GBEnd1 b) (GROne)))) (else no)))
        ((Succ d2) (GCYes gs d b (Zero) (GCNilBad gs d b (EB2 d2 b))))))))

(def-fns _ $ (many check-gcov : (many (GSet) gs) (many (Nat) d) (many (Bool) b) (subterm many (Nat) n) -> (many (GCovRes gs d b n) r))
  (let ((many no)) (GCNo gs d b n))
  (let-match many (lt-dec (Succ n) d) (No _ _ _ _ _) ((Yes _ _ _ _ lv) (GCYes gs d b n (GCVac gs d n b lv))))
  (let-match many n (Succ n1) ((Zero) (gcov-end gs d b)))
  (let ((many g0) (erased s0)) (gsel-c gs (GPush)))
  (let-match many (notail $ check-gcov g0 (Succ d) b n1) (GCYes _ _ _ _ k0) ((GCNo _ _ _ _) no))
  (let ((erased a0)) (GCAOk gs g0 d (Succ d) n1 b b (GPush) (GStPush d b) s0 k0))
  (let ((many c) (erased nt)) (not-c b))
  (let ((many g1) (erased s1)) (gsel-c gs (GSkip)))
  (let-match many (notail $ check-gcov g1 d c n1) (GCYes _ _ _ _ k1) ((GCNo _ _ _ _) no))
  (let ((erased a1)) (GCAOk gs g1 d d n1 b c (GSkip) (GStSkip d b c nt) s1 k1))
  (match many d _
    ((Zero) (GCYes gs d b n (GCCons gs d n1 b a0 a1 (GCAPop0 gs b n1) (GCAPop1 gs b n1))))
    ((Succ d1)
      (let ((many g2) (erased s2)) (gsel-c gs (GPop0)))
      (let-match many (notail $ check-gcov g2 d1 b n1) (GCYes _ _ _ _ k2) ((GCNo _ _ _ _) no))
      (let ((many g3) (erased s3)) (gsel-c gs (GPop1)))
      (let-match many (notail $ check-gcov g3 d1 c n1) (GCYes _ _ _ _ k3) ((GCNo _ _ _ _) no))
      (GCYes gs d b n (GCCons gs d n1 b a0 a1 (GCAOk gs g2 d d1 n1 b b (GPop0) (GStPop0 d1 b) s2 k2)
        (GCAOk gs g3 d d1 n1 b c (GPop1) (GStPop1 d1 b c nt) s3 k3))))))

(def-fns _ $ (many permc-c : (many (Perm) g) (many (Col) c) -> (many (Col) d) (erased (PermC g c d) p))
  (let-match many g (MkPerm p1 p2 p3))
  (match many c _ ((C0) (values c (PC0 g))) ((C1) (values p1 (PC1 p1 p2 p3))) ((C2) (values p2 (PC2 p1 p2 p3))) ((C3) (values p3 (PC3 p1 p2 p3)))))

(def-fns _ $ (many esstep-c : (many (ES) st) (many (Col) c) -> (many (ES) st2) (erased (ESStep st c st2) p))
  (match many st _
    ((ESStart)
      (match many c _
        ((C0) (values (ESEven) (EStS0)))
        ((C1) (values (ESTail p123) (EStS1)))
        ((C2) (values (ESTail p312) (EStS2)))
        ((C3) (values (ESTail p231) (EStS3)))))
    ((ESTail g)
      (let ((many d) (erased p)) (permc-c g c))
      (match many d _
        ((C0) (values st (EStT0 g c p)))
        ((C1) (values st (EStT1 g c p)))
        ((C2) (values (ESEven) (EStT2 g c p)))
        ((C3) (values (ESOdd) (EStT3 g c p)))))
    ((ESEven) (values st (EStE c)))
    ((ESOdd) (values st (EStO c)))))

(def-adts $ (CEvRes : ((Ctree) t) ((ES) st) -> Type)
  enum
  (many CEvYes : (erased (Ctree) t) (erased (ES) st) (erased (CEv t st) c) -> (CEvRes t st))
  (many CEvNo : (erased (Ctree) t) (erased (ES) st) -> (CEvRes t st)))

(def-adts $ (StKind : ((ES) st) -> Type)
  enum
  (many SKOdd : -> (StKind (ESOdd)))
  (many SKEven : -> (StKind (ESEven)))
  (many SKOther : (erased (ES) st) (erased (NotOdd st) n) -> (StKind st)))

(def-fns _ $ (many st-kind : (many (ES) st) -> (many (StKind st) k))
  (match many st _ ((ESOdd) (SKOdd)) ((ESEven) (SKEven)) ((ESStart) (SKOther st (NOS))) ((ESTail g) (SKOther st (NOT g)))))

(def-fns _ $ (many check-cev : (subterm many (Ctree) t) (many (ES) st) -> (many (CEvRes t st) r))
  (let ((many no)) (CEvNo t st))
  (match many (st-kind st) _
    ((SKEven) (CEvYes t st (CEvEv t)))
    ((SKOdd) (match many t _ ((CEmpty) (CEvYes t st (CEvE st))) (else no)))
    ((SKOther _ n)
      (match many t _
        ((CEmpty) (CEvYes t st (CEvE st)))
        ((CLeaf lf) (CEvYes t st (CEvL lf st n)))
        ((CNode t1 t2 t3)
          (let ((many s0) (erased p0)) (esstep-c st (C0)))
          (let ((many s1) (erased p1)) (esstep-c st (C1)))
          (let-match many (notail $ check-cev t1 s1) (CEvYes _ _ c1) ((CEvNo _ _) no))
          (let ((many s2) (erased p2)) (esstep-c st (C2)))
          (let-match many (notail $ check-cev t2 s2) (CEvYes _ _ c2) ((CEvNo _ _) no))
          (let ((many s3) (erased p3)) (esstep-c st (C3)))
          (let-match many (notail $ check-cev t3 s3) (CEvYes _ _ c3) ((CEvNo _ _) no))
          (CEvYes t st (CEvN t1 t2 t3 st (MkCEvAt t (CEmpty) st s0 (C0) (SelN0 t1 t2 t3) p0 (CEvE s0))
            (MkCEvAt t t1 st s1 (C1) (SelN1 t1 t2 t3) p1 c1) (MkCEvAt t t2 st s2 (C2) (SelN2 t1 t2 t3) p2 c2)
            (MkCEvAt t t3 st s3 (C3) (SelN3 t1 t2 t3) p3 c3))))))))

(def-adts $ (HRes : ((Nat) h) ((Ctree) t) -> Type)
  enum
  (many HYes2 : (erased (Nat) h) (erased (Ctree) t) (erased (CtH h t) p) -> (HRes h t))
  (many HNo2 : (erased (Nat) h) (erased (Ctree) t) -> (HRes h t)))

(def-fns _ $ (many check-h : (many (Nat) h) (subterm many (Ctree) t) -> (many (HRes h t) r))
  (let ((many no)) (HNo2 h t))
  (match many t _
    ((CEmpty) (HYes2 h t (HE h)))
    ((CLeaf lf) (match many h _ ((Zero) (let-match many (notail $ check-h h lf) (HYes2 _ _ p) ((HNo2 _ _) no)) (HYes2 h t (HL lf p))) (else no)))
    ((CNode t1 t2 t3)
      (let-match many h (Succ h1) ((Zero) no))
      (let-match many (notail $ check-h h1 t1) (HYes2 _ _ p1) ((HNo2 _ _) no))
      (let-match many (notail $ check-h h1 t2) (HYes2 _ _ p2) ((HNo2 _ _) no))
      (let-match many (notail $ check-h h1 t3) (HYes2 _ _ p3) ((HNo2 _ _) no))
      (HYes2 h t (HN h1 t1 t2 t3 p1 p2 p3)))))

(def-fns _ $ (many root-count-c : (subterm many (Ctree) t) -> (many (Nat) n) (erased (CtRoot t n) p))
  (match many t _
    ((CLeaf lf) (let ((many n) (erased p)) (notail $ root-count-c lf)) (values (Succ n) (RootL lf n p)))
    ((CNode t1 t2 t3) (values (Zero) (RootN t1 t2 t3)))
    ((CEmpty) (values (Zero) (RootE)))))

(def-fns _ $ (many pieces-root-c : (subterm many (List RS) ps) -> (many (Nat) k) (erased (PCnt ps (Nil (Col)) k) p))
  (let-match many ps (Cons _ x rest) ((Nil _) (values (Zero) (PCNil (Nil _)))))
  (let-match many x (MkRx _ bs gs))
  (let ((many k) (erased p)) (notail $ pieces-root-c rest))
  (match many gs _
    ((GSOne) (values (Succ k) (PCCons bs gs rest (Nil _) (Succ (Zero)) k (Succ k) (MCNil gs bs (Succ (Zero)) (GROne)) p (AddSucc (Zero) k k (AddZero k)))))
    ((GSG g) (values k (PCCons bs gs rest (Nil _) (Zero) k k (MCNil gs bs (Zero) (GRG g)) p (AddZero k))))))

(def-fns _ $ (many rscons-c : (many (Bstack) bs) (many (GSet) gs) (many (List RS) a) -> (many (List RS) b) (erased (RSCons bs gs a b) p))
  (match many gs _
    ((GSG g) (match many g _ ((GEmpty) (values a (RSE bs a))) (else (values (Cons _ (MkRx _ bs gs) a) (RSC bs gs a)))))
    ((GSOne) (values (Cons _ (MkRx _ bs gs) a) (RSC bs gs a)))))

(def-fns _ $ (many pstep-c : (many (Bstack) bs) (many (GSet) gs) (many (Col) e) (many (List RS) a) ->
    (many (List RS) b) (erased (PStepE (MkRx (GSet) bs gs) e a b) p))
  (match many e _
    ((C0) (values a (PSE0 (MkRx (GSet) bs gs) a)))
    ((C1)
      (let ((many g1) (erased s1)) (gsel-c gs (GSkip)))
      (let ((many b) (erased q)) (rscons-c bs g1 a))
      (values b (PSE1 bs gs g1 a b s1 q)))
    ((C2)
      (let ((many g1) (erased s1)) (gsel-c gs (GPush)))
      (let ((many (List RS) c) (erased (PPop bs e gs a c) pp))
        (match many bs _
          ((BS0) (values a (PPNone e gs a)))
          ((BP0 b0) (let ((many g2) (erased s2)) (gsel-c gs (GPop0))) (let ((many c) (erased q)) (rscons-c b0 g2 a))
            (values c (PPSome bs b0 (GPop0) e gs g2 a c (Popped0 b0) (SPop02 b0) s2 q)))
          ((BP1 b0) (let ((many g2) (erased s2)) (gsel-c gs (GPop1))) (let ((many c) (erased q)) (rscons-c b0 g2 a))
            (values c (PPSome bs b0 (GPop1) e gs g2 a c (Popped1 b0) (SPop12 b0) s2 q)))))
      (let ((many b) (erased q)) (rscons-c (BP0 bs) g1 c))
      (values b (PSE23 bs (BP0 bs) e gs g1 a c b (SPush2 bs) s1 pp q)))
    ((C3)
      (let ((many g1) (erased s1)) (gsel-c gs (GPush)))
      (let ((many (List RS) c) (erased (PPop bs e gs a c) pp))
        (match many bs _
          ((BS0) (values a (PPNone e gs a)))
          ((BP0 b0) (let ((many g2) (erased s2)) (gsel-c gs (GPop1))) (let ((many c) (erased q)) (rscons-c b0 g2 a))
            (values c (PPSome bs b0 (GPop1) e gs g2 a c (Popped0 b0) (SPop13 b0) s2 q)))
          ((BP1 b0) (let ((many g2) (erased s2)) (gsel-c gs (GPop0))) (let ((many c) (erased q)) (rscons-c b0 g2 a))
            (values c (PPSome bs b0 (GPop0) e gs g2 a c (Popped1 b0) (SPop03 b0) s2 q)))))
      (let ((many b) (erased q)) (rscons-c (BP1 bs) g1 c))
      (values b (PSE23 bs (BP1 bs) e gs g1 a c b (SPush3 bs) s1 pp q)))))

(def-fns _ $ (many psplit-c : (many (Col) e) (many (List RS) a) (subterm many (List RS) ps) -> (many (List RS) s) (erased (PSplitE e a ps s) p))
  (let-match many ps (Cons _ x rest) ((Nil _) (values a (PSNil e a))))
  (let-match many x (MkRx _ bs gs))
  (let ((many b) (erased p)) (pstep-c bs gs e a))
  (let ((many s) (erased q)) (tail $ psplit-c e b rest))
  (values s (PSCons e x a b rest s p q)))

(def-fns _ $ (erased sel-c0 : (erased (Ctree) t) -> (erased (CtSel t (C0) (CEmpty)) s))
  (match erased t _ ((CNode t1 t2 t3) (SelN0 t1 t2 t3)) ((CLeaf lf) (SelL lf (C0))) ((CEmpty) (SelE (C0)))))

(def-adts $ (GERes : ((Ctree) t) ((List RS) ps) ((ES) st) -> Type)
  enum
  (many GEYes : (erased (Ctree) t) (erased (List RS) ps) (erased (ES) st) (erased (GE t ps st) g) -> (GERes t ps st))
  (many GENo : (erased (Ctree) t) (erased (List RS) ps) (erased (ES) st) -> (GERes t ps st)))

(def-fns _ $ (many ge-dead-at : (erased (Ctree) t) (many (List RS) ps) (many (ES) st) (many (Col) e) (erased (CtSel t e (CEmpty)) sl) ->
    (many (Maybe (GEAt t ps st e)) r))
  (let ((many ps2) (erased sp)) (psplit-c e (Nil _) ps))
  (let ((many st2) (erased p)) (esstep-c st e))
  (let-match many ps2 (Nil _) (else (None _)))
  (Some _ (MkGEAt t (CEmpty) ps ps2 st st2 e sl sp p (GEDead (CEmpty) ps2 st2 (PZNil)))))

(def-fns _ $ (many check-ge : (subterm many (Ctree) t) (many (List RS) ps) (many (ES) st) -> (many (GERes t ps st) r))
  (let ((many no)) (GENo t ps st))
  (let-match many ps (Cons _ _ _) ((Nil _) (GEYes t ps st (GEDead t ps st (PZNil)))))
  (let-match many st (ESOdd)
    (else
      (let ((many n) (erased rt)) (root-count-c t))
      (let ((many k) (erased pk)) (pieces-root-c ps))
      (let-match many (lt-dec k (Succ n)) (Yes _ _ _ _ le) ((No _ _ _ _ _) no))
      (let-match many (ge-dead-at t ps st (C0) (sel-c0 t)) (Some _ a0) ((None _) no))
      (match many t _
        ((CNode t1 t2 t3)
          (let ((many q1) (erased sp1)) (psplit-c (C1) (Nil _) ps))
          (let ((many s1) (erased e1)) (esstep-c st (C1)))
          (let-match many (notail $ check-ge t1 q1 s1) (GEYes _ _ _ g1) ((GENo _ _ _) no))
          (let ((many q2) (erased sp2)) (psplit-c (C2) (Nil _) ps))
          (let ((many s2) (erased e2)) (esstep-c st (C2)))
          (let-match many (notail $ check-ge t2 q2 s2) (GEYes _ _ _ g2) ((GENo _ _ _) no))
          (let ((many q3) (erased sp3)) (psplit-c (C3) (Nil _) ps))
          (let ((many s3) (erased e3)) (esstep-c st (C3)))
          (let-match many (notail $ check-ge t3 q3 s3) (GEYes _ _ _ g3) ((GENo _ _ _) no))
          (GEYes t ps st (GES t ps st n k rt pk le a0 (MkGEAt t t1 ps q1 st s1 (C1) (SelN1 t1 t2 t3) sp1 e1 g1)
            (MkGEAt t t2 ps q2 st s2 (C2) (SelN2 t1 t2 t3) sp2 e2 g2) (MkGEAt t t3 ps q3 st s3 (C3) (SelN3 t1 t2 t3) sp3 e3 g3))))
        ((CLeaf lf)
          (let-match many (ge-dead-at t ps st (C1) (SelL lf (C1))) (Some _ a1) ((None _) no))
          (let-match many (ge-dead-at t ps st (C2) (SelL lf (C2))) (Some _ a2) ((None _) no))
          (let-match many (ge-dead-at t ps st (C3) (SelL lf (C3))) (Some _ a3) ((None _) no))
          (GEYes t ps st (GES t ps st n k rt pk le a0 a1 a2 a3)))
        ((CEmpty)
          (let-match many (ge-dead-at t ps st (C1) (SelE (C1))) (Some _ a1) ((None _) no))
          (let-match many (ge-dead-at t ps st (C2) (SelE (C2))) (Some _ a2) ((None _) no))
          (let-match many (ge-dead-at t ps st (C3) (SelE (C3))) (Some _ a3) ((None _) no))
          (GEYes t ps st (GES t ps st n k rt pk le a0 a1 a2 a3))))))
  (GEYes t ps st (GEOdd t ps)))

(def-adts $ (BaseRes : ((Nat) h) ((Ctree) ctu) ((Gtree) gtu) -> Type)
  enum
  (many BaseYes : (erased (Nat) h) (erased (Ctree) ctu) (erased (Gtree) gtu) (erased (CEv ctu (ESStart)) ce)
      (erased (GE ctu (Cons RS (MkRx (GSet) (BS0) (GSG gtu)) (Nil RS)) (ESStart)) ge) (erased (GCov (GSG gtu) (Zero) (BFalse) (Succ h)) gc)
      (erased (CtH (Succ h) ctu) hc) -> (BaseRes h ctu gtu))
  (many BaseNo : (erased (Nat) h) (erased (Ctree) ctu) (erased (Gtree) gtu) -> (BaseRes h ctu gtu)))

(def-fns _ $ (many check-base : (many (Nat) h) (many (Ctree) ctu) (many (Gtree) gtu) -> (many (BaseRes h ctu gtu) r))
  (let ((many no)) (BaseNo h ctu gtu))
  (let-match many (check-h (Succ h) ctu) (HYes2 _ _ hc) ((HNo2 _ _) no))
  (let-match many (check-cev ctu (ESStart)) (CEvYes _ _ ce) ((CEvNo _ _) no))
  (let-match many (check-ge ctu (Cons _ (MkRx _ (BS0) (GSG gtu)) $ Nil _) (ESStart)) (GEYes _ _ _ ge) ((GENo _ _ _) no))
  (let-match many (check-gcov (GSG gtu) (Zero) (BFalse) (Succ h)) (GCYes _ _ _ _ gc) ((GCNo _ _ _ _) no))
  (BaseYes h ctu gtu ce ge gc hc))

(def-adts $ (AnyT : ((List (Col)) et) -> Type)
  enum
  (many MkAnyT : (erased (List (Col)) et) -> (AnyT et)))

(def-fns _ $ (erased capp-any : (subterm erased (Ctree) t) (erased (List (Col)) pre) -> (erased (CtAllP AnyT t pre) a))
  (match erased t _
    ((CEmpty) (CAPE AnyT pre))
    ((CLeaf lf) (let ((erased et) (erased r)) (revapp-exists (Col) pre (Nil _))) (CAPL AnyT lf pre et r (MkAnyT et)))
    ((CNode t1 t2 t3) (CAPN AnyT t1 t2 t3 pre (capp-any t1 (Cons _ (C1) pre)) (capp-any t2 (Cons _ (C2) pre)) (capp-any t3 (Cons _ (C3) pre))))))

(def-adts $ (InitFor : ((Nat) h) -> Type)
  enum
  (many IFYes : (erased (Nat) h) (many (Ctree) ctu) (many (Gtree) gtu) (erased (CEv ctu (ESStart)) ce)
      (erased (GE ctu (Cons RS (MkRx (GSet) (BS0) (GSG gtu)) (Nil RS)) (ESStart)) ge) (erased (GCov (GSG gtu) (Zero) (BFalse) (Succ h)) gc)
      (erased (CtH (Succ h) ctu) hc) -> (InitFor h))
  (many IFNo : (erased (Nat) h) -> (InitFor h)))

(def-adts $ (InitE : -> Type)
  enum
  (many MkInitE : (many (Nat) h) (many (InitFor h) i) -> (InitE)))

(def-fns _ $ (many init-lookup : (many (Nat) h) (subterm many (List (InitE)) cache) -> (many (Maybe (InitFor h)) r))
  (let-match many cache (Cons _ x rest) ((Nil _) (None _)))
  (let-match many x (MkInitE h2 i))
  (match many (nat-eq h2 h) _ ((Equal _ _ _) (Some _ i)) ((Unequal _ _ _ _ _) (tail $ init-lookup h rest))))

(def-fns _ $ (many init-for : (many (Nat) h) (many (List (InitE)) cache) -> (many (InitFor h) i) (many (List (InitE)) cache2))
  (let-match many (init-lookup h cache) (None _) ((Some _ i) (values i cache)))
  (let ((many ctu)) (ctree-init (Succ h)))
  (let ((many gtu)) (gtree-init (Succ h)))
  (let ((many (InitFor h) i))
    (match many (check-base h ctu gtu) _
      ((BaseYes _ _ _ ce ge gc hc) (IFYes h ctu gtu ce ge gc hc))
      ((BaseNo _ _ _) (IFNo h))))
  (values i (Cons _ (MkInitE h i) cache)))

(def-fns _ $ (many kempe-tree-chk : (many (List (Step)) cp) (many (List (InitE)) cache) -> (many (Maybe (Ctree)) r) (many (List (InitE)) cache2))
  (let-match many (cprsize cp) (Succ n1) ((Zero) (values (Some _ (CEmpty)) cache)))
  (let-match many n1 (Succ h) ((Zero) (values (Some _ (CEmpty)) cache)))
  (let ((many i) (many cache2)) (init-for h cache))
  (match many i _
    ((IFYes _ ctu gtu ce ge gc hc)
      (let ((many ctr)) (cpcolor cp))
      (let ((many kt) (erased ks)) (kempe-tree-c AnyT h ctu ctr gtu ce ge gc (capp-any ctr (Nil _)) hc))
      (values (Some _ kt) cache2))
    ((IFNo _) (values (None _) cache2))))

(def-fns _ $ (many check-reducible-c : (many (Config) cf) (many (List (InitE)) cache) -> (many (Bool) b) (many (List (InitE)) cache2))
  (let-match many cf (MkConfig _ _ cp))
  (let-match many (contract-ctree cf) (Some _ ct) ((None _) (values (BFalse) cache)))
  (let ((many k) (many cache2)) (kempe-tree-chk cp cache))
  (let-match many k (Some _ kt) ((None _) (values (BFalse) cache2)))
  (match many (ctree-disjoint kt ct) _ ((DjYes _ _ _) (values (BTrue) cache2)) ((DjNo _ _ _) (values (BFalse) cache2))))

(def-fns _ $ (many check-all-c : (subterm many (List (Config)) cfs) (many (List (InitE)) cache) -> (many (Bool) b))
  (let-match many cfs (Cons _ cf rest) ((Nil _) (BTrue)))
  (let ((many b) (many cache2)) (check-reducible-c cf cache))
  (match many b _ ((BTrue) (tail $ check-all-c rest cache2)) ((BFalse) (BFalse))))
