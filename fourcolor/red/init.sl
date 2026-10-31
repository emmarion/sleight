; Certified initial trees, in place of ctree-init and gtree-init of red.sl, and the runtime helpers they use.

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


(def-fns _ $ (many pieces-root-c : (subterm many (List RS) ps) -> (many (Nat) k) (erased (PCnt ps (Nil (Col)) k) p))
  (let-match many ps (Cons _ x rest) ((Nil _) (values (Zero) (PCNil (Nil _)))))
  (let-match many x (MkRx _ bs gs))
  (let ((many k) (erased p)) (notail $ pieces-root-c rest))
  (match many gs _
    ((GSOne) (values (Succ k) (PCCons bs gs rest (Nil _) (Succ (Zero)) k (Succ k) (MCNil gs bs (Succ (Zero)) (GROne)) p (AddSucc (Zero) k k (AddZero k)))))
    ((GSG g) (values k (PCCons bs gs rest (Nil _) (Zero) k k (MCNil gs bs (Zero) (GRG g)) p (AddZero k))))))

(def-fns _ $ (many rscons-c : (many (Bstack) bs) (many (GSet) gs) (many (List RS) a) -> (many (List RS) b) (erased (RSCons bs gs a b) p))
  (let-match many gs (GSG g)
    ((GSOne) (values (Cons _ (MkRx _ bs gs) a) (RSC bs gs a))))
  (match many g _ ((GEmpty) (values a (RSE bs a))) (else (values (Cons _ (MkRx _ bs gs) a) (RSC bs gs a)))))

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


; The covered sets of a row of the initial gtree, for one open-chord count d and each parity (after gtree_table of initgtree.v).
(def-adts $ (GEnt : ((Nat) n) ((Nat) d) -> Type)
  enum
  (many MkGEnt : (erased (Nat) n d) (many (Gtree) tt tf) (erased (GCov (GSG tt) d (BTrue) n) ct) (erased (GCov (GSG tf) d (BFalse) n) cf)
      -> (GEnt n d)))

(def-adts $ (GRow : ((Nat) n) ((Nat) d) -> Type)
  enum
  (many GREnd : (erased (Nat) n d) (erased (Lt (Succ n) d) l) -> (GRow n d))
  (many GRCons : (erased (Nat) n d) (many (GEnt n d) e) (many (GRow n (Succ d)) rest) -> (GRow n d)))

(def-adts $ (GPrev : ((Nat) n) ((Nat) d) -> Type)
  enum
  (many PNo : (erased (Nat) n) -> (GPrev n (Zero)))
  (many PYes : (erased (Nat) n d) (many (GEnt n d) e) -> (GPrev n (Succ d))))

(def-adts $ (GPopCov : ((Nat) n) ((Nat) d) ((Bool) b) ((Gtree) t2) ((Gtree) t3) -> Type)
  enum
  (many GPCZ : (erased (Nat) n) (erased (Bool) b) (erased (Gtree) t2 t3) -> (GPopCov n (Zero) b t2 t3))
  (many GPCS : (erased (Nat) n d) (erased (Bool) b c) (erased (Gtree) t2 t3) (erased (Not b c) nt) (erased (GCov (GSG t2) d b n) p2)
      (erased (GCov (GSG t3) d c n) p3) -> (GPopCov n (Succ d) b t2 t3)))

(def-adts $ (BOk : ((Bool) x) ((Nat) d) ((Bool) b) -> Type)
  enum
  (many BOkT : (erased (Nat) d) (erased (Bool) b) -> (BOk (BTrue) d b))
  (many BOkF : (erased (Nat) d) (erased (Bool) b) (erased (EndBad d b) e) -> (BOk (BFalse) d b)))

(def-fns _ $ (erased cov-one : (erased (Nat) d) (erased (Bool) b) -> (erased (GCov (GSOne) d b (Zero)) c))
  (match erased (end-dec d b) _
    ((InL _ _ g) (GCNilOk (GSOne) d b g (GROne)))
    ((InR _ _ e) (GCNilBad (GSOne) d b e))))

(def-fns _ $ (erased leaf-at : (erased (Gtree) g) (erased (Bool) b0 b1 b2 b3 x) (erased (Gsym) s) (erased (Nat) d d2) (erased (Bool) b c)
    (erased (LeafSet g (MkBits b0 b1 b2 b3)) l) (erased (Pick4 (Bool) s b0 b1 b2 b3 x) pk) (erased (GStep d b s d2 c) st) (erased (BOk x d2 c) ok)
    -> (erased (GCovAt (GSG g) d b (Zero) s) r))
  (match erased ok _
    ((BOkT _ _) (GCAOk (GSG g) (GSOne) d d2 (Zero) b c s st (GSelL g b0 b1 b2 b3 x s (GSOne) l pk (BSetT)) (cov-one d2 c)))
    ((BOkF _ _ e) (GCAOk (GSG g) (GSG (GEmpty)) d d2 (Zero) b c s st (GSelL g b0 b1 b2 b3 x s (GSG (GEmpty)) l pk (BSetF)) (GCNilBad _ d2 c e)))))

(def-fns _ $ (erased leaf-cov0 : (erased (Gtree) g) (erased (Bool) b0 b1 b2 b3 b c) (erased (Not b c) nt) (erased (LeafSet g (MkBits b0 b1 b2 b3)) l)
    (erased (BOk b0 (Succ (Zero)) b) k0) (erased (BOk b1 (Zero) c) k1) -> (erased (GCov (GSG g) (Zero) b (Succ (Zero))) r))
  (GCCons (GSG g) (Zero) (Zero) b
    (leaf-at g b0 b1 b2 b3 b0 (GPush) (Zero) (Succ (Zero)) b b l (PkPush _ b0 b1 b2 b3) (GStPush (Zero) b) k0)
    (leaf-at g b0 b1 b2 b3 b1 (GSkip) (Zero) (Zero) b c l (PkSkip _ b0 b1 b2 b3) (GStSkip (Zero) b c nt) k1)
    (GCAPop0 (GSG g) b (Zero)) (GCAPop1 (GSG g) b (Zero))))

(def-fns _ $ (erased leaf-cov : (erased (Gtree) g) (erased (Nat) d) (erased (Bool) b0 b1 b2 b3 b c) (erased (Not b c) nt)
    (erased (LeafSet g (MkBits b0 b1 b2 b3)) l) (erased (BOk b0 (Succ (Succ d)) b) k0) (erased (BOk b1 (Succ d) c) k1)
    (erased (BOk b2 d b) k2) (erased (BOk b3 d c) k3) -> (erased (GCov (GSG g) (Succ d) b (Succ (Zero))) r))
  (GCCons (GSG g) (Succ d) (Zero) b
    (leaf-at g b0 b1 b2 b3 b0 (GPush) (Succ d) (Succ (Succ d)) b b l (PkPush _ b0 b1 b2 b3) (GStPush (Succ d) b) k0)
    (leaf-at g b0 b1 b2 b3 b1 (GSkip) (Succ d) (Succ d) b c l (PkSkip _ b0 b1 b2 b3) (GStSkip (Succ d) b c nt) k1)
    (leaf-at g b0 b1 b2 b3 b2 (GPop0) (Succ d) d b b l (PkPop0 _ b0 b1 b2 b3) (GStPop0 d b) k2)
    (leaf-at g b0 b1 b2 b3 b3 (GPop1) (Succ d) d b c l (PkPop1 _ b0 b1 b2 b3) (GStPop1 d b c nt) k3)))

(def-fns _ $ (many grow1 : -> (many (GRow (Succ (Zero)) (Zero)) r))
  (let ((erased one) (erased two)) (values (Succ (Zero)) (Succ (Succ (Zero)))))
  (let ((erased T) (erased F)) (values (BTrue) (BFalse)))
  (let ((many e0)) (MkGEnt one (Zero) (GL0) (GL01)
    (leaf-cov0 (GL0) T F F F T F (NotT) (LS0) (BOkT one T) (BOkF (Zero) F (EB0)))
    (leaf-cov0 (GL01) T T F F F T (NotF) (LS01) (BOkT one F) (BOkT (Zero) T))))
  (let ((many e1)) (MkGEnt one one (GL12) (GL13)
    (leaf-cov (GL12) (Zero) F T T F T F (NotT) (LS12) (BOkF two T (EB2 (Zero) T)) (BOkT one F) (BOkT (Zero) T) (BOkF (Zero) F (EB0)))
    (leaf-cov (GL13) (Zero) F T F T F T (NotF) (LS13) (BOkF two F (EB2 (Zero) F)) (BOkT one T) (BOkF (Zero) F (EB0)) (BOkT (Zero) T))))
  (let ((many e2)) (MkGEnt one two (GL23) (GL23)
    (leaf-cov (GL23) one F F T T T F (NotT) (LS23) (BOkF (Succ two) T (EB2 one T)) (BOkF two F (EB2 (Zero) F)) (BOkT one T) (BOkT one F))
    (leaf-cov (GL23) one F F T T F T (NotF) (LS23) (BOkF (Succ two) F (EB2 one F)) (BOkF two T (EB2 (Zero) T)) (BOkT one F) (BOkT one T))))
  (GRCons one (Zero) e0 $ GRCons one one e1 $ GRCons one two e2 $ GREnd one (Succ two) (LtS one two (LtS (Zero) one (LtZ (Zero))))))

(def-fns _ $ (many gent-vac : (erased (Nat) n d) (erased (Lt (Succ n) d) l) -> (many (GEnt n d) e))
  (MkGEnt n d (GEmpty) (GEmpty) (GCVac (GSG (GEmpty)) d n (BTrue) l) (GCVac (GSG (GEmpty)) d n (BFalse) l)))

(def-fns _ $ (many row-head : (erased (Nat) n d) (many (GRow n d) r) -> (many (GEnt n d) e))
  (match many r _ ((GREnd _ _ l) (gent-vac n d l)) ((GRCons _ _ e _) e)))

(def-fns _ $ (erased node-cov : (erased (Nat) n d) (erased (Bool) b c) (erased (Not b c) nt) (erased (Gtree) t0 t1 t2 t3)
    (erased (GCov (GSG t0) (Succ d) b n) p0) (erased (GCov (GSG t1) d c n) p1) (erased (GPopCov n d b t2 t3) pp) ->
    (erased (GCov (GSG (GNode t0 t1 t2 t3)) d b (Succ n)) r))
  (let ((erased g)) (GSG (GNode t0 t1 t2 t3)))
  (let ((erased a0)) (GCAOk g (GSG t0) d (Succ d) n b b (GPush) (GStPush d b) (GSelN t0 t1 t2 t3 t0 (GPush) (PkPush _ t0 t1 t2 t3)) p0))
  (let ((erased a1)) (GCAOk g (GSG t1) d d n b c (GSkip) (GStSkip d b c nt) (GSelN t0 t1 t2 t3 t1 (GSkip) (PkSkip _ t0 t1 t2 t3)) p1))
  (let-match erased pp (GPCS _ d1 _ c2 _ _ nt2 p2 p3) ((GPCZ _ _ _ _) (GCCons g d n b a0 a1 (GCAPop0 g b n) (GCAPop1 g b n))))
  (let-match erased (not-fn b c c2 nt nt2) (Refl _ _))
  (GCCons g d n b a0 a1 (GCAOk g (GSG t2) d d1 n b b (GPop0) (GStPop0 d1 b) (GSelN t0 t1 t2 t3 t2 (GPop0) (PkPop0 _ t0 t1 t2 t3)) p2)
    (GCAOk g (GSG t3) d d1 n b c (GPop1) (GStPop1 d1 b c nt) (GSelN t0 t1 t2 t3 t3 (GPop1) (PkPop1 _ t0 t1 t2 t3)) p3)))

(def-fns _ $ (many mk-ent : (erased (Nat) n d) (many (GEnt n (Succ d)) push) (many (GEnt n d) skip) (many (GPrev n d) prev) ->
    (many (GEnt (Succ n) d) e))
  (let-match many push (MkGEnt _ _ a0 b0 pa0 pb0))
  (let-match many skip (MkGEnt _ _ a1 b1 pa1 pb1))
  (let ((many (Gtree) a2) (many (Gtree) b2) (erased (GPopCov n d (BTrue) a2 b2) qa) (erased (GPopCov n d (BFalse) b2 a2) qb))
    (match many prev _
      ((PNo _) (values (GEmpty) (GEmpty) (GPCZ n (BTrue) (GEmpty) (GEmpty)) (GPCZ n (BFalse) (GEmpty) (GEmpty))))
      ((PYes _ d1 pe)
        (let-match many pe (MkGEnt _ _ a b pa pb))
        (values a b (GPCS n d1 (BTrue) (BFalse) a b (NotT) pa pb) (GPCS n d1 (BFalse) (BTrue) b a (NotF) pb pa)))))
  (MkGEnt (Succ n) d (GNode a0 b1 a2 b2) (GNode b0 a1 b2 a2)
    (node-cov n d (BTrue) (BFalse) (NotT) a0 b1 a2 b2 pa0 pb1 qa) (node-cov n d (BFalse) (BTrue) (NotF) b0 a1 b2 a2 pb0 pa1 qb)))

(def-fns _ $ (many gstep : (erased (Nat) n d) (many (GPrev n d) prev) (subterm many (GRow n d) cur) -> (many (GRow (Succ n) d) r))
  (match many cur _
    ((GREnd _ _ l)
      (GRCons (Succ n) d (mk-ent n d (gent-vac n (Succ d) (lt-weaken (Succ n) d l)) (gent-vac n d l) prev)
        (GREnd (Succ n) (Succ d) (LtS (Succ n) d l))))
    ((GRCons _ _ e rest)
      (GRCons (Succ n) d (mk-ent n d (row-head n (Succ d) rest) e prev) (notail $ gstep n (Succ d) (PYes n d e) rest)))))

(def-fns _ $ (many grow-to : (subterm many (Nat) k) -> (many (GRow (Succ k) (Zero)) r))
  (match many k _
    ((Zero) (grow1))
    ((Succ k1) (gstep (Succ k1) (Zero) (PNo (Succ k1)) (notail $ grow-to k1)))))

; After gtree_mem_init_tree of initgtree.v, one direction: every balanced partial chromogram of h + 1 symbols is in gtu.
(def-fns _ $ (many gtree-full : (many (Nat) h) -> (many (Gtree) gtu) (erased (GCov (GSG gtu) (Zero) (BFalse) (Succ h)) gc))
  (let-match many (row-head (Succ h) (Zero) (grow-to h)) (MkGEnt _ _ _ tf _ cf))
  (values tf cf))

(def-adts $ (OddK : ((ES) st) -> Type)
  enum
  (many OKOdd : -> (OddK (ESOdd)))
  (many OKNot : (erased (ES) st) (erased (NotOdd st) n) -> (OddK st)))

(def-fns _ $ (many odd-kind : (many (ES) st) -> (many (OddK st) k))
  (match many st _ ((ESOdd) (OKOdd)) ((ESEven) (OKNot st (NOE))) ((ESStart) (OKNot st (NOS))) ((ESTail g) (OKNot st (NOT g)))))

(def-fns _ $ (many leaf-of : (erased (ES) st) (erased (NotOdd st) no) (subterm many (Nat) n) ->
    (many (Ctree) t) (erased (CtRoot t n) r) (erased (CtH (Zero) t) k) (erased (CEv t st) c))
  (let-match many n (Succ n1) ((Zero) (values (CEmpty) (RootE) (HE (Zero)) (CEvE st))))
  (let ((many t) (erased r) (erased k) (erased _)) (notail $ leaf-of st no n1))
  (values (CLeaf t) (RootL t n1 r) (HL t k) (CEvL t st no)))

(def-adts $ (LeafC : -> Type)
  enum
  (many MkLeafC : (many (Nat) n) (many (Ctree) t) (erased (CtRoot t n) r) (erased (CtH (Zero) t) k) -> (LeafC)))

(def-fns _ $ (many leaf-chains : (subterm many (Nat) k) (many (Nat) n) (many (Ctree) t) (erased (CtRoot t n) r) (erased (CtH (Zero) t) h)
    -> (many (List (LeafC)) tbl))
  (let ((many e)) (MkLeafC n t r h))
  (let-match many k (Succ k1) ((Zero) (Cons _ e (Nil _))))
  (Cons _ e (notail $ leaf-chains k1 (Succ n) (CLeaf t) (RootL t n r) (HL t h))))

(def-fns _ $ (erased leaf-cev : (erased (ES) st) (erased (NotOdd st) no) (erased (Ctree) t) (erased (CtH (Zero) t) h) -> (erased (CEv t st) c))
  (match erased h _ ((HE _) (CEvE st)) ((HL lf _) (CEvL lf st no))))

(def-fns _ $ (many leaf-get : (erased (ES) st) (erased (NotOdd st) no) (many (Nat) n) (subterm many (List (LeafC)) tbl) ->
    (many (Ctree) t) (erased (CtRoot t n) r) (erased (CtH (Zero) t) k) (erased (CEv t st) c))
  (let-match many tbl (Cons _ e rest) ((Nil _) (leaf-of st no n)))
  (let-match many e (MkLeafC m t r h))
  (let-match many (nat-eq m n) (Equal _ _ _) (else (tail $ leaf-get st no n rest)))
  (values t r h (leaf-cev st no t h)))

(def-fns _ $ (erased psplit-c0 : (erased (List RS) a ps s) (subterm erased (PSplitE (C0) a ps s) sp) -> (erased (Eq (List RS) s a) e))
  (let-match erased sp (PSCons _ x _ b rest _ st q) ((PSNil _ _) (Refl _ s)))
  (let-match erased st (PSE0 _ _) (absurd (PSE23 _ _ _ _ _ _ _ _ y _ _ _) y))
  (psplit-c0 a rest s q))

(def-fns _ $ (erased cons-cev : (erased (Ctree) t1 t2 t3 t) (erased (ES) st s0 s1 s2 s3) (erased (CtCons t1 t2 t3 t) tc)
    (erased (ESStep st (C0) s0) e0) (erased (ESStep st (C1) s1) e1) (erased (ESStep st (C2) s2) e2) (erased (ESStep st (C3) s3) e3)
    (erased (CEv t1 s1) c1) (erased (CEv t2 s2) c2) (erased (CEv t3 s3) c3) -> (erased (CEv t st) r))
  (match erased tc _
    ((CCEmpty) (CEvE st))
    ((CCNode _ _ _)
      (CEvN t1 t2 t3 st (MkCEvAt t (CEmpty) st s0 (C0) (SelN0 t1 t2 t3) e0 (CEvE s0)) (MkCEvAt t t1 st s1 (C1) (SelN1 t1 t2 t3) e1 c1)
        (MkCEvAt t t2 st s2 (C2) (SelN2 t1 t2 t3) e2 c2) (MkCEvAt t t3 st s3 (C3) (SelN3 t1 t2 t3) e3 c3)))))

; After ctree_sub_init_tree of initctree.v, one direction: the multiplicity of each even trace of length k in t is its number of
; matches in ps, read from the evenness state st.
(def-fns _ $ (many ct-build : (many (List (LeafC)) tbl) (subterm many (Nat) k) (many (List RS) ps) (many (ES) st) ->
    (many (Ctree) t) (erased (GE t ps st k) g) (erased (CEv t st) c) (erased (CtH k t) hk))
  (let-match many ps (Cons _ _ _) ((Nil _) (values (CEmpty) (GEDead (CEmpty) ps st k (PZNil)) (CEvE st) (HE k))))
  (let-match many (odd-kind st) (OKNot _ no) ((OKOdd) (values (CEmpty) (GEOdd (CEmpty) ps k) (CEvE st) (HE k))))
  (let-match many k (Succ k1)
    ((Zero)
      (let ((many c) (erased pc)) (pieces-root-c ps))
      (let ((many t) (erased rt) (erased hz) (erased ce)) (leaf-get st no c tbl))
      (values t (GENil t ps st c c rt pc (lt-succ c)) ce hz)))
  (let ((erased p0) (erased sp0)) (psplit-c (C0) (Nil _) ps))
  (let-match erased (psplit-c0 (Nil RS) ps p0 sp0) (Refl _ _))
  (let ((erased s0) (erased e0)) (esstep-c st (C0)))
  (let ((many p1) (erased sp1)) (psplit-c (C1) (Nil _) ps))
  (let ((many s1) (erased e1)) (esstep-c st (C1)))
  (let ((many t1) (erased g1) (erased c1) (erased h1)) (notail $ ct-build tbl k1 p1 s1))
  (let ((many p2) (erased sp2)) (psplit-c (C2) (Nil _) ps))
  (let ((many s2) (erased e2)) (esstep-c st (C2)))
  (let ((many t2) (erased g2) (erased c2) (erased h2)) (notail $ ct-build tbl k1 p2 s2))
  (let ((many p3) (erased sp3)) (psplit-c (C3) (Nil _) ps))
  (let ((many s3) (erased e3)) (esstep-c st (C3)))
  (let ((many t3) (erased g3) (erased c3) (erased h3)) (notail $ ct-build tbl k1 p3 s3))
  (let ((many t) (erased tc)) (ctree-cons t1 t2 t3))
  (values t
    (GES t ps st k1 (MkGEAt t (CEmpty) ps p0 st s0 k1 (C0) (sel-c0 t) sp0 e0 (GEDead (CEmpty) p0 s0 k1 (PZNil)))
      (MkGEAt t t1 ps p1 st s1 k1 (C1) (cons-sel-back t1 t2 t3 t t1 (C1) tc (SelN1 t1 t2 t3)) sp1 e1 g1)
      (MkGEAt t t2 ps p2 st s2 k1 (C2) (cons-sel-back t1 t2 t3 t t2 (C2) tc (SelN2 t1 t2 t3)) sp2 e2 g2)
      (MkGEAt t t3 ps p3 st s3 k1 (C3) (cons-sel-back t1 t2 t3 t t3 (C3) tc (SelN3 t1 t2 t3)) sp3 e3 g3))
    (cons-cev t1 t2 t3 t st s0 s1 s2 s3 tc e0 e1 e2 e3 c1 c2 c3)
    (cons-h k1 t1 t2 t3 t tc h1 h2 h3)))

(def-fns _ $ (many ctree-full : (many (Nat) h) (many (Gtree) gtu) ->
    (many (Ctree) ctu) (erased (GE ctu (Cons RS (MkRx (GSet) (BS0) (GSG gtu)) (Nil RS)) (ESStart) (Succ h)) ge) (erased (CEv ctu (ESStart)) ce)
    (erased (CtH (Succ h) ctu) hc))
  (ct-build (leaf-chains 1500 (Zero) (CEmpty) (RootE) (HE (Zero))) (Succ h) (Cons _ (MkRx _ (BS0) (GSG gtu)) $ Nil _) (ESStart)))
