(let ((erased RG)) (Rx (Gtree)))

; After ctr_sub of ctreerestrict.v: n matches of et in the restriction list r.
(def-adts $ (RCnt : ((List RG) r) ((List (Col)) et) ((Nat) n) -> Type)
  enum
  (many RCNil : (erased (List (Col)) et) -> (RCnt (Nil RG) et (Zero)))
  (many RCCons : (erased (Bstack) bs) (erased (Gtree) g) (erased (List RG) r) (erased (List (Col)) et) (erased (Nat) a b n)
      (erased (MC (GSG g) bs et a) m) (erased (RCnt r et b) c) (erased (Add a b n) p) -> (RCnt (Cons RG (MkRx (Gtree) bs g) r) et n)))

(def-fns _ $ (erased rcnt-exists : (subterm erased (List RG) r) (erased (List (Col)) et) -> (erased (Nat) n) (erased (RCnt r et n) c))
  (let-match erased r (Cons _ x rest) ((Nil _) (values (Zero) (RCNil et))))
  (let-match erased x (MkRx _ bs g))
  (let ((erased a) (erased m)) (mc-exists (GSG g) bs et))
  (let ((erased b) (erased c)) (rcnt-exists rest et))
  (let ((erased n) (erased p)) (add a b))
  (values n (RCCons bs g rest et a b n m c p)))

(def-fns _ $ (erased rcnt-fn : (erased (List RG) r) (erased (List (Col)) et) (erased (Nat) n m) (subterm erased (RCnt r et n) p)
    (erased (RCnt r et m) q) -> (erased (Eq (Nat) n m) e))
  (match erased p _
    ((RCNil _) (let-match erased q (RCNil _)) (Refl _ n))
    ((RCCons bs g rest _ a b _ ma ca pa)
      (let-match erased q (RCCons _ _ _ _ a2 b2 _ ma2 ca2 pa2))
      (let-match erased (mc-fn (GSG g) bs et a a2 ma ma2) (Refl _ _))
      (let-match erased (rcnt-fn rest et b b2 ca ca2) (Refl _ _))
      (add-fn a b n m pa pa2))))

; m is n minus k, truncated at zero.
(def-adts $ (Monus : ((Nat) n) ((Nat) k) ((Nat) m) -> Type)
  enum
  (many MoZ : (erased (Nat) n) -> (Monus n (Zero) n))
  (many MoE : (erased (Nat) k) -> (Monus (Zero) (Succ k) (Zero)))
  (many MoS : (erased (Nat) n k m) (erased (Monus n k m) p) -> (Monus (Succ n) (Succ k) m)))

(def-fns _ $ (erased monus-zero : (subterm erased (Nat) k) -> (erased (Monus (Zero) k (Zero)) p))
  (match erased k _ ((Zero) (MoZ (Zero))) ((Succ k1) (MoE k1))))

(def-fns _ $ (erased monus-add : (erased (Nat) n a m b m2 ab) (subterm erased (Monus n a m) p) (erased (Monus m b m2) q) (erased (Add a b ab) s) ->
    (erased (Monus n ab m2) r))
  (match erased p _
    ((MoZ _) (let-match erased s (AddZero _)) q)
    ((MoE a1) (let-match erased s (AddSucc _ _ ab1 _)) (match erased q _ ((MoZ _) (MoE ab1)) ((MoE _) (MoE ab1))))
    ((MoS n1 a1 _ p1) (let-match erased s (AddSucc _ _ ab1 s1)) (MoS n1 ab1 m2 (monus-add n1 a1 m b m2 ab1 p1 q s1)))))

(def-adts $ (RCons : ((Bstack) bs) ((Gtree) t) ((List RG) a) ((List RG) b) -> Type)
  enum
  (many RCE : (erased (Bstack) bs) (erased (List RG) a) -> (RCons bs (GEmpty) a a))
  (many RCC : (erased (Bstack) bs) (erased (Gtree) t) (erased (List RG) a) -> (RCons bs t a (Cons RG (MkRx (Gtree) bs t) a))))

(def-fns _ $ (many rg-cons : (many (Bstack) bs) (many (Gtree) t) (erased (List RG) a) (many (RxL (Gtree) a) al) ->
    (erased (List RG) b) (many (RxL (Gtree) b) bl) (erased (RCons bs t a b) p))
  (match many t _ ((GEmpty) (values a al (RCE bs a))) (else (values (Cons _ (MkRx _ bs t) a) (RxCons _ bs t a al) (RCC bs t a)))))

; c is a with the restriction popping the stack bs against e, if any, out of the node t0 t1 t2 t3.
(def-adts $ (PopRC : ((Bstack) bs) ((Col) e) ((Gtree) t0) ((Gtree) t1) ((Gtree) t2) ((Gtree) t3) ((List RG) a) ((List RG) c) -> Type)
  enum
  (many PRNone : (erased (Col) e) (erased (Gtree) t0 t1 t2 t3) (erased (List RG) a) -> (PopRC (BS0) e t0 t1 t2 t3 a a))
  (many PRSome : (erased (Bstack) bs b) (erased (Gsym) s) (erased (Col) e) (erased (Gtree) t0 t1 t2 t3 ts) (erased (List RG) a c)
      (erased (Popped bs b) pp) (erased (Sym s bs e b) z) (erased (Pick4 (Gtree) s t0 t1 t2 t3 ts) pk) (erased (RCons b ts a c) p)
      -> (PopRC bs e t0 t1 t2 t3 a c)))

; b is a with the matches that the restriction x has on traces beginning with e, shifted past e (after ctr_split of ctreerestrict.v).
(def-adts $ (CStepE : (RG x) ((Col) e) ((List RG) a) ((List RG) b) -> Type)
  enum
  (many SENone : (erased (Bstack) bs) (erased (Gtree) g) (erased (Bits) q) (erased (Col) e) (erased (List RG) a) (erased (LeafSet g q) l)
      -> (CStepE (MkRx (Gtree) bs g) e a a))
  (many SESkip : (erased (Bstack) bs) (erased (Gtree) t0 t1 t2 t3) (erased (List RG) a b) (erased (RCons bs t1 a b) p)
      -> (CStepE (MkRx (Gtree) bs (GNode t0 t1 t2 t3)) (C1) a b))
  (many SEP : (erased (Bstack) bs bs1) (erased (Col) e) (erased (Gtree) t0 t1 t2 t3) (erased (List RG) a c b)
      (erased (Sym (GPush) bs e bs1) y) (erased (PopRC bs e t0 t1 t2 t3 a c) pr) (erased (RCons bs1 t0 c b) p)
      -> (CStepE (MkRx (Gtree) bs (GNode t0 t1 t2 t3)) e a b)))

(def-adts $ (CSplitE : ((Col) e) ((List RG) a) ((List RG) r) ((List RG) s) -> Type)
  enum
  (many CSNil : (erased (Col) e) (erased (List RG) a) -> (CSplitE e a (Nil RG) a))
  (many CSCons : (erased (Col) e) (erased RG x) (erased (List RG) a b rest s) (erased (CStepE x e a b) p) (erased (CSplitE e b rest s) q)
      -> (CSplitE e a (Cons RG x rest) s)))

(def-fns _ $ (many ctr-pop : (many (Bstack) bs) (erased (Gtree) t0 t1) (many (Gtree) t2 t3) (erased (List RG) r2 r3) (many (RxL (Gtree) r2) l2)
    (many (RxL (Gtree) r3) l3) -> (erased (List RG) a2 a3) (many (RxL (Gtree) a2) m2) (many (RxL (Gtree) a3) m3)
    (erased (PopRC bs (C2) t0 t1 t2 t3 r2 a2) k2) (erased (PopRC bs (C3) t0 t1 t2 t3 r3 a3) k3))
  (match many bs _
    ((BS0) (values r2 r3 l2 l3 (PRNone (C2) t0 t1 t2 t3 r2) (PRNone (C3) t0 t1 t2 t3 r3)))
    ((BP0 b)
      (let ((erased a2) (many m2) (erased p2)) (rg-cons b t2 r2 l2))
      (let ((erased a3) (many m3) (erased p3)) (rg-cons b t3 r3 l3))
      (values a2 a3 m2 m3
        (PRSome bs b (GPop0) (C2) t0 t1 t2 t3 t2 r2 a2 (Popped0 b) (SPop02 b) (PkPop0 _ t0 t1 t2 t3) p2)
        (PRSome bs b (GPop1) (C3) t0 t1 t2 t3 t3 r3 a3 (Popped0 b) (SPop13 b) (PkPop1 _ t0 t1 t2 t3) p3)))
    ((BP1 b)
      (let ((erased a2) (many m2) (erased p2)) (rg-cons b t3 r2 l2))
      (let ((erased a3) (many m3) (erased p3)) (rg-cons b t2 r3 l3))
      (values a2 a3 m2 m3
        (PRSome bs b (GPop1) (C2) t0 t1 t2 t3 t3 r2 a2 (Popped1 b) (SPop12 b) (PkPop1 _ t0 t1 t2 t3) p2)
        (PRSome bs b (GPop0) (C3) t0 t1 t2 t3 t2 r3 a3 (Popped1 b) (SPop03 b) (PkPop0 _ t0 t1 t2 t3) p3)))))

(def-adts $ (MCX : (RG x) ((List (Col)) et) ((Nat) n) -> Type)
  enum
  (many MkMCX : (erased (Bstack) bs) (erased (Gtree) g) (erased (List (Col)) et) (erased (Nat) n) (erased (MC (GSG g) bs et n) m)
      -> (MCX (MkRx (Gtree) bs g) et n)))

(def-adts $ (GKind : ((Gtree) g) -> Type)
  enum
  (many GKNode : (erased (Gtree) g t0 t1 t2 t3) (erased (Eq (Gtree) g (GNode t0 t1 t2 t3)) e) -> (GKind g))
  (many GKLeaf : (erased (Gtree) g) (erased (Bits) q) (erased (LeafSet g q) l) -> (GKind g)))

(def-fns _ $ (many gtree-kind : (many (Gtree) g) -> (many (GKind g) k))
  (match many g _
    ((GNode t0 t1 t2 t3) (GKNode g t0 t1 t2 t3 (Refl _ g)))
    ((GL0) (GKLeaf g _ (LS0)))
    ((GL1) (GKLeaf g _ (LS1)))
    ((GL2) (GKLeaf g _ (LS2)))
    ((GL3) (GKLeaf g _ (LS3)))
    ((GL01) (GKLeaf g _ (LS01)))
    ((GL12) (GKLeaf g _ (LS12)))
    ((GL13) (GKLeaf g _ (LS13)))
    ((GL23) (GKLeaf g _ (LS23)))
    ((GEmpty) (GKLeaf g _ (LSE)))))

(def-fns _ $ (many ctr-split-c : (erased (List RG) r1 r2 r3) (many (RxL (Gtree) r1) l1) (many (RxL (Gtree) r2) l2) (many (RxL (Gtree) r3) l3)
    (erased (List RG) r) (subterm many (RxL (Gtree) r) rl) ->
    (erased (List RG) s1 s2 s3) (many (RxL (Gtree) s1) m1) (many (RxL (Gtree) s2) m2) (many (RxL (Gtree) s3) m3)
    (erased (CSplitE (C1) r1 r s1) p1) (erased (CSplitE (C2) r2 r s2) p2) (erased (CSplitE (C3) r3 r s3) p3))
  (let-match many rl (RxCons _ bs g rest tl) ((RxNil _) (values r1 r2 r3 l1 l2 l3 (CSNil (C1) r1) (CSNil (C2) r2) (CSNil (C3) r3))))
  (let ((erased x)) (MkRx (Gtree) bs g))
  (match many (gtree-kind g) _
    ((GKLeaf _ q l)
      (let ((erased s1) (erased s2) (erased s3) (many m1) (many m2) (many m3) (erased p1) (erased p2) (erased p3))
        (tail $ ctr-split-c r1 r2 r3 l1 l2 l3 rest tl))
      (values s1 s2 s3 m1 m2 m3 (CSCons (C1) x r1 r1 rest s1 (SENone bs g q (C1) r1 l) p1) (CSCons (C2) x r2 r2 rest s2 (SENone bs g q (C2) r2 l) p2)
        (CSCons (C3) x r3 r3 rest s3 (SENone bs g q (C3) r3 l) p3)))
    ((GKNode _ u0 u1 u2 u3 eq)
      (let-match erased eq (Refl _ _))
      (let-match many g (GNode t0 t1 t2 t3))
      (let ((erased a2) (erased a3) (many n2) (many n3) (erased k2) (erased k3)) (ctr-pop bs t0 t1 t2 t3 r2 r3 l2 l3))
      (let ((erased b1) (many o1) (erased q1)) (rg-cons bs t1 r1 l1))
      (let ((erased b2) (many o2) (erased q2)) (rg-cons (BP0 bs) t0 a2 n2))
      (let ((erased b3) (many o3) (erased q3)) (rg-cons (BP1 bs) t0 a3 n3))
      (let ((erased s1) (erased s2) (erased s3) (many m1) (many m2) (many m3) (erased p1) (erased p2) (erased p3))
        (tail $ ctr-split-c b1 b2 b3 o1 o2 o3 rest tl))
      (values s1 s2 s3 m1 m2 m3 (CSCons (C1) x r1 b1 rest s1 (SESkip bs t0 t1 t2 t3 r1 b1 q1) p1)
        (CSCons (C2) x r2 b2 rest s2 (SEP bs (BP0 bs) (C2) t0 t1 t2 t3 r2 a2 b2 (SPush2 bs) k2 q2) p2)
        (CSCons (C3) x r3 b3 rest s3 (SEP bs (BP1 bs) (C3) t0 t1 t2 t3 r3 a3 b3 (SPush3 bs) k3 q3) p3)))))

(def-fns _ $ (erased rcons-cnt : (erased (Bstack) bs) (erased (Gtree) t) (erased (List RG) a b) (erased (List (Col)) et) (erased (Nat) u v w)
    (erased (RCons bs t a b) p) (erased (RCnt a et u) ca) (erased (RCnt b et w) cb) (erased (MC (GSG t) bs et v) m) -> (erased (Add v u w) r))
  (match erased p _
    ((RCE _ _) (let-match erased (mc-zero bs et v m) (Refl _ _)) (let-match erased (rcnt-fn a et u w ca cb) (Refl _ _)) (AddZero u))
    ((RCC _ _ _)
      (let-match erased cb (RCCons _ _ _ _ v2 u2 _ m2 c2 s))
      (let-match erased (mc-fn (GSG t) bs et v v2 m m2) (Refl _ _))
      (let-match erased (rcnt-fn a et u u2 ca c2) (Refl _ _))
      s)))

(def-fns _ $ (erased mc-one-long : (erased (Bstack) bs) (erased (Col) e) (erased (List (Col)) et) (erased (Nat) n)
    (erased (MC (GSOne) bs (Cons (Col) e et) n) m) -> (erased (Eq (Nat) n (Zero)) r))
  (match erased (col-kind e bs) _
    ((K0 _) (mc-inv-0 (GSOne) bs et n m))
    ((K1 _)
      (let ((erased g1) (erased p) (erased q)) (mc-inv-skip (GSOne) bs et n m))
      (let-match erased p (GSelOne _))
      (mc-zero bs et n q))
    ((K23 _ _ bs1 y po)
      (match erased po _
        ((PNone _)
          (let ((erased g1) (erased p) (erased q)) (mc-inv-push (GSOne) bs1 e et n y m))
          (let-match erased p (GSelOne _))
          (mc-zero bs1 et n q))
        ((PSome _ b _ s pp z)
          (let ((erased n1) (erased n2) (erased g1) (erased g2) (erased p1) (erased q1) (erased p2) (erased q2) (erased a))
            (mc-inv-pp (GSOne) bs b bs1 s e et n y pp z m))
          (let-match erased p1 (GSelOne _))
          (let-match erased p2 (GSelOne _))
          (let-match erased (mc-zero bs1 et n1 q1) (Refl _ _))
          (let-match erased (mc-zero b et n2 q2) (Refl _ _))
          (let-match erased a (AddZero _))
          (Refl _ n))))))

(def-fns _ $ (erased mc-bset-long : (erased (Bool) b) (erased (GSet) gs) (erased (Bstack) bs) (erased (Col) e) (erased (List (Col)) et)
    (erased (Nat) n) (erased (BSet b gs) p) (erased (MC gs bs (Cons (Col) e et) n) m) -> (erased (Eq (Nat) n (Zero)) r))
  (match erased p _
    ((BSetT) (mc-one-long bs e et n m))
    ((BSetF) (mc-zero bs (Cons _ e et) n m))))

(def-fns _ $ (erased leaf-sel-long : (erased (Gtree) g) (erased (Bits) q) (erased (Gsym) s) (erased (GSet) gs) (erased (Bstack) bs) (erased (Col) e)
    (erased (List (Col)) et) (erased (Nat) n) (erased (LeafSet g q) l) (erased (GSel (GSG g) s gs) p) (erased (MC gs bs (Cons (Col) e et) n) m) ->
    (erased (Eq (Nat) n (Zero)) r))
  (let-match erased p (GSelL _ b0 b1 b2 b3 b _ _ l2 pk bsp) (absurd (GSelN _ _ _ _ _ _ _) l))
  (mc-bset-long b gs bs e et n bsp m))

(def-fns _ $ (erased mc-leaf-long : (erased (Gtree) g) (erased (Bits) q) (erased (Bstack) bs) (erased (Col) e e2) (erased (List (Col)) et)
    (erased (Nat) n) (erased (LeafSet g q) l) (erased (MC (GSG g) bs (Cons (Col) e (Cons (Col) e2 et)) n) m) -> (erased (Eq (Nat) n (Zero)) r))
  (let ((erased et1)) (Cons (Col) e2 et))
  (match erased (col-kind e bs) _
    ((K0 _) (mc-inv-0 (GSG g) bs et1 n m))
    ((K1 _)
      (let ((erased g1) (erased p) (erased q1)) (mc-inv-skip (GSG g) bs et1 n m))
      (leaf-sel-long g q (GSkip) g1 bs e2 et n l p q1))
    ((K23 _ _ bs1 y po)
      (match erased po _
        ((PNone _)
          (let ((erased g1) (erased p) (erased q1)) (mc-inv-push (GSG g) bs1 e et1 n y m))
          (leaf-sel-long g q (GPush) g1 bs1 e2 et n l p q1))
        ((PSome _ b _ s pp z)
          (let ((erased n1) (erased n2) (erased g1) (erased g2) (erased p1) (erased q1) (erased p2) (erased q2) (erased a))
            (mc-inv-pp (GSG g) bs b bs1 s e et1 n y pp z m))
          (let-match erased (leaf-sel-long g q (GPush) g1 bs1 e2 et n1 l p1 q1) (Refl _ _))
          (let-match erased (leaf-sel-long g q s g2 b e2 et n2 l p2 q2) (Refl _ _))
          (let-match erased a (AddZero _))
          (Refl _ n))))))

(def-fns _ $ (erased node-sel : (erased (Gtree) t0 t1 t2 t3 u) (erased (Gsym) s) (erased (GSet) gs) (erased (Pick4 (Gtree) s t0 t1 t2 t3 u) pk)
    (erased (GSel (GSG (GNode t0 t1 t2 t3)) s gs) p) -> (erased (Eq (GSet) gs (GSG u)) e))
  (gsel-fn (GSG (GNode t0 t1 t2 t3)) gs (GSG u) s p (GSelN t0 t1 t2 t3 u s pk)))

(def-fns _ $ (erased cstepe-cnt : (erased RG x) (erased (Col) e e2) (erased (List RG) a b) (erased (List (Col)) et) (erased (Nat) u v w)
    (erased (CStepE x e a b) st) (erased (RCnt a (Cons (Col) e2 et) u) ca) (erased (RCnt b (Cons (Col) e2 et) w) cb)
    (erased (MCX x (Cons (Col) e (Cons (Col) e2 et)) v) mx) -> (erased (Add v u w) r))
  (let ((erased et1)) (Cons (Col) e2 et))
  (let-match erased mx (MkMCX bs g _ _ m))
  (match erased st _
    ((SENone _ _ q _ _ l)
      (let-match erased (mc-leaf-long g q bs e e2 et v l m) (Refl _ _))
      (let-match erased (rcnt-fn a et1 u w ca cb) (Refl _ _))
      (AddZero u))
    ((SESkip _ t0 t1 t2 t3 _ _ p)
      (let ((erased g1) (erased sl) (erased m1)) (mc-inv-skip (GSG g) bs et1 v m))
      (let-match erased (node-sel t0 t1 t2 t3 t1 (GSkip) g1 (PkSkip _ t0 t1 t2 t3) sl) (Refl _ _))
      (rcons-cnt bs t1 a b et1 u v w p ca cb m1))
    ((SEP _ bs1 _ t0 t1 t2 t3 _ c _ y pr p)
      (let ((erased cn) (erased rc)) (rcnt-exists c et1))
      (match erased pr _
        ((PRNone _ _ _ _ _ _)
          (let ((erased g1) (erased sl) (erased m1)) (mc-inv-push (GSG g) bs1 e et1 v y m))
          (let-match erased (node-sel t0 t1 t2 t3 t0 (GPush) g1 (PkPush _ t0 t1 t2 t3) sl) (Refl _ _))
          (rcons-cnt bs1 t0 a b et1 u v w p ca cb m1))
        ((PRSome _ b1 s _ _ _ _ _ ts _ _ pp z pk q)
          (let ((erased n1) (erased n2) (erased g1) (erased g2) (erased s1) (erased m1) (erased s2) (erased m2) (erased ad))
            (mc-inv-pp (GSG g) bs b1 bs1 s e et1 v y pp z m))
          (let-match erased (node-sel t0 t1 t2 t3 t0 (GPush) g1 (PkPush _ t0 t1 t2 t3) s1) (Refl _ _))
          (let-match erased (node-sel t0 t1 t2 t3 ts s g2 pk s2) (Refl _ _))
          (let ((erased q2)) (rcons-cnt b1 ts a c et1 u n2 cn q ca rc m2))
          (let ((erased q3)) (rcons-cnt bs1 t0 c b et1 cn n1 w p rc cb m1))
          (let ((erased k) (erased q4) (erased q5)) (add-assoc-back n1 n2 u cn w q3 q2))
          (let-match erased (add-fn n1 n2 k v q4 ad) (Refl _ _))
          q5)))))

(def-fns _ $ (erased csplit-cnt : (erased (Col) e e2) (erased (List RG) a r s) (erased (List (Col)) et) (erased (Nat) u v w)
    (subterm erased (CSplitE e a r s) sp) (erased (RCnt a (Cons (Col) e2 et) u) ca) (erased (RCnt s (Cons (Col) e2 et) w) cs)
    (erased (RCnt r (Cons (Col) e (Cons (Col) e2 et)) v) cr) -> (erased (Add v u w) res))
  (let ((erased et1)) (Cons (Col) e2 et))
  (match erased sp _
    ((CSNil _ _) (let-match erased cr (RCNil _)) (let-match erased (rcnt-fn a et1 u w ca cs) (Refl _ _)) (AddZero u))
    ((CSCons _ x _ b rest _ st q)
      (let-match erased cr (RCCons bs g _ _ a1 b1 _ m c p))
      (let ((erased ub) (erased cb)) (rcnt-exists b et1))
      (let ((erased q1)) (cstepe-cnt x e e2 a b et u a1 ub st ca cb (MkMCX bs g (Cons _ e et1) a1 m)))
      (let ((erased q2)) (csplit-cnt e e2 b rest s et ub b1 w q cb cs c))
      (let ((erased k) (erased q3) (erased q4)) (add-assoc-back b1 a1 u ub w q2 q1))
      (let-match erased (add-fn b1 a1 k v q3 (add-comm a1 b1 v p)) (Refl _ _))
      q4)))

(def-adts $ (B2N : ((Bool) b) ((Nat) n) -> Type)
  enum
  (many B2NT : -> (B2N (BTrue) (Succ (Zero))))
  (many B2NF : -> (B2N (BFalse) (Zero))))

(def-fns _ $ (many decr-if-c : (many (Bool) b) (many (Ctree) lf) (erased (Nat) n) (erased (CtRoot lf n) p) (erased (CtH (Zero) lf) hh) ->
    (many (Ctree) r) (erased (Nat) m k) (erased (CtRoot r m) q) (erased (CtH (Zero) r) hr) (erased (B2N b k) bk) (erased (Monus n k m) o))
  (let ((erased one)) (Succ (Zero)))
  (match many b _
    ((BFalse) (values lf n (Zero) p hh (B2NF) (MoZ n)))
    ((BTrue)
      (match many lf _
        ((CLeaf l) (let-match erased p (RootL _ n1 p1)) (let-match erased hh (HL _ h1)) (values l n1 one p1 h1 (B2NT) (MoS n1 (Zero) n1 (MoZ n1))))
        ((CEmpty) (let-match erased p (RootE)) (values lf n one p hh (B2NT) (MoE (Zero))))
        ((CNode _ _ _) (let-match erased p (RootN _ _ _)) (values lf n one p hh (B2NT) (MoE (Zero))))))))

; The symbols in a gtree as a set of one-symbol chromograms: those of a leaf, none for a node.
(def-adts $ (GBitsOf : ((Gtree) g) ((Bits) q) -> Type)
  enum
  (many GBLeaf : (erased (Gtree) g) (erased (Bits) q) (erased (LeafSet g q) l) -> (GBitsOf g q))
  (many GBNode : (erased (Gtree) t0 t1 t2 t3) -> (GBitsOf (GNode t0 t1 t2 t3) (MkBits (BFalse) (BFalse) (BFalse) (BFalse)))))

(def-fns _ $ (many gbits-c : (many (Gtree) g) -> (many (Bool) b0 b1 b2 b3) (erased (GBitsOf g (MkBits b0 b1 b2 b3)) p))
  (let ((many T) (many F)) (values (BTrue) (BFalse)))
  (match many g _
    ((GNode t0 t1 t2 t3) (values F F F F (GBNode t0 t1 t2 t3)))
    ((GL0) (values T F F F (GBLeaf g _ (LS0))))
    ((GL1) (values F T F F (GBLeaf g _ (LS1))))
    ((GL2) (values F F T F (GBLeaf g _ (LS2))))
    ((GL3) (values F F F T (GBLeaf g _ (LS3))))
    ((GL01) (values T T F F (GBLeaf g _ (LS01))))
    ((GL12) (values F T T F (GBLeaf g _ (LS12))))
    ((GL13) (values F T F T (GBLeaf g _ (LS13))))
    ((GL23) (values F F T T (GBLeaf g _ (LS23))))
    ((GEmpty) (values F F F F (GBLeaf g _ (LSE))))))

(def-fns _ $ (erased gsel-root : (erased (Gtree) g) (erased (Bool) b0 b1 b2 b3 b) (erased (Gsym) s) (erased (Nat) k)
    (erased (GBitsOf g (MkBits b0 b1 b2 b3)) gb) (erased (Pick4 (Bool) s b0 b1 b2 b3 b) pk) (erased (B2N b k) bk) ->
    (erased (GSet) gs) (erased (GSel (GSG g) s gs) sl) (erased (GRoot gs k) rt))
  (match erased gb _
    ((GBNode t0 t1 t2 t3)
      (let ((erased u) (erased pu)) (pick4-exists (Gtree) s t0 t1 t2 t3))
      (match erased pk _
        ((PkPush _ _ _ _ _) (let-match erased bk (B2NF)) (values (GSG u) (GSelN t0 t1 t2 t3 u s pu) (GRG u)))
        ((PkSkip _ _ _ _ _) (let-match erased bk (B2NF)) (values (GSG u) (GSelN t0 t1 t2 t3 u s pu) (GRG u)))
        ((PkPop0 _ _ _ _ _) (let-match erased bk (B2NF)) (values (GSG u) (GSelN t0 t1 t2 t3 u s pu) (GRG u)))
        ((PkPop1 _ _ _ _ _) (let-match erased bk (B2NF)) (values (GSG u) (GSelN t0 t1 t2 t3 u s pu) (GRG u)))))
    ((GBLeaf _ _ l)
      (match erased bk _
        ((B2NT) (values (GSOne) (GSelL g b0 b1 b2 b3 b s (GSOne) l pk (BSetT)) (GROne)))
        ((B2NF) (values (GSG (GEmpty)) (GSelL g b0 b1 b2 b3 b s (GSG (GEmpty)) l pk (BSetF)) (GRG (GEmpty))))))))

; One colour's decrement: lf with root n became l, with root c, n less the k matches of x on [e].
(def-adts $ (DecrRes : (RG x) ((Col) e) ((Nat) n) ((Ctree) l) -> Type)
  enum
  (many MkDecrRes : (erased RG x) (erased (Col) e) (erased (Nat) n c k) (erased (Ctree) l) (erased (CtRoot l c) q) (erased (CtH (Zero) l) hl)
      (erased (MCX x (Cons (Col) e (Nil (Col))) k) m) (erased (Monus n k c) o) -> (DecrRes x e n l)))

(def-fns _ $ (erased mc1-push : (erased (Gtree) g) (erased (Bool) b0 b1 b2 b3) (erased (Bstack) bs1) (erased (Col) e) (erased (Nat) k)
    (erased (GBitsOf g (MkBits b0 b1 b2 b3)) gb) (erased (B2N b0 k) bk) (erased (Sym (GPush) (BS0) e bs1) y) ->
    (erased (MCX (MkRx (Gtree) (BS0) g) (Cons (Col) e (Nil (Col))) k) m))
  (let ((erased gs) (erased sl) (erased rt)) (gsel-root g b0 b1 b2 b3 b0 (GPush) k gb (PkPush _ b0 b1 b2 b3) bk))
  (MkMCX (BS0) g (Cons _ e (Nil _)) k (MCPush (GSG g) gs bs1 e (Nil _) k y sl (MCNil gs bs1 k rt))))

(def-fns _ $ (erased mc1-skip : (erased (Gtree) g) (erased (Bool) b0 b1 b2 b3) (erased (Bstack) bs) (erased (Nat) k)
    (erased (GBitsOf g (MkBits b0 b1 b2 b3)) gb) (erased (B2N b1 k) bk) ->
    (erased (MCX (MkRx (Gtree) bs g) (Cons (Col) (C1) (Nil (Col))) k) m))
  (let ((erased gs) (erased sl) (erased rt)) (gsel-root g b0 b1 b2 b3 b1 (GSkip) k gb (PkSkip _ b0 b1 b2 b3) bk))
  (MkMCX bs g (Cons _ (C1) (Nil _)) k (MCSkip (GSG g) gs bs (Nil _) k sl (MCNil gs bs k rt))))

(def-fns _ $ (erased mc1-pp : (erased (Gtree) g) (erased (Bool) b0 b1 b2 b3 bp) (erased (Bstack) bs b bs1) (erased (Gsym) s) (erased (Col) e)
    (erased (Nat) k0 kp k) (erased (GBitsOf g (MkBits b0 b1 b2 b3)) gb) (erased (B2N b0 k0) bk0) (erased (Pick4 (Bool) s b0 b1 b2 b3 bp) pk)
    (erased (B2N bp kp) bkp) (erased (Popped bs b) pp) (erased (Sym (GPush) bs e bs1) y) (erased (Sym s bs e b) z) (erased (Add k0 kp k) a) ->
    (erased (MCX (MkRx (Gtree) bs g) (Cons (Col) e (Nil (Col))) k) m))
  (let ((erased g1) (erased s1) (erased r1)) (gsel-root g b0 b1 b2 b3 b0 (GPush) k0 gb (PkPush _ b0 b1 b2 b3) bk0))
  (let ((erased g2) (erased s2) (erased r2)) (gsel-root g b0 b1 b2 b3 bp s kp gb pk bkp))
  (MkMCX bs g (Cons _ e (Nil _)) k (MCPP (GSG g) g1 g2 bs b bs1 s e (Nil _) k0 kp k pp y s1 (MCNil g1 bs1 k0 r1) z s2 (MCNil g2 b kp r2) a)))

(def-fns _ $ (many decr2 : (erased (Gtree) g) (erased (Bool) b1 b2 b3) (many (Bool) b0 bp) (erased (Bstack) bs b bs1) (erased (Gsym) s) (erased (Col) e)
    (many (Ctree) lf) (erased (Nat) n) (erased (CtRoot lf n) p) (erased (CtH (Zero) lf) hh) (erased (GBitsOf g (MkBits b0 b1 b2 b3)) gb)
    (erased (Pick4 (Bool) s b0 b1 b2 b3 bp) pk) (erased (Popped bs b) pp) (erased (Sym (GPush) bs e bs1) y) (erased (Sym s bs e b) z) ->
    (many (Ctree) l) (erased (DecrRes (MkRx (Gtree) bs g) e n l) d))
  (let ((many l1) (erased c1) (erased kp) (erased q1) (erased h1) (erased bkp) (erased o1)) (decr-if-c bp lf n p hh))
  (let ((many l) (erased c) (erased k0) (erased q) (erased h) (erased bk0) (erased o)) (decr-if-c b0 l1 c1 q1 h1))
  (let ((erased k) (erased a)) (add k0 kp))
  (values l (MkDecrRes (MkRx (Gtree) bs g) e n c k l q h (mc1-pp g b0 b1 b2 b3 bp bs b bs1 s e k0 kp k gb bk0 pk bkp pp y z a)
    (monus-add n kp c1 k0 c k o1 o (add-comm k0 kp k a)))))

(def-fns _ $ (many decr-step : (many (Bstack) bs) (many (Gtree) g) (many (Ctree) lf1 lf2 lf3) (erased (Nat) n1 n2 n3)
    (erased (CtRoot lf1 n1) p1) (erased (CtRoot lf2 n2) p2) (erased (CtRoot lf3 n3) p3)
    (erased (CtH (Zero) lf1) h1) (erased (CtH (Zero) lf2) h2) (erased (CtH (Zero) lf3) h3) ->
    (many (Ctree) l1 l2 l3) (erased (DecrRes (MkRx (Gtree) bs g) (C1) n1 l1) d1) (erased (DecrRes (MkRx (Gtree) bs g) (C2) n2 l2) d2)
    (erased (DecrRes (MkRx (Gtree) bs g) (C3) n3 l3) d3))
  (let ((erased x)) (MkRx (Gtree) bs g))
  (let ((many b0) (many b1) (many b2) (many b3) (erased gb)) (gbits-c g))
  (let ((many l1) (erased c1) (erased k1) (erased q1) (erased hl1) (erased bk1) (erased o1)) (decr-if-c b1 lf1 n1 p1 h1))
  (let ((erased d1)) (MkDecrRes x (C1) n1 c1 k1 l1 q1 hl1 (mc1-skip g b0 b1 b2 b3 bs k1 gb bk1) o1))
  (match many bs _
    ((BS0)
      (let ((many l2) (erased c2) (erased k2) (erased q2) (erased hl2) (erased bk2) (erased o2)) (decr-if-c b0 lf2 n2 p2 h2))
      (let ((many l3) (erased c3) (erased k3) (erased q3) (erased hl3) (erased bk3) (erased o3)) (decr-if-c b0 lf3 n3 p3 h3))
      (values l1 l2 l3 d1 (MkDecrRes x (C2) n2 c2 k2 l2 q2 hl2 (mc1-push g b0 b1 b2 b3 (BP0 bs) (C2) k2 gb bk2 (SPush2 bs)) o2)
        (MkDecrRes x (C3) n3 c3 k3 l3 q3 hl3 (mc1-push g b0 b1 b2 b3 (BP1 bs) (C3) k3 gb bk3 (SPush3 bs)) o3)))
    ((BP0 b)
      (let ((many l2) (erased d2))
        (decr2 g b1 b2 b3 b0 b2 bs b (BP0 bs) (GPop0) (C2) lf2 n2 p2 h2 gb (PkPop0 _ b0 b1 b2 b3) (Popped0 b) (SPush2 bs) (SPop02 b)))
      (let ((many l3) (erased d3))
        (decr2 g b1 b2 b3 b0 b3 bs b (BP1 bs) (GPop1) (C3) lf3 n3 p3 h3 gb (PkPop1 _ b0 b1 b2 b3) (Popped0 b) (SPush3 bs) (SPop13 b)))
      (values l1 l2 l3 d1 d2 d3))
    ((BP1 b)
      (let ((many l2) (erased d2))
        (decr2 g b1 b2 b3 b0 b3 bs b (BP0 bs) (GPop1) (C2) lf2 n2 p2 h2 gb (PkPop1 _ b0 b1 b2 b3) (Popped1 b) (SPush2 bs) (SPop12 b)))
      (let ((many l3) (erased d3))
        (decr2 g b1 b2 b3 b0 b2 bs b (BP1 bs) (GPop0) (C3) lf3 n3 p3 h3 gb (PkPop0 _ b0 b1 b2 b3) (Popped1 b) (SPush3 bs) (SPop03 b)))
      (values l1 l2 l3 d1 d2 d3))))

; The decrements of all of r on one colour.
(def-adts $ (DecrAll : ((List RG) r) ((Col) e) ((Nat) n) ((Ctree) l) -> Type)
  enum
  (many MkDecrAll : (erased (List RG) r) (erased (Col) e) (erased (Nat) n c k) (erased (Ctree) l) (erased (CtRoot l c) q) (erased (CtH (Zero) l) hl)
      (erased (RCnt r (Cons (Col) e (Nil (Col))) k) m) (erased (Monus n k c) o) -> (DecrAll r e n l)))

(def-fns _ $ (erased decr-cons : (erased RG x) (erased (List RG) rest) (erased (Col) e) (erased (Nat) n c) (erased (Ctree) l m)
    (erased (DecrRes x e n l) d) (erased (CtRoot l c) ql) (erased (DecrAll rest e c m) da) -> (erased (DecrAll (Cons RG x rest) e n m) r))
  (let-match erased d (MkDecrRes _ _ _ c1 k1 _ q1 _ mx o1))
  (let-match erased (root-fn l c c1 ql q1) (Refl _ _))
  (let-match erased da (MkDecrAll _ _ _ c2 k2 _ q2 h2 m2 o2))
  (let-match erased mx (MkMCX bs g _ _ mc))
  (let ((erased k) (erased a)) (add k1 k2))
  (MkDecrAll (Cons RG x rest) e n c2 k m q2 h2 (RCCons bs g rest (Cons _ e (Nil _)) k1 k2 k mc m2 a) (monus-add n k1 c1 k2 c2 k o1 o2 a)))

(def-fns _ $ (many ctr-decr-c : (many (Ctree) lf1 lf2 lf3) (erased (List RG) r) (subterm many (RxL (Gtree) r) rl) (erased (Nat) n1 n2 n3)
    (erased (CtRoot lf1 n1) p1) (erased (CtRoot lf2 n2) p2) (erased (CtRoot lf3 n3) p3)
    (erased (CtH (Zero) lf1) h1) (erased (CtH (Zero) lf2) h2) (erased (CtH (Zero) lf3) h3) ->
    (many (Ctree) m1 m2 m3) (erased (DecrAll r (C1) n1 m1) d1) (erased (DecrAll r (C2) n2 m2) d2) (erased (DecrAll r (C3) n3 m3) d3))
  (let-match many rl (RxCons _ bs g rest tl)
    ((RxNil _) (values lf1 lf2 lf3 (MkDecrAll r (C1) n1 n1 (Zero) lf1 p1 h1 (RCNil _) (MoZ n1)) (MkDecrAll r (C2) n2 n2 (Zero) lf2 p2 h2 (RCNil _) (MoZ n2))
      (MkDecrAll r (C3) n3 n3 (Zero) lf3 p3 h3 (RCNil _) (MoZ n3)))))
  (let ((erased x)) (MkRx (Gtree) bs g))
  (let ((many l1) (many l2) (many l3) (erased e1) (erased e2) (erased e3)) (decr-step bs g lf1 lf2 lf3 n1 n2 n3 p1 p2 p3 h1 h2 h3))
  (let-match erased e1 (MkDecrRes _ _ _ c1 _ _ q1 k1 _ _))
  (let-match erased e2 (MkDecrRes _ _ _ c2 _ _ q2 k2 _ _))
  (let-match erased e3 (MkDecrRes _ _ _ c3 _ _ q3 k3 _ _))
  (let ((many m1) (many m2) (many m3) (erased d1) (erased d2) (erased d3)) (tail $ ctr-decr-c l1 l2 l3 rest tl c1 c2 c3 q1 q2 q3 k1 k2 k3))
  (values m1 m2 m3 (decr-cons x rest (C1) n1 c1 l1 m1 e1 q1 d1) (decr-cons x rest (C2) n2 c2 l2 m2 e2 q2 d2) (decr-cons x rest (C3) n3 c3 l3 m3 e3 q3 d3)))

(def-adts $ (IfE : ((Ctree) t) ((Ctree) l) ((Ctree) g) -> Type)
  enum
  (many IEY : (erased (Ctree) t) -> (IfE t (CEmpty) t))
  (many IEN : (erased (Ctree) t l) -> (IfE t l (CEmpty))))

(def-fns _ $ (many if-e-c : (many (Ctree) t l) -> (many (Ctree) g) (erased (IfE t l g) p))
  (match many l _ ((CEmpty) (values t (IEY t))) (else (values (CEmpty) (IEN t l)))))

(def-fns _ $ (erased ife-h : (erased (Ctree) t l g) (erased (IfE t l g) p) (erased (CtH (Zero) t) h) -> (erased (CtH (Zero) g) r))
  (match erased p _ ((IEY _) h) ((IEN _ _) (HE (Zero)))))

; After ctree_restrict of ctreerestrict.v: keep holds the traces of t less their matches in r, gone those of t that keep lost.
(def-adts $ (CRes : ((Nat) h) ((Ctree) t) ((List RG) r) ((Ctree) keep) ((Ctree) gone) -> Type)
  enum
  (many CRNil : (erased (Nat) h) (erased (Ctree) t) -> (CRes h t (Nil RG) t (CEmpty)))
  (many CRE : (erased (Nat) h) (erased (List RG) r) -> (CRes h (CEmpty) r (CEmpty) (CEmpty)))
  (many CRS : (erased (Nat) h) (erased (Ctree) t1 t2 t3 a1 a2 a3 b1 b2 b3 keep gone) (erased (List RG) r r1 r2 r3)
      (erased (CSplitE (C1) (Nil RG) r r1) s1) (erased (CSplitE (C2) (Nil RG) r r2) s2) (erased (CSplitE (C3) (Nil RG) r r3) s3)
      (erased (CRes h t1 r1 a1 b1) c1) (erased (CRes h t2 r2 a2 b2) c2) (erased (CRes h t3 r3 a3 b3) c3)
      (erased (CtCons a1 a2 a3 keep) ck) (erased (CtCons b1 b2 b3 gone) cg) -> (CRes (Succ h) (CNode t1 t2 t3) r keep gone))
  (many CRZ : (erased (Ctree) t1 t2 t3 l1 l2 l3 g1 g2 g3 keep gone) (erased (List RG) r) (erased (Nat) n1 n2 n3)
      (erased (CtRoot t1 n1) p1) (erased (CtRoot t2 n2) p2) (erased (CtRoot t3 n3) p3)
      (erased (DecrAll r (C1) n1 l1) d1) (erased (DecrAll r (C2) n2 l2) d2) (erased (DecrAll r (C3) n3 l3) d3) (erased (CtCons l1 l2 l3 keep) ck)
      (erased (IfE t1 l1 g1) f1) (erased (IfE t2 l2 g2) f2) (erased (IfE t3 l3 g3) f3) (erased (CtCons g1 g2 g3 gone) cg)
      -> (CRes (Zero) (CNode t1 t2 t3) r keep gone)))

; A ctree whose nodes are held unique, so that ctree-restrict-u rewrites them in place; UBot holds a node of leaves.
(def-adts $ (UTree : -> Type)
  enum
  (many UNode : (unique (UTree) u1 u2 u3) -> (UTree))
  (many UBot : (many (Ctree) l1 l2 l3) -> (UTree))
  (many UEmpty : -> (UTree)))

; u holds t, which has height h + 1.
(def-adts $ (UT : ((Nat) h) ((UTree) u) ((Ctree) t) -> Type)
  enum
  (many UTE : (erased (Nat) h) -> (UT h (UEmpty) (CEmpty)))
  (many UTB : (erased (Ctree) l1 l2 l3) (erased (CtH (Zero) l1) k1) (erased (CtH (Zero) l2) k2) (erased (CtH (Zero) l3) k3)
      -> (UT (Zero) (UBot l1 l2 l3) (CNode l1 l2 l3)))
  (many UTN : (erased (Nat) h) (erased (UTree) u1 u2 u3) (erased (Ctree) t1 t2 t3) (erased (UT h u1 t1) p1) (erased (UT h u2 t2) p2)
      (erased (UT h u3 t3) p3) -> (UT (Succ h) (UNode u1 u2 u3) (CNode t1 t2 t3))))

(def-adts $ (KeepE : ((Ctree) t) -> Type)
  enum
  (many KEmpty : -> (KeepE (CEmpty)))
  (many KLive : (erased (Ctree) t) -> (KeepE t)))

(def-adts $ (CtConsK : ((Ctree) t1) ((Ctree) t2) ((Ctree) t3) -> Type)
  enum
  (many CKE : -> (CtConsK (CEmpty) (CEmpty) (CEmpty)))
  (many CKN : (erased (Ctree) t1 t2 t3) -> (CtConsK t1 t2 t3)))

(def-fns _ $ (many ct-cons-k : (many (Ctree) t1 t2 t3) -> (many (CtConsK t1 t2 t3) k))
  (let-match many t1 (CEmpty) (else (CKN t1 t2 t3)))
  (let-match many t2 (CEmpty) (else (CKN t1 t2 t3)))
  (let-match many t3 (CEmpty) (else (CKN t1 t2 t3)))
  (CKE))

(def-fns _ $ (many keep3 : (erased (Ctree) a b c) (many (KeepE a) x) (many (KeepE b) y) (many (KeepE c) z) -> (many (CtConsK a b c) k))
  (let-match many x (KEmpty) (else (CKN a b c)))
  (let-match many y (KEmpty) (else (CKN a b c)))
  (let-match many z (KEmpty) (else (CKN a b c)))
  (CKE))

(def-fns _ $ (erased ut-h : (erased (Nat) h) (erased (UTree) u) (erased (Ctree) t) (subterm erased (UT h u t) p) -> (erased (CtH (Succ h) t) k))
  (match erased p _
    ((UTE _) (HE (Succ h)))
    ((UTB l1 l2 l3 k1 k2 k3) (HN (Zero) l1 l2 l3 k1 k2 k3))
    ((UTN h1 u1 u2 u3 t1 t2 t3 p1 p2 p3) (HN h t1 t2 t3 (ut-h h1 u1 t1 p1) (ut-h h1 u2 t2 p2) (ut-h h1 u3 t3 p3)))))

(def-fns _ $ (many ut-of : (subterm many (Nat) h) (many (Ctree) t) (erased (CtH (Succ h) t) k) ->
    (unique (UTree) u) (erased (UT h u t) p) (many (KeepE t) e))
  (let-match many t (CNode t1 t2 t3) ((CEmpty) (values (UEmpty) (UTE h) (KEmpty))) (absurd (CLeaf lf) k))
  (let-match erased k (HN _ _ _ _ k1 k2 k3))
  (let-match many h (Succ h1) ((Zero) (values (UBot t1 t2 t3) (UTB t1 t2 t3 k1 k2 k3) (KLive t))))
  (let ((unique u1) (erased p1) (many _)) (notail $ ut-of h1 t1 k1))
  (let ((unique u2) (erased p2) (many _)) (notail $ ut-of h1 t2 k2))
  (let ((unique u3) (erased p3) (many _)) (notail $ ut-of h1 t3 k3))
  (values (UNode u1 u2 u3) (UTN h1 u1 u2 u3 t1 t2 t3 p1 p2 p3) (KLive t)))

(def-fns _ $ (many ct-of : (erased (Nat) h) (subterm unique (UTree) u) (erased (Ctree) t) (erased (UT h u t) p) -> (many t is c))
  (match unique u _
    ((UEmpty) (let-match erased p (UTE _)) (CEmpty))
    ((UBot l1 l2 l3) (let-match erased p (UTB _ _ _ _ _ _)) (CNode l1 l2 l3))
    ((UNode u1 u2 u3)
      (let-match erased p (UTN h1 _ _ _ t1 t2 t3 p1 p2 p3))
      (let ((many c1)) (notail $ ct-of h1 u1 t1 p1))
      (let ((many c2)) (notail $ ct-of h1 u2 t2 p2))
      (let ((many c3)) (notail $ ct-of h1 u3 t3 p3))
      (CNode c1 c2 c3))))

(def-fns _ $ (many ctree-restrict-u : (subterm many (Nat) h) (unique (UTree) u) (erased (Ctree) t) (erased (UT h u t) ut) (erased (List RG) r)
    (many (RxL (Gtree) r) rl) ->
    (unique (UTree) ku) (many (Ctree) gone) (erased (Ctree) keep) (erased (UT h ku keep) uk) (erased (CRes h t r keep gone) c)
    (erased (CtH (Succ h) gone) hg) (many (KeepE keep) e))
  (match unique u _
    ((UEmpty) (let-match erased ut (UTE _)) (values (UEmpty) (CEmpty) (CEmpty) (UTE h) (CRE h r) (HE (Succ h)) (KEmpty)))
    ((UBot l1 l2 l3 cell)
      (let-match erased ut (UTB _ _ _ k1 k2 k3))
      (let-match many rl (RxCons _ _ _ _ _) ((RxNil _) (values (at unique (cell l1 l2 l3)) (CEmpty) t ut (CRNil h t) (HE (Succ h)) (KLive t))))
      (let ((erased n1) (erased p1)) (root-exists l1))
      (let ((erased n2) (erased p2)) (root-exists l2))
      (let ((erased n3) (erased p3)) (root-exists l3))
      (let ((many m1) (many m2) (many m3) (erased d1) (erased d2) (erased d3)) (ctr-decr-c l1 l2 l3 r rl n1 n2 n3 p1 p2 p3 k1 k2 k3))
      (let-match erased d1 (MkDecrAll _ _ _ _ _ _ _ hl1 _ _))
      (let-match erased d2 (MkDecrAll _ _ _ _ _ _ _ hl2 _ _))
      (let-match erased d3 (MkDecrAll _ _ _ _ _ _ _ hl3 _ _))
      (let ((unique (UTree) ku) (erased (Ctree) keep) (erased (UT h ku keep) uk) (erased (CtCons m1 m2 m3 keep) ck) (many (KeepE keep) e))
        (match many (ct-cons-k m1 m2 m3) _
          ((CKE) (values (UEmpty) (CEmpty) (UTE h) (CCEmpty) (KEmpty)))
          ((CKN _ _ _) (values (cell m1 m2 m3) (CNode m1 m2 m3) (UTB m1 m2 m3 hl1 hl2 hl3) (CCNode m1 m2 m3) (KLive (CNode m1 m2 m3))))))
      (let ((many g1) (erased f1)) (if-e-c l1 m1))
      (let ((many g2) (erased f2)) (if-e-c l2 m2))
      (let ((many g3) (erased f3)) (if-e-c l3 m3))
      (let ((many gone) (erased cg)) (ctree-cons g1 g2 g3))
      (values ku gone keep uk (CRZ l1 l2 l3 m1 m2 m3 g1 g2 g3 keep gone r n1 n2 n3 p1 p2 p3 d1 d2 d3 ck f1 f2 f3 cg)
        (cons-h (Zero) g1 g2 g3 gone cg (ife-h l1 m1 g1 f1 k1) (ife-h l2 m2 g2 f2 k2) (ife-h l3 m3 g3 f3 k3)) e))
    ((UNode u1 u2 u3 cell)
      (let-match erased ut (UTN h0 _ _ _ t1 t2 t3 q1 q2 q3))
      (let-match many h (Succ h1))
      (let-match many rl (RxCons _ _ _ _ _) ((RxNil _) (values (at unique (cell u1 u2 u3)) (CEmpty) t ut (CRNil h t) (HE (Succ h)) (KLive t))))
      (let ((erased r1) (erased r2) (erased r3) (many l1) (many l2) (many l3) (erased s1) (erased s2) (erased s3))
        (ctr-split-c (Nil _) (Nil _) (Nil _) (RxNil _) (RxNil _) (RxNil _) r rl))
      (let ((unique k1) (many b1) (erased a1) (erased w1) (erased c1) (erased kb1) (many e1)) (notail $ ctree-restrict-u h1 u1 t1 q1 r1 l1))
      (let ((unique k2) (many b2) (erased a2) (erased w2) (erased c2) (erased kb2) (many e2)) (notail $ ctree-restrict-u h1 u2 t2 q2 r2 l2))
      (let ((unique k3) (many b3) (erased a3) (erased w3) (erased c3) (erased kb3) (many e3)) (notail $ ctree-restrict-u h1 u3 t3 q3 r3 l3))
      (let ((unique (UTree) ku) (erased (Ctree) keep) (erased (UT h ku keep) uk) (erased (CtCons a1 a2 a3 keep) ck) (many (KeepE keep) e))
        (match many (keep3 a1 a2 a3 e1 e2 e3) _
          ((CKE) (values (UEmpty) (CEmpty) (UTE h) (CCEmpty) (KEmpty)))
          ((CKN _ _ _) (values (cell k1 k2 k3) (CNode a1 a2 a3) (UTN h1 k1 k2 k3 a1 a2 a3 w1 w2 w3) (CCNode a1 a2 a3) (KLive (CNode a1 a2 a3))))))
      (let ((many gone) (erased cg)) (ctree-cons b1 b2 b3))
      (values ku gone keep uk (CRS h1 t1 t2 t3 a1 a2 a3 b1 b2 b3 keep gone r r1 r2 r3 s1 s2 s3 c1 c2 c3 ck cg)
        (cons-h h b1 b2 b3 gone cg kb1 kb2 kb3) e))))

(def-fns _ $ (erased keep-sel : (erased (Ctree) a1 a2 a3 keep u) (erased (Col) e) (erased (List (Col)) et) (erased (Nat) m)
    (erased (CtCons a1 a2 a3 keep) ck) (erased (CtSel (CNode a1 a2 a3) e u) sl) (erased (CtSub u et m) s) -> (erased (CtSub keep (Cons (Col) e et) m) r))
  (SubCons keep u e et m (cons-sel-back a1 a2 a3 keep u e ck sl) s))

(def-fns _ $ (erased split-cnt0 : (erased (Col) e e2) (erased (List RG) r r1) (erased (List (Col)) et) (erased (Nat) k)
    (erased (CSplitE e (Nil RG) r r1) sp) (erased (RCnt r (Cons (Col) e (Cons (Col) e2 et)) k) rk) -> (erased (RCnt r1 (Cons (Col) e2 et) k) res))
  (let ((erased k1) (erased rc1)) (rcnt-exists r1 (Cons _ e2 et)))
  (let ((erased a)) (csplit-cnt e e2 (Nil RG) r r1 et (Zero) k k1 sp (RCNil _) rc1 rk))
  (let-match erased (add-fn k (Zero) k1 k a (add-zero-right k)) (Refl _ _))
  rc1)

(def-adts $ (KeepSub : ((Ctree) keep) ((List (Col)) et) ((Nat) n) ((Nat) k) -> Type)
  enum
  (many MkKeepSub : (erased (Ctree) keep) (erased (List (Col)) et) (erased (Nat) n k m) (erased (Monus n k m) o) (erased (CtSub keep et m) s)
      -> (KeepSub keep et n k)))

(def-fns _ $ (erased keep-lift : (erased (Ctree) a1 a2 a3 keep u) (erased (Col) e) (erased (List (Col)) et) (erased (Nat) n k)
    (erased (CtCons a1 a2 a3 keep) ck) (erased (CtSel (CNode a1 a2 a3) e u) sl) (erased (KeepSub u et n k) ks) ->
    (erased (KeepSub keep (Cons (Col) e et) n k) r))
  (let-match erased ks (MkKeepSub _ _ _ _ m o s))
  (MkKeepSub keep (Cons _ e et) n k m o (keep-sel a1 a2 a3 keep u e et m ck sl s)))

(def-fns _ $ (erased cres-sub : (erased (Nat) h) (erased (Ctree) t keep gone) (erased (List RG) r) (erased (List (Col)) et) (erased (Nat) n k)
    (subterm erased (CRes h t r keep gone) c) (erased (CtH (Succ h) t) ht) (erased (Length (Col) et (Succ h)) len) (erased (CtSub t et n) s)
    (erased (RCnt r et k) rk) -> (erased (KeepSub keep et n k) res))
  (match erased c _
    ((CRNil _ _) (let-match erased rk (RCNil _)) (MkKeepSub keep et n k n (MoZ n) s))
    ((CRE _ _) (let-match erased (sub-fn t et n (Zero) s (empty-sub et)) (Refl _ _)) (MkKeepSub keep et n k (Zero) (monus-zero k) (empty-sub et)))
    ((CRS h1 t1 t2 t3 a1 a2 a3 b1 b2 b3 _ _ _ r1 r2 r3 s1 s2 s3 c1 c2 c3 ck cg)
      (let-match erased ht (HN _ _ _ _ q1 q2 q3))
      (let-match erased len (LengthCons _ e et1 _ len1))
      (let-match erased len1 (LengthCons _ e2 et2 _ _))
      (let-match erased s (SubCons _ u _ _ _ sl s4))
      (match erased sl _
        ((SelN0 _ _ _)
          (let-match erased (sub-fn u et1 n (Zero) s4 (empty-sub et1)) (Refl _ _))
          (MkKeepSub keep et n k (Zero) (monus-zero k) (keep-sel a1 a2 a3 keep (CEmpty) e et1 (Zero) ck (SelN0 a1 a2 a3) (empty-sub et1))))
        ((SelN1 _ _ _)
          (keep-lift a1 a2 a3 keep a1 e et1 n k ck (SelN1 a1 a2 a3)
            (cres-sub h1 t1 a1 b1 r1 et1 n k c1 q1 len1 s4 (split-cnt0 e e2 r r1 et2 k s1 rk))))
        ((SelN2 _ _ _)
          (keep-lift a1 a2 a3 keep a2 e et1 n k ck (SelN2 a1 a2 a3)
            (cres-sub h1 t2 a2 b2 r2 et1 n k c2 q2 len1 s4 (split-cnt0 e e2 r r2 et2 k s2 rk))))
        ((SelN3 _ _ _)
          (keep-lift a1 a2 a3 keep a3 e et1 n k ck (SelN3 a1 a2 a3)
            (cres-sub h1 t3 a3 b3 r3 et1 n k c3 q3 len1 s4 (split-cnt0 e e2 r r3 et2 k s3 rk))))))
    ((CRZ t1 t2 t3 l1 l2 l3 g1 g2 g3 _ _ _ n1 n2 n3 p1 p2 p3 d1 d2 d3 ck _ _ _ _)
      (let-match erased len (LengthCons _ e et1 _ len1))
      (let-match erased len1 (LengthNil _))
      (let-match erased s (SubCons _ u _ _ _ sl s4))
      (let-match erased s4 (SubNil _ _ ru))
      (match erased sl _
        ((SelN0 _ _ _)
          (let-match erased ru (RootE))
          (MkKeepSub keep et n k (Zero) (monus-zero k) (keep-sel l1 l2 l3 keep (CEmpty) e et1 (Zero) ck (SelN0 l1 l2 l3) (empty-sub et1))))
        ((SelN1 _ _ _)
          (let-match erased (root-fn t1 n n1 ru p1) (Refl _ _))
          (let-match erased d1 (MkDecrAll _ _ _ cv k1 _ q _ m o))
          (let-match erased (rcnt-fn r et k k1 rk m) (Refl _ _))
          (MkKeepSub keep et n k cv o (keep-sel l1 l2 l3 keep l1 e et1 cv ck (SelN1 l1 l2 l3) (SubNil l1 cv q))))
        ((SelN2 _ _ _)
          (let-match erased (root-fn t2 n n2 ru p2) (Refl _ _))
          (let-match erased d2 (MkDecrAll _ _ _ cv k1 _ q _ m o))
          (let-match erased (rcnt-fn r et k k1 rk m) (Refl _ _))
          (MkKeepSub keep et n k cv o (keep-sel l1 l2 l3 keep l2 e et1 cv ck (SelN2 l1 l2 l3) (SubNil l2 cv q))))
        ((SelN3 _ _ _)
          (let-match erased (root-fn t3 n n3 ru p3) (Refl _ _))
          (let-match erased d3 (MkDecrAll _ _ _ cv k1 _ q _ m o))
          (let-match erased (rcnt-fn r et k k1 rk m) (Refl _ _))
          (MkKeepSub keep et n k cv o (keep-sel l1 l2 l3 keep l3 e et1 cv ck (SelN3 l1 l2 l3) (SubNil l3 cv q))))))))

(def-adts $ (Gone : ((Ctree) t) ((Ctree) keep) ((List (Col)) et) -> Type)
  enum
  (many MkGone : (erased (Ctree) t keep) (erased (List (Col)) et) (erased (CtMem t et) m) (erased (CtSub keep et (Zero)) s) -> (Gone t keep et)))

(def-fns _ $ (erased gone-lift : (erased (Ctree) t1 t2 t3 a1 a2 a3 keep u v) (erased (Col) e) (erased (List (Col)) et)
    (erased (CtCons a1 a2 a3 keep) ck) (erased (CtSel (CNode t1 t2 t3) e u) st) (erased (CtSel (CNode a1 a2 a3) e v) sa)
    (erased (Gone u v et) g) -> (erased (Gone (CNode t1 t2 t3) keep (Cons (Col) e et)) r))
  (let-match erased g (MkGone _ _ _ m s))
  (MkGone (CNode t1 t2 t3) keep (Cons _ e et) (mem-cons (CNode t1 t2 t3) u e et st m) (keep-sel a1 a2 a3 keep v e et (Zero) ck sa s)))

(def-fns _ $ (erased gone-leaf : (erased (Ctree) t1 t2 t3 tu l1 l2 l3 keep lu gu) (erased (Col) e) (erased (CtCons l1 l2 l3 keep) ck)
    (erased (CtSel (CNode t1 t2 t3) e tu) st) (erased (CtSel (CNode l1 l2 l3) e lu) sl) (erased (IfE tu lu gu) i)
    (erased (CtMem gu (Nil (Col))) m) -> (erased (Gone (CNode t1 t2 t3) keep (Cons (Col) e (Nil (Col)))) r))
  (match erased i _
    ((IEY _) (MkGone (CNode t1 t2 t3) keep (Cons _ e (Nil _)) (mem-cons (CNode t1 t2 t3) tu e (Nil _) st m)
      (keep-sel l1 l2 l3 keep lu e (Nil _) (Zero) ck sl (empty-sub (Nil _)))))
    (absurd (IEN _ _) (mem-empty (Nil _) m))))

(def-fns _ $ (erased cres-gone : (erased (Nat) h) (erased (Ctree) t keep gone) (erased (List RG) r) (erased (List (Col)) et)
    (subterm erased (CRes h t r keep gone) c) (erased (Length (Col) et (Succ h)) len) (erased (CtMem gone et) mg) -> (erased (Gone t keep et) res))
  (match erased c _
    (absurd (CRNil _ _) (mem-empty et mg))
    (absurd (CRE _ _) (mem-empty et mg))
    ((CRS h1 t1 t2 t3 a1 a2 a3 b1 b2 b3 _ _ _ r1 r2 r3 s1 s2 s3 c1 c2 c3 ck cg)
      (let ((erased e) (erased et1) (erased q) (erased u) (erased sl) (erased m1)) (cons-mem b1 b2 b3 gone et cg mg))
      (let-match erased q (Refl _ _))
      (let-match erased len (LengthCons _ _ _ _ len1))
      (match erased sl _
        (absurd (SelN0 _ _ _) (mem-empty et1 m1))
        ((SelN1 _ _ _) (gone-lift t1 t2 t3 a1 a2 a3 keep t1 a1 e et1 ck (SelN1 t1 t2 t3) (SelN1 a1 a2 a3) (cres-gone h1 t1 a1 b1 r1 et1 c1 len1 m1)))
        ((SelN2 _ _ _) (gone-lift t1 t2 t3 a1 a2 a3 keep t2 a2 e et1 ck (SelN2 t1 t2 t3) (SelN2 a1 a2 a3) (cres-gone h1 t2 a2 b2 r2 et1 c2 len1 m1)))
        ((SelN3 _ _ _) (gone-lift t1 t2 t3 a1 a2 a3 keep t3 a3 e et1 ck (SelN3 t1 t2 t3) (SelN3 a1 a2 a3) (cres-gone h1 t3 a3 b3 r3 et1 c3 len1 m1)))))
    ((CRZ t1 t2 t3 l1 l2 l3 g1 g2 g3 _ _ _ n1 n2 n3 p1 p2 p3 d1 d2 d3 ck f1 f2 f3 cg)
      (let ((erased e) (erased et1) (erased q) (erased u) (erased sl) (erased m1)) (cons-mem g1 g2 g3 gone et cg mg))
      (let-match erased q (Refl _ _))
      (let-match erased len (LengthCons _ _ _ _ len1))
      (let-match erased len1 (LengthNil _))
      (match erased sl _
        (absurd (SelN0 _ _ _) (mem-empty et1 m1))
        ((SelN1 _ _ _) (gone-leaf t1 t2 t3 t1 l1 l2 l3 keep l1 g1 e ck (SelN1 t1 t2 t3) (SelN1 l1 l2 l3) f1 m1))
        ((SelN2 _ _ _) (gone-leaf t1 t2 t3 t2 l1 l2 l3 keep l2 g2 e ck (SelN2 t1 t2 t3) (SelN2 l1 l2 l3) f2 m1))
        ((SelN3 _ _ _) (gone-leaf t1 t2 t3 t3 l1 l2 l3 keep l3 g3 e ck (SelN3 t1 t2 t3) (SelN3 l1 l2 l3) f3 m1))))))
