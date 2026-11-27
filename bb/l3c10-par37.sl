(def-adts
  ((DigEv : ((Nat) k b n) ((List (Nat)) zs ys) -> Type)
    enum
    (many DgZ : (erased (Nat) b n) (erased (List (Nat)) zs) -> (DigEv (Zero) b n zs zs))
    (many DgS : (erased (Nat) k b n q m r) (erased (List (Nat)) zs ys) (erased (Mul q b m) mm) (erased (Add m r n) ad) (erased (Lt r b) lt)
       (erased (DigEv k b q zs ys) p) -> (DigEv (Succ k) b n zs (Cons (Nat) r ys)))))

(def-fns _ $ (erased dig-fn : (erased (Nat) k b n) (erased (List (Nat)) zs ys ys2) (subterm erased (DigEv k b n zs ys) p) (erased (DigEv k b n zs ys2) p2)
    -> (erased (Eq (List (Nat)) ys ys2) e))
  (match erased p _
    ((DgZ _ _ _) (let-match erased p2 (DgZ _ _ _)) (Refl _ ys))
    ((DgS kp _ _ q m r _ y1 mm ad lt p1)
      (let-match erased p2 (DgS _ _ _ q2 m2 r2 _ y2 mm2 ad2 lt2 p21))
      (let ((erased e1) (erased e2)) (dm-uniq b n q m r q2 m2 r2 mm ad lt mm2 ad2 lt2))
      (let-match erased e1 (Refl _ _))
      (let-match erased e2 (Refl _ _))
      (let-match erased (dig-fn kp b q zs y1 y2 p1 p21) (Refl _ _))
      (Refl _ ys))))

(def-fns _ $ (many dig-loop : (subterm many (Nat) k) (many (Nat) b n) (erased (Lt (Zero) b) pos) (many (List (Nat)) zs)
    -> (many (List (Nat)) ys) (erased (DigEv k b n zs ys) p))
  (let-match many k (Succ kp) ((Zero) (values zs (DgZ b n zs))))
  (let ((many q) (many r) (erased m) (erased mm) (erased ad) (erased lt)) (divmod n b pos))
  (let ((many ys1) (erased p1)) (notail $ dig-loop kp b q pos zs))
  (values (Cons _ r ys1) (DgS kp b n q m r zs ys1 mm ad lt p1)))

(def-adts
  ((PGen : -> Type)
    enum
    (many PNil : -> (PGen))
    (many PDig : (many (Nat) k b n) (many (PGen) g) -> (PGen))
    (many PG : (many (NGen) h) (many (PGen) g) -> (PGen))))

(def-adts
  ((PEv : ((PGen) g) ((List (Nat)) ys) -> Type)
    enum
    (many PeNil : -> (PEv (PNil) (Nil (Nat))))
    (many PeDig : (erased (Nat) k b n) (erased (PGen) g) (erased (List (Nat)) zs ys) (erased (PEv g zs) p) (erased (DigEv k b n zs ys) d) -> (PEv (PDig k b n g) ys))
    (many PeG : (erased (NGen) h) (erased (PGen) g) (erased (List (Nat)) zs ys) (erased (PEv g zs) p) (erased (GEv h zs ys) d) -> (PEv (PG h g) ys))))

(def-fns _ $ (erased pev-fn : (erased (PGen) g) (erased (List (Nat)) ys ys2) (subterm erased (PEv g ys) p) (erased (PEv g ys2) p2) -> (erased (Eq (List (Nat)) ys ys2) e))
  (match erased p _
    ((PeNil) (let-match erased p2 (PeNil)) (Refl _ ys))
    ((PeDig k b n g1 zs _ p1 d)
      (let-match erased p2 (PeDig _ _ _ _ zs2 _ q1 d2))
      (let-match erased (pev-fn g1 zs zs2 p1 q1) (Refl _ _))
      (dig-fn k b n zs ys ys2 d d2))
    ((PeG h g1 zs _ p1 d)
      (let-match erased p2 (PeG _ _ zs2 _ q1 d2))
      (let-match erased (pev-fn g1 zs zs2 p1 q1) (Refl _ _))
      (gev-fn h zs ys ys2 d d2))))

(def-adts
  ((PvR : ((PGen) g) -> Type)
    enum
    (many PvOk : (erased (PGen) g) (many (List (Nat)) ys) (erased (PEv g ys) p) -> (PvR g))
    (many PvNo : (erased (PGen) g) -> (PvR g))))

(def-fns _ $ (many pev : (subterm many (PGen) g) -> (many (PvR g) r))
  (match many g _
    ((PNil) (PvOk g (Nil _) (PeNil)))
    ((PDig k b n g1)
      (let-match many (notail $ pev g1) (PvOk _ zs p) ((PvNo _) (PvNo g)))
      (let-match many b (Succ bp) ((Zero) (PvNo g)))
      (let ((many ys) (erased d)) (dig-loop k b n (LtZ bp) zs))
      (PvOk g ys (PeDig k b n g1 zs ys p d)))
    ((PG h g1)
      (let-match many (notail $ pev g1) (PvOk _ zs p) ((PvNo _) (PvNo g)))
      (let-match many (gev h 0 zs) (GOk _ _ ys d) ((GNo _ _) (PvNo g)))
      (PvOk g ys (PeG h g1 zs ys p d)))))

(def-adts $ (PQ : -> Type)
  enum
  (many MkPQ : (many (Nat) q) (many (Bool) h bl) (many (PGen) gl) (many (Bool) br) (many (PGen) gr) -> (PQ)))

(def-adts
  ((GenP : ((PQ) g) ((Rq) e) -> Type)
    enum
    (many MkGenP : (erased (Nat) q) (erased (Bool) h bl) (erased (PGen) gl) (erased (Bool) br) (erased (PGen) gr) (erased (List (Nat)) xs ys)
       (erased (List (Rn)) L R) (erased (PEv gl xs) pl) (erased (PEv gr ys) pr) (erased (AltEv bl xs L) al) (erased (AltEv br ys R) ar)
       -> (GenP (MkPQ q h bl gl br gr) (MkRq q L h R)))))

(def-fns _ $ (erased genp-fn : (erased (PQ) g) (erased (Rq) e e2) (erased (GenP g e) p) (erased (GenP g e2) p2) -> (erased (Eq (Rq) e e2) r))
  (let-match erased p (MkGenP q h bl gl br gr xs ys L R pl pr al ar))
  (let-match erased p2 (MkGenP _ _ _ _ _ _ xs2 ys2 L2 R2 pl2 pr2 al2 ar2))
  (let-match erased (pev-fn gl xs xs2 pl pl2) (Refl _ _))
  (let-match erased (pev-fn gr ys ys2 pr pr2) (Refl _ _))
  (let-match erased (alt-fn bl xs L L2 al al2) (Refl _ _))
  (let-match erased (alt-fn br ys R R2 ar ar2) (Refl _ _))
  (Refl _ e))

(def-adts
  ((GPR : ((PQ) g) -> Type)
    enum
    (many GPOk : (erased (PQ) g) (many (Rq) e) (erased (GenP g e) p) -> (GPR g))
    (many GPNo : (erased (PQ) g) -> (GPR g))))

(def-fns _ $ (many gen-p : (many (PQ) g) -> (many (GPR g) r))
  (let-match many g (MkPQ q h bl gl br gr))
  (let-match many (pev gl) (PvOk _ xs pl) ((PvNo _) (GPNo g)))
  (let-match many (pev gr) (PvOk _ ys pr) ((PvNo _) (GPNo g)))
  (let ((many L) (erased al)) (alt bl xs))
  (let ((many R) (erased ar)) (alt br ys))
  (GPOk g (MkRq q L h R) (MkGenP q h bl gl br gr xs ys L R pl pr al ar)))

(def-adts
  ((RchP : ((List (Tr)) m) ((Conf) c0) ((PQ) g) -> Type)
    enum
    (many MkRchP : (erased (List (Tr)) m) (erased (Conf) c0) (erased (PQ) g) (erased (Rq) e) (erased (GenP g e) p) (erased (Rch m c0 e) ch) -> (RchP m c0 g))))

(def-adts
  ((ReachP : ((List (Tr)) m) ((PQ) g g2) -> Type)
    enum
    (many MkReachP : (erased (List (Tr)) m) (erased (PQ) g g2) (erased (Rq) e e2) (erased (GenP g e) p) (erased (GenP g2 e2) p2) (erased (ReachQ m e e2) rr)
       -> (ReachP m g g2))))

(def-adts
  ((SpanP : ((List (Tr)) m) ((PQ) g) ((Nat) n) -> Type)
    enum
    (many MkSpanP : (erased (List (Tr)) m) (erased (PQ) g) (erased (Nat) n) (erased (Level) lv)
       (erased (Fn lv (erased (RchP m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) g) ch) -> (erased (Span m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) n) s)) f)
       -> (SpanP m g n))))

(def-fns _ $ (erased rchp-cat : (erased (List (Tr)) m) (erased (Conf) c0) (erased (PQ) g g2) (erased (RchP m c0 g) ch) (erased (ReachP m g g2) rg)
    -> (erased (RchP m c0 g2) ch2))
  (let-match erased ch (MkRchP _ _ _ e p c))
  (let-match erased rg (MkReachP _ _ _ e1 e2 p1 p2 rr))
  (let-match erased (genp-fn g e e1 p p1) (Refl _ _))
  (MkRchP m c0 g2 e2 p2 (rr-cat m c0 e e2 c rr)))

(def-fns _ $ (many run-from3 : (many (Nat) n) (many (Rq) e) -> (many (Rq) f) (erased (ReachQ l3 e f) rr))
  (let ((erased c) (erased dc)) (rq-conf e))
  (let ((many _) (many f) (erased ch)) (c10-run3 c n e (MkRch l3 c c c e (Zero) (RNil l3 c) dc (cez-refl c))))
  (values f (MkReachQ l3 e f c dc ch)))

(def-fns _ $ (many rp-run : (many (Nat) n) (many (PQ) g g2) -> (many (Res (ReachP l3 g g2)) r))
  (let-match many (gen-p g) (GPOk _ e p) ((GPNo _) (RFail _)))
  (let-match many (gen-p g2) (GPOk _ e2 p2) ((GPNo _) (RFail _)))
  (let ((many f) (erased rr)) (run-from3 n e))
  (let-match many (rq-eq f e2) (ESome _ eq) ((ENone _) (RFail _)))
  (let-match erased eq (Refl _ _))
  (ROk _ (MkReachP l3 g g2 e e2 p p2 rr)))

(def-fns _ $ (many rp-span : (many (Nat) n bnd) (many (PQ) g) -> (many (Res (SpanP l3 g bnd)) r))
  (let-match many (gen-p g) (GPOk _ e p) ((GPNo _) (RFail _)))
  (let ((many f) (erased rr)) (run-from3 n e))
  (let-match many (span-all l3 bnd f) (ROk _ sa) ((RFail _) (RFail _)))
  (let-match erased sa (MkSpanAll _ _ _ lv h))
  (def-fns _ $ (erased span-of : (erased (RchP l3 (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) g) ch) -> (erased (Span l3 (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) bnd) s))
    (let-match erased ch (MkRchP _ _ _ e1 p1 c))
    (let-match erased (genp-fn g e1 e p1 p) (Refl _ _))
    (h (rr-cat l3 _ e f c rr)))
  (ROk _ (MkSpanP l3 g bnd (level-of span-of) span-of)))

(def-fns _ $ (erased rchp0 : -> (erased (RchP l3 (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) (MkPQ (Zero) (BFalse) (BFalse) (PNil) (BFalse) (PNil))) ch))
  (MkRchP l3 _ _ _ (MkGenP (Zero) (BFalse) (BFalse) (PNil) (BFalse) (PNil) (Nil (Nat)) (Nil (Nat)) (Nil (Rn)) (Nil (Rn)) (PeNil) (PeNil) (AltN _) (AltN _)) (rch0 l3)))
