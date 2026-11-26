(def-adts
  ((ReachQ : ((List (Tr)) m) ((Rq) e e2) -> Type)
    enum
    (many MkReachQ : (erased (List (Tr)) m) (erased (Rq) e e2) (erased (Conf) c) (erased (Dc e c) dc) (erased (Rch m c e2) ch) -> (ReachQ m e e2))))

(def-fns _ $ (erased rq-conf : (erased (Rq) e) -> (erased (Conf) c) (erased (Dc e c) dc))
  (let-match erased e (MkRq q L h R))
  (let ((erased l) (erased dl)) (den-ex L))
  (let ((erased r) (erased dr)) (den-ex R))
  (values (MkConf q l h r) (MkDc q L R h l r dl dr)))

(def-fns _ $ (erased rr-cat : (erased (List (Tr)) m) (erased (Conf) c0) (erased (Rq) e e2) (erased (Rch m c0 e) ch) (erased (ReachQ m e e2) rr)
    -> (erased (Rch m c0 e2) ch2))
  (let-match erased rr (MkReachQ _ _ _ c dc ch1))
  (let-match erased ch1 (MkRch _ _ a2 c2 _ t r dc2 z2))
  (rch-z m c0 c c a2 c2 e e2 t ch dc (cez-refl c) r dc2 (cez-sym c2 a2 z2)))

(def-adts
  ((SpanAll : ((List (Tr)) m) ((Rq) e) ((Nat) n) -> Type)
    enum
    (many MkSpanAll : (erased (List (Tr)) m) (erased (Rq) e) (erased (Nat) n) (erased (Level) lv)
       (erased (Fn lv (erased (Rch m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) e) ch) -> (erased (Span m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) n) s)) f)
       -> (SpanAll m e n))))

(def-fns _ $ (many span-all : (erased (List (Tr)) m) (many (Nat) bnd) (many (Rq) e) -> (many (Res (SpanAll m e bnd)) res))
  (let-match many e (MkRq q L h R))
  (let ((erased l) (erased dl)) (den-ex L))
  (let ((erased r) (erased dr)) (den-ex R))
  (let ((many L2) (erased yl) (erased dl2) (erased e1) (many t1)) (rtrim L l dl))
  (let ((many R2) (erased yr) (erased dr2) (erased e2) (many t2)) (rtrim R r dr))
  (let ((many nl) (erased ll)) (rsum L2 yl dl2))
  (let ((many nr) (erased lr)) (rsum R2 yr dr2))
  (let ((many n) (erased an)) (add nl nr))
  (let-match many (lt-dec bnd (Succ n)) (Yes _ _ _ _ big) ((No _ _ _ _ _) (RFail _)))
  (def-fns _ $ (erased span-of : (erased (Rch m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) e) ch) -> (erased (Span m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) bnd) s))
    (let-match erased ch (MkRch _ c0 a c _ t r0 dc z))
    (let-match erased (dc-fn e (MkConf q l h r) c (MkDc q L R h l r dl dr) dc) (Refl _ _))
    (let-match erased z (MkCEz _ _ _ la ra _ el er))
    (let ((erased kl) (erased lla)) (len-ex (Bool) la))
    (let ((erased kr) (erased lra)) (len-ex (Bool) ra))
    (let ((erased S) (erased aS)) (add-ex kl kr))
    (let ((erased S2) (erased z2) (erased le2)) (run-csz m c0 a t r0 (MkCsz (Zero) (Nil (Bool)) (Nil (Bool)) (BFalse) (Zero) (Zero) (Zero) (LengthNil _) (LengthNil _) (AddZero (Zero)))))
    (let-match erased (csz-fn a S S2 (MkCsz q la ra h kl kr S lla lra aS) z2) (Refl _ _))
    (let ((erased gl)) (rtrim-len yl la nl kl (eqz-trans yl l la (eqz-sym l yl e1) el) t1 ll lla))
    (let ((erased gr)) (rtrim-len yr ra nr kr (eqz-trans yr r ra (eqz-sym r yr e2) er) t2 lr lra))
    (let ((erased M) (erased aM)) (add-ex kl nr))
    (let ((erased gn)) (le-tr n M S (add-mono nl kl nr n M an aM gl) (add-mono nr kr kl M S (add-comm kl nr M aM) (add-comm kl kr S aS) gr)))
    (MkSpan m c0 a bnd t r0 (le-tr bnd n t big (le-tr n S t gn le2))))
  (ROk _ (MkSpanAll m e bnd (level-of span-of) span-of)))

(def-fns _ $ (many run-from : (many (Nat) n) (many (Rq) e) -> (many (Rq) f) (erased (ReachQ l3 e f) rr))
  (let ((erased c) (erased dc)) (rq-conf e))
  (let ((many _) (many f) (erased ch)) (c10-run2 c n e (MkRch l3 c c c e (Zero) (RNil l3 c) dc (cez-refl c))))
  (values f (MkReachQ l3 e f c dc ch)))

(def-fns _ $ (many rr-run : (many (Nat) n) (many (Rq) e e2) -> (many (Res (ReachQ l3 e e2)) r))
  (let ((many f) (erased rr)) (run-from n e))
  (let-match many (rq-eq f e2) (ESome _ eq) ((ENone _) (RFail _)))
  (let-match erased eq (Refl _ _))
  (ROk _ rr))

(def-fns _ $ (many rr-span : (many (Nat) n bnd) (many (Rq) e) -> (many (Res (SpanAll l3 e bnd)) r))
  (let ((many f) (erased rr)) (run-from n e))
  (let-match many (span-all l3 bnd f) (ROk _ sa) ((RFail _) (RFail _)))
  (let-match erased sa (MkSpanAll _ _ _ lv g))
  (def-fns _ $ (erased span-of : (erased (Rch l3 (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) e) ch) -> (erased (Span l3 (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) bnd) s))
    (g (rr-cat l3 _ e f ch rr)))
  (ROk _ (MkSpanAll l3 e bnd (level-of span-of) span-of)))

(def-adts
  ((NGen : -> Type)
    enum
    (many GNil : -> (NGen))
    (many GCons : (many (Nat) x) (many (NGen) g) -> (NGen))
    (many GRep : (many (Nat) k) (many (NGen) b g) -> (NGen))
    (many GTrn : (many (Nat) k v a c s) (many (GBlk) bk) (many (NGen) g) -> (NGen)))
  ((GBlk : -> Type)
    enum
    (many MkGBlk : (many (NGen) before after) -> (GBlk))))

(def-adts
  ((GEv : ((NGen) g) ((List (Nat)) acc ys) -> Type)
    enum
    (many GeNil : (erased (List (Nat)) acc) -> (GEv (GNil) acc acc))
    (many GeCons : (erased (Nat) x) (erased (NGen) g) (erased (List (Nat)) acc ys) (erased (GEv g acc ys) p) -> (GEv (GCons x g) acc (Cons (Nat) x ys)))
    (many GeRep : (erased (Nat) k) (erased (NGen) b g) (erased (List (Nat)) acc zs ys) (erased (GEv g acc zs) p) (erased (RepEv k b zs ys) r)
       -> (GEv (GRep k b g) acc ys))
    (many GeTrn : (erased (Nat) k v a c s) (erased (GBlk) bk) (erased (NGen) g) (erased (List (Nat)) acc zs ys) (erased (GEv g acc zs) p)
       (erased (TrnEv k v a c s bk zs ys) t) -> (GEv (GTrn k v a c s bk g) acc ys)))
  ((RepEv : ((Nat) k) ((NGen) b) ((List (Nat)) zs ys) -> Type)
    enum
    (many ReZ : (erased (NGen) b) (erased (List (Nat)) zs) -> (RepEv (Zero) b zs zs))
    (many ReS : (erased (Nat) k) (erased (NGen) b) (erased (List (Nat)) zs ys1 ys) (erased (RepEv k b zs ys1) r) (erased (GEv b ys1 ys) p)
       -> (RepEv (Succ k) b zs ys)))
  ((TrnEv : ((Nat) k v a c s) ((GBlk) bk) ((List (Nat)) zs ys) -> Type)
    enum
    (many TeZ : (erased (Nat) v a c s) (erased (GBlk) bk) (erased (List (Nat)) zs) -> (TrnEv (Zero) v a c s bk zs zs))
    (many TeS : (erased (Nat) k v a c s av w v2) (erased (NGen) before after) (erased (List (Nat)) zs p1 p2 ys)
       (erased (GEv after zs p1) q1) (erased (GEv before (Cons (Nat) v p1) p2) q2) (erased (Mul a v av) m) (erased (Add av c w) ad) (erased (Add s v2 w) sb)
       (erased (TrnEv k v2 a c s (MkGBlk before after) p2 ys) t) -> (TrnEv (Succ k) v a c s (MkGBlk before after) zs ys))))

(def-fns _
  ((erased gev-fn : (erased (NGen) g) (erased (List (Nat)) acc ys ys2) (subterm erased (GEv g acc ys) p) (erased (GEv g acc ys2) q)
      -> (erased (Eq (List (Nat)) ys ys2) e))
    (match erased p _
      ((GeNil _) (let-match erased q (GeNil _)) (Refl _ ys))
      ((GeCons x g1 _ y1 p1) (let-match erased q (GeCons _ _ _ y2 q1)) (let-match erased (gev-fn g1 acc y1 y2 p1 q1) (Refl _ _)) (Refl _ ys))
      ((GeRep k b g1 _ zs _ p1 r1)
        (let-match erased q (GeRep _ _ _ _ zs2 _ q1 r2))
        (let-match erased (gev-fn g1 acc zs zs2 p1 q1) (Refl _ _))
        (repev-fn k b zs ys ys2 r1 r2))
      ((GeTrn k v a c s bk g1 _ zs _ p1 t1)
        (let-match erased q (GeTrn _ _ _ _ _ _ _ _ zs2 _ q1 t2))
        (let-match erased (gev-fn g1 acc zs zs2 p1 q1) (Refl _ _))
        (trnev-fn k v a c s bk zs ys ys2 t1 t2))))
  ((erased repev-fn : (erased (Nat) k) (erased (NGen) b) (erased (List (Nat)) zs ys ys2) (subterm erased (RepEv k b zs ys) r) (erased (RepEv k b zs ys2) q)
      -> (erased (Eq (List (Nat)) ys ys2) e))
    (match erased r _
      ((ReZ _ _) (let-match erased q (ReZ _ _)) (Refl _ ys))
      ((ReS k1 _ _ y1 _ r1 p1)
        (let-match erased q (ReS _ _ _ y2 _ q1 p2))
        (let-match erased (repev-fn k1 b zs y1 y2 r1 q1) (Refl _ _))
        (gev-fn b y1 ys ys2 p1 p2))))
  ((erased trnev-fn : (erased (Nat) k v a c s) (erased (GBlk) bk) (erased (List (Nat)) zs ys ys2) (subterm erased (TrnEv k v a c s bk zs ys) t) (erased (TrnEv k v a c s bk zs ys2) q)
      -> (erased (Eq (List (Nat)) ys ys2) e))
    (match erased t _
      ((TeZ _ _ _ _ _ _) (let-match erased q (TeZ _ _ _ _ _ _)) (Refl _ ys))
      ((TeS k1 _ _ _ _ av w v2 before after _ p1 p2 _ q1 q2 m ad sb t1)
        (let-match erased q (TeS _ _ _ _ _ av' w' v2' _ _ _ p1' p2' _ q1' q2' m' ad' sb' t2))
        (let-match erased (gev-fn after zs p1 p1' q1 q1') (Refl _ _))
        (let-match erased (gev-fn before (Cons (Nat) v p1) p2 p2' q2 q2') (Refl _ _))
        (let-match erased (mul-fn a v av av' m m') (Refl _ _))
        (let-match erased (add-fn av c w w' ad ad') (Refl _ _))
        (let-match erased (add-cancel s v2 v2' w sb sb') (Refl _ _))
        (trnev-fn k1 v2 a c s bk p2 ys ys2 t1 t2)))))

(def-adts
  ((GR : ((NGen) g) ((List (Nat)) acc) -> Type)
    enum
    (many GOk : (erased (NGen) g) (erased (List (Nat)) acc) (many (List (Nat)) ys) (erased (GEv g acc ys) p) -> (GR g acc))
    (many GNo : (erased (NGen) g) (erased (List (Nat)) acc) -> (GR g acc))))

(def-adts
  ((RR : ((Nat) k) ((NGen) b) ((List (Nat)) zs) -> Type)
    enum
    (many ROk2 : (erased (Nat) k) (erased (NGen) b) (erased (List (Nat)) zs) (many (List (Nat)) ys) (erased (RepEv k b zs ys) p) -> (RR k b zs))
    (many RNo2 : (erased (Nat) k) (erased (NGen) b) (erased (List (Nat)) zs) -> (RR k b zs))))

(def-adts
  ((TR : ((Nat) k v a c s) ((GBlk) bk) ((List (Nat)) zs) -> Type)
    enum
    (many TOk : (erased (Nat) k v a c s) (erased (GBlk) bk) (erased (List (Nat)) zs) (many (List (Nat)) ys) (erased (TrnEv k v a c s bk zs ys) p) -> (TR k v a c s bk zs))
    (many TNo : (erased (Nat) k v a c s) (erased (GBlk) bk) (erased (List (Nat)) zs) -> (TR k v a c s bk zs))))

(def-fns _
  ((many gev : (subterm many (NGen) g) (subterm many (Nat) n) (many (List (Nat)) acc) -> (many (GR g acc) r))
    (match many g _
      ((GNil) (GOk g acc acc (GeNil acc)))
      ((GCons x g1)
        (let-match many (gev g1 n acc) (GOk _ _ ys p) ((GNo _ _) (GNo g acc)))
        (GOk g acc (Cons _ x ys) (GeCons x g1 acc ys p)))
      ((GRep k b g1)
        (let-match many (gev g1 n acc) (GOk _ _ zs p) ((GNo _ _) (GNo g acc)))
        (let-match many (rep-loop b k zs) (ROk2 _ _ _ ys r) ((RNo2 _ _ _) (GNo g acc)))
        (GOk g acc ys (GeRep k b g1 acc zs ys p r)))
      ((GTrn k v a c s bk g1)
        (let-match many (gev g1 n acc) (GOk _ _ zs p) ((GNo _ _) (GNo g acc)))
        (let-match many (trn-loop bk k v a c s zs) (TOk _ _ _ _ _ _ _ ys t) ((TNo _ _ _ _ _ _ _) (GNo g acc)))
        (GOk g acc ys (GeTrn k v a c s bk g1 acc zs ys p t)))))
  ((many rep-loop : (subterm many (NGen) b) (subterm many (Nat) k) (many (List (Nat)) zs) -> (many (RR k b zs) r))
    (let-match many k (Succ k1) ((Zero) (ROk2 k b zs zs (ReZ b zs))))
    (let-match many (rep-loop b k1 zs) (ROk2 _ _ _ ys1 r) ((RNo2 _ _ _) (RNo2 k b zs)))
    (let-match many (gev b k1 ys1) (GOk _ _ ys p) ((GNo _ _) (RNo2 k b zs)))
    (ROk2 k b zs ys (ReS k1 b zs ys1 ys r p)))
  ((many trn-loop : (subterm many (GBlk) bk) (subterm many (Nat) k) (many (Nat) v a c s) (many (List (Nat)) zs) -> (many (TR k v a c s bk zs) r))
    (let-match many k (Succ k1) ((Zero) (TOk k v a c s bk zs zs (TeZ v a c s bk zs))))
    (let-match many bk (MkGBlk before after))
    (let-match many (gev after k zs) (GOk _ _ p1 q1) ((GNo _ _) (TNo k v a c s bk zs)))
    (let-match many (gev before k (Cons _ v p1)) (GOk _ _ p2 q2) ((GNo _ _) (TNo k v a c s bk zs)))
    (let ((many av) (erased m)) (mul a v))
    (let ((many w) (erased ad)) (add av c))
    (let ((many v2)) (monus w s))
    (let ((many w2) (erased sb)) (add s v2))
    (let-match many (nat-eq w2 w) (Equal _ _ _) ((Unequal _ _ _ _ _) (TNo k v a c s bk zs)))
    (let-match many (trn-loop bk k1 v2 a c s p2) (TOk _ _ _ _ _ _ _ ys t) ((TNo _ _ _ _ _ _ _) (TNo k v a c s bk zs)))
    (TOk k v a c s bk zs ys (TeS k1 v a c s av w v2 before after zs p1 p2 ys q1 q2 m ad sb t))))

(def-adts
  ((AltEv : ((Bool) b) ((List (Nat)) xs) ((List (Rn)) L) -> Type)
    enum
    (many AlN : (erased (Bool) b) -> (AltEv b (Nil (Nat)) (Nil (Rn))))
    (many AlT : (erased (Nat) n) (erased (List (Nat)) xs) (erased (List (Rn)) L) (erased (AltEv (BFalse) xs L) p)
       -> (AltEv (BTrue) (Cons (Nat) n xs) (Cons (Rn) (MkRn (BTrue) n) L)))
    (many AlF : (erased (Nat) n) (erased (List (Nat)) xs) (erased (List (Rn)) L) (erased (AltEv (BTrue) xs L) p)
       -> (AltEv (BFalse) (Cons (Nat) n xs) (Cons (Rn) (MkRn (BFalse) n) L)))))

(def-fns _ $ (many alt : (many (Bool) b) (subterm many (List (Nat)) xs) -> (many (List (Rn)) L) (erased (AltEv b xs L) p))
  (let-match many xs (Cons _ n xs1) ((Nil _) (values (Nil _) (AlN b))))
  (match many b _
    ((BTrue) (let ((many L) (erased p)) (alt (BFalse) xs1)) (values (Cons _ (MkRn b n) L) (AlT n xs1 L p)))
    ((BFalse) (let ((many L) (erased p)) (alt (BTrue) xs1)) (values (Cons _ (MkRn b n) L) (AlF n xs1 L p)))))

(def-fns _ $ (erased alt-fn : (erased (Bool) b) (erased (List (Nat)) xs) (erased (List (Rn)) L L2) (subterm erased (AltEv b xs L) p) (erased (AltEv b xs L2) q)
    -> (erased (Eq (List (Rn)) L L2) e))
  (match erased p _
    ((AlN _) (let-match erased q (AlN _)) (Refl _ L))
    ((AlT n xs1 L1 p1) (let-match erased q (AlT _ _ M1 q1)) (let-match erased (alt-fn (BFalse) xs1 L1 M1 p1 q1) (Refl _ _)) (Refl _ L))
    ((AlF n xs1 L1 p1) (let-match erased q (AlF _ _ M1 q1)) (let-match erased (alt-fn (BTrue) xs1 L1 M1 p1 q1) (Refl _ _)) (Refl _ L))))

(def-adts $ (QGen : -> Type)
  enum
  (many MkQGen : (many (Nat) q) (many (Bool) h bl) (many (NGen) gl) (many (Bool) br) (many (NGen) gr) -> (QGen)))

(def-adts
  ((GenQ : ((QGen) g) ((Rq) e) -> Type)
    enum
    (many MkGenQ : (erased (Nat) q) (erased (Bool) h bl) (erased (NGen) gl) (erased (Bool) br) (erased (NGen) gr) (erased (List (Nat)) xs ys)
       (erased (List (Rn)) L R) (erased (GEv gl (Nil (Nat)) xs) pl) (erased (GEv gr (Nil (Nat)) ys) pr) (erased (AltEv bl xs L) al) (erased (AltEv br ys R) ar)
       -> (GenQ (MkQGen q h bl gl br gr) (MkRq q L h R)))))

(def-fns _ $ (erased genq-fn : (erased (QGen) g) (erased (Rq) e e2) (erased (GenQ g e) p) (erased (GenQ g e2) p2) -> (erased (Eq (Rq) e e2) r))
  (let-match erased p (MkGenQ q h bl gl br gr xs ys L R pl pr al ar))
  (let-match erased p2 (MkGenQ _ _ _ _ _ _ xs2 ys2 L2 R2 pl2 pr2 al2 ar2))
  (let-match erased (gev-fn gl (Nil (Nat)) xs xs2 pl pl2) (Refl _ _))
  (let-match erased (gev-fn gr (Nil (Nat)) ys ys2 pr pr2) (Refl _ _))
  (let-match erased (alt-fn bl xs L L2 al al2) (Refl _ _))
  (let-match erased (alt-fn br ys R R2 ar ar2) (Refl _ _))
  (Refl _ e))

(def-adts
  ((GQR : ((QGen) g) -> Type)
    enum
    (many GQOk : (erased (QGen) g) (many (Rq) e) (erased (GenQ g e) p) -> (GQR g))
    (many GQNo : (erased (QGen) g) -> (GQR g))))

(def-fns _ $ (many gen-q : (many (QGen) g) -> (many (GQR g) r))
  (let-match many g (MkQGen q h bl gl br gr))
  (let-match many (gev gl 0 (Nil _)) (GOk _ _ xs pl) ((GNo _ _) (GQNo g)))
  (let-match many (gev gr 0 (Nil _)) (GOk _ _ ys pr) ((GNo _ _) (GQNo g)))
  (let ((many L) (erased al)) (alt bl xs))
  (let ((many R) (erased ar)) (alt br ys))
  (GQOk g (MkRq q L h R) (MkGenQ q h bl gl br gr xs ys L R pl pr al ar)))

(def-adts
  ((RchG : ((List (Tr)) m) ((Conf) c0) ((QGen) g) -> Type)
    enum
    (many MkRchG : (erased (List (Tr)) m) (erased (Conf) c0) (erased (QGen) g) (erased (Rq) e) (erased (GenQ g e) p) (erased (Rch m c0 e) ch) -> (RchG m c0 g))))

(def-adts
  ((ReachG : ((List (Tr)) m) ((QGen) g g2) -> Type)
    enum
    (many MkReachG : (erased (List (Tr)) m) (erased (QGen) g g2) (erased (Rq) e e2) (erased (GenQ g e) p) (erased (GenQ g2 e2) p2) (erased (ReachQ m e e2) rr)
       -> (ReachG m g g2))))

(def-adts
  ((SpanG : ((List (Tr)) m) ((QGen) g) ((Nat) n) -> Type)
    enum
    (many MkSpanG : (erased (List (Tr)) m) (erased (QGen) g) (erased (Nat) n) (erased (Level) lv)
       (erased (Fn lv (erased (RchG m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) g) ch) -> (erased (Span m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) n) s)) f)
       -> (SpanG m g n))))

(def-fns _ $ (erased rchg-cat : (erased (List (Tr)) m) (erased (Conf) c0) (erased (QGen) g g2) (erased (RchG m c0 g) ch) (erased (ReachG m g g2) rg)
    -> (erased (RchG m c0 g2) ch2))
  (let-match erased ch (MkRchG _ _ _ e p c))
  (let-match erased rg (MkReachG _ _ _ e1 e2 p1 p2 rr))
  (let-match erased (genq-fn g e e1 p p1) (Refl _ _))
  (MkRchG m c0 g2 e2 p2 (rr-cat m c0 e e2 c rr)))

(def-fns _ $ (many rg-run : (many (Nat) n) (many (QGen) g g2) -> (many (Res (ReachG l3 g g2)) r))
  (let-match many (gen-q g) (GQOk _ e p) ((GQNo _) (RFail _)))
  (let-match many (gen-q g2) (GQOk _ e2 p2) ((GQNo _) (RFail _)))
  (let ((many f) (erased rr)) (run-from n e))
  (let-match many (rq-eq f e2) (ESome _ eq) ((ENone _) (RFail _)))
  (let-match erased eq (Refl _ _))
  (ROk _ (MkReachG l3 g g2 e e2 p p2 rr)))

(def-fns _ $ (many rg-span : (many (Nat) n bnd) (many (QGen) g) -> (many (Res (SpanG l3 g bnd)) r))
  (let-match many (gen-q g) (GQOk _ e p) ((GQNo _) (RFail _)))
  (let-match many (rr-span n bnd e) (ROk _ sa) ((RFail _) (RFail _)))
  (let-match erased sa (MkSpanAll _ _ _ lv f))
  (def-fns _ $ (erased span-of : (erased (RchG l3 (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) g) ch) -> (erased (Span l3 (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) bnd) s))
    (let-match erased ch (MkRchG _ _ _ e1 p1 c))
    (let-match erased (genq-fn g e1 e p1 p) (Refl _ _))
    (f c))
  (ROk _ (MkSpanG l3 g bnd (level-of span-of) span-of)))

(def-fns _ $ (erased rchg0 : -> (erased (RchG l3 (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) (MkQGen (Zero) (BFalse) (BFalse) (GNil) (BFalse) (GNil))) ch))
  (MkRchG l3 _ _ _ (MkGenQ (Zero) (BFalse) (BFalse) (GNil) (BFalse) (GNil) (Nil (Nat)) (Nil (Nat)) (Nil (Rn)) (Nil (Rn)) (GeNil _) (GeNil _) (AlN _) (AlN _)) (rch0 l3)))
