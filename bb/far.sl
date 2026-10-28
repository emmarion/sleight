(def-adts
  ((Pick : ((Bool) c) ((Nat) a) ((Nat) b) ((Nat) x) -> Type)
    enum
    (many Pick0 : (erased (Nat) a b) -> (Pick (BFalse) a b a))
    (many Pick1 : (erased (Nat) a b) -> (Pick (BTrue) a b b))))

(def-adts
  ((DRun : ((List (Pair (Nat) (Nat))) dfa) ((List (Bool)) l) ((Nat) d) -> Type)
    enum
    (many DRNil : (erased (List (Pair (Nat) (Nat))) dfa) -> (DRun dfa (Nil (Bool)) (Zero)))
    (many DRCons : (erased (List (Pair (Nat) (Nat))) dfa) (erased (List (Bool)) l) (erased (Nat) d a b x) (erased (Bool) c)
       (erased (DRun dfa l d) r) (erased (Nth (Pair (Nat) (Nat)) dfa d (MkPair (Nat) (Nat) a b)) nd) (erased (Pick c a b x) pk)
       -> (DRun dfa (Cons (Bool) c l) x))))

(def-adts
  ((NIx : ((Nat) K) ((Nat) d) ((Nat) q) ((Nat) i) -> Type)
    enum
    (many MkNIx : (erased (Nat) K d q x i) (erased (Mul d K x) mu) (erased (Add x q i) ad) -> (NIx K d q i))))

(def-adts
  ((TRow : ((List (List (Nat))) t0) ((List (List (Nat))) t1) ((Bool) b) ((Nat) i) ((List (Nat)) row) -> Type)
    enum
    (many TR0 : (erased (List (List (Nat))) t0 t1) (erased (Nat) i) (erased (List (Nat)) row) (erased (Nth (List (Nat)) t0 i row) nr)
       -> (TRow t0 t1 (BFalse) i row))
    (many TR1 : (erased (List (List (Nat))) t0 t1) (erased (Nat) i) (erased (List (Nat)) row) (erased (Nth (List (Nat)) t1 i row) nr)
       -> (TRow t0 t1 (BTrue) i row))))

(def-adts
  ((FEdge : ((List (List (Nat))) t0) ((List (List (Nat))) t1) ((Bool) b) ((Nat) i) ((Nat) j) -> Type)
    enum
    (many MkFEdge : (erased (List (List (Nat))) t0 t1) (erased (Bool) b) (erased (Nat) i j) (erased (List (Nat)) row)
       (erased (TRow t0 t1 b i row) tr) (erased (Mem (Nat) j row) mj) -> (FEdge t0 t1 b i j))))

(def-adts
  ((NAcc : ((List (List (Nat))) t0) ((List (List (Nat))) t1) ((Nat) bot) ((Nat) j) ((List (Bool)) w) -> Type)
    enum
    (many NAEnd : (erased (List (List (Nat))) t0 t1) (erased (Nat) bot) -> (NAcc t0 t1 bot bot (Nil (Bool))))
    (many NAZero : (erased (List (List (Nat))) t0 t1) (erased (Nat) bot j k) (erased (FEdge t0 t1 (BFalse) j k) e)
       (erased (NAcc t0 t1 bot k (Nil (Bool))) a) -> (NAcc t0 t1 bot j (Nil (Bool))))
    (many NAStep : (erased (List (List (Nat))) t0 t1) (erased (Nat) bot j k) (erased (Bool) b) (erased (List (Bool)) w)
       (erased (FEdge t0 t1 b j k) e) (erased (NAcc t0 t1 bot k w) a) -> (NAcc t0 t1 bot j (Cons (Bool) b w)))))

(def-adts
  ((CAcc : ((Nat) K) ((List (Pair (Nat) (Nat))) dfa) ((List (List (Nat))) t0) ((List (List (Nat))) t1) ((Nat) bot) ((Conf) c) -> Type)
    enum
    (many MkCA : (erased (Nat) K) (erased (List (Pair (Nat) (Nat))) dfa) (erased (List (List (Nat))) t0 t1) (erased (Nat) bot q d i)
       (erased (List (Bool)) l r) (erased (Bool) h) (erased (DRun dfa l d) dr) (erased (NIx K d q i) ix)
       (erased (NAcc t0 t1 bot i (Cons (Bool) h r)) na) -> (CAcc K dfa t0 t1 bot (MkConf q l h r)))))

(def-adts
  ((AllY : ((List (List (Nat))) t0) ((List (List (Nat))) t1) ((Bool) b) ((Nat) i) ((List (Nat)) ys) -> Type)
    enum
    (many AYNil : (erased (List (List (Nat))) t0 t1) (erased (Bool) b) (erased (Nat) i) -> (AllY t0 t1 b i (Nil (Nat))))
    (many AYCons : (erased (List (List (Nat))) t0 t1) (erased (Bool) b) (erased (Nat) i y) (erased (List (Nat)) ys)
       (erased (FEdge t0 t1 b i y) e) (erased (AllY t0 t1 b i ys) rest) -> (AllY t0 t1 b i (Cons (Nat) y ys)))))

(def-adts
  ((AllX : ((List (List (Nat))) t0) ((List (List (Nat))) t1) ((Bool) b) ((Nat) i) ((Bool) w) ((List (Nat)) xs) -> Type)
    enum
    (many AXNil : (erased (List (List (Nat))) t0 t1) (erased (Bool) b) (erased (Nat) i) (erased (Bool) w) -> (AllX t0 t1 b i w (Nil (Nat))))
    (many AXCons : (erased (List (List (Nat))) t0 t1) (erased (Bool) b) (erased (Nat) i) (erased (Bool) w) (erased (Nat) x) (erased (List (Nat)) xs row)
       (erased (TRow t0 t1 w x row) tr) (erased (AllY t0 t1 b i row) ay) (erased (AllX t0 t1 b i w xs) rest)
       -> (AllX t0 t1 b i w (Cons (Nat) x xs)))))

(def-adts
  ((LC : ((Nat) K) ((List (List (Nat))) t0) ((List (List (Nat))) t1) ((Nat) q) ((Bool) b) ((Bool) w) ((Nat) q2) ((Bool) c)
      ((Nat) d) ((Nat) a0) ((Nat) a1) -> Type)
    enum
    (many MkLC : (erased (Nat) K) (erased (List (List (Nat))) t0 t1) (erased (Nat) q) (erased (Bool) b w) (erased (Nat) q2) (erased (Bool) c)
       (erased (Nat) d a0 a1 dc i i2) (erased (List (Nat)) row)
       (erased (Pick c a0 a1 dc) pk) (erased (NIx K d q2 i) ix) (erased (NIx K dc q i2) ix2) (erased (TRow t0 t1 c i row) tr)
       (erased (AllX t0 t1 b i2 w row) ax) -> (LC K t0 t1 q b w q2 c d a0 a1))))

(def-adts
  ((FCond : ((Nat) K) ((List (List (Nat))) t0) ((List (List (Nat))) t1) ((Nat) bot) ((Nat) q) ((Bool) b) ((PT) x)
      ((Nat) d) ((Nat) a0) ((Nat) a1) -> Type)
    enum
    (many FCU : (erased (Nat) K) (erased (List (List (Nat))) t0 t1) (erased (Nat) bot q) (erased (Bool) b) (erased (Nat) d a0 a1 i)
       (erased (NIx K d q i) ix) (erased (FEdge t0 t1 b i bot) e) -> (FCond K t0 t1 bot q b (Undef) d a0 a1))
    (many FCH : (erased (Nat) K) (erased (List (List (Nat))) t0 t1) (erased (Nat) bot q) (erased (Bool) b) (erased (Nat) d a0 a1 i)
       (erased (NIx K d q i) ix) (erased (FEdge t0 t1 b i bot) e) -> (FCond K t0 t1 bot q b (Def (Hlt)) d a0 a1))
    (many FCR : (erased (Nat) K) (erased (List (List (Nat))) t0 t1) (erased (Nat) bot q) (erased (Bool) b w) (erased (Nat) q2 d a0 a1 i dw i2)
       (erased (NIx K d q i) ix) (erased (Pick w a0 a1 dw) pk) (erased (NIx K dw q2 i2) ix2) (erased (FEdge t0 t1 b i i2) e)
       -> (FCond K t0 t1 bot q b (Def (Mov w (DR) q2)) d a0 a1))
    (many FCL : (erased (Nat) K) (erased (List (List (Nat))) t0 t1) (erased (Nat) bot q) (erased (Bool) b w) (erased (Nat) q2 d a0 a1)
       (erased (LC K t0 t1 q b w q2 (BFalse) d a0 a1) lc0) (erased (LC K t0 t1 q b w q2 (BTrue) d a0 a1) lc1)
       -> (FCond K t0 t1 bot q b (Def (Mov w (DL) q2)) d a0 a1))))

(def-adts
  ((FD : ((Nat) K) ((List (Pair (Nat) (Nat))) dfa) ((List (List (Nat))) t0) ((List (List (Nat))) t1) ((Nat) bot) ((Nat) q) ((Bool) b) ((PT) x)
      ((List (Nat)) ds) -> Type)
    enum
    (many FDNil : (erased (Nat) K) (erased (List (Pair (Nat) (Nat))) dfa) (erased (List (List (Nat))) t0 t1) (erased (Nat) bot q) (erased (Bool) b)
       (erased (PT) x) -> (FD K dfa t0 t1 bot q b x (Nil (Nat))))
    (many FDCons : (erased (Nat) K) (erased (List (Pair (Nat) (Nat))) dfa) (erased (List (List (Nat))) t0 t1) (erased (Nat) bot q) (erased (Bool) b)
       (erased (PT) x) (erased (Nat) d a0 a1) (erased (List (Nat)) ds) (erased (Nth (Pair (Nat) (Nat)) dfa d (MkPair (Nat) (Nat) a0 a1)) nd)
       (erased (FCond K t0 t1 bot q b x d a0 a1) fc) (erased (FD K dfa t0 t1 bot q b x ds) rest) -> (FD K dfa t0 t1 bot q b x (Cons (Nat) d ds)))))

(def-adts
  ((FP : ((Nat) K) ((List (Pair (Nat) (Nat))) dfa) ((List (List (Nat))) t0) ((List (List (Nat))) t1) ((Nat) bot) ((List (Nat)) ds)
      ((Nat) q) ((List (PT)) p) -> Type)
    enum
    (many FPNil : (erased (Nat) K) (erased (List (Pair (Nat) (Nat))) dfa) (erased (List (List (Nat))) t0 t1) (erased (Nat) bot) (erased (List (Nat)) ds)
       (erased (Nat) q) -> (FP K dfa t0 t1 bot ds q (Nil (PT))))
    (many FPCons : (erased (Nat) K) (erased (List (Pair (Nat) (Nat))) dfa) (erased (List (List (Nat))) t0 t1) (erased (Nat) bot) (erased (List (Nat)) ds)
       (erased (Nat) q) (erased (PT) x0 x1) (erased (List (PT)) rest)
       (erased (FD K dfa t0 t1 bot q (BFalse) x0 ds) f0) (erased (FD K dfa t0 t1 bot q (BTrue) x1 ds) f1) (erased (FP K dfa t0 t1 bot ds (Succ q) rest) fr)
       -> (FP K dfa t0 t1 bot ds q (Cons (PT) x0 (Cons (PT) x1 rest))))))

(def-adts
  ((DC : ((List (Pair (Nat) (Nat))) dfa) ((List (Nat)) ds) ((List (Nat)) es) -> Type)
    enum
    (many DCNil : (erased (List (Pair (Nat) (Nat))) dfa) (erased (List (Nat)) ds) -> (DC dfa ds (Nil (Nat))))
    (many DCCons : (erased (List (Pair (Nat) (Nat))) dfa) (erased (List (Nat)) ds es) (erased (Nat) d a0 a1)
       (erased (Nth (Pair (Nat) (Nat)) dfa d (MkPair (Nat) (Nat) a0 a1)) nd) (erased (Mem (Nat) a0 ds) m0) (erased (Mem (Nat) a1 ds) m1)
       (erased (DC dfa ds es) rest) -> (DC dfa ds (Cons (Nat) d es)))))

(def-adts
  ((Sub : ((List (Nat)) xs) ((List (Nat)) R) -> Type)
    enum
    (many SubNil : (erased (List (Nat)) R) -> (Sub (Nil (Nat)) R))
    (many SubCons : (erased (Nat) x) (erased (List (Nat)) xs R) (erased (Mem (Nat) x R) mx) (erased (Sub xs R) rest) -> (Sub (Cons (Nat) x xs) R))))

(def-adts
  ((RC : ((List (List (Nat))) t0) ((List (List (Nat))) t1) ((List (Nat)) R) ((List (Nat)) es) -> Type)
    enum
    (many RCNil : (erased (List (List (Nat))) t0 t1) (erased (List (Nat)) R) -> (RC t0 t1 R (Nil (Nat))))
    (many RCCons : (erased (List (List (Nat))) t0 t1) (erased (List (Nat)) R es row) (erased (Nat) x)
       (erased (TRow t0 t1 (BFalse) x row) tr) (erased (Sub row R) am) (erased (RC t0 t1 R es) rest) -> (RC t0 t1 R (Cons (Nat) x es)))))

(def-adts
  ((NotIn : ((Nat) y) ((List (Nat)) xs) -> Type)
    enum
    (many NINil : (erased (Nat) y) -> (NotIn y (Nil (Nat))))
    (many NICons : (erased (Nat) y x) (erased (List (Nat)) xs) (erased (Apart (Nat) Lt x y) ap) (erased (NotIn y xs) rest) -> (NotIn y (Cons (Nat) x xs)))))

(def-adts
  ((FarOK : ((List (PT)) p) -> Type)
    enum
    (many MkFarOK : (erased (List (PT)) p) (erased (Nat) K) (erased (List (Pair (Nat) (Nat))) dfa) (erased (List (List (Nat))) t0 t1)
       (erased (Nat) bot a1 i00) (erased (List (Nat)) ds R row00)
       (erased (Nth (Pair (Nat) (Nat)) dfa (Zero) (MkPair (Nat) (Nat) (Zero) a1)) z) (erased (Mem (Nat) (Zero) ds) m0) (erased (DC dfa ds ds) dc)
       (erased (FP K dfa t0 t1 bot ds (Zero) p) fp) (erased (FEdge t0 t1 (BFalse) bot bot) e0) (erased (FEdge t0 t1 (BTrue) bot bot) e1)
       (erased (NIx K (Zero) (Zero) i00) ix0) (erased (TRow t0 t1 (BFalse) i00 row00) tr0) (erased (Sub row00 R) am0)
       (erased (RC t0 t1 R R) rc) (erased (NotIn bot R) ni) -> (FarOK p))))

(def-adts
  ((Stops : ((PT) x) -> Type)
    enum
    (many StU : -> (Stops (Undef)))
    (many StH : -> (Stops (Def (Hlt))))))

(def-adts
  ((ExtAt : ((PT) x) ((Tr) t) -> Type)
    enum
    (many EAU : (erased (Tr) t) -> (ExtAt (Undef) t))
    (many EAD : (erased (Tr) t) -> (ExtAt (Def t) t))))

(def-fns _ $ (erased pick-fn : (erased (Bool) c) (erased (Nat) a b x y) (erased (Pick c a b x) p1) (erased (Pick c a b y) p2) -> (erased (Eq (Nat) x y) e))
  (match erased p1 _
    ((Pick0 _ _) (let-match erased p2 (Pick0 _ _)) (Refl (Nat) x))
    ((Pick1 _ _) (let-match erased p2 (Pick1 _ _)) (Refl (Nat) x))))

(def-fns _ $ (erased idx-fn : (erased (Nat) K d q i j) (erased (NIx K d q i) a) (erased (NIx K d q j) b) -> (erased (Eq (Nat) i j) e))
  (let-match erased a (MkNIx _ _ _ x _ mu ad))
  (let-match erased b (MkNIx _ _ _ y _ mu2 ad2))
  (let-match erased (mul-fn d K x y mu mu2) (Refl _ _))
  (add-fn x q i j ad ad2))

(def-fns _ $ (erased trow-fn : (erased (List (List (Nat))) t0 t1) (erased (Bool) b) (erased (Nat) i) (erased (List (Nat)) r1 r2)
    (erased (TRow t0 t1 b i r1) a) (erased (TRow t0 t1 b i r2) c) -> (erased (Eq (List (Nat)) r1 r2) e))
  (match erased a _
    ((TR0 _ _ _ _ n1) (let-match erased c (TR0 _ _ _ _ n2)) (nth-fn _ t0 i r1 r2 n1 n2))
    ((TR1 _ _ _ _ n1) (let-match erased c (TR1 _ _ _ _ n2)) (nth-fn _ t1 i r1 r2 n1 n2))))

(def-fns _ $ (erased sub-get : (erased (Nat) x) (erased (List (Nat)) xs R) (erased (Sub xs R) am) (subterm erased (Mem (Nat) x xs) mx) ->
    (erased (Mem (Nat) x R) r))
  (match erased mx _
    ((MemHere _ _ _) (let-match erased am (SubCons _ _ _ m _)) m)
    ((MemThere _ _ _ rest mx1) (let-match erased am (SubCons _ _ _ _ am1)) (sub-get x rest R am1 mx1))))

(def-fns _ $ (erased ally-get : (erased (List (List (Nat))) t0 t1) (erased (Bool) b) (erased (Nat) i y) (erased (List (Nat)) ys)
    (erased (AllY t0 t1 b i ys) ay) (subterm erased (Mem (Nat) y ys) my) -> (erased (FEdge t0 t1 b i y) e))
  (match erased my _
    ((MemHere _ _ _) (let-match erased ay (AYCons _ _ _ _ _ _ e _)) e)
    ((MemThere _ _ _ rest my1) (let-match erased ay (AYCons _ _ _ _ _ _ _ ay1)) (ally-get t0 t1 b i y rest ay1 my1))))

(def-fns _ $ (erased allx-get : (erased (List (List (Nat))) t0 t1) (erased (Bool) b) (erased (Nat) i) (erased (Bool) w) (erased (Nat) x y)
    (erased (List (Nat)) xs) (erased (AllX t0 t1 b i w xs) ax) (subterm erased (Mem (Nat) x xs) mx) (erased (FEdge t0 t1 w x y) e) ->
    (erased (FEdge t0 t1 b i y) r))
  (match erased mx _
    ((MemHere _ _ _)
      (let-match erased ax (AXCons _ _ _ _ _ _ _ row tr ay _))
      (let-match erased e (MkFEdge _ _ _ _ _ row2 tr2 my))
      (let-match erased (trow-fn t0 t1 w x row row2 tr tr2) (Refl _ _))
      (ally-get t0 t1 b i y row ay my))
    ((MemThere _ _ _ rest mx1) (let-match erased ax (AXCons _ _ _ _ _ _ _ _ _ _ ax1)) (allx-get t0 t1 b i w x y rest ax1 mx1 e))))

(def-fns _ $ (erased rc-get : (erased (List (List (Nat))) t0 t1) (erased (List (Nat)) R es) (erased (Nat) x) (erased (RC t0 t1 R es) rc)
    (subterm erased (Mem (Nat) x es) mx) -> (erased (List (Nat)) row) (erased (TRow t0 t1 (BFalse) x row) tr) (erased (Sub row R) am))
  (match erased mx _
    ((MemHere _ _ _) (let-match erased rc (RCCons _ _ _ _ row _ tr am _)) (values row tr am))
    ((MemThere _ _ _ rest mx1) (let-match erased rc (RCCons _ _ _ _ _ _ _ _ rc1)) (rc-get t0 t1 R rest x rc1 mx1))))

(def-fns _ $ (erased zpath : (erased (List (List (Nat))) t0 t1) (erased (Nat) bot k) (erased (List (Nat)) R) (erased (RC t0 t1 R R) rc)
    (erased (Mem (Nat) k R) mk) (subterm erased (NAcc t0 t1 bot k (Nil (Bool))) na) -> (erased (Mem (Nat) bot R) r))
  (let-match erased na (NAZero _ _ _ _ k2 e na1) ((NAEnd _ _ _) mk))
  (let-match erased e (MkFEdge _ _ _ _ _ row tr my))
  (let ((erased row2) (erased tr2) (erased am)) (rc-get t0 t1 R R k rc mk))
  (let-match erased (trow-fn t0 t1 (BFalse) k row row2 tr tr2) (Refl _ _))
  (zpath t0 t1 bot k2 R rc (sub-get k2 row R am my) na1))

(def-fns _ $ (erased absurd notin-mem : (erased (Nat) y) (erased (List (Nat)) xs) (erased (NotIn y xs) ni) (subterm erased (Mem (Nat) y xs) my) -> (erased (False) f))
  (match erased my _
    (absurd (MemHere _ _ _) (let-match erased ni (NICons _ _ _ ap _)) (apart-irrefl y ap))
    (absurd (MemThere _ _ _ rest my1) (let-match erased ni (NICons _ _ _ _ ni1)) (notin-mem y rest ni1 my1))))

(def-fns _ $ (erased nacc-bot : (erased (List (List (Nat))) t0 t1) (erased (Nat) bot) (erased (FEdge t0 t1 (BFalse) bot bot) e0)
    (erased (FEdge t0 t1 (BTrue) bot bot) e1) (subterm erased (List (Bool)) w) -> (erased (NAcc t0 t1 bot bot w) a))
  (let-match erased w (Cons _ b w1) ((Nil _) (NAEnd t0 t1 bot)))
  (let ((erased a1)) (nacc-bot t0 t1 bot e0 e1 w1))
  (match erased b _
    ((BFalse) (NAStep t0 t1 bot bot bot b w1 e0 a1))
    ((BTrue) (NAStep t0 t1 bot bot bot b w1 e1 a1))))

(def-fns _ $ (erased dc-get : (erased (List (Pair (Nat) (Nat))) dfa) (erased (List (Nat)) ds es) (erased (Nat) d) (erased (DC dfa ds es) dc)
    (subterm erased (Mem (Nat) d es) md) -> (erased (Nat) a0 a1) (erased (Nth (Pair (Nat) (Nat)) dfa d (MkPair (Nat) (Nat) a0 a1)) nd)
    (erased (Mem (Nat) a0 ds) m0) (erased (Mem (Nat) a1 ds) m1))
  (match erased md _
    ((MemHere _ _ _) (let-match erased dc (DCCons _ _ _ _ a0 a1 nd m0 m1 _)) (values a0 a1 nd m0 m1))
    ((MemThere _ _ _ rest md1) (let-match erased dc (DCCons _ _ _ _ _ _ _ _ _ dc1)) (dc-get dfa ds rest d dc1 md1))))

(def-fns _ $ (erased pick-mem : (erased (Bool) c) (erased (Nat) a b x) (erased (List (Nat)) ds) (erased (Pick c a b x) pk)
    (erased (Mem (Nat) a ds) ma) (erased (Mem (Nat) b ds) mb) -> (erased (Mem (Nat) x ds) mx))
  (match erased pk _ ((Pick0 _ _) ma) ((Pick1 _ _) mb)))

(def-fns _ $ (erased pick-of : (erased (Bool) c) (erased (Nat) a b) -> (erased (Nat) x) (erased (Pick c a b x) pk))
  (match erased c _ ((BFalse) (values a (Pick0 a b))) ((BTrue) (values b (Pick1 a b)))))

(def-fns _ $ (erased drun-mem : (erased (List (Pair (Nat) (Nat))) dfa) (erased (List (Nat)) ds) (erased (List (Bool)) l) (erased (Nat) d)
    (erased (Mem (Nat) (Zero) ds) m0) (erased (DC dfa ds ds) dc) (subterm erased (DRun dfa l d) dr) -> (erased (Mem (Nat) d ds) md))
  (let-match erased dr (DRCons _ l1 d1 a b _ c r1 nd pk) ((DRNil _) m0))
  (let ((erased md1)) (drun-mem dfa ds l1 d1 m0 dc r1))
  (let ((erased _) (erased _) (erased nd2) (erased ma) (erased mb)) (dc-get dfa ds ds d1 dc md1))
  (let-match erased (nth-fn _ dfa d1 _ _ nd nd2) (Refl _ _))
  (pick-mem c a b d ds pk ma mb))

(def-fns _ $ (erased drun-ex : (erased (List (Pair (Nat) (Nat))) dfa) (erased (List (Nat)) ds) (subterm erased (List (Bool)) l)
    (erased (Mem (Nat) (Zero) ds) m0) (erased (DC dfa ds ds) dc) -> (erased (Nat) d) (erased (DRun dfa l d) dr) (erased (Mem (Nat) d ds) md))
  (let-match erased l (Cons _ c l1) ((Nil _) (values (Zero) (DRNil dfa) m0)))
  (let ((erased d1) (erased r1) (erased md1)) (drun-ex dfa ds l1 m0 dc))
  (let ((erased a0) (erased a1) (erased nd) (erased ma) (erased mb)) (dc-get dfa ds ds d1 dc md1))
  (let ((erased x) (erased pk)) (pick-of c a0 a1))
  (values x (DRCons dfa l1 d1 a0 a1 x c r1 nd pk) (pick-mem c a0 a1 x ds pk ma mb)))

(def-fns _ $ (erased fd-get : (erased (Nat) K) (erased (List (Pair (Nat) (Nat))) dfa) (erased (List (List (Nat))) t0 t1) (erased (Nat) bot q)
    (erased (Bool) b) (erased (PT) x) (erased (List (Nat)) ds) (erased (Nat) d) (erased (FD K dfa t0 t1 bot q b x ds) fd)
    (subterm erased (Mem (Nat) d ds) md) -> (erased (Nat) a0 a1) (erased (Nth (Pair (Nat) (Nat)) dfa d (MkPair (Nat) (Nat) a0 a1)) nd)
    (erased (FCond K t0 t1 bot q b x d a0 a1) fc))
  (match erased md _
    ((MemHere _ _ _) (let-match erased fd (FDCons _ _ _ _ _ _ _ _ _ a0 a1 _ nd fc _)) (values a0 a1 nd fc))
    ((MemThere _ _ _ rest md1) (let-match erased fd (FDCons _ _ _ _ _ _ _ _ _ _ _ _ _ _ fd1)) (fd-get K dfa t0 t1 bot q b x rest d fd1 md1))))

(def-fns _ $ (erased fp-get : (erased (Nat) K) (erased (List (Pair (Nat) (Nat))) dfa) (erased (List (List (Nat))) t0 t1) (erased (Nat) bot)
    (erased (List (Nat)) ds) (erased (Nat) q0 j q) (erased (List (PT)) p) (erased (Bool) b) (erased (PT) x)
    (erased (FP K dfa t0 t1 bot ds q0 p) fp) (subterm erased (PLook p j b x) pl) (erased (Add j q0 q) ad) -> (erased (FD K dfa t0 t1 bot q b x ds) fd))
  (match erased pl _
    ((PL0 _ _ _) (let-match erased ad (AddZero _)) (let-match erased fp (FPCons _ _ _ _ _ _ _ _ _ _ f0 _ _)) f0)
    ((PL1 _ _ _) (let-match erased ad (AddZero _)) (let-match erased fp (FPCons _ _ _ _ _ _ _ _ _ _ _ f1 _)) f1)
    ((PLS _ _ rest j1 _ _ pl1)
      (let-match erased fp (FPCons _ _ _ _ _ _ _ _ _ _ _ _ fr))
      (fp-get K dfa t0 t1 bot ds (Succ q0) j1 q rest b x fr pl1 (add-unshift j1 q0 q ad)))))

(def-fns _ $ (erased ext-two : (erased (List (PT)) p) (erased (Tr) t0 t1) (erased (List (Tr)) rest) (erased (Ext p (Cons (Tr) t0 (Cons (Tr) t1 rest))) ex) ->
    (erased (PT) x0 x1) (erased (List (PT)) p2) (erased (Eq (List (PT)) p (Cons (PT) x0 (Cons (PT) x1 p2))) e)
    (erased (ExtAt x0 t0) a0) (erased (ExtAt x1 t1) a1) (erased (Ext p2 rest) ex2))
  (match erased ex _
    ((ExU _ _ _ ex1)
      (match erased ex1 _
        ((ExU _ p2 _ ex2) (values (Undef) (Undef) p2 (Refl _ p) (EAU t0) (EAU t1) ex2))
        ((ExD _ p2 _ ex2) (values (Undef) (Def t1) p2 (Refl _ p) (EAU t0) (EAD t1) ex2))))
    ((ExD _ _ _ ex1)
      (match erased ex1 _
        ((ExU _ p2 _ ex2) (values (Def t0) (Undef) p2 (Refl _ p) (EAD t0) (EAU t1) ex2))
        ((ExD _ p2 _ ex2) (values (Def t0) (Def t1) p2 (Refl _ p) (EAD t0) (EAD t1) ex2))))))

(def-fns _ $ (erased pl-of : (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Nat) q) (erased (Bool) b) (erased (Tr) t)
    (erased (Ext p m) ex) (subterm erased (Look m q b t) lk) -> (erased (PT) x) (erased (PLook p q b x) pl) (erased (ExtAt x t) ea))
  (match erased lk _
    ((Look0 t0 t1 rest)
      (let ((erased x0) (erased x1) (erased p2) (erased e) (erased a0) (erased _) (erased _)) (ext-two p t0 t1 rest ex))
      (let-match erased e (Refl _ _))
      (values x0 (PL0 x0 x1 p2) a0))
    ((Look1 t0 t1 rest)
      (let ((erased x0) (erased x1) (erased p2) (erased e) (erased _) (erased a1) (erased _)) (ext-two p t0 t1 rest ex))
      (let-match erased e (Refl _ _))
      (values x1 (PL1 x0 x1 p2) a1))
    ((LookS t0 t1 rest q1 _ _ lk1)
      (let ((erased x0) (erased x1) (erased p2) (erased e) (erased _) (erased _) (erased ex2)) (ext-two p t0 t1 rest ex))
      (let-match erased e (Refl _ _))
      (let ((erased x) (erased pl1) (erased ea)) (pl-of p2 rest q1 b t ex2 lk1))
      (values x (PLS x0 x1 p2 q1 b x pl1) ea))))

(def-fns _ $ (erased acc-stop : (erased (Nat) K) (erased (List (Pair (Nat) (Nat))) dfa) (erased (List (List (Nat))) t0 t1) (erased (Nat) bot q)
    (erased (Bool) h) (erased (PT) x) (erased (List (Nat)) ds) (erased (List (Bool)) l r)
    (erased (Mem (Nat) (Zero) ds) m0) (erased (DC dfa ds ds) dc) (erased (FD K dfa t0 t1 bot q h x ds) fd) (erased (Stops x) sx)
    (erased (FEdge t0 t1 (BFalse) bot bot) e0) (erased (FEdge t0 t1 (BTrue) bot bot) e1) -> (erased (CAcc K dfa t0 t1 bot (MkConf q l h r)) ca))
  (let ((erased d) (erased dr) (erased md)) (drun-ex dfa ds l m0 dc))
  (let ((erased _) (erased _) (erased _) (erased fc)) (fd-get K dfa t0 t1 bot q h x ds d fd md))
  (let ((erased i) (erased ix) (erased e))
    (match erased sx (((Nat) i) ((NIx K d q i) ix) ((FEdge t0 t1 h i bot) e))
      ((StU) (let-match erased fc (FCU _ _ _ _ _ _ _ _ _ i ix e)) (values i ix e))
      ((StH) (let-match erased fc (FCH _ _ _ _ _ _ _ _ _ i ix e)) (values i ix e))))
  (MkCA K dfa t0 t1 bot q d i l r h dr ix (NAStep t0 t1 bot i bot h r e (nacc-bot t0 t1 bot e0 e1 r))))

(def-fns _ $ (erased far-acc : (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Ext p m) ex)
    (erased (Nat) K) (erased (List (Pair (Nat) (Nat))) dfa) (erased (List (List (Nat))) t0 t1) (erased (Nat) bot a1z) (erased (List (Nat)) ds)
    (erased (Nth (Pair (Nat) (Nat)) dfa (Zero) (MkPair (Nat) (Nat) (Zero) a1z)) z) (erased (Mem (Nat) (Zero) ds) m0) (erased (DC dfa ds ds) dc)
    (erased (FP K dfa t0 t1 bot ds (Zero) p) fp) (erased (FEdge t0 t1 (BFalse) bot bot) e0) (erased (FEdge t0 t1 (BTrue) bot bot) e1)
    (erased (Conf) c) (erased (Nat) s) (subterm erased (HaltsAt m c s) hs) -> (erased (CAcc K dfa t0 t1 bot c) ca))
  (match erased hs _
    ((HStop _ q l r h lk)
      (let ((erased x) (erased pl) (erased ea)) (pl-of p m q h _ ex lk))
      (let ((erased fd)) (fp-get K dfa t0 t1 bot ds (Zero) q q p h x fp pl (add-zero-right q)))
      (let ((erased sx)) (match erased ea (((Stops x) sx)) ((EAU _) (StU)) ((EAD _) (StH))))
      (acc-stop K dfa t0 t1 bot q h x ds l r m0 dc fd sx e0 e1))
    ((HMove _ _ cd s1 st rest)
      (let-match erased (far-acc p m ex K dfa t0 t1 bot a1z ds z m0 dc fp e0 e1 cd s1 rest) (MkCA _ _ _ _ _ q2 d1 i1 l1 _ h1 dr1 ix1 na1))
      (match erased st _
        ((StepR _ q _ l r _ h w _ lk pp)
          (let ((erased x) (erased pl) (erased ea)) (pl-of p m q h _ ex lk))
          (let ((erased fd)) (fp-get K dfa t0 t1 bot ds (Zero) q q p h x fp pl (add-zero-right q)))
          (let-match erased ea (EAD _) ((EAU _) (acc-stop K dfa t0 t1 bot q h x ds l r m0 dc fd (StU) e0 e1)))
          (let-match erased dr1 (DRCons _ _ d0 a b _ _ r0 nd pk))
          (let ((erased _) (erased _) (erased nd2) (erased fc)) (fd-get K dfa t0 t1 bot q h x ds d0 fd (drun-mem dfa ds l d0 m0 dc r0)))
          (let-match erased (nth-fn _ dfa d0 _ _ nd nd2) (Refl _ _))
          (let-match erased fc (FCR _ _ _ _ _ _ _ _ _ _ _ i dw i2 ix pk2 ix2 e))
          (let-match erased (pick-fn w a b d1 dw pk pk2) (Refl _ _))
          (let-match erased (idx-fn K d1 q2 i1 i2 ix1 ix2) (Refl _ _))
          (let ((erased na))
            (match erased pp (((NAcc t0 t1 bot i1 r) na))
              ((PullCons _ _) na1)
              ((PullNil) (let-match erased na1 (NAStep _ _ _ _ k _ _ ez nz)) (NAZero t0 t1 bot i1 k ez nz))))
          (MkCA K dfa t0 t1 bot q d0 i l r h r0 ix (NAStep t0 t1 bot i i1 h r e na)))
        ((StepL _ q _ l r _ h w _ lk pp)
          (let ((erased x) (erased pl) (erased ea)) (pl-of p m q h _ ex lk))
          (let ((erased fd)) (fp-get K dfa t0 t1 bot ds (Zero) q q p h x fp pl (add-zero-right q)))
          (let-match erased ea (EAD _) ((EAU _) (acc-stop K dfa t0 t1 bot q h x ds l r m0 dc fd (StU) e0 e1)))
          (let ((erased a0) (erased a1) (erased nd) (erased fc)) (fd-get K dfa t0 t1 bot q h x ds d1 fd (drun-mem dfa ds l1 d1 m0 dc dr1)))
          (let-match erased fc (FCL _ _ _ _ _ _ _ _ _ _ _ lc0 lc1))
          (let-match erased na1 (NAStep _ _ _ _ x1 _ _ ea1 na2))
          (let-match erased na2 (NAStep _ _ _ _ y _ _ ew na3))
          (let ((erased dc1) (erased i2) (erased dr) (erased ix2) (erased eb))
            (match erased h1 (((Nat) dc1) ((Nat) i2) ((DRun dfa l dc1) dr) ((NIx K dc1 q i2) ix2) ((FEdge t0 t1 h i2 y) eb))
              ((BFalse)
                (let-match erased lc0 (MkLC _ _ _ _ _ _ _ _ _ _ _ dn i i2 row pk ix ix2 tr ax))
                (let-match erased (idx-fn K d1 q2 i1 i ix1 ix) (Refl _ _))
                (let-match erased ea1 (MkFEdge _ _ _ _ _ row2 tr2 mx))
                (let-match erased (trow-fn t0 t1 h1 i1 row row2 tr tr2) (Refl _ _))
                (let ((erased eb)) (allx-get t0 t1 h i2 w x1 y row ax mx ew))
                (let ((erased dr))
                  (match erased pp (((DRun dfa l dn) dr))
                    ((PullCons _ _) (DRCons dfa l1 d1 a0 a1 dn h1 dr1 nd pk))
                    ((PullNil)
                      (let-match erased dr1 (DRNil _))
                      (let-match erased (nth-fn _ dfa (Zero) _ _ nd z) (Refl _ _))
                      (let-match erased pk (Pick0 _ _))
                      (DRNil dfa))))
                (values dn i2 dr ix2 eb))
              ((BTrue)
                (let-match erased lc1 (MkLC _ _ _ _ _ _ _ _ _ _ _ dn i i2 row pk ix ix2 tr ax))
                (let-match erased (idx-fn K d1 q2 i1 i ix1 ix) (Refl _ _))
                (let-match erased ea1 (MkFEdge _ _ _ _ _ row2 tr2 mx))
                (let-match erased (trow-fn t0 t1 h1 i1 row row2 tr tr2) (Refl _ _))
                (let ((erased eb)) (allx-get t0 t1 h i2 w x1 y row ax mx ew))
                (let-match erased pp (PullCons _ _))
                (values dn i2 (DRCons dfa l1 d1 a0 a1 dn h1 dr1 nd pk) ix2 eb))))
          (MkCA K dfa t0 t1 bot q dc1 i2 l r h dr ix2 (NAStep t0 t1 bot i2 y h r eb na3)))))))

(def-fns _ $ (erased absurd never-far : (erased (List (PT)) p) (erased (List (Tr)) m) (erased (FarOK p) fo) (erased (Ext p m) ex)
    (erased (Nat) s) (erased (HaltsAt m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) hs) -> (erased (False) f))
  (let-match erased fo (MkFarOK _ K dfa t0 t1 bot a1 i00 ds R row00 z m0 dc fp e0 e1 ix0 tr0 am0 rc ni))
  (let-match erased (far-acc p m ex K dfa t0 t1 bot a1 ds z m0 dc fp e0 e1 _ s hs) (MkCA _ _ _ _ _ _ _ i _ _ _ dr ix na))
  (let-match erased dr (DRNil _))
  (let-match erased (idx-fn K (Zero) (Zero) i i00 ix ix0) (Refl _ _))
  (let-match erased na (NAStep _ _ _ _ k _ _ e nk))
  (let-match erased e (MkFEdge _ _ _ _ _ row tr mk))
  (let-match erased (trow-fn t0 t1 (BFalse) i row row00 tr tr0) (Refl _ _))
  (notin-mem bot R ni (zpath t0 t1 bot k R rc (sub-get k row R am0 mk) nk)))

(def-fns _ $ (erased mir-halts : (erased (Bool) f) (erased (List (PT)) p p2) (erased (List (Tr)) m) (erased (Mir f p p2) mi) (erased (Ext p m) ex)
    (erased (Nat) s) (erased (HaltsAt m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) hs) ->
    (erased (List (Tr)) m2) (erased (Ext p2 m2) ex2) (erased (HaltsAt m2 (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) hs2))
  (let-match erased mi (MirY _ _ xp) ((MirN _) (values m ex hs)))
  (let ((erased v) (erased x)) (xm-of (BTrue) (Zero) (Zero) m))
  (values v (ext-xp p p2 m v ex x xp)
    (pm-halts (BTrue) (Zero) (Zero) m v (Zero) (Zero) (Nil (Bool)) (Nil (Bool)) (Nil (Bool)) (Nil (Bool)) (BFalse) s hs
      (PMId (BTrue) (Zero) m v x) (SwA (Zero) (Zero)) (FC1 (Nil (Bool)) (Nil (Bool))))))

(def-adts $ (FarCert : -> Type)
  enum
  (many MkFC : (many (Nat) K) (many (List (Pair (Nat) (Nat))) dfa) (many (List (List (Nat))) t0 t1) (many (Nat) bot)
     (many (List (Nat)) ds R) -> (FarCert)))

(def-adts
  ((TRowR : ((List (List (Nat))) t0) ((List (List (Nat))) t1) ((Bool) b) ((Nat) i) -> Type)
    enum
    (many TROk : (erased (List (List (Nat))) t0 t1) (erased (Bool) b) (erased (Nat) i) (many (List (Nat)) row) (erased (TRow t0 t1 b i row) tr)
       -> (TRowR t0 t1 b i))
    (many TRNo : (erased (List (List (Nat))) t0 t1) (erased (Bool) b) (erased (Nat) i) -> (TRowR t0 t1 b i))))

(def-adts $ (FA : ((List (List (Nat))) t0) ((List (List (Nat))) t1) -> Type)
  enum
  (many MkFA : (erased (List (List (Nat))) t0 t1) (many (AV (List (Nat)) t0) T0) (many (AV (List (Nat)) t1) T1) -> (FA t0 t1)))

(def-fns _ $ (many trow-of : (erased (List (List (Nat))) t0 t1) (many (FA t0 t1) fa) (many (Bool) b) (many (Nat) i) -> (many (TRowR t0 t1 b i) r))
  (let-match many fa (MkFA _ _ T0 T1))
  (match many b _
    ((BFalse) (match many (aget _ _ T0 i) _ ((NOk _ _ _ row nr) (TROk t0 t1 b i row (TR0 t0 t1 i row nr))) ((NNo _ _ _) (TRNo t0 t1 b i))))
    ((BTrue) (match many (aget _ _ T1 i) _ ((NOk _ _ _ row nr) (TROk t0 t1 b i row (TR1 t0 t1 i row nr))) ((NNo _ _ _) (TRNo t0 t1 b i))))))

(def-fns _ $ (many mem-n : (many (Nat) y) (subterm many (List (Nat)) xs) -> (many (Res (Mem (Nat) y xs)) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (RFail _)))
  (let-match many (eq-nat y x) (None _) ((Some _ e) (let-match erased e (Refl _ _)) (ROk _ (MemHere (Nat) y rest))))
  (let-match many (notail $ mem-n y rest) (ROk _ mm) ((RFail _) (RFail _)))
  (ROk _ (MemThere (Nat) y x rest mm)))

(def-fns _ $ (many edge-of : (erased (List (List (Nat))) t0 t1) (many (FA t0 t1) fa) (many (Bool) b) (many (Nat) i j) -> (many (Res (FEdge t0 t1 b i j)) r))
  (let-match many (trow-of t0 t1 fa b i) (TROk _ _ _ _ row tr) ((TRNo _ _ _ _) (RFail _)))
  (let-match many (mem-n j row) (ROk _ mj) ((RFail _) (RFail _)))
  (ROk _ (MkFEdge t0 t1 b i j row tr mj)))

(def-fns _ $ (many ally-of : (erased (List (List (Nat))) t0 t1) (many (FA t0 t1) fa) (many (Bool) b) (many (Nat) i) (subterm many (List (Nat)) ys) ->
    (many (Res (AllY t0 t1 b i ys)) r))
  (let-match many ys (Cons _ y rest) ((Nil _) (ROk _ (AYNil t0 t1 b i))))
  (let-match many (edge-of t0 t1 fa b i y) (ROk _ e) ((RFail _) (RFail _)))
  (let-match many (notail $ ally-of t0 t1 fa b i rest) (ROk _ ay) ((RFail _) (RFail _)))
  (ROk _ (AYCons t0 t1 b i y rest e ay)))

(def-fns _ $ (many allx-of : (erased (List (List (Nat))) t0 t1) (many (FA t0 t1) fa) (many (Bool) b) (many (Nat) i) (many (Bool) w) (subterm many (List (Nat)) xs) ->
    (many (Res (AllX t0 t1 b i w xs)) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (ROk _ (AXNil t0 t1 b i w))))
  (let-match many (trow-of t0 t1 fa w x) (TROk _ _ _ _ row tr) ((TRNo _ _ _ _) (RFail _)))
  (let-match many (ally-of t0 t1 fa b i row) (ROk _ ay) ((RFail _) (RFail _)))
  (let-match many (notail $ allx-of t0 t1 fa b i w rest) (ROk _ ax) ((RFail _) (RFail _)))
  (ROk _ (AXCons t0 t1 b i w x rest row tr ay ax)))

(def-fns _ $ (many idx-of : (many (Nat) K d q) -> (many (Nat) i) (erased (NIx K d q i) ix))
  (let ((many x) (erased mu)) (mul d K))
  (let ((many i) (erased ad)) (add x q))
  (values i (MkNIx K d q x i mu ad)))

(def-fns _ $ (many pick-n : (many (Bool) c) (many (Nat) a b) -> (many (Nat) x) (erased (Pick c a b x) pk))
  (match many c _ ((BFalse) (values a (Pick0 a b))) ((BTrue) (values b (Pick1 a b)))))

(def-fns _ $ (many lc-of : (many (Nat) K) (erased (List (List (Nat))) t0 t1) (many (FA t0 t1) fa) (many (Nat) q) (many (Bool) b w) (many (Nat) q2)
    (many (Bool) c) (many (Nat) d a0 a1) -> (many (Res (LC K t0 t1 q b w q2 c d a0 a1)) r))
  (let ((many dn) (erased pk)) (pick-n c a0 a1))
  (let ((many i) (erased ix)) (idx-of K d q2))
  (let ((many i2) (erased ix2)) (idx-of K dn q))
  (let-match many (trow-of t0 t1 fa c i) (TROk _ _ _ _ row tr) ((TRNo _ _ _ _) (RFail _)))
  (let-match many (allx-of t0 t1 fa b i2 w row) (ROk _ ax) ((RFail _) (RFail _)))
  (ROk _ (MkLC K t0 t1 q b w q2 c d a0 a1 dn i i2 row pk ix ix2 tr ax)))

(def-fns _ $ (many fcond-of : (many (Nat) K) (erased (List (List (Nat))) t0 t1) (many (FA t0 t1) fa) (many (Nat) bot q) (many (Bool) b) (many (PT) x)
    (many (Nat) d a0 a1) -> (many (Res (FCond K t0 t1 bot q b x d a0 a1)) r))
  (let ((many i) (erased ix)) (idx-of K d q))
  (let-match many x (Def t)
    ((Undef) (match many (edge-of t0 t1 fa b i bot) _ ((ROk _ e) (ROk _ (FCU K t0 t1 bot q b d a0 a1 i ix e))) ((RFail _) (RFail _)))))
  (let-match many t (Mov w mv q2)
    ((Hlt) (match many (edge-of t0 t1 fa b i bot) _ ((ROk _ e) (ROk _ (FCH K t0 t1 bot q b d a0 a1 i ix e))) ((RFail _) (RFail _)))))
  (match many mv _
    ((DR)
      (let ((many dw) (erased pk)) (pick-n w a0 a1))
      (let ((many i2) (erased ix2)) (idx-of K dw q2))
      (let-match many (edge-of t0 t1 fa b i i2) (ROk _ e) ((RFail _) (RFail _)))
      (ROk _ (FCR K t0 t1 bot q b w q2 d a0 a1 i dw i2 ix pk ix2 e)))
    ((DL)
      (let-match many (lc-of K t0 t1 fa q b w q2 (BFalse) d a0 a1) (ROk _ lc0) ((RFail _) (RFail _)))
      (let-match many (lc-of K t0 t1 fa q b w q2 (BTrue) d a0 a1) (ROk _ lc1) ((RFail _) (RFail _)))
      (ROk _ (FCL K t0 t1 bot q b w q2 d a0 a1 lc0 lc1)))))

(def-fns _ $ (many fd-of : (many (Nat) K) (many (List (Pair (Nat) (Nat))) dfa) (many (AV (Pair (Nat) (Nat)) dfa) DA) (erased (List (List (Nat))) t0 t1)
    (many (FA t0 t1) fa) (many (Nat) bot q) (many (Bool) b) (many (PT) x) (subterm many (List (Nat)) ds) -> (many (Res (FD K dfa t0 t1 bot q b x ds)) r))
  (let-match many ds (Cons _ d rest) ((Nil _) (ROk _ (FDNil K dfa t0 t1 bot q b x))))
  (let-match many (aget _ _ DA d) (NOk _ _ _ pr nd) ((NNo _ _ _) (RFail _)))
  (let-match many pr (MkPair _ _ a0 a1))
  (let-match many (fcond-of K t0 t1 fa bot q b x d a0 a1) (ROk _ fc) ((RFail _) (RFail _)))
  (let-match many (notail $ fd-of K dfa DA t0 t1 fa bot q b x rest) (ROk _ fd) ((RFail _) (RFail _)))
  (ROk _ (FDCons K dfa t0 t1 bot q b x d a0 a1 rest nd fc fd)))

(def-fns _ $ (many fp-of : (many (Nat) K) (many (List (Pair (Nat) (Nat))) dfa) (many (AV (Pair (Nat) (Nat)) dfa) DA) (erased (List (List (Nat))) t0 t1)
    (many (FA t0 t1) fa) (many (Nat) bot) (many (List (Nat)) ds) (many (Nat) q) (subterm many (List (PT)) p) -> (many (Res (FP K dfa t0 t1 bot ds q p)) r))
  (let-match many p (Cons _ x0 p1) ((Nil _) (ROk _ (FPNil K dfa t0 t1 bot ds q))))
  (let-match many p1 (Cons _ x1 rest) ((Nil _) (RFail _)))
  (let-match many (fd-of K dfa DA t0 t1 fa bot q (BFalse) x0 ds) (ROk _ f0) ((RFail _) (RFail _)))
  (let-match many (fd-of K dfa DA t0 t1 fa bot q (BTrue) x1 ds) (ROk _ f1) ((RFail _) (RFail _)))
  (let-match many (notail $ fp-of K dfa DA t0 t1 fa bot ds (Succ q) rest) (ROk _ fr) ((RFail _) (RFail _)))
  (ROk _ (FPCons K dfa t0 t1 bot ds q x0 x1 rest f0 f1 fr)))

(def-fns _ $ (many dc-of : (many (List (Pair (Nat) (Nat))) dfa) (many (AV (Pair (Nat) (Nat)) dfa) DA) (many (List (Nat)) ds) (subterm many (List (Nat)) es) ->
    (many (Res (DC dfa ds es)) r))
  (let-match many es (Cons _ d rest) ((Nil _) (ROk _ (DCNil dfa ds))))
  (let-match many (aget _ _ DA d) (NOk _ _ _ pr nd) ((NNo _ _ _) (RFail _)))
  (let-match many pr (MkPair _ _ a0 a1))
  (let-match many (mem-n a0 ds) (ROk _ m0) ((RFail _) (RFail _)))
  (let-match many (mem-n a1 ds) (ROk _ m1) ((RFail _) (RFail _)))
  (let-match many (notail $ dc-of dfa DA ds rest) (ROk _ dc) ((RFail _) (RFail _)))
  (ROk _ (DCCons dfa ds rest d a0 a1 nd m0 m1 dc)))

(def-fns _ $ (many sub-chk : (subterm many (List (Nat)) xs) (many (List (Nat)) R) -> (many (Res (Sub xs R)) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (ROk _ (SubNil R))))
  (let-match many (mem-n x R) (ROk _ mx) ((RFail _) (RFail _)))
  (let-match many (notail $ sub-chk rest R) (ROk _ sr) ((RFail _) (RFail _)))
  (ROk _ (SubCons x rest R mx sr)))

(def-fns _ $ (many rc-of : (erased (List (List (Nat))) t0 t1) (many (FA t0 t1) fa) (many (List (Nat)) R) (subterm many (List (Nat)) es) -> (many (Res (RC t0 t1 R es)) r))
  (let-match many es (Cons _ x rest) ((Nil _) (ROk _ (RCNil t0 t1 R))))
  (let-match many (trow-of t0 t1 fa (BFalse) x) (TROk _ _ _ _ row tr) ((TRNo _ _ _ _) (RFail _)))
  (let-match many (sub-chk row R) (ROk _ am) ((RFail _) (RFail _)))
  (let-match many (notail $ rc-of t0 t1 fa R rest) (ROk _ rc) ((RFail _) (RFail _)))
  (ROk _ (RCCons t0 t1 R rest row x tr am rc)))

(def-fns _ $ (many notin-of : (many (Nat) y) (subterm many (List (Nat)) xs) -> (many (Res (NotIn y xs)) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (ROk _ (NINil y))))
  (let-match many (nat-eq x y) (Unequal _ _ _ _ ap) ((Equal _ _ _) (RFail _)))
  (let-match many (notail $ notin-of y rest) (ROk _ ni) ((RFail _) (RFail _)))
  (ROk _ (NICons y x rest ap ni)))

(def-fns _ $ (many check-far : (many (List (PT)) p) (many (FarCert) ct) -> (many (Res (FarOK p)) r))
  (let-match many ct (MkFC K dfa t0 t1 bot ds R))
  (let ((many DA)) (mk-av _ dfa))
  (let ((many fa)) (MkFA t0 t1 (mk-av _ t0) (mk-av _ t1)))
  (let-match many (aget _ _ DA 0) (NOk _ _ _ pr z) ((NNo _ _ _) (RFail _)))
  (let-match many pr (MkPair _ _ a0 a1))
  (let-match many a0 (Zero) ((Succ _) (RFail _)))
  (let-match many (mem-n 0 ds) (ROk _ m0) ((RFail _) (RFail _)))
  (let-match many (dc-of dfa DA ds ds) (ROk _ dc) ((RFail _) (RFail _)))
  (let-match many (fp-of K dfa DA t0 t1 fa bot ds (Zero) p) (ROk _ fp) ((RFail _) (RFail _)))
  (let-match many (edge-of t0 t1 fa (BFalse) bot bot) (ROk _ e0) ((RFail _) (RFail _)))
  (let-match many (edge-of t0 t1 fa (BTrue) bot bot) (ROk _ e1) ((RFail _) (RFail _)))
  (let ((many i00) (erased ix0)) (idx-of K (Zero) (Zero)))
  (let-match many (trow-of t0 t1 fa (BFalse) i00) (TROk _ _ _ _ row00 tr0) ((TRNo _ _ _ _) (RFail _)))
  (let-match many (sub-chk row00 R) (ROk _ am0) ((RFail _) (RFail _)))
  (let-match many (rc-of t0 t1 fa R R) (ROk _ rc) ((RFail _) (RFail _)))
  (let-match many (notin-of bot R) (ROk _ ni) ((RFail _) (RFail _)))
  (ROk _ (MkFarOK p K dfa t0 t1 bot a1 i00 ds R row00 z m0 dc fp e0 e1 ix0 tr0 am0 rc ni)))

(def-fns _ $ (many has-n : (many (Nat) y) (subterm many (List (Nat)) xs) -> (many (Bool) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (BFalse)))
  (match many (nat-eq y x) _ ((Equal _ _ _) (BTrue)) (else (tail $ has-n y rest))))

(def-fns _ $ (many union-n : (subterm many (List (Nat)) ys) (many (List (Nat)) xs) -> (many (List (Nat)) r))
  (let-match many ys (Cons _ y rest) ((Nil _) xs))
  (match many (has-n y xs) _ ((BTrue) (tail $ union-n rest xs)) ((BFalse) (tail $ union-n rest (Cons (Nat) y xs)))))

(def-fns _ $ (many row-at : (subterm many (List (List (Nat))) t) (many (Nat) i) -> (many (List (Nat)) r))
  (let-match many t (Cons _ row rest) ((Nil _) (Nil (Nat))))
  (let-match many i (Succ i1) ((Zero) row))
  (tail $ row-at rest i1))

(def-fns _ $ (many row-add : (subterm many (List (List (Nat))) t) (many (Nat) i) (many (List (Nat)) ys) -> (many (List (List (Nat))) r))
  (let-match many t (Cons _ row rest) ((Nil _) t))
  (let-match many i (Succ i1) ((Zero) (Cons _ (union-n ys row) rest)))
  (Cons _ row (notail $ row-add rest i1 ys)))

(def-fns _ $ (many len-n : (erased Type A) (subterm many (List A) xs) -> (many (Nat) n))
  (let-match many xs (Cons _ _ rest) ((Nil _) 0))
  (Succ (notail $ len-n A rest)))

(def-fns _ $ (many sizes : (subterm many (List (List (Nat))) t) -> (many (Nat) n))
  (let-match many t (Cons _ row rest) ((Nil _) 0))
  (let ((many a)) (len-n _ row))
  (let ((many n) (erased _)) (add a (notail $ sizes rest)))
  n)

(def-adts $ (NFA2 : -> Type)
  enum
  (many MkN2 : (many (List (List (Nat))) t0 t1) -> (NFA2)))

(def-fns _ $ (many n2-row : (many (NFA2) g) (many (Bool) b) (many (Nat) i) -> (many (List (Nat)) r))
  (let-match many g (MkN2 t0 t1))
  (match many b _ ((BFalse) (row-at t0 i)) ((BTrue) (row-at t1 i))))

(def-fns _ $ (many n2-add : (many (NFA2) g) (many (Bool) b) (many (Nat) i) (many (List (Nat)) ys) -> (many (NFA2) r))
  (let-match many g (MkN2 t0 t1))
  (match many b _ ((BFalse) (MkN2 (row-add t0 i ys) t1)) ((BTrue) (MkN2 t0 (row-add t1 i ys)))))

(def-fns _ $ (many dfa-at : (many (List (Pair (Nat) (Nat))) dfa) (many (Nat) d) (many (Bool) c) -> (many (Nat) r))
  (let-match many (nth-opt _ dfa d) (Some _ pr) ((None _) 0))
  (let-match many pr (MkPair _ _ a0 a1))
  (match many c _ ((BFalse) a0) ((BTrue) a1)))

(def-fns _ $ (many succ-rows : (many (NFA2) g) (many (Bool) w) (subterm many (List (Nat)) xs) -> (many (List (Nat)) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (Nil (Nat))))
  (tail $ union-n (n2-row g w x) (notail $ succ-rows g w rest)))

(def-fns _ $ (many fact-tg : (many (Nat) K bot) (many (List (Pair (Nat) (Nat))) dfa) (many (Nat) d) (many (PT) x) -> (many (List (Nat)) r))
  (let ((many hb)) (Cons _ bot (Nil _)))
  (let-match many x (Def t) ((Undef) hb))
  (let-match many t (Mov w mv q2) ((Hlt) hb))
  (let-match many mv (DR) ((DL) (Nil _)))
  (let ((many j) (erased _)) (idx-of K (dfa-at dfa d w) q2))
  (Cons _ j (Nil _)))

(def-fns _ $ (many ent-fact : (many (Nat) K bot) (many (List (Pair (Nat) (Nat))) dfa) (many (Nat) q) (many (Bool) b) (many (PT) x)
    (subterm many (List (Nat)) ds) (many (NFA2) g) -> (many (NFA2) r))
  (let-match many ds (Cons _ d rest) ((Nil _) g))
  (let ((many i) (erased _)) (idx-of K d q))
  (tail $ ent-fact K bot dfa q b x rest (n2-add g b i (fact-tg K bot dfa d x))))

(def-fns _ $ (many ent-left : (many (Nat) K) (many (List (Pair (Nat) (Nat))) dfa) (many (Nat) q) (many (Bool) b) (many (PT) x)
    (subterm many (List (Nat)) ds) (many (NFA2) g) -> (many (NFA2) r))
  (let-match many ds (Cons _ d rest) ((Nil _) g))
  (let-match many x (Def t) ((Undef) g))
  (let-match many t (Mov w mv q2) ((Hlt) g))
  (let-match many mv (DL) ((DR) g))
  (let ((many i) (erased _)) (idx-of K d q2))
  (let ((many ia) (erased _)) (idx-of K (dfa-at dfa d (BFalse)) q))
  (let ((many ib) (erased _)) (idx-of K (dfa-at dfa d (BTrue)) q))
  (let ((many g1)) (n2-add g b ia (succ-rows g w (n2-row g (BFalse) i))))
  (let ((many g2)) (n2-add g1 b ib (succ-rows g1 w (n2-row g1 (BTrue) i))))
  (tail $ ent-left K dfa q b x rest g2))

(def-adts $ (EntR : -> Type)
  enum
  (many MkEntR : (many (Nat) K bot) (many (List (Pair (Nat) (Nat))) dfa) (many (List (Nat)) ds) (many (Bool) left) -> (EntR)))

(def-fns _ $ (many all-ents : (many (EntR) er) (many (Nat) q) (subterm many (List (PT)) p) (many (NFA2) g) -> (many (NFA2) r))
  (let-match many p (Cons _ x0 p1) ((Nil _) g))
  (let-match many p1 (Cons _ x1 rest) ((Nil _) g))
  (let-match many er (MkEntR K bot dfa ds left))
  (let ((many g2))
    (match many left (((NFA2) r))
      ((BFalse) (ent-fact K bot dfa q (BTrue) x1 ds (ent-fact K bot dfa q (BFalse) x0 ds g)))
      ((BTrue) (ent-left K dfa q (BTrue) x1 ds (ent-left K dfa q (BFalse) x0 ds g)))))
  (tail $ all-ents er (Succ q) rest g2))

(def-fns _ $ (many n2-size : (many (NFA2) g) -> (many (Nat) n))
  (let-match many g (MkN2 t0 t1))
  (let ((many n) (erased _)) (add (sizes t0) (sizes t1)))
  n)

(def-fns _ $ (many far-fix : (many (EntR) er) (many (List (PT)) p) (subterm many (Nat) fuel) (many (NFA2) g) -> (many (NFA2) r))
  (let-match many fuel (Succ f) ((Zero) g))
  (let ((many g2)) (all-ents er 0 p g))
  (match many (nat-eq (n2-size g) (n2-size g2)) _ ((Equal _ _ _) g2) (else (tail $ far-fix er p f g2))))

(def-fns _ $ (many zclose : (many (List (List (Nat))) t0) (subterm many (Nat) fuel) (many (List (Nat)) todo) (many (List (Nat)) R) -> (many (List (Nat)) r))
  (let-match many fuel (Succ f) ((Zero) R))
  (let-match many todo (Cons _ x rest) ((Nil _) R))
  (match many (has-n x R) _
    ((BTrue) (tail $ zclose t0 f rest R))
    ((BFalse) (tail $ zclose t0 f (cat _ (row-at t0 x) rest) (Cons (Nat) x R)))))

(def-fns _ $ (many far-gen : (many (List (PT)) p) (many (Nat) K) (many (List (Pair (Nat) (Nat))) dfa) -> (many (FarCert) ct))
  (let ((many n)) (len-n _ dfa))
  (let ((many bot) (erased _)) (mul n K))
  (let ((many M) (erased _)) (add bot 1))
  (let ((many ds) (erased _)) (range n))
  (let ((many e)) (repeat _ M (Nil (Nat))))
  (let ((many g0)) (MkN2 e e))
  (let ((many g1)) (n2-add (n2-add g0 (BFalse) bot (Cons _ bot (Nil _))) (BTrue) bot (Cons _ bot (Nil _))))
  (let ((many g2)) (all-ents (MkEntR K bot dfa ds (BFalse)) 0 p g1))
  (let-match many (far-fix (MkEntR K bot dfa ds (BTrue)) p 1000 g2) (MkN2 t0 t1))
  (let ((many i00) (erased _)) (idx-of K 0 0))
  (let ((many fuel) (erased _)) (mul M M))
  (MkFC K dfa t0 t1 bot ds (zclose t0 fuel (row-at t0 i00) (Nil (Nat)))))
