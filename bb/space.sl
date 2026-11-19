(def-adts
  ((Un : ((Nat) n) ((List (Bool)) t x) -> Type)
    enum
    (many UnZ : (erased (List (Bool)) t) -> (Un (Zero) t t))
    (many UnS : (erased (Nat) n) (erased (List (Bool)) t x) (erased (Un n t x) p) -> (Un (Succ n) t (Cons (Bool) (BTrue) x)))))

(def-adts
  ((Csz : ((Conf) c) ((Nat) n) -> Type)
    enum
    (many MkCsz : (erased (Nat) q) (erased (List (Bool)) l r) (erased (Bool) h) (erased (Nat) a b n)
       (erased (Length (Bool) l a) la) (erased (Length (Bool) r b) lb) (erased (Add a b n) ad) -> (Csz (MkConf q l h r) n))))

(def-adts
  ((Grow : ((Nat) n n2) -> Type)
    enum
    (many GrE : (erased (Nat) n) -> (Grow n n))
    (many GrS : (erased (Nat) n) -> (Grow n (Succ n)))))

(def-adts
  ((HRun : ((List (Tr)) m) ((Conf) c d) ((Nat) s) -> Type)
    enum
    (many HRStop : (erased (List (Tr)) m) (erased (Nat) q) (erased (List (Bool)) l r) (erased (Bool) h) (erased (Look m q h (Hlt)) lk)
       -> (HRun m (MkConf q l h r) (MkConf q l h r) (Succ (Zero))))
    (many HRMove : (erased (List (Tr)) m) (erased (Conf) c c1 d) (erased (Nat) s) (erased (Stp m c c1) st) (erased (HRun m c1 d s) h)
       -> (HRun m c d (Succ s)))))

(def-fns _ $ (erased len-ex : (erased Type A) (subterm erased (List A) xs) -> (erased (Nat) n) (erased (Length A xs n) p))
  (let-match erased xs (Cons _ x rest) ((Nil _) (values (Zero) (LengthNil A))))
  (let ((erased n) (erased p)) (len-ex A rest))
  (values (Succ n) (LengthCons A x rest n p)))

(def-fns _ $ (erased len-fn : (erased Type A) (erased (List A) xs) (erased (Nat) n k) (subterm erased (Length A xs n) p) (erased (Length A xs k) q) -> (erased (Eq (Nat) n k) e))
  (let-match erased p (LengthCons _ x rest n1 p1) ((LengthNil _) (let-match erased q (LengthNil _)) (Refl _ n)))
  (let-match erased q (LengthCons _ _ _ j1 q1))
  (let-match erased (len-fn A rest n1 j1 p1 q1) (Refl _ _))
  (Refl _ n))

(def-fns _ $ (erased csz-ex : (erased (Conf) c) -> (erased (Nat) n) (erased (Csz c n) z))
  (let-match erased c (MkConf q l h r))
  (let ((erased a) (erased la)) (len-ex (Bool) l))
  (let ((erased b) (erased lb)) (len-ex (Bool) r))
  (let ((erased n) (erased ad)) (add-ex a b))
  (values n (MkCsz q l r h a b n la lb ad)))

(def-fns _ $ (erased csz-fn : (erased (Conf) c) (erased (Nat) n k) (erased (Csz c n) p) (erased (Csz c k) q) -> (erased (Eq (Nat) n k) e))
  (let-match erased p (MkCsz q0 l r h a b _ la lb ad))
  (let-match erased q (MkCsz _ _ _ _ a2 b2 _ la2 lb2 ad2))
  (let-match erased (len-fn (Bool) l a a2 la la2) (Refl _ _))
  (let-match erased (len-fn (Bool) r b b2 lb lb2) (Refl _ _))
  (add-fn a b n k ad ad2))

(def-fns _ $ (erased stp-sz : (erased (List (Tr)) m) (erased (Conf) c d) (erased (Stp m c d) st) (erased (Nat) n) (erased (Csz c n) z) ->
    (erased (Nat) n2) (erased (Csz d n2) z2) (erased (Grow n n2) g))
  (let-match erased z (MkCsz q l r h a b _ la lb ad))
  (match erased st _
    ((StepL _ _ q2 _ _ l2 _ w h2 lk pp)
      (match erased pp _
        ((PullNil)
          (let-match erased la (LengthNil _))
          (let-match erased ad (AddZero _))
          (values (Succ n) (MkCsz q2 l2 (Cons (Bool) w r) h2 (Zero) (Succ b) (Succ b) (LengthNil _) (LengthCons _ w r b lb) (AddZero (Succ b))) (GrS n)))
        ((PullCons _ _)
          (let-match erased la (LengthCons _ _ _ a1 la1))
          (let-match erased ad (AddSucc _ _ n1 ad1))
          (values n (MkCsz q2 l2 (Cons (Bool) w r) h2 a1 (Succ b) n la1 (LengthCons _ w r b lb) (add-succ-right a1 b n1 ad1)) (GrE n)))))
    ((StepR _ _ q2 _ _ r2 _ w h2 lk pp)
      (match erased pp _
        ((PullNil)
          (let-match erased lb (LengthNil _))
          (let-match erased (add-fn a (Zero) n a ad (add-zero-right a)) (Refl _ _))
          (values (Succ n) (MkCsz q2 (Cons (Bool) w l) r2 h2 (Succ a) (Zero) (Succ n) (LengthCons _ w l a la) (LengthNil _) (AddSucc a (Zero) a (add-zero-right a))) (GrS n)))
        ((PullCons _ _)
          (let-match erased lb (LengthCons _ _ _ b1 lb1))
          (let ((erased n1) (erased e) (erased ad1)) (add-succ-right-inv a b1 n ad))
          (let-match erased e (Refl _ _))
          (values n (MkCsz q2 (Cons (Bool) w l) r2 h2 (Succ a) b1 n (LengthCons _ w l a la) lb1 (AddSucc a b1 n1 ad1)) (GrE n)))))))

(def-fns _ $ (erased hrun-halts : (erased (List (Tr)) m) (erased (Conf) c d) (erased (Nat) s) (subterm erased (HRun m c d s) h) -> (erased (HaltsAt m c s) h2))
  (match erased h _
    ((HRStop _ q l r b lk) (HStop m q l r b lk))
    ((HRMove _ _ c1 _ s1 st h1) (HMove m c c1 s1 st (hrun-halts m c1 d s1 h1)))))

(def-fns _ $ (erased hrun-lo : (erased (List (Tr)) m) (erased (Conf) c d) (erased (Nat) s) (subterm erased (HRun m c d s) h) (erased (Nat) n S)
    (erased (Csz c n) z) (erased (Csz d S) zd) -> (erased (Nat) t) (erased (Add n s t) ad) (erased (Lt S t) lt))
  (match erased h _
    ((HRStop _ q l r b lk)
      (let-match erased (csz-fn c n S z zd) (Refl _ _))
      (values (Succ n) (add-succ-right n (Zero) n (add-zero-right n)) (lt-succ n)))
    ((HRMove _ _ c1 _ s1 st h1)
      (let ((erased n1) (erased z1) (erased g)) (stp-sz m c c1 st n z))
      (let ((erased t1) (erased ad1) (erased lt1)) (hrun-lo m c1 d s1 h1 n1 S z1 zd))
      (let-match erased g (GrS _) ((GrE _) (values (Succ t1) (add-succ-right n s1 t1 ad1) (lt-weaken S t1 lt1))))
      (let-match erased ad1 (AddSucc _ _ t0 ad0))
      (values t1 (add-succ-right n s1 t0 ad0) lt1))))

(def-fns _ $ (erased hrun-sz : (erased (List (Tr)) m) (erased (Conf) c d) (erased (Nat) s) (subterm erased (HRun m c d s) h) (erased (Nat) n S)
    (erased (Csz c n) z) (erased (Csz d S) zd) -> (erased (Lt n (Succ S)) le))
  (match erased h _
    ((HRStop _ q l r b lk) (let-match erased (csz-fn c n S z zd) (Refl _ _)) (lt-succ n))
    ((HRMove _ _ c1 _ s1 st h1)
      (let ((erased n1) (erased z1) (erased g)) (stp-sz m c c1 st n z))
      (let ((erased le1)) (hrun-sz m c1 d s1 h1 n1 S z1 zd))
      (match erased g _
        ((GrE _) le1)
        ((GrS _) (lt-trans n (Succ n) (Succ S) (lt-succ n) le1))))))

(def-fns _ $ (erased look-lt : (erased (List (Tr)) m) (erased (Nat) q) (erased (Bool) b) (erased (Tr) t) (subterm erased (Look m q b t) lk)
    (erased (Nat) k) (erased (Length (Tr) m k) ln) -> (erased (Lt q k) lt))
  (let-match erased lk (LookS t0 t1 rest q1 _ _ lk1)
    ((Look0 _ _ _) (let-match erased ln (LengthCons _ _ _ j1 _)) (LtZ j1))
    ((Look1 _ _ _) (let-match erased ln (LengthCons _ _ _ j1 _)) (LtZ j1)))
  (let-match erased ln (LengthCons _ _ _ j1 ln1))
  (let-match erased ln1 (LengthCons _ _ _ j2 ln2))
  (LtS q1 j1 (lt-weaken q1 j2 (look-lt rest q1 b t lk1 j2 ln2))))

(def-adts
  ((Dl : ((List (Bool)) l t y) -> Type)
    enum
    (many DlN : (erased (List (Bool)) t) -> (Dl (Nil (Bool)) t t))
    (many DlC : (erased (Bool) b) (erased (List (Bool)) l t y) (erased (Dl l t y) p) -> (Dl (Cons (Bool) b l) t (Cons (Bool) b (Cons (Bool) b y))))))

(def-adts
  ((Eb : ((List (Bool)) xs) ((Nat) v) -> Type)
    enum
    (many EbN : -> (Eb (Nil (Bool)) (Succ (Zero))))
    (many Eb0 : (erased (List (Bool)) xs) (erased (Nat) v d) (erased (Eb xs v) p) (erased (Double v d) dd) -> (Eb (Cons (Bool) (BFalse) xs) d))
    (many Eb1 : (erased (List (Bool)) xs) (erased (Nat) v d) (erased (Eb xs v) p) (erased (Double v d) dd) -> (Eb (Cons (Bool) (BTrue) xs) (Succ d)))))

(def-adts
  ((Code : ((Conf) c) ((Nat) v) -> Type)
    enum
    (many MkCode : (erased (Nat) q) (erased (List (Bool)) l r) (erased (Bool) h) (erased (List (Bool)) x y z) (erased (Nat) v)
       (erased (Un q (Cons (Bool) (BFalse) (Cons (Bool) h y)) x) u) (erased (Dl l (Cons (Bool) (BFalse) (Cons (Bool) (BTrue) z)) y) dl)
       (erased (Dl r (Nil (Bool)) z) dr) (erased (Eb x v) eb) -> (Code (MkConf q l h r) v))))

(def-fns _ $ (erased dbl-ex : (subterm erased (Nat) a) -> (erased (Nat) b) (erased (Double a b) d))
  (let-match erased a (Succ a1) ((Zero) (values (Zero) (D0))))
  (let ((erased b1) (erased d1)) (dbl-ex a1))
  (values (Succ (Succ b1)) (DS a1 b1 d1)))

(def-fns _ $ (erased pow2-ex : (subterm erased (Nat) k) -> (erased (Nat) v) (erased (Pow2 k v) p))
  (let-match erased k (Succ i1) ((Zero) (values (Succ (Zero)) (P0))))
  (let ((erased v1) (erased p1)) (pow2-ex i1))
  (let ((erased w) (erased d)) (dbl-ex v1))
  (values w (PS i1 v1 w p1 d)))

(def-fns _ $ (erased un-ex : (subterm erased (Nat) n) (erased (List (Bool)) t) -> (erased (List (Bool)) x) (erased (Un n t x) p))
  (let-match erased n (Succ n1) ((Zero) (values t (UnZ t))))
  (let ((erased x1) (erased p1)) (un-ex n1 t))
  (values (Cons (Bool) (BTrue) x1) (UnS n1 t x1 p1)))

(def-fns _ $ (erased dl-ex : (subterm erased (List (Bool)) l) (erased (List (Bool)) t) -> (erased (List (Bool)) y) (erased (Dl l t y) p))
  (let-match erased l (Cons _ b l1) ((Nil _) (values t (DlN t))))
  (let ((erased y1) (erased p1)) (dl-ex l1 t))
  (values (Cons (Bool) b (Cons (Bool) b y1)) (DlC b l1 t y1 p1)))

(def-fns _ $ (erased eb-ex : (subterm erased (List (Bool)) xs) -> (erased (Nat) v) (erased (Eb xs v) p))
  (let-match erased xs (Cons _ b xs1) ((Nil _) (values (Succ (Zero)) (EbN))))
  (let ((erased v1) (erased p1)) (eb-ex xs1))
  (let ((erased d) (erased dd)) (dbl-ex v1))
  (match erased b _
    ((BFalse) (values d (Eb0 xs1 v1 d p1 dd)))
    ((BTrue) (values (Succ d) (Eb1 xs1 v1 d p1 dd)))))

(def-fns _ $ (erased code-ex : (erased (Conf) c) -> (erased (Nat) v) (erased (Code c v) cd))
  (let-match erased c (MkConf q l h r))
  (let ((erased z) (erased dr)) (dl-ex r (Nil (Bool))))
  (let ((erased y) (erased dl)) (dl-ex l (Cons (Bool) (BFalse) (Cons (Bool) (BTrue) z))))
  (let ((erased x) (erased u)) (un-ex q (Cons (Bool) (BFalse) (Cons (Bool) h y))))
  (let ((erased v) (erased eb)) (eb-ex x))
  (values v (MkCode q l r h x y z v u dl dr eb)))

(def-fns _ $ (erased eb-pos : (erased (List (Bool)) xs) (erased (Nat) v) (subterm erased (Eb xs v) p) -> (erased (Lt (Zero) v) q))
  (let-match erased p (Eb0 xs1 v1 _ p1 dd) ((EbN) (LtZ (Zero))) ((Eb1 xs1 v1 d p1 dd) (LtZ d)))
  (double-pos v1 v (eb-pos xs1 v1 p1) dd))

(def-fns _ $ (erased eb-inj : (erased (List (Bool)) xs ys) (erased (Nat) v) (subterm erased (Eb xs v) p) (erased (Eb ys v) q) -> (erased (Eq (List (Bool)) xs ys) e))
  (match erased p _
    ((EbN)
      (match erased q _
        ((EbN) (Refl _ xs))
        (absurd (Eb0 ys1 w1 _ q1 dd) (double-parity w1 (Zero) (Zero) dd (D0)))
        (absurd (Eb1 ys1 w1 _ q1 dd) (let-match erased dd (D0)) (eb-pos ys1 (Zero) q1))))
    ((Eb0 xs1 v1 _ p1 dd)
      (let-match erased q (Eb0 ys1 w1 _ q1 dd2)
        (absurd (EbN) (double-parity v1 (Zero) (Zero) dd (D0)))
        (absurd (Eb1 ys1 w1 d2 q1 dd2) (double-parity v1 w1 d2 dd dd2)))
      (let-match erased (double-inj v1 w1 v dd dd2) (Refl _ _))
      (let-match erased (eb-inj xs1 ys1 v1 p1 q1) (Refl _ _))
      (Refl _ xs))
    ((Eb1 xs1 v1 d p1 dd)
      (let-match erased q (Eb1 ys1 w1 _ q1 dd2)
        (absurd (EbN) (let-match erased dd (D0)) (eb-pos xs1 (Zero) p1))
        (absurd (Eb0 ys1 w1 _ q1 dd2) (double-parity w1 v1 d dd2 dd)))
      (let-match erased (double-inj v1 w1 d dd dd2) (Refl _ _))
      (let-match erased (eb-inj xs1 ys1 v1 p1 q1) (Refl _ _))
      (Refl _ xs))))

(def-fns _ $ (erased un-inj : (erased (Nat) n k) (erased (List (Bool)) a b x) (subterm erased (Un n (Cons (Bool) (BFalse) a) x) p) (erased (Un k (Cons (Bool) (BFalse) b) x) q) ->
    (erased (Eq (Nat) n k) e) (erased (Eq (List (Bool)) a b) f))
  (match erased p _
    ((UnZ _) (let-match erased q (UnZ _)) (values (Refl _ n) (Refl _ a)))
    ((UnS n1 _ x1 p1)
      (let-match erased q (UnS j1 _ _ q1))
      (let ((erased e) (erased f)) (un-inj n1 j1 a b x1 p1 q1))
      (let-match erased e (Refl _ _))
      (values (Refl _ n) f))))

(def-fns _ $ (erased dl-inj : (erased (List (Bool)) l k z z2 y) (subterm erased (Dl l (Cons (Bool) (BFalse) (Cons (Bool) (BTrue) z)) y) p)
    (erased (Dl k (Cons (Bool) (BFalse) (Cons (Bool) (BTrue) z2)) y) q) -> (erased (Eq (List (Bool)) l k) e) (erased (Eq (List (Bool)) z z2) f))
  (let-match erased p (DlC b l1 _ y1 p1) ((DlN _) (let-match erased q (DlN _)) (values (Refl _ l) (Refl _ z))))
  (let-match erased q (DlC _ j1 _ y2 q1))
  (let ((erased e) (erased f)) (dl-inj l1 j1 z z2 y1 p1 q1))
  (let-match erased e (Refl _ _))
  (values (Refl _ l) f))

(def-fns _ $ (erased dl-inj0 : (erased (List (Bool)) l k y) (subterm erased (Dl l (Nil (Bool)) y) p) (erased (Dl k (Nil (Bool)) y) q) -> (erased (Eq (List (Bool)) l k) e))
  (let-match erased p (DlC b l1 _ y1 p1) ((DlN _) (let-match erased q (DlN _)) (Refl _ l)))
  (let-match erased q (DlC _ j1 _ y2 q1))
  (let-match erased (dl-inj0 l1 j1 y1 p1 q1) (Refl _ _))
  (Refl _ l))

(def-fns _ $ (erased code-inj : (erased (Conf) c d) (erased (Nat) v) (erased (Code c v) p) (erased (Code d v) q) -> (erased (Eq (Conf) c d) e))
  (let-match erased p (MkCode q1 l r h x y z _ u dl dr eb))
  (let-match erased q (MkCode q2 l2 r2 h2 x2 y2 z2 _ u2 dl2 dr2 eb2))
  (let-match erased (eb-inj x x2 v eb eb2) (Refl _ _))
  (let ((erased e1) (erased f1)) (un-inj q1 q2 (Cons (Bool) h y) (Cons (Bool) h2 y2) x u u2))
  (let-match erased e1 (Refl _ _))
  (let-match erased f1 (Refl _ _))
  (let ((erased e2) (erased f2)) (dl-inj l l2 z z2 y dl dl2))
  (let-match erased e2 (Refl _ _))
  (let-match erased f2 (Refl _ _))
  (let-match erased (dl-inj0 r r2 z dr dr2) (Refl _ _))
  (Refl _ c))

(def-fns _ $ (erased un-len : (erased (Nat) q k) (erased (List (Bool)) t x) (subterm erased (Un q t x) u) (erased (Length (Bool) t k) lt) ->
    (erased (Nat) k2) (erased (Length (Bool) x k2) lx) (erased (Add q k k2) ad))
  (let-match erased u (UnS q1 _ x1 u1) ((UnZ _) (values k lt (AddZero k))))
  (let ((erased i1) (erased l1) (erased a1)) (un-len q1 k t x1 u1 lt))
  (values (Succ i1) (LengthCons _ (BTrue) x1 i1 l1) (AddSucc q1 k i1 a1)))

(def-fns _ $ (erased dl-len : (erased (List (Bool)) l t y) (subterm erased (Dl l t y) dl) (erased (Nat) a k) (erased (Length (Bool) l a) la) (erased (Length (Bool) t k) lt) ->
    (erased (Nat) d k2) (erased (Double a d) dd) (erased (Length (Bool) y k2) ly) (erased (Add d k k2) ad))
  (let-match erased dl (DlC b l1 _ y1 dl1) ((DlN _) (let-match erased la (LengthNil _)) (values (Zero) k (D0) lt (AddZero k))))
  (let-match erased la (LengthCons _ _ _ a1 la1))
  (let ((erased d1) (erased i1) (erased dd1) (erased ly1) (erased ad1)) (dl-len l1 t y1 dl1 a1 k la1 lt))
  (values (Succ (Succ d1)) (Succ (Succ i1)) (DS a1 d1 dd1) (LengthCons _ b _ _ (LengthCons _ b y1 i1 ly1)) (AddSucc _ k _ (AddSucc d1 k i1 ad1))))

(def-fns _ $ (erased eb-lt : (erased (List (Bool)) xs) (erased (Nat) v k P) (subterm erased (Eb xs v) e) (erased (Length (Bool) xs k) lx) (erased (Pow2 (Succ k) P) pp) ->
    (erased (Lt v P) lt))
  (let-match erased pp (PS _ P1 _ pp1 dP))
  (match erased e _
    ((EbN) (let-match erased lx (LengthNil _)) (let-match erased pp1 (P0)) (let-match erased dP (DS _ _ dP1)) (let-match erased dP1 (D0)) (LtS (Zero) (Succ (Zero)) (LtZ (Zero))))
    ((Eb0 xs1 v1 _ e1 dd) (let-match erased lx (LengthCons _ _ _ i1 lx1)) (double-mono v1 P1 v P (eb-lt xs1 v1 i1 P1 e1 lx1 pp1) dd dP))
    ((Eb1 xs1 v1 d e1 dd) (let-match erased lx (LengthCons _ _ _ i1 lx1)) (lt-double-succ v1 P1 d P (eb-lt xs1 v1 i1 P1 e1 lx1 pp1) dd dP))))

(def-fns _ $ (erased code-lt : (erased (Nat) q) (erased (List (Bool)) l r) (erased (Bool) h) (erased (Nat) v n S Q D2 E1 NB)
    (erased (Code (MkConf q l h r) v) cd) (erased (Csz (MkConf q l h r) n) zc) (erased (Lt n (Succ S)) ns) (erased (Lt q Q) lq) (erased (Double S D2) d2) (erased (Add Q (Succ (Succ D2)) E1) ae) (erased (Pow2 (Succ (Succ (Succ (Succ (Succ E1))))) NB) pn) ->
    (erased (Lt v NB) lt))
  (let-match erased cd (MkCode _ _ _ _ x y z _ u dl dr eb))
  (let-match erased zc (MkCsz _ _ _ _ nl nr _ la lb ad))
  (let ((erased dr0) (erased kz) (erased ddr) (erased lz) (erased az)) (dl-len r (Nil (Bool)) z dr nr (Zero) lb (LengthNil _)))
  (let-match erased (add-fn dr0 (Zero) kz dr0 az (add-zero-right dr0)) (Refl _ _))
  (let ((erased dl0) (erased ky) (erased ddl) (erased ly) (erased ay))
    (dl-len l (Cons (Bool) (BFalse) (Cons (Bool) (BTrue) z)) y dl nl (Succ (Succ kz)) la (LengthCons _ _ _ _ (LengthCons _ _ _ _ lz))))
  (let ((erased kx) (erased lx) (erased ax)) (un-len q (Succ (Succ ky)) (Cons (Bool) (BFalse) (Cons (Bool) h y)) x u (LengthCons _ _ _ _ (LengthCons _ _ _ _ ly))))
  (let ((erased dn) (erased ddn)) (dbl-ex n))
  (let ((erased an)) (add-doubles nl nr n dl0 dr0 dn ad ddl ddr ddn))
  (let-match erased (add-fn dl0 (Succ (Succ dr0)) ky (Succ (Succ dn)) ay (add-succ-right _ _ _ (add-succ-right _ _ _ an))) (Refl _ _))
  (let ((erased i1) (erased e1) (erased ax1)) (add-succ-right-inv q (Succ ky) kx ax))
  (let-match erased e1 (Refl _ _))
  (let ((erased k2) (erased e2) (erased ax2)) (add-succ-right-inv q ky i1 ax1))
  (let-match erased e2 (Refl _ _))
  (let ((erased k3) (erased e3) (erased ax3)) (add-succ-right-inv q (Succ dn) k2 ax2))
  (let-match erased e3 (Refl _ _))
  (let ((erased k4) (erased e4) (erased ax4)) (add-succ-right-inv q dn k3 ax3))
  (let-match erased e4 (Refl _ _))
  (let ((erased k5) (erased a5)) (add-ex dn Q))
  (let ((erased l5)) (add-lt-mono dn q Q k4 k5 (add-comm _ _ _ ax4) a5 lq))
  (let ((erased l6)) (add-lt-mono Q dn (Succ (Succ D2)) k5 E1 (add-comm _ _ _ a5) ae (double-mono n (Succ S) dn (Succ (Succ D2)) ns ddn (DS S D2 d2))))
  (let ((erased P) (erased pp)) (pow2-ex (Succ kx)))
  (let ((erased l7)) (lt-trans k4 k5 E1 l5 l6))
  (lt-trans v P NB (eb-lt x v kx P eb lx pp)
    (pow2-lt _ _ P NB (LtS _ _ (LtS _ _ (LtS _ _ (LtS _ _ (LtS _ _ l7))))) pp pn)))

(def-adts
  ((Ne : ((Nat) x y) -> Type)
    enum
    (many NeL : (erased (Nat) x y) (erased (Lt x y) p) -> (Ne x y))
    (many NeG : (erased (Nat) x y) (erased (Lt y x) p) -> (Ne x y))))

(def-adts
  ((Fr : ((Nat) x) ((List (Nat)) xs) -> Type)
    enum
    (many FrN : (erased (Nat) x) -> (Fr x (Nil (Nat))))
    (many FrC : (erased (Nat) x y) (erased (List (Nat)) ys) (erased (Ne x y) n) (erased (Fr x ys) p) -> (Fr x (Cons (Nat) y ys)))))

(def-adts
  ((Dn : ((List (Nat)) xs) -> Type)
    enum
    (many DnN : -> (Dn (Nil (Nat))))
    (many DnC : (erased (Nat) x) (erased (List (Nat)) xs) (erased (Fr x xs) f) (erased (Dn xs) p) -> (Dn (Cons (Nat) x xs)))))

(def-adts
  ((Al : ((Nat) n) ((List (Nat)) xs) -> Type)
    enum
    (many AlN : (erased (Nat) n) -> (Al n (Nil (Nat))))
    (many AlC : (erased (Nat) n x) (erased (List (Nat)) xs) (erased (Lt x n) l) (erased (Al n xs) p) -> (Al n (Cons (Nat) x xs)))))

(def-adts
  ((Rm : ((List (Nat)) xs ys) -> Type)
    enum
    (many RmH : (erased (Nat) y) (erased (List (Nat)) ys) -> (Rm (Cons (Nat) y ys) ys))
    (many RmT : (erased (Nat) x) (erased (List (Nat)) xs ys) (erased (Rm xs ys) p) -> (Rm (Cons (Nat) x xs) (Cons (Nat) x ys)))))

(def-adts
  ((RmR : ((Nat) n) ((List (Nat)) xs) ((Nat) k) -> Type)
    enum
    (many RA : (erased (Nat) n k) (erased (List (Nat)) xs) (erased (Al n xs) a) -> (RmR n xs k))
    (many RB : (erased (Nat) n k) (erased (List (Nat)) xs ys) (erased (Dn ys) d) (erased (Al n ys) a) (erased (Length (Nat) ys k) l) (erased (Rm xs ys) r)
       -> (RmR n xs (Succ k)))))

(def-adts
  ((T3 : ((Nat) x y) -> Type)
    enum
    (many TLt : (erased (Nat) x y) (erased (Lt x y) p) -> (T3 x y))
    (many TEq : (erased (Nat) x) -> (T3 x x))
    (many TGt : (erased (Nat) x y) (erased (Lt y x) p) -> (T3 x y))))

(def-fns _ $ (erased tri : (subterm erased (Nat) x) (erased (Nat) y) -> (erased (T3 x y) t))
  (let-match erased x (Succ x1) ((Zero) (match erased y _ ((Zero) (TEq x)) ((Succ y1) (TLt x y (LtZ y1))))))
  (let-match erased y (Succ y1) ((Zero) (TGt x y (LtZ x1))))
  (match erased (tri x1 y1) _
    ((TLt _ _ p) (TLt x y (LtS x1 y1 p)))
    ((TEq _) (TEq x))
    ((TGt _ _ p) (TGt x y (LtS y1 x1 p)))))

(def-fns _ $ (erased absurd lt-irr : (erased (Nat) x) (subterm erased (Lt x x) p) -> (erased (False) f))
  (let-match erased p (LtS x1 _ p1))
  (lt-irr x1 p1))

(def-fns _ $ (erased fr-rm : (erased (Nat) z) (erased (List (Nat)) xs ys) (subterm erased (Rm xs ys) r) (erased (Fr z xs) f) -> (erased (Fr z ys) g))
  (match erased r _
    ((RmH _ _) (let-match erased f (FrC _ y xs1 n f1)) f1)
    ((RmT y xs1 ys1 r1) (let-match erased f (FrC _ _ _ n f1)) (FrC z y ys1 n (fr-rm z xs1 ys1 r1 f1)))))

(def-fns _ $ (erased fr-al : (erased (Nat) n) (erased (List (Nat)) xs) (subterm erased (Fr n xs) f) (erased (Al (Succ n) xs) a) -> (erased (Al n xs) b))
  (let-match erased f (FrC _ y ys ne f1) ((FrN _) (AlN n)))
  (let-match erased a (AlC _ _ _ ly a1))
  (let-match erased (lt-succ-cases y n ly) (InR _ _ l2)
    (absurd (InL _ _ e) (let-match erased e (Refl _ _)) (match erased ne _ (absurd (NeL _ _ p) (lt-irr y p)) (absurd (NeG _ _ p) (lt-irr y p)))))
  (AlC n y ys l2 (fr-al n ys f1 a1)))

(def-fns _ $ (erased rmv : (erased (Nat) n k) (erased (List (Nat)) xs) (subterm erased (Dn xs) d) (erased (Al (Succ n) xs) a) (erased (Length (Nat) xs k) l) ->
    (erased (RmR n xs k) r))
  (let-match erased d (DnC x xs1 f d1) ((DnN) (RA n k xs (AlN n))))
  (let-match erased a (AlC _ _ _ lx a1))
  (let-match erased l (LengthCons _ _ _ i1 l1))
  (let-match erased (lt-succ-cases x n lx) (InR _ _ lx2)
    ((InL _ _ e) (let-match erased e (Refl _ _)) (RB n i1 xs xs1 d1 (fr-al n xs1 f a1) l1 (RmH x xs1))))
  (match erased (rmv n i1 xs1 d1 a1 l1) _
    ((RA _ _ _ a2) (RA n k xs (AlC n x xs1 lx2 a2)))
    ((RB _ k2 _ ys d2 a2 l2 r2)
      (RB n (Succ k2) xs (Cons (Nat) x ys) (DnC x ys (fr-rm x xs1 ys r2 f) d2) (AlC n x ys lx2 a2) (LengthCons _ x ys k2 l2) (RmT x xs1 ys r2)))))

(def-fns _ $ (erased pigeon : (subterm erased (Nat) n) (erased (Nat) k) (erased (List (Nat)) xs) (erased (Dn xs) d) (erased (Al n xs) a) (erased (Length (Nat) xs k) l) ->
    (erased (Lt k (Succ n)) r))
  (let-match erased n (Succ n1)
    ((Zero)
      (let-match erased a (AlN _) (absurd (AlC _ _ _ lx _) lx))
      (let-match erased l (LengthNil _))
      (LtZ (Zero))))
  (match erased (rmv n1 k xs d a l) _
    ((RA _ _ _ a2) (lt-weaken k n (pigeon n1 k xs d a2 l)))
    ((RB _ k2 _ ys d2 a2 l2 r2) (LtS k2 n (pigeon n1 k2 ys d2 a2 l2)))))

(def-adts
  ((Rcd : ((List (Tr)) m) ((Conf) c d) ((Nat) s) ((List (Nat)) xs) -> Type)
    enum
    (many RCStop : (erased (List (Tr)) m) (erased (Nat) q) (erased (List (Bool)) l r) (erased (Bool) h) (erased (Look m q h (Hlt)) lk) (erased (Nat) v)
       (erased (Code (MkConf q l h r) v) cd) -> (Rcd m (MkConf q l h r) (MkConf q l h r) (Succ (Zero)) (Cons (Nat) v (Nil (Nat)))))
    (many RCMove : (erased (List (Tr)) m) (erased (Conf) c c1 d) (erased (Nat) s v) (erased (List (Nat)) xs) (erased (Stp m c c1) st) (erased (Rcd m c1 d s xs) h)
       (erased (Code c v) cd) -> (Rcd m c d (Succ s) (Cons (Nat) v xs)))))

(def-fns _ $ (erased rcd-of : (erased (List (Tr)) m) (erased (Conf) c d) (erased (Nat) s) (subterm erased (HRun m c d s) h) -> (erased (List (Nat)) xs) (erased (Rcd m c d s xs) rc))
  (let ((erased v) (erased cd)) (code-ex c))
  (let-match erased h (HRMove _ _ c1 _ s1 st h1) ((HRStop _ q l r b lk) (values (Cons (Nat) v (Nil (Nat))) (RCStop m q l r b lk v cd))))
  (let ((erased xs) (erased rc)) (rcd-of m c1 d s1 h1))
  (values (Cons (Nat) v xs) (RCMove m c c1 d s1 v xs st rc cd)))

(def-fns _ $ (erased rc-hrun : (erased (List (Tr)) m) (erased (Conf) c d) (erased (Nat) s) (erased (List (Nat)) xs) (subterm erased (Rcd m c d s xs) rc) -> (erased (HRun m c d s) h))
  (match erased rc _
    ((RCStop _ q l r b lk v cd) (HRStop m q l r b lk))
    ((RCMove _ _ c1 _ s1 v xs1 st rc1 cd) (HRMove m c c1 d s1 st (rc-hrun m c1 d s1 xs1 rc1)))))

(def-fns _ $ (erased rc-len : (erased (List (Tr)) m) (erased (Conf) c d) (erased (Nat) s) (erased (List (Nat)) xs) (subterm erased (Rcd m c d s xs) rc) -> (erased (Length (Nat) xs s) l))
  (match erased rc _
    ((RCStop _ q l r b lk v cd) (LengthCons _ v _ _ (LengthNil _)))
    ((RCMove _ _ c1 _ s1 v xs1 st rc1 cd) (LengthCons _ v xs1 s1 (rc-len m c1 d s1 xs1 rc1)))))

(def-fns _ $ (erased ne-code : (erased (List (Tr)) m) (erased (Conf) c e) (erased (Nat) vc ve sc t) (erased (Code c vc) cc) (erased (Code e ve) ce)
    (erased (HaltsAt m c sc) hc) (erased (HaltsAt m e t) he) (erased (Lt t sc) lt) -> (erased (Ne vc ve) n))
  (match erased (tri vc ve) _
    ((TLt _ _ p) (NeL vc ve p))
    ((TGt _ _ p) (NeG vc ve p))
    (absurd (TEq _)
      (let-match erased (code-inj c e vc cc ce) (Refl _ _))
      (let-match erased (halts-fn m c sc t hc he) (Refl _ _))
      (lt-irr t lt))))

(def-fns _ $ (erased fr-run : (erased (List (Tr)) m) (erased (Conf) c e d) (erased (Nat) vc sc t) (erased (List (Nat)) xs) (erased (Code c vc) cc)
    (erased (HaltsAt m c sc) hc) (subterm erased (Rcd m e d t xs) rc) (erased (Lt t sc) lt) -> (erased (Fr vc xs) f))
  (let ((erased he)) (hrun-halts m e d t (rc-hrun m e d t xs rc)))
  (match erased rc _
    ((RCStop _ q l r b lk v cd) (FrC vc v _ (ne-code m c e vc v sc t cc cd hc he lt) (FrN vc)))
    ((RCMove _ _ e1 _ t1 v xs1 st rc1 cd)
      (FrC vc v xs1 (ne-code m c e vc v sc t cc cd hc he lt) (fr-run m c e1 d vc sc t1 xs1 cc hc rc1 (lt-trans t1 t sc (lt-succ t1) lt))))))

(def-fns _ $ (erased rc-dn : (erased (List (Tr)) m) (erased (Conf) c d) (erased (Nat) s) (erased (List (Nat)) xs) (subterm erased (Rcd m c d s xs) rc) -> (erased (Dn xs) dn))
  (match erased rc _
    ((RCStop _ q l r b lk v cd) (DnC v _ (FrN v) (DnN)))
    ((RCMove _ _ c1 _ s1 v xs1 st rc1 cd)
      (DnC v xs1 (fr-run m c c1 d v s s1 xs1 cd (hrun-halts m c d s (rc-hrun m c d s xs rc)) rc1 (lt-succ s1)) (rc-dn m c1 d s1 xs1 rc1)))))

(def-fns _ $ (erased stp-lt : (erased (List (Tr)) m) (erased (Nat) q) (erased (List (Bool)) l r) (erased (Bool) h) (erased (Conf) d)
    (erased (Stp m (MkConf q l h r) d) st) (erased (Nat) k) (erased (Length (Tr) m k) ln) -> (erased (Lt q k) lt))
  (match erased st _
    ((StepL _ _ q2 _ _ l2 _ w h2 lk pp) (look-lt m q h _ lk k ln))
    ((StepR _ _ q2 _ _ r2 _ w h2 lk pp) (look-lt m q h _ lk k ln))))

(def-fns _ $ (erased rc-al : (erased (List (Tr)) m) (erased (Conf) c d) (erased (Nat) s) (erased (List (Nat)) xs) (subterm erased (Rcd m c d s xs) rc)
    (erased (Nat) S Q D2 E1 NB) (erased (Csz d S) zd) (erased (Length (Tr) m Q) ln) (erased (Double S D2) d2) (erased (Add Q (Succ (Succ D2)) E1) ae)
    (erased (Pow2 (Succ (Succ (Succ (Succ (Succ E1))))) NB) pn) -> (erased (Al NB xs) a))
  (let ((erased n) (erased z)) (csz-ex c))
  (let ((erased ns)) (hrun-sz m c d s (rc-hrun m c d s xs rc) n S z zd))
  (let-match erased rc (RCMove _ _ c1 _ s1 v xs1 st rc1 cd)
    ((RCStop _ q l r b lk v cd) (AlC NB v _ (code-lt q l r b v n S Q D2 E1 NB cd z ns (look-lt m q b _ lk Q ln) d2 ae pn) (AlN NB))))
  (let-match erased c (MkConf q l b r))
  (AlC NB v xs1 (code-lt q l r b v n S Q D2 E1 NB cd z ns (stp-lt m q l r b c1 st Q ln) d2 ae pn) (rc-al m c1 d s1 xs1 rc1 S Q D2 E1 NB zd ln d2 ae pn)))

(def-fns _ $ (erased hrun-up : (erased (List (Tr)) m) (erased (Conf) c d) (erased (Nat) s) (erased (HRun m c d s) h) (erased (Nat) S Q D2 E1 NB)
    (erased (Csz d S) zd) (erased (Length (Tr) m Q) ln) (erased (Double S D2) d2) (erased (Add Q (Succ (Succ D2)) E1) ae)
    (erased (Pow2 (Succ (Succ (Succ (Succ (Succ E1))))) NB) pn) -> (erased (Lt s (Succ NB)) lt))
  (let ((erased xs) (erased rc)) (rcd-of m c d s h))
  (pigeon NB s xs (rc-dn m c d s xs rc) (rc-al m c d s xs rc S Q D2 E1 NB zd ln d2 ae pn) (rc-len m c d s xs rc)))

(def-fns _ $ (erased le-lt-trans : (erased (Nat) a b c) (erased (Lt a (Succ b)) p) (erased (Lt b c) q) -> (erased (Lt a c) r))
  (lt-le-trans a (Succ b) c p (LtS b c q)))

(def-fns _ $ (erased dbl-gt : (erased (Nat) v d) (erased (Double v d) dd) (erased (Lt (Zero) v) pos) -> (erased (Lt v d) r))
  (let-match erased dd (DS v1 d1 dd1) (absurd (D0) pos))
  (LtS v1 (Succ d1) (double-lt v1 d1 dd1)))

(def-fns _ $ (erased dbl-add : (subterm erased (Nat) v) (erased (Nat) d) (erased (Double v d) dd) -> (erased (Add v v d) a))
  (let-match erased dd (DS v1 d1 dd1) ((D0) (AddZero (Zero))))
  (AddSucc v1 (Succ v1) (Succ d1) (add-succ-right v1 v1 d1 (dbl-add v1 d1 dd1))))

(def-fns _ $ (erased pow2-gt : (erased (Nat) x p) (subterm erased (Pow2 x p) pp) -> (erased (Lt x p) r))
  (let-match erased pp (PS x1 p1 _ pp1 d) ((P0) (LtZ (Zero))))
  (le-lt-trans (Succ x1) p1 p (LtS x1 p1 (pow2-gt x1 p1 pp1)) (dbl-gt p1 p d (pow2-pos x1 p1 pp1))))

(def-fns _ $ (erased pow2-le : (erased (Nat) x y p q) (erased (Lt x (Succ y)) l) (erased (Pow2 x p) pp) (erased (Pow2 y q) pq) -> (erased (Lt p (Succ q)) r))
  (let-match erased (lt-succ-cases x y l) (InR _ _ l2) ((InL _ _ e) (let-match erased e (Refl _ _)) (let-match erased (pow2-fn x p q pp pq) (Refl _ _)) (lt-succ p)))
  (lt-weaken p q (pow2-lt x y p q l2 pp pq)))

(def-fns _ $ (erased pw-c : (subterm erased (Nat) T) (erased (Nat) D P) (erased (Lt (Succ (Succ (Succ (Zero)))) T) l) (erased (Double T D) dd) (erased (Pow2 T P) pp) ->
    (erased (Lt (Succ (Succ D)) P) r))
  (let-match erased T (Succ T1) (absurd (Zero) l))
  (let-match erased dd (DS _ D1 dd1))
  (let-match erased pp (PS _ P1 _ pp1 dP))
  (let-match erased (lt-succ-cases _ T1 l) (InR _ _ l2)
    ((InL _ _ e)
      (let-match erased e (Refl _ _))
      (let-match erased dd1 (DS _ _ dd2)) (let-match erased dd2 (DS _ _ dd3)) (let-match erased dd3 (DS _ _ dd4)) (let-match erased dd4 (D0))
      (let-match erased pp1 (PS _ _ _ pp2 d2)) (let-match erased pp2 (PS _ _ _ pp3 d3)) (let-match erased pp3 (PS _ _ _ pp4 d4)) (let-match erased pp4 (P0))
      (let-match erased d4 (DS _ _ d4a)) (let-match erased d4a (D0))
      (let-match erased d3 (DS _ _ d3a)) (let-match erased d3a (DS _ _ d3b)) (let-match erased d3b (D0))
      (let-match erased d2 (DS _ _ d2a)) (let-match erased d2a (DS _ _ d2b)) (let-match erased d2b (DS _ _ d2c)) (let-match erased d2c (DS _ _ d2d)) (let-match erased d2d (D0))
      (let-match erased dP (DS _ _ e1)) (let-match erased e1 (DS _ _ e2)) (let-match erased e2 (DS _ _ e3)) (let-match erased e3 (DS _ _ e4))
      (let-match erased e4 (DS _ _ e5)) (let-match erased e5 (DS _ _ e6)) (let-match erased e6 (DS _ _ e7)) (let-match erased e7 (DS _ _ e8)) (let-match erased e8 (D0))
      (LtS _ _ $ LtS _ _ $ LtS _ _ $ LtS _ _ $ LtS _ _ $ LtS _ _ $ LtS _ _ $ LtS _ _ $ LtS _ _ $ LtS _ _ (LtZ _))))
  (let ((erased ih)) (pw-c T1 D1 P1 l2 dd1 pp1))
  (let ((erased E) (erased dE)) (dbl-ex D1))
  (le-lt-trans _ _ P (LtS _ _ $ LtS _ _ $ LtS _ _ $ LtS _ _ (double-lt D1 E dE))
    (double-mono (Succ (Succ D1)) P1 (Succ (Succ (Succ (Succ E)))) P ih (DS _ _ (DS _ _ dE)) dP)))

(def-fns _ $ (erased add-le2 : (erased (Nat) x x2 y y2 z z2) (erased (Lt x (Succ x2)) lx) (erased (Lt y (Succ y2)) ly) (erased (Add x y z) a) (erased (Add x2 y2 z2) a2) ->
    (erased (Lt z (Succ z2)) r))
  (let ((erased w) (erased aw)) (add-ex x2 y))
  (le-tr z w z2 (add-mono x x2 y z w a aw lx) (add-mono y y2 x2 w z2 (add-comm _ _ _ aw) (add-comm _ _ _ a2) ly)))

(def-fns _ $ (erased dbl-gt2 : (erased (Nat) v d) (erased (Double v d) dd) (erased (Lt (Succ (Zero)) v) l) -> (erased (Lt (Succ v) d) r))
  (let-match erased dd (DS v1 d1 dd1) (absurd (D0) l))
  (let-match erased l (LtS _ _ l1))
  (LtS _ _ (LtS _ _ (dbl-gt v1 d1 dd1 l1))))

(def-fns _ $ (erased low : (erased (Nat) T b T2 b2 P) (erased (Lt (Succ (Zero)) T) l1) (erased (Lt T b) lt) (erased (Pow2 T T2) p1) (erased (Pow2 b P) p2)
    (erased (Lt P (Succ (Succ b2))) lp) -> (erased (Lt T2 b2) r))
  (let ((erased W) (erased dW)) (dbl-ex T2))
  (let ((erased lw)) (le-tr W P (Succ b2) (pow2-le (Succ T) b W P (LtS T b lt) (PS T T2 W p1 dW) p2) lp))
  (let ((erased l3)) (dbl-gt2 T2 W dW (lt-trans _ T T2 l1 (pow2-gt T T2 p1))))
  (let-match erased (lt-le-trans (Succ T2) W (Succ b2) l3 lw) (LtS _ _ r))
  r)

(def-adts
  ((Tw : ((Nat) k x y) -> Type)
    enum
    (many TwZ : (erased (Nat) x) -> (Tw (Zero) x x))
    (many TwS : (erased (Nat) k x y z) (erased (Tw k x y) t) (erased (Pow2 y z) p) -> (Tw (Succ k) x z))))

(def-fns _ $ (erased tw-ex : (subterm erased (Nat) k) (erased (Nat) x) -> (erased (Nat) y) (erased (Tw k x y) t))
  (let-match erased k (Succ k2) ((Zero) (values x (TwZ x))))
  (let ((erased y1) (erased t1)) (tw-ex k2 x))
  (let ((erased y) (erased p)) (pow2-ex y1))
  (values y (TwS k2 x y1 y t1 p)))

(def-fns _ $ (erased tw-fn : (erased (Nat) k x y y2) (subterm erased (Tw k x y) t) (erased (Tw k x y2) t2) -> (erased (Eq (Nat) y y2) e))
  (let-match erased t (TwS k2 _ y1 _ t1 p) ((TwZ _) (let-match erased t2 (TwZ _)) (Refl _ y)))
  (let-match erased t2 (TwS _ _ y3 _ t3 p3))
  (let-match erased (tw-fn k2 x y1 y3 t1 t3) (Refl _ _))
  (pow2-fn y1 y y2 p p3))

(def-fns _ $ (erased tw-lt-h : (erased (Nat) h h2 x y y2) (erased (Lt h h2) l) (erased (Tw h x y) t) (subterm erased (Tw h2 x y2) t2) -> (erased (Lt y y2) r))
  (let-match erased t2 (TwS k2 _ y1 _ t1 p) (absurd (TwZ _) l))
  (let ((erased g)) (pow2-gt y1 y2 p))
  (let-match erased (lt-succ-cases h k2 l) (InR _ _ l2) ((InL _ _ e) (let-match erased e (Refl _ _)) (let-match erased (tw-fn h x y y1 t t1) (Refl _ _)) g))
  (lt-trans y y1 y2 (tw-lt-h h k2 x y y1 l2 t t1) g))

(def-fns _ $ (erased tw-le-h : (erased (Nat) h h2 x y y2) (erased (Lt h (Succ h2)) l) (erased (Tw h x y) t) (erased (Tw h2 x y2) t2) -> (erased (Lt y (Succ y2)) r))
  (let-match erased (lt-succ-cases h h2 l) (InR _ _ l2) ((InL _ _ e) (let-match erased e (Refl _ _)) (let-match erased (tw-fn h x y y2 t t2) (Refl _ _)) (lt-succ y)))
  (lt-weaken y y2 (tw-lt-h h h2 x y y2 l2 t t2)))

(def-fns _ $ (erased tw-le-b : (erased (Nat) k x x2 y y2) (erased (Lt x (Succ x2)) l) (subterm erased (Tw k x y) t) (erased (Tw k x2 y2) t2) -> (erased (Lt y (Succ y2)) r))
  (let-match erased t (TwS kq _ y1 _ t1 p) ((TwZ _) (let-match erased t2 (TwZ _)) l))
  (let-match erased t2 (TwS _ _ y3 _ t3 p3))
  (pow2-le y1 y3 y y2 (tw-le-b kq x x2 y1 y3 l t1 t3) p p3))

(def-fns _ $ (erased tw-add : (erased (Nat) k k2 k3 x y z) (erased (Tw k x y) t) (subterm erased (Tw k2 y z) t2) (erased (Add k2 k k3) a) -> (erased (Tw k3 x z) r))
  (let-match erased t2 (TwS kq _ z1 _ t1 p) ((TwZ _) (let-match erased a (AddZero _)) t))
  (let-match erased a (AddSucc _ _ k4 a1))
  (TwS k4 x z1 z (tw-add k kq k4 x y z1 t t1 a1) p))

(def-fns _ $ (erased tw-gt-h : (erased (Nat) n v) (subterm erased (Tw n (Succ (Zero)) v) t) -> (erased (Lt n v) r))
  (let-match erased t (TwS n1 _ v1 _ t1 p) ((TwZ _) (LtZ (Zero))))
  (le-lt-trans (Succ n1) v1 v (LtS n1 v1 (tw-gt-h n1 v1 t1)) (pow2-gt v1 v p)))

(def-fns _ $ (erased tw-gap : (erased (Nat) k a b x y) (subterm erased (Tw k a x) t) (erased (Tw k b y) t2)
    (erased (Lt (Succ (Succ (Succ (Succ a)))) (Succ b)) l) -> (erased (Lt (Succ (Succ (Succ (Succ x)))) (Succ y)) r))
  (let-match erased t (TwS kq _ x1 _ t1 p) ((TwZ _) (let-match erased t2 (TwZ _)) l))
  (let-match erased t2 (TwS _ _ y1 _ t3 p3))
  (let ((erased l1)) (tw-gap kq a b x1 y1 t1 t3 l))
  (let ((erased a1) (erased d1)) (dbl-ex x))
  (let ((erased a2) (erased d2)) (dbl-ex a1))
  (let ((erased a3) (erased d3)) (dbl-ex a2))
  (let ((erased a4) (erased d4)) (dbl-ex a3))
  (let ((erased px)) (pow2-pos x1 x p))
  (let ((erased g1)) (dbl-gt x a1 d1 px))
  (let ((erased g2)) (dbl-gt a1 a2 d2 (lt-trans _ x a1 px g1)))
  (let ((erased g3)) (dbl-gt a2 a3 d3 (lt-trans _ a1 a2 (lt-trans _ x a1 px g1) g2)))
  (let ((erased g4)) (dbl-gt a3 a4 d4 (lt-trans _ a2 a3 (lt-trans _ a1 a2 (lt-trans _ x a1 px g1) g2) g3)))
  (let ((erased h2)) (le-lt-trans (Succ x) a1 a2 (LtS _ _ g1) g2))
  (let ((erased h3)) (le-lt-trans (Succ (Succ x)) a2 a3 (LtS _ _ h2) g3))
  (let ((erased h4)) (le-lt-trans (Succ (Succ (Succ x))) a3 a4 (LtS _ _ h3) g4))
  (le-tr _ a4 y (LtS _ _ h4)
    (pow2-le (Succ (Succ (Succ (Succ x1)))) y1 a4 y l1 (PS _ _ _ (PS _ _ _ (PS _ _ _ (PS _ _ _ p d1) d2) d3) d4) p3)))

(def-adts
  ((Sm : ((Nat) x T) -> Type)
    enum
    (many MkSm : (erased (Nat) x T P) (erased (Pow2 T P) p) (erased (Lt x (Succ P)) l) -> (Sm x T))))

(def-fns _ $ (erased sm-of : (erased (Nat) x T) (erased (Lt x (Succ (Succ T))) l) -> (erased (Sm x T) s))
  (let ((erased P) (erased p)) (pow2-ex T))
  (MkSm x T P p (le-tr x (Succ T) P l (LtS T P (pow2-gt T P p)))))

(def-fns _ $ (erased sm-add : (erased (Nat) x y z T) (erased (Sm x T) sx) (erased (Sm y T) sy) (erased (Add x y z) a) -> (erased (Sm z (Succ T)) s))
  (let-match erased sx (MkSm _ _ P p lx))
  (let-match erased sy (MkSm _ _ P2 p2 ly))
  (let-match erased (pow2-fn T P2 P p2 p) (Refl _ _))
  (let ((erased D) (erased d)) (dbl-ex P))
  (MkSm z (Succ T) D (PS T P D p d) (add-le2 x P y P z D lx ly a (dbl-add P D d))))

(def-fns _ $ (erased sm-mono : (erased (Nat) x T T2) (erased (Lt T (Succ T2)) l) (erased (Sm x T) s) -> (erased (Sm x T2) s2))
  (let-match erased s (MkSm _ _ P p lx))
  (let ((erased P2) (erased p2)) (pow2-ex T2))
  (MkSm x T2 P2 p2 (le-tr x P P2 lx (pow2-le T T2 P P2 l p p2))))

(def-fns _ $ (erased add-sh : (erased (Nat) x y z) (erased (Add x (Succ y) z) p) -> (erased (Add (Succ x) y z) q))
  (let ((erased z1) (erased e) (erased q1)) (add-succ-right-inv x y z p))
  (let-match erased e (Refl _ _))
  (AddSucc x y z1 q1))

(def-fns _ $ (erased dbl-lq : (erased (Nat) a b c d) (erased (Lt a (Succ b)) l) (erased (Double a c) p) (erased (Double b d) q) -> (erased (Lt c (Succ d)) r))
  (let-match erased (lt-succ-cases a b l) (InR _ _ l2) ((InL _ _ e) (let-match erased e (Refl _ _)) (let-match erased (double-fn a c d p q) (Refl _ _)) (lt-succ c)))
  (lt-weaken c d (double-mono a b c d l2 p q)))

(def-adts
  ((Th : ((Nat) n m) -> Type)
    enum
    (many ThZ : -> (Th (Zero) (Zero)))
    (many ThS : (erased (Nat) n m) (erased (Th n m) p) -> (Th (Succ n) (Succ (Succ (Succ m)))))))

(def-fns _ $ (erased th-add : (erased (Nat) n m) (subterm erased (Th n m) t) -> (erased (Nat) d) (erased (Double n d) dd) (erased (Add d n m) a))
  (let-match erased t (ThS n1 m1 t1) ((ThZ) (values (Zero) (D0) (AddZero (Zero)))))
  (let ((erased d1) (erased dd1) (erased a1)) (th-add n1 m1 t1))
  (values (Succ (Succ d1)) (DS n1 d1 dd1) (AddSucc _ _ _ (AddSucc _ _ _ (add-succ-right d1 n1 m1 a1)))))

(def-fns _ $ (erased th-sm : (erased (Nat) n m T) (erased (Th n m) t) (erased (Sm n T) s) -> (erased (Sm m (Succ (Succ T))) s2))
  (let ((erased d) (erased dd) (erased a)) (th-add n m t))
  (let ((erased sd)) (sm-add n n d T s s (dbl-add n d dd)))
  (sm-add d n m (Succ T) sd (sm-mono n T (Succ T) (lt-weaken _ _ (lt-succ T)) s) a))
