(def-adts $ (Rn : -> Type)
  enum
  (many MkRn : (many (Bool) b) (many (Nat) n) -> (Rn)))

(def-adts
  ((Rp : ((Bool) b) ((Nat) n) ((List (Bool)) t x) -> Type)
    enum
    (many RpZ : (erased (Bool) b) (erased (List (Bool)) t) -> (Rp b (Zero) t t))
    (many RpS : (erased (Bool) b) (erased (Nat) n) (erased (List (Bool)) t x) (erased (Rp b n t x) p) -> (Rp b (Succ n) t (Cons (Bool) b x)))))

(def-adts
  ((Den : ((List (Rn)) L) ((List (Bool)) x) -> Type)
    enum
    (many DeN : -> (Den (Nil (Rn)) (Nil (Bool))))
    (many DeC : (erased (Bool) b) (erased (Nat) n) (erased (List (Rn)) L) (erased (List (Bool)) t x) (erased (Den L t) d) (erased (Rp b n t x) p)
       -> (Den (Cons (Rn) (MkRn b n) L) x))))

(def-adts $ (Rq : -> Type)
  enum
  (many MkRq : (many (Nat) q) (many (List (Rn)) L) (many (Bool) h) (many (List (Rn)) R) -> (Rq)))

(def-adts
  ((Dc : ((Rq) e) ((Conf) c) -> Type)
    enum
    (many MkDc : (erased (Nat) q) (erased (List (Rn)) L R) (erased (Bool) h) (erased (List (Bool)) l r) (erased (Den L l) dl) (erased (Den R r) dr)
       -> (Dc (MkRq q L h R) (MkConf q l h r)))))

(def-adts
  ((Rch : ((List (Tr)) m) ((Conf) c0) ((Rq) e) -> Type)
    enum
    (many MkRch : (erased (List (Tr)) m) (erased (Conf) c0 a c) (erased (Rq) e) (erased (Nat) t) (erased (Run m c0 t a) r) (erased (Dc e c) d)
       (erased (CEz c a) z) -> (Rch m c0 e))))

(def-adts
  ((NoHaltBelow : ((List (Tr)) m) ((Conf) c0) ((Nat) n) -> Type)
    enum
    (many MkNHB : (erased (List (Tr)) m) (erased (Conf) c0) (erased (Nat) n) (erased (Level) lv)
       (erased (Fn lv (erased (Nat) k) (erased (HaltsAt m c0 k) h) -> (erased (Lt n k) p)) f) -> (NoHaltBelow m c0 n))))

(def-adts
  ((LookR : ((List (Tr)) m) ((Nat) q) ((Bool) b) -> Type)
    enum
    (many LkOk : (erased (List (Tr)) m) (erased (Nat) q) (erased (Bool) b) (many (Tr) t) (erased (Look m q b t) lk) -> (LookR m q b))
    (many LkNo : (erased (List (Tr)) m) (erased (Nat) q) (erased (Bool) b) -> (LookR m q b))))

(def-fns _ $ (many tlook : (subterm many (List (Tr)) m) (many (Nat) q) (many (Bool) b) -> (many (LookR m q b) r))
  (let-match many m (Cons _ t0 m1) ((Nil _) (LkNo m q b)))
  (let-match many m1 (Cons _ t1 rest) ((Nil _) (LkNo m q b)))
  (match many q _
    ((Zero)
      (match many b _
        ((BFalse) (LkOk m q b t0 (Look0 t0 t1 rest)))
        ((BTrue) (LkOk m q b t1 (Look1 t0 t1 rest)))))
    ((Succ q1)
      (match many (notail $ tlook rest q1 b) _
        ((LkOk _ _ _ t lk) (LkOk m q b t (LookS t0 t1 rest q1 b t lk)))
        ((LkNo _ _ _) (LkNo m q b))))))

(def-adts
  ((Span : ((List (Tr)) m) ((Conf) c0) ((Nat) n) -> Type)
    enum
    (many MkSpan : (erased (List (Tr)) m) (erased (Conf) c0 a) (erased (Nat) n t) (erased (Run m c0 t a) r) (erased (Lt n (Succ t)) le)
       -> (Span m c0 n))))

(def-adts
  ((Rs : ((List (Tr)) m) ((Conf) c0) -> Type)
    enum
    (many RsOk : (erased (List (Tr)) m) (erased (Conf) c0) (many (Rq) e) (erased (Rch m c0 e) ch) -> (Rs m c0))
    (many RsNo : (erased (List (Tr)) m) (erased (Conf) c0) (many (Rq) e) (erased (Rch m c0 e) ch) -> (Rs m c0))))

(def-adts
  ((Last1 : ((List (Bool)) x) -> Type)
    enum
    (many L1H : -> (Last1 (Cons (Bool) (BTrue) (Nil (Bool)))))
    (many L1C : (erased (Bool) b) (erased (List (Bool)) x) (erased (Last1 x) p) -> (Last1 (Cons (Bool) b x)))))

(def-adts
  ((Trim : ((List (Bool)) x) -> Type)
    enum
    (many TrN : -> (Trim (Nil (Bool))))
    (many TrL : (erased (List (Bool)) x) (erased (Last1 x) p) -> (Trim x))))

(def-fns _ $ (erased rp-fn : (erased (Bool) b) (erased (Nat) n) (erased (List (Bool)) t x y) (subterm erased (Rp b n t x) p) (erased (Rp b n t y) q)
    -> (erased (Eq (List (Bool)) x y) e))
  (match erased p _
    ((RpZ _ _) (let-match erased q (RpZ _ _)) (Refl _ x))
    ((RpS _ n1 _ x1 p1) (let-match erased q (RpS _ _ _ y1 q1)) (let-match erased (rp-fn b n1 t x1 y1 p1 q1) (Refl _ _)) (Refl _ x))))

(def-fns _ $ (erased den-fn : (erased (List (Rn)) L) (erased (List (Bool)) x y) (subterm erased (Den L x) p) (erased (Den L y) q)
    -> (erased (Eq (List (Bool)) x y) e))
  (match erased p _
    ((DeN) (let-match erased q (DeN)) (Refl _ x))
    ((DeC b n L1 t _ p1 r1)
      (let-match erased q (DeC _ _ _ t2 _ q1 r2))
      (let-match erased (den-fn L1 t t2 p1 q1) (Refl _ _))
      (rp-fn b n t x y r1 r2))))

(def-fns _ $ (erased dc-fn : (erased (Rq) e) (erased (Conf) c d) (erased (Dc e c) p) (erased (Dc e d) q) -> (erased (Eq (Conf) c d) r))
  (let-match erased p (MkDc q0 L R h l r dl dr))
  (let-match erased q (MkDc _ _ _ _ l2 r2 dl2 dr2))
  (let-match erased (den-fn L l l2 dl dl2) (Refl _ _))
  (let-match erased (den-fn R r r2 dr dr2) (Refl _ _))
  (Refl _ c))

(def-fns _ $ (erased run-eqz : (erased (List (Tr)) m) (erased (Conf) c d a) (erased (Nat) s) (subterm erased (Run m c s d) r) (erased (CEz c a) z)
    -> (erased (Conf) a2) (erased (Run m a s a2) r2) (erased (CEz d a2) z2))
  (let-match erased r (RSnoc _ _ c1 _ s1 r1 st) ((RNil _ _) (values a (RNil m a) z)))
  (let ((erased a1) (erased q1) (erased z1)) (run-eqz m c c1 a s1 r1 z))
  (let ((erased a2) (erased st2) (erased z2)) (stp-eqz m c1 a1 d st z1))
  (values a2 (RSnoc m a a1 a2 s1 q1 st2) z2))

(def-fns _ $ (erased run-cat : (erased (List (Tr)) m) (erased (Conf) c0 a b) (erased (Nat) t s) (erased (Run m c0 t a) r1) (subterm erased (Run m a s b) r2)
    -> (erased (Nat) u) (erased (Run m c0 u b) r))
  (let-match erased r2 (RSnoc _ _ b1 _ s1 q1 st) ((RNil _ _) (values t r1)))
  (let ((erased u1) (erased p1)) (run-cat m c0 a b1 t s1 r1 q1))
  (values (Succ u1) (RSnoc m c0 b1 b u1 p1 st)))

(def-fns _ $ (erased rch-run : (erased (List (Tr)) m) (erased (Conf) c0 c d) (erased (Rq) e e2) (erased (Nat) s)
    (erased (Rch m c0 e) ch) (erased (Dc e c) dc) (erased (Run m c s d) r) (erased (Dc e2 d) dc2) -> (erased (Rch m c0 e2) ch2))
  (let-match erased ch (MkRch _ _ a c1 _ t r0 dc1 z))
  (let-match erased (dc-fn e c c1 dc dc1) (Refl _ _))
  (let ((erased a2) (erased r2) (erased z2)) (run-eqz m c d a s r z))
  (let ((erased u) (erased r3)) (run-cat m c0 a a2 t s r0 r2))
  (MkRch m c0 a2 d e2 u r3 dc2 z2))

(def-fns _ $ (erased rch-stp : (erased (List (Tr)) m) (erased (Conf) c0 c d) (erased (Rq) e e2)
    (erased (Rch m c0 e) ch) (erased (Dc e c) dc) (erased (Stp m c d) st) (erased (Dc e2 d) dc2) -> (erased (Rch m c0 e2) ch2))
  (rch-run m c0 c d e e2 (Succ (Zero)) ch dc (RSnoc m c c d (Zero) (RNil m c) st) dc2))

(def-fns _ $ (many push : (many (Bool) w) (many (List (Rn)) L) (erased (List (Bool)) x) (erased (Den L x) d) ->
    (many (List (Rn)) L2) (erased (Den L2 (Cons (Bool) w x)) d2))
  (let ((many fresh)) (Cons _ (MkRn w (Succ (Zero))) L))
  (let ((erased dfresh)) (DeC w (Succ (Zero)) L x (Cons (Bool) w x) d (RpS w (Zero) x x (RpZ w x))))
  (let-match many L (Cons _ rn L1) ((Nil _) (values fresh dfresh)))
  (let-match many rn (MkRn b n))
  (let-match many (eq-bit w b) (ESome _ eq) ((ENone _) (values fresh dfresh)))
  (let-match erased eq (Refl _ _))
  (let-match erased d (DeC _ _ _ t _ d1 p))
  (values (Cons _ (MkRn b (Succ n)) L1) (DeC b (Succ n) L1 t (Cons (Bool) w x) d1 (RpS b n t x p))))

(def-fns _ $ (many rpop : (subterm many (List (Rn)) L) (erased (List (Bool)) x) (erased (Den L x) d) ->
    (many (Bool) h) (many (List (Rn)) L2) (erased (List (Bool)) y) (many (Pull x h y) pp) (erased (Den L2 y) d2))
  (let-match many L (Cons _ rn L1) ((Nil _) (let-match erased d (DeN)) (values (BFalse) L (Nil (Bool)) (PullNil) (DeN))))
  (let-match many rn (MkRn b n))
  (let-match erased d (DeC _ _ _ t _ d1 p))
  (match many n _
    ((Zero) (let-match erased p (RpZ _ _)) (tail $ rpop L1 x d1))
    ((Succ n1)
      (let-match erased p (RpS _ _ _ x1 p1))
      (let-match many (nat-zero-dec n1) (IsZero) ((IsSucc _) (values b (Cons _ (MkRn b n1) L1) x1 (PullCons b x1) (DeC b n1 L1 t x1 d1 p1))))
      (let-match erased p1 (RpZ _ _))
      (values b L1 x1 (PullCons b x1) d1))))

(def-fns _ $ (many rstep : (many (List (Tr)) m) (erased (Conf) c0) (many (Rq) e) (erased (Rch m c0 e) ch) -> (many (Rs m c0) r))
  (let-match erased ch (MkRch _ _ a c _ t r0 dc z))
  (let-match many e (MkRq q L h R))
  (let-match erased dc (MkDc _ _ _ _ l r dl dr))
  (let-match many (tlook m q h) (LkOk _ _ _ tr lk) ((LkNo _ _ _) (RsNo m c0 e ch)))
  (let-match many tr (Mov w d q2) ((Hlt) (RsNo m c0 e ch)))
  (match many d _
    ((DR)
      (let ((many L2) (erased dl2)) (push w L l dl))
      (let ((many h2) (many R2) (erased r2) (erased pp) (erased dr2)) (rpop R r dr))
      (let ((many e2)) (MkRq q2 L2 h2 R2))
      (RsOk m c0 e2 (rch-stp m c0 c _ e e2 ch dc (StepR m q q2 l r r2 h w h2 lk pp) (MkDc q2 L2 R2 h2 (Cons (Bool) w l) r2 dl2 dr2))))
    ((DL)
      (let ((many R2) (erased dr2)) (push w R r dr))
      (let ((many h2) (many L2) (erased l2) (erased pp) (erased dl2)) (rpop L l dl))
      (let ((many e2)) (MkRq q2 L2 h2 R2))
      (RsOk m c0 e2 (rch-stp m c0 c _ e e2 ch dc (StepL m q q2 l r l2 h w h2 lk pp) (MkDc q2 L2 R2 h2 l2 (Cons (Bool) w r) dl2 dr2))))))

(def-fns _ $ (erased rp-ex : (erased (Bool) b) (subterm erased (Nat) n) (erased (List (Bool)) t) -> (erased (List (Bool)) x) (erased (Rp b n t x) p))
  (let-match erased n (Succ n1) ((Zero) (values t (RpZ b t))))
  (let ((erased x1) (erased p1)) (rp-ex b n1 t))
  (values (Cons (Bool) b x1) (RpS b n1 t x1 p1)))

(def-fns _ $ (erased rp-eqz : (erased (Bool) b) (erased (Nat) n) (erased (List (Bool)) t t2 x y) (subterm erased (Rp b n t x) p) (erased (Rp b n t2 y) q)
    (erased (Eqz t t2) e) -> (erased (Eqz x y) f))
  (let-match erased p (RpS _ n1 _ x1 p1) ((RpZ _ _) (let-match erased q (RpZ _ _)) e))
  (let-match erased q (RpS _ _ _ y1 q1))
  (EC b x1 y1 (rp-eqz b n1 t t2 x1 y1 p1 q1 e)))

(def-fns _ $ (erased rp-zeros : (erased (Nat) n) (erased (List (Bool)) t x) (subterm erased (Rp (BFalse) n t x) p) (erased (Zeros t) z) -> (erased (Zeros x) zx))
  (let-match erased p (RpS _ n1 _ x1 p1) ((RpZ _ _) z))
  (ZC x1 (rp-zeros n1 t x1 p1 z)))

(def-fns _ $ (erased rp-last : (erased (Bool) b) (erased (Nat) n) (erased (List (Bool)) t x) (subterm erased (Rp b n t x) p) (erased (Last1 t) l) -> (erased (Last1 x) lx))
  (let-match erased p (RpS _ n1 _ x1 p1) ((RpZ _ _) l))
  (L1C b x1 (rp-last b n1 t x1 p1 l)))

(def-fns _ $ (erased rp-one : (erased (Nat) n) (erased (List (Bool)) x) (subterm erased (Rp (BTrue) (Succ n) (Nil (Bool)) x) p) -> (erased (Last1 x) lx))
  (let-match erased p (RpS _ _ _ x1 p1))
  (let-match erased p1 (RpS _ n2 _ x2 p2) ((RpZ _ _) (L1H)))
  (L1C (BTrue) x1 (rp-one n2 x1 p1)))

(def-fns _ $ (erased rp-len : (erased (Bool) b) (erased (Nat) n k s) (erased (List (Bool)) t x) (subterm erased (Rp b n t x) p) (erased (Length (Bool) t k) l)
    (erased (Add n k s) a) -> (erased (Length (Bool) x s) lx))
  (let-match erased p (RpS _ n1 _ x1 p1) ((RpZ _ _) (let-match erased a (AddZero _)) l))
  (let-match erased a (AddSucc _ _ s1 a1))
  (LengthCons (Bool) b x1 s1 (rp-len b n1 k s1 t x1 p1 l a1)))

(def-fns _ $ (erased absurd last-zeros : (erased (List (Bool)) x) (subterm erased (Last1 x) l) (erased (Zeros x) z) -> (erased (False) f))
  (match erased l _
    (absurd (L1H) z)
    (absurd (L1C _ x1 l1) (let-match erased z (ZC _ z1)) (last-zeros x1 l1 z1))))

(def-fns _ $ (erased eqz-len : (erased (List (Bool)) x y) (erased (Nat) n k) (subterm erased (Eqz x y) e) (erased (Last1 x) l)
    (erased (Length (Bool) x n) lx) (erased (Length (Bool) y k) ly) -> (erased (Lt n (Succ k)) r))
  (let-match erased e (EC b x1 y1 e1) (absurd (EZ _ _ zx _) (last-zeros x l zx)))
  (let-match erased lx (LengthCons _ _ _ n1 lx1))
  (let-match erased ly (LengthCons _ _ _ k1 ly1))
  (let-match erased l (L1C _ _ l1)
    ((L1H) (let-match erased lx1 (LengthNil _)) (LtS (Zero) (Succ k1) (LtZ k1))))
  (LtS n1 (Succ k1) (eqz-len x1 y1 n1 k1 e1 l1 lx1 ly1)))

(def-fns _ $ (erased rtrim-len : (erased (List (Bool)) x y) (erased (Nat) n k) (erased (Eqz x y) e) (erased (Trim x) tr)
    (erased (Length (Bool) x n) lx) (erased (Length (Bool) y k) ly) -> (erased (Lt n (Succ k)) r))
  (let-match erased tr (TrL _ l) ((TrN) (let-match erased lx (LengthNil _)) (LtZ k)))
  (eqz-len x y n k e l lx ly))

(def-fns _ $ (many rtrim : (subterm many (List (Rn)) L) (erased (List (Bool)) x) (erased (Den L x) d) ->
    (many (List (Rn)) L2) (erased (List (Bool)) y) (erased (Den L2 y) d2) (erased (Eqz x y) ez) (many (Trim y) tr))
  (let-match many L (Cons _ rn L1) ((Nil _) (let-match erased d (DeN)) (values L (Nil (Bool)) (DeN) (EZ _ _ (ZN) (ZN)) (TrN))))
  (let-match many rn (MkRn b n))
  (let-match erased d (DeC _ _ _ t _ d1 p))
  (let ((many L3) (erased y1) (erased d3) (erased e1) (many tr1)) (notail $ rtrim L1 t d1))
  (let ((erased y) (erased py)) (rp-ex b n y1))
  (let ((many keep)) (Cons _ rn L3))
  (let ((erased dk)) (DeC b n L3 y1 y d3 py))
  (let ((erased ek)) (rp-eqz b n t y1 x y p py e1))
  (let-match many tr1 (TrN) ((TrL _ l1) (values keep y dk ek (TrL y (rp-last b n y1 y py l1)))))
  (let-match many b (BTrue)
    ((BFalse) (values (Nil _) (Nil (Bool)) (DeN) (EZ _ _ (rp-zeros n t x p (eqz-zeros y1 t (eqz-sym t y1 e1) (ZN))) (ZN)) (TrN))))
  (let-match many n (Succ n1) ((Zero) (let-match erased p (RpZ _ _)) (values (Nil _) (Nil (Bool)) (DeN) e1 (TrN))))
  (values keep y dk ek (TrL y (rp-one n1 y py))))

(def-fns _ $ (many rsum : (subterm many (List (Rn)) L) (erased (List (Bool)) x) (erased (Den L x) d) -> (many (Nat) n) (erased (Length (Bool) x n) l))
  (let-match many L (Cons _ rn L1) ((Nil _) (let-match erased d (DeN)) (values (Zero) (LengthNil (Bool)))))
  (let-match many rn (MkRn b k))
  (let-match erased d (DeC _ _ _ t _ d1 p))
  (let ((many n1) (erased l1)) (notail $ rsum L1 t d1))
  (let ((many n) (erased a)) (add k n1))
  (values n (rp-len b k n1 n t x p l1 a)))

(def-fns _ $ (erased run-csz : (erased (List (Tr)) m) (erased (Conf) c0 a) (erased (Nat) t) (subterm erased (Run m c0 t a) r) (erased (Csz c0 (Zero)) z0)
    -> (erased (Nat) S) (erased (Csz a S) z) (erased (Lt S (Succ t)) le))
  (let-match erased r (RSnoc _ _ c1 _ t1 r1 st) ((RNil _ _) (values (Zero) z0 (LtZ (Zero)))))
  (let ((erased S1) (erased z1) (erased le1)) (run-csz m c0 c1 t1 r1 z0))
  (let ((erased S2) (erased z2) (erased g)) (stp-sz m c1 a st S1 z1))
  (let-match erased g (GrS _) ((GrE _) (values S1 z2 (lt-weaken S1 (Succ t1) le1))))
  (values S2 z2 (LtS S1 (Succ t1) le1)))

(def-fns _ $ (erased run-halts : (erased (List (Tr)) m) (erased (Conf) c0 a) (erased (Nat) t k) (subterm erased (Run m c0 t a) r) (erased (HaltsAt m c0 k) h)
    -> (erased (Nat) v) (erased (HaltsAt m a v) ha) (erased (Add t v k) ad))
  (let-match erased r (RSnoc _ _ c1 _ t1 r1 st) ((RNil _ _) (values k h (AddZero k))))
  (let ((erased v1) (erased h1) (erased ad1)) (run-halts m c0 c1 t1 k r1 h))
  (let-match erased h1 (HMove _ _ d2 v2 st2 h2)
    (absurd (HStop _ q l rr b lk)
      (match erased st _
        (absurd (StepL _ _ _ _ _ _ _ _ _ lk2 _) (look-fn m q b _ _ lk lk2))
        (absurd (StepR _ _ _ _ _ _ _ _ _ lk2 _) (look-fn m q b _ _ lk lk2)))))
  (let-match erased (step-fn m c1 a d2 st st2) (Refl _ _))
  (values v2 h2 (add-shift t1 v2 k ad1)))

(def-fns _ $ (erased halts-pos : (erased (List (Tr)) m) (erased (Conf) c) (erased (Nat) v) (erased (HaltsAt m c v) h) -> (erased (Lt (Zero) v) p))
  (match erased h _
    ((HStop _ _ _ _ _ _) (LtZ (Zero)))
    ((HMove _ _ _ s _ _) (LtZ s))))

(def-fns _ $ (erased span-bound : (erased (List (Tr)) m) (erased (Conf) c0) (erased (Nat) n k) (erased (Span m c0 n) sp) (erased (HaltsAt m c0 k) h)
    -> (erased (Lt n k) p))
  (let-match erased sp (MkSpan _ _ a _ t r le))
  (let ((erased v) (erased ha) (erased ad)) (run-halts m c0 a t k r h))
  (lt-le-trans n (Succ t) k le (LtS t k (add-pos-lt t v k ad (halts-pos m a v ha)))))

(def-adts
  ((SpanR : ((List (Tr)) m) ((Conf) c0) ((Nat) n) -> Type)
    enum
    (many SpOk : (erased (List (Tr)) m) (erased (Conf) c0) (erased (Nat) n) (erased (Span m c0 n) sp) -> (SpanR m c0 n))
    (many SpLow : (erased (List (Tr)) m) (erased (Conf) c0) (erased (Nat) n) (many (Nat) got) -> (SpanR m c0 n))))

(def-fns _ $ (many span-check : (erased (List (Tr)) m) (many (Nat) N) (many (Rq) e) (erased (Rch m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) e) ch)
    -> (many (SpanR m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) N) r))
  (let-match erased ch (MkRch _ c0 a c _ t r0 dc z))
  (let-match many e (MkRq q L h R))
  (let-match erased dc (MkDc _ _ _ _ l r dl dr))
  (let-match erased z (MkCEz _ _ _ la ra _ el er))
  (let ((many L2) (erased yl) (erased dl2) (erased e1) (many t1)) (rtrim L l dl))
  (let ((many R2) (erased yr) (erased dr2) (erased e2) (many t2)) (rtrim R r dr))
  (let ((many nl) (erased ll)) (rsum L2 yl dl2))
  (let ((many nr) (erased lr)) (rsum R2 yr dr2))
  (let ((many n) (erased an)) (add nl nr))
  (let-match many (lt-dec N (Succ n)) (Yes _ _ _ _ big) ((No _ _ _ _ _) (SpLow m c0 N n)))
  (let ((erased kl) (erased lla)) (len-ex (Bool) la))
  (let ((erased kr) (erased lra)) (len-ex (Bool) ra))
  (let ((erased S) (erased aS)) (add-ex kl kr))
  (let ((erased S2) (erased z2) (erased le2)) (run-csz m c0 a t r0 (MkCsz (Zero) (Nil (Bool)) (Nil (Bool)) (BFalse) (Zero) (Zero) (Zero) (LengthNil _) (LengthNil _) (AddZero (Zero)))))
  (let-match erased (csz-fn a S S2 (MkCsz q la ra h kl kr S lla lra aS) z2) (Refl _ _))
  (let ((erased gl)) (rtrim-len yl la nl kl (eqz-trans yl l la (eqz-sym l yl e1) el) t1 ll lla))
  (let ((erased gr)) (rtrim-len yr ra nr kr (eqz-trans yr r ra (eqz-sym r yr e2) er) t2 lr lra))
  (let ((erased M) (erased aM)) (add-ex kl nr))
  (let ((erased gn)) (le-tr n M S (add-mono nl kl nr n M an aM gl) (add-mono nr kr kl M S (add-comm kl nr M aM) (add-comm kl kr S aS) gr)))
  (SpOk m c0 N (MkSpan m c0 a N t r0 (le-tr N n t big (le-tr n S t gn le2)))))

(def-fns _ $ (erased rch0 : (erased (List (Tr)) m) -> (erased (Rch m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) (MkRq (Zero) (Nil (Rn)) (BFalse) (Nil (Rn)))) ch))
  (let ((erased c0)) (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))))
  (MkRch m c0 c0 c0 _ (Zero) (RNil m c0) (MkDc (Zero) (Nil (Rn)) (Nil (Rn)) (BFalse) (Nil (Bool)) (Nil (Bool)) (DeN) (DeN))
    (MkCEz (Zero) (Nil (Bool)) (Nil (Bool)) (Nil (Bool)) (Nil (Bool)) (BFalse) (EZ _ _ (ZN) (ZN)) (EZ _ _ (ZN) (ZN)))))

(def-fns _ $ (many rrun : (many (List (Tr)) m) (erased (Conf) c0) (subterm many (Nat) fuel) (many (Rq) e) (erased (Rch m c0 e) ch)
    -> (many (Rq) e2) (erased (Rch m c0 e2) ch2))
  (let-match many fuel (Succ f) ((Zero) (values e ch)))
  (let-match many (rstep m c0 e ch) (RsOk _ _ e1 ch1) ((RsNo _ _ e1 ch1) (values e1 ch1)))
  (tail $ rrun m c0 f e1 ch1))

(def-adts
  ((TRun : ((List (Tr)) m) ((Conf) c) ((Conf) d) -> Type)
    enum
    (many TR0 : (erased (List (Tr)) m) (erased (Conf) c) -> (TRun m c c))
    (many TRL : (erased (List (Tr)) m) (erased (Nat) q q2) (erased (List (Bool)) l r) (erased (Bool) h h2 w) (erased (Conf) d)
       (erased (Look m q h (Mov w (DL) q2)) lk) (erased (TRun m (MkConf q2 l h2 (Cons (Bool) w r)) d) p)
       -> (TRun m (MkConf q (Cons (Bool) h2 l) h r) d))
    (many TRR : (erased (List (Tr)) m) (erased (Nat) q q2) (erased (List (Bool)) l r) (erased (Bool) h h2 w) (erased (Conf) d)
       (erased (Look m q h (Mov w (DR) q2)) lk) (erased (TRun m (MkConf q2 (Cons (Bool) w l) h2 r) d) p)
       -> (TRun m (MkConf q l h (Cons (Bool) h2 r)) d))))

(def-adts
  ((Fr : ((List (Bool)) L R) ((Conf) c) ((Conf) d) -> Type)
    enum
    (many MkFr : (erased (List (Bool)) L R l r l2 r2) (erased (Nat) q) (erased (Bool) h) (erased (Cat (Bool) l L l2) cl) (erased (Cat (Bool) r R r2) cr)
       -> (Fr L R (MkConf q l h r) (MkConf q l2 h r2)))))

(def-fns _ $ (erased run-pre : (erased (List (Tr)) m) (erased (Conf) a b c) (erased (Nat) t) (erased (Stp m a b) st) (subterm erased (Run m b t c) r)
    -> (erased (Run m a (Succ t) c) r2))
  (let-match erased r (RSnoc _ _ c1 _ t1 r1 st1) ((RNil _ _) (RSnoc m a a b (Zero) (RNil m a) st)))
  (RSnoc m a c1 c (Succ t1) (run-pre m a b c1 t1 st r1) st1))

(def-fns _ $ (erased trun-frame : (erased (List (Tr)) m) (erased (List (Bool)) L R) (erased (Conf) c d c2) (subterm erased (TRun m c d) p) (erased (Fr L R c c2) f)
    -> (erased (Conf) d2) (erased (Nat) t) (erased (Run m c2 t d2) r) (erased (Fr L R d d2) f2))
  (match erased p _
    ((TR0 _ _) (values c2 (Zero) (RNil m c2) f))
    ((TRL _ q q2 l r h h2 w _ lk p1)
      (let-match erased f (MkFr _ _ _ _ _ _ _ _ cl cr))
      (let-match erased cl (CatC _ _ _ _ l3 cl1))
      (let ((erased d2) (erased t) (erased r1) (erased f2)) (trun-frame m L R _ d _ p1 (MkFr L R l (Cons (Bool) w r) l3 _ q2 h2 cl1 (CatC _ w r R _ cr))))
      (values d2 (Succ t) (run-pre m c2 _ d2 t (StepL m q q2 (Cons (Bool) h2 l3) _ l3 h w h2 lk (PullCons h2 l3)) r1) f2))
    ((TRR _ q q2 l r h h2 w _ lk p1)
      (let-match erased f (MkFr _ _ _ _ _ _ _ _ cl cr))
      (let-match erased cr (CatC _ _ _ _ r3 cr1))
      (let ((erased d2) (erased t) (erased r1) (erased f2)) (trun-frame m L R _ d _ p1 (MkFr L R (Cons (Bool) w l) r _ r3 q2 h2 (CatC _ w l L _ cl) cr1)))
      (values d2 (Succ t) (run-pre m c2 _ d2 t (StepR m q q2 _ (Cons (Bool) h2 r3) r3 h w h2 lk (PullCons h2 r3)) r1) f2))))

(def-adts
  ((TSim : ((List (Tr)) m) ((Nat) q) ((Bool) h) ((Conf) c) -> Type)
    enum
    (many TSOk : (erased (List (Tr)) m) (erased (Nat) q) (erased (Bool) h) (erased (Conf) c) (many (List (Bool)) v)
       (erased (TRun m c (MkConf q (Nil (Bool)) h v)) p) -> (TSim m q h c))
    (many TSNo : (erased (List (Tr)) m) (erased (Nat) q) (erased (Bool) h) (erased (Conf) c) -> (TSim m q h c))))

(def-adts
  ((Stop : ((Nat) q0) ((Bool) h0) ((Nat) q) ((List (Bool)) l) ((Bool) h) -> Type)
    enum
    (many MkStop : (erased (Nat) q) (erased (Bool) h) -> (Stop q h q (Nil (Bool)) h))))

(def-fns _ $ (many stop-at : (many (Nat) q0) (many (Bool) h0) (many (Nat) q) (many (List (Bool)) l) (many (Bool) h)
    -> (many (ErasedMaybe (Stop q0 h0 q l h)) r))
  (let-match many l (Nil _) ((Cons _ _ _) (ENone _)))
  (let-match many (eq-nat q q0) (ESome _ e1) ((ENone _) (ENone _)))
  (let-match many (eq-bit h h0) (ESome _ e2) ((ENone _) (ENone _)))
  (let-match erased e1 (Refl _ _))
  (let-match erased e2 (Refl _ _))
  (ESome _ (MkStop q h)))

(def-fns _ $ (many tsim : (many (List (Tr)) m) (many (Nat) q0) (many (Bool) h0) (subterm many (Nat) fuel) (many (Nat) q) (many (List (Bool)) l) (many (Bool) h)
    (many (List (Bool)) r) -> (many (TSim m q0 h0 (MkConf q l h r)) s))
  (let-match many fuel (Succ f) ((Zero) (TSNo m q0 h0 _)))
  (let-match many (tlook m q h) (LkOk _ _ _ tr lk) ((LkNo _ _ _) (TSNo m q0 h0 _)))
  (let-match many tr (Mov w d q2) ((Hlt) (TSNo m q0 h0 _)))
  (match many d _
    ((DL)
      (let-match many l (Cons _ h2 l2) ((Nil _) (TSNo m q0 h0 _)))
      (let ((many c2)) (MkConf q2 l2 h2 (Cons (Bool) w r)))
      (let-match many (stop-at q0 h0 q2 l2 h2) (ESome _ e)
        ((ENone _)
          (let-match many (notail $ tsim m q0 h0 f q2 l2 h2 (Cons (Bool) w r)) (TSOk _ _ _ _ v p) ((TSNo _ _ _ _) (TSNo m q0 h0 _)))
          (TSOk m q0 h0 _ v (TRL m q q2 l2 r h h2 w _ lk p))))
      (let-match erased e (MkStop _ _))
      (TSOk m q0 h0 _ (Cons (Bool) w r) (TRL m q q2 l2 r h h2 w _ lk (TR0 m c2))))
    ((DR)
      (let-match many r (Cons _ h2 r2) ((Nil _) (TSNo m q0 h0 _)))
      (let-match many (notail $ tsim m q0 h0 f q2 (Cons (Bool) w l) h2 r2) (TSOk _ _ _ _ v p) ((TSNo _ _ _ _) (TSNo m q0 h0 _)))
      (TSOk m q0 h0 _ v (TRR m q q2 l r2 h h2 w _ lk p)))))

(def-adts
  ((Pw : ((List (Bool)) v) ((Nat) n) ((List (Bool)) R y) -> Type)
    enum
    (many PwZ : (erased (List (Bool)) v R) -> (Pw v (Zero) R R))
    (many PwS : (erased (List (Bool)) v R vR y) (erased (Nat) n) (erased (Cat (Bool) v R vR) c) (erased (Pw v n vR y) p) -> (Pw v (Succ n) R y))))

(def-fns _ $ (erased shift-run : (erased (List (Tr)) m) (erased (Nat) q) (erased (Bool) h b) (erased (List (Bool)) v)
    (erased (TRun m (MkConf q (Cons (Bool) b (Nil (Bool))) h (Nil (Bool))) (MkConf q (Nil (Bool)) h v)) w)
    (erased (Nat) n) (erased (List (Bool)) L x R y) (subterm erased (Rp b n L x) p) (erased (Pw v n R y) pw)
    -> (erased (Nat) t) (erased (Run m (MkConf q x h R) t (MkConf q L h y)) r))
  (let-match erased p (RpS _ n1 _ x1 p1) ((RpZ _ _) (let-match erased pw (PwZ _ _)) (values (Zero) (RNil m _))))
  (let-match erased pw (PwS _ _ vR _ _ cv pw1))
  (let ((erased d2) (erased t1) (erased r1) (erased f2))
    (trun-frame m x1 R _ _ _ w (MkFr x1 R (Cons (Bool) b (Nil (Bool))) (Nil (Bool)) _ R q h (CatC _ b _ x1 x1 (CatN _ x1)) (CatN _ R))))
  (let-match erased f2 (MkFr _ _ _ _ l2 r2 _ _ cl cr))
  (let-match erased cl (CatN _ _))
  (let-match erased (cat-fn (Bool) v R r2 vR cr cv) (Refl _ _))
  (let ((erased t2) (erased r2b)) (shift-run m q h b v w n1 L x1 vR y p1 pw1))
  (run-cat m _ _ _ t1 t2 r1 r2b))

(def-fns _ $ (erased rp-shift : (erased (Bool) c) (erased (Nat) n) (erased (List (Bool)) R y) (subterm erased (Rp c (Succ n) R y) p)
    -> (erased (Rp c n (Cons (Bool) c R) y) q))
  (let-match erased p (RpS _ _ _ y1 p1))
  (let-match erased p1 (RpS _ n2 _ y2 p2) ((RpZ _ _) (RpZ c (Cons (Bool) c R))))
  (RpS c n2 (Cons (Bool) c R) y1 (rp-shift c n2 R y1 p1)))

(def-fns _ $ (erased rp-pw : (erased (Bool) c) (subterm erased (Nat) n) (erased (List (Bool)) R y) (erased (Rp c n R y) p)
    -> (erased (Pw (Cons (Bool) c (Nil (Bool))) n R y) q))
  (let-match erased n (Succ n1) ((Zero) (let-match erased p (RpZ _ _)) (PwZ _ R)))
  (PwS _ R (Cons (Bool) c R) y n1 (CatC _ c _ R R (CatN _ R)) (rp-pw c n1 (Cons (Bool) c R) y (rp-shift c n1 R y p))))

(def-fns _ $ (erased rp-add : (erased (Bool) c) (erased (Nat) n k s) (erased (List (Bool)) t x y) (subterm erased (Rp c n x y) p) (erased (Rp c k t x) q)
    (erased (Add n k s) a) -> (erased (Rp c s t y) r))
  (let-match erased p (RpS _ n1 _ y1 p1) ((RpZ _ _) (let-match erased a (AddZero _)) q))
  (let-match erased a (AddSucc _ _ s1 a1))
  (RpS c s1 t y1 (rp-add c n1 k s1 t x y1 p1 q a1)))

(def-fns _ $ (many pushrun : (many (Bool) c) (many (Nat) n) (many (List (Rn)) R) (erased (List (Bool)) x) (erased (Den R x) d)
    -> (many (List (Rn)) R2) (erased (List (Bool)) y) (erased (Rp c n x y) p) (erased (Den R2 y) d2))
  (let ((erased y0) (erased p0)) (rp-ex c n x))
  (let ((many fresh)) (Cons _ (MkRn c n) R))
  (let-match many R (Cons _ rn R1) ((Nil _) (values fresh y0 p0 (DeC c n R x y0 d p0))))
  (let-match many rn (MkRn b k))
  (let-match many (eq-bit c b) (ESome _ eq) ((ENone _) (values fresh y0 p0 (DeC c n R x y0 d p0))))
  (let-match erased eq (Refl _ _))
  (let-match erased d (DeC _ _ _ t _ d1 q))
  (let ((many s) (erased a)) (add n k))
  (values (Cons _ (MkRn c s) R1) y0 p0 (DeC c s R1 t y0 d1 (rp-add c n k s t x y0 p0 q a))))

(def-adts
  ((MirT : ((Tr) a) ((Tr) b) -> Type)
    enum
    (many MtH : -> (MirT (Hlt) (Hlt)))
    (many MtL : (erased (Bool) w) (erased (Nat) q) -> (MirT (Mov w (DL) q) (Mov w (DR) q)))
    (many MtR : (erased (Bool) w) (erased (Nat) q) -> (MirT (Mov w (DR) q) (Mov w (DL) q)))))

(def-adts
  ((MirM : ((List (Tr)) m) ((List (Tr)) m2) -> Type)
    enum
    (many MmN : -> (MirM (Nil (Tr)) (Nil (Tr))))
    (many MmC : (erased (Tr) a b) (erased (List (Tr)) m m2) (erased (MirT a b) t) (erased (MirM m m2) p) -> (MirM (Cons (Tr) a m) (Cons (Tr) b m2)))))

(def-adts
  ((MirC : ((Conf) c) ((Conf) d) -> Type)
    enum
    (many MkMirC : (erased (Nat) q) (erased (List (Bool)) l r) (erased (Bool) h) -> (MirC (MkConf q l h r) (MkConf q r h l)))))

(def-fns _ $ (many mirm : (subterm many (List (Tr)) m) -> (many (List (Tr)) m2) (erased (MirM m m2) p) (erased (MirM m2 m) p2))
  (let-match many m (Cons _ a m1) ((Nil _) (values (Nil (Tr)) (MmN) (MmN))))
  (let ((many m3) (erased p) (erased p2)) (notail $ mirm m1))
  (let-match many a (Mov w d q) ((Hlt) (values (Cons _ (Hlt) m3) (MmC _ _ m1 m3 (MtH) p) (MmC _ _ m3 m1 (MtH) p2))))
  (match many d _
    ((DL) (values (Cons _ (Mov w (DR) q) m3) (MmC _ _ m1 m3 (MtL w q) p) (MmC _ _ m3 m1 (MtR w q) p2)))
    ((DR) (values (Cons _ (Mov w (DL) q) m3) (MmC _ _ m1 m3 (MtR w q) p) (MmC _ _ m3 m1 (MtL w q) p2)))))

(def-fns _ $ (erased mir-look : (erased (List (Tr)) m m2) (erased (Nat) q) (erased (Bool) b) (erased (Tr) t) (erased (MirM m m2) mm)
    (subterm erased (Look m q b t) lk) -> (erased (Tr) t2) (erased (Look m2 q b t2) lk2) (erased (MirT t t2) mt))
  (match erased lk _
    ((Look0 t0 t1 rest)
      (let-match erased mm (MmC _ u0 _ m3 mt0 mm1))
      (let-match erased mm1 (MmC _ u1 _ m4 _ _))
      (values u0 (Look0 u0 u1 m4) mt0))
    ((Look1 t0 t1 rest)
      (let-match erased mm (MmC _ u0 _ m3 _ mm1))
      (let-match erased mm1 (MmC _ u1 _ m4 mt1 _))
      (values u1 (Look1 u0 u1 m4) mt1))
    ((LookS t0 t1 rest q1 _ _ lk1)
      (let-match erased mm (MmC _ u0 _ m3 _ mm1))
      (let-match erased mm1 (MmC _ u1 _ m4 _ mm2))
      (let ((erased t2) (erased lk2) (erased mt)) (mir-look rest m4 q1 b t mm2 lk1))
      (values t2 (LookS u0 u1 m4 q1 b t2 lk2) mt))))

(def-fns _ $ (erased mir-stp : (erased (List (Tr)) m m2) (erased (Conf) c d c2) (erased (MirM m m2) mm) (erased (Stp m c d) st) (erased (MirC c c2) mc)
    -> (erased (Conf) d2) (erased (Stp m2 c2 d2) st2) (erased (MirC d d2) md))
  (match erased st _
    ((StepL _ q q2 l r l2 h w h2 lk pp)
      (let ((erased t2) (erased lk2) (erased mt)) (mir-look m m2 q h _ mm lk))
      (let-match erased mt (MtL _ _))
      (let-match erased mc (MkMirC _ _ _ _))
      (values (MkConf q2 (Cons (Bool) w r) h2 l2) (StepR m2 q q2 r l l2 h w h2 lk2 pp) (MkMirC q2 l2 (Cons (Bool) w r) h2)))
    ((StepR _ q q2 l r r2 h w h2 lk pp)
      (let ((erased t2) (erased lk2) (erased mt)) (mir-look m m2 q h _ mm lk))
      (let-match erased mt (MtR _ _))
      (let-match erased mc (MkMirC _ _ _ _))
      (values (MkConf q2 r2 h2 (Cons (Bool) w l)) (StepL m2 q q2 r l r2 h w h2 lk2 pp) (MkMirC q2 (Cons (Bool) w l) r2 h2)))))

(def-fns _ $ (erased mir-run : (erased (List (Tr)) m m2) (erased (Conf) c d c2) (erased (Nat) t) (erased (MirM m m2) mm) (subterm erased (Run m c t d) r)
    (erased (MirC c c2) mc) -> (erased (Conf) d2) (erased (Run m2 c2 t d2) r2) (erased (MirC d d2) md))
  (let-match erased r (RSnoc _ _ c1 _ t1 r1 st) ((RNil _ _) (values c2 (RNil m2 c2) mc)))
  (let ((erased e1) (erased q1) (erased m1)) (mir-run m m2 c c1 c2 t1 mm r1 mc))
  (let ((erased d2) (erased st2) (erased md)) (mir-stp m m2 c1 d e1 mm st m1))
  (values d2 (RSnoc m2 c2 e1 d2 t1 q1 st2) md))

(def-fns _ $ (erased pw-nil : (subterm erased (Nat) n) (erased (List (Bool)) R) -> (erased (Pw (Nil (Bool)) n R R) p))
  (let-match erased n (Succ n1) ((Zero) (PwZ _ R)))
  (PwS _ R R R n1 (CatN _ R) (pw-nil n1 R)))

(def-adts
  ((Sh : ((List (Tr)) m) ((Nat) q) ((Bool) h) ((List (Bool)) s o) -> Type)
    enum
    (many ShOk : (erased (List (Tr)) m) (erased (Nat) q) (erased (Bool) h) (erased (List (Bool)) s o s2 o2) (many (List (Rn)) S2 O2)
       (erased (Den S2 s2) ds) (erased (Den O2 o2) do) (erased (Nat) t) (erased (Run m (MkConf q s h o) t (MkConf q s2 h o2)) r) -> (Sh m q h s o))
    (many ShNo : (erased (List (Tr)) m) (erased (Nat) q) (erased (Bool) h) (erased (List (Bool)) s o) -> (Sh m q h s o))))

(def-fns _ $ (many shcore : (many (List (Tr)) m) (many (Nat) q) (many (Bool) h) (many (Nat) fuel) (many (List (Rn)) S) (erased (List (Bool)) s) (erased (Den S s) ds)
    (many (List (Rn)) O) (erased (List (Bool)) o) (erased (Den O o) do) -> (many (Sh m q h s o) r))
  (let-match many S (Cons _ rn S1) ((Nil _) (ShNo m q h s o)))
  (let-match many rn (MkRn b n))
  (let-match erased ds (DeC _ _ _ t _ d1 p))
  (let-match many (tsim m q h fuel q (Cons (Bool) b (Nil (Bool))) h (Nil (Bool))) (TSOk _ _ _ _ v w) ((TSNo _ _ _ _) (ShNo m q h s o)))
  (let-match many v (Cons _ c v1) ((Nil _)
    (let ((erased t1) (erased r1)) (shift-run m q h b v w n t s o o p (pw-nil n o)))
    (ShOk m q h s o t o S1 O d1 do t1 r1)))
  (let-match many v1 (Nil _) ((Cons _ _ _) (ShNo m q h s o)))
  (let ((many O2) (erased y) (erased py) (erased dy)) (pushrun c n O o do))
  (let ((erased t1) (erased r1)) (shift-run m q h b v w n t s o y p (rp-pw c n o y py)))
  (ShOk m q h s o t y S1 O2 d1 dy t1 r1))

(def-fns _ $ (many rshift : (many (List (Tr)) m m2) (erased (MirM m2 m) mm) (many (Nat) fuel) (erased (Conf) c0) (many (Rq) e) (erased (Rch m c0 e) ch)
    -> (many (Rs m c0) r))
  (let-match erased ch (MkRch _ _ a c _ t0 r0 dc z))
  (let-match many e (MkRq q L h R))
  (let-match erased dc (MkDc _ _ _ _ l r dl dr))
  (let-match many (shcore m q h fuel L l dl R r dr) (ShNo _ _ _ _ _)
    ((ShOk _ _ _ _ _ l2 r2 L2 R2 dl2 dr2 t1 r1) (RsOk m c0 (MkRq q L2 h R2) (rch-run m c0 c _ e _ t1 ch dc r1 (MkDc q L2 R2 h l2 r2 dl2 dr2)))))
  (let-match many (shcore m2 q h fuel R r dr L l dl) (ShOk _ _ _ _ _ r2 l2 R2 L2 dr2 dl2 t1 r1) ((ShNo _ _ _ _ _) (RsNo m c0 e ch)))
  (let ((erased d2) (erased r3) (erased md)) (mir-run m2 m (MkConf q r h l) (MkConf q r2 h l2) c t1 mm r1 (MkMirC q r l h)))
  (let-match erased md (MkMirC _ _ _ _))
  (RsOk m c0 (MkRq q L2 h R2) (rch-run m c0 c _ e _ t1 ch dc r3 (MkDc q L2 R2 h l2 r2 dl2 dr2))))

(def-fns _ $ (many rmove : (many (List (Tr)) m m2) (erased (MirM m2 m) mm) (erased (Conf) c0) (many (Rq) e) (erased (Rch m c0 e) ch) -> (many (Rs m c0) r))
  (let-match many (rshift m m2 mm 64 c0 e ch) (RsNo _ _ e1 ch1) ((RsOk _ _ e1 ch1) (RsOk m c0 e1 ch1)))
  (rstep m c0 e1 ch1))

(def-fns _ $ (many mrun : (many (List (Tr)) m m2) (erased (MirM m2 m) mm) (erased (Conf) c0) (subterm many (Nat) fuel) (many (Rq) e) (erased (Rch m c0 e) ch)
    -> (many (Rq) e2) (erased (Rch m c0 e2) ch2))
  (let-match many fuel (Succ f) ((Zero) (values e ch)))
  (let-match many (rmove m m2 mm c0 e ch) (RsOk _ _ e1 ch1) ((RsNo _ _ e1 ch1) (values e1 ch1)))
  (tail $ mrun m m2 mm c0 f e1 ch1))

(def-fns _ $ (erased rp-split : (erased (Bool) b) (erased (Nat) c u w) (erased (List (Bool)) r x) (subterm erased (Add c u w) a) (erased (Rp b w r x) p)
    -> (erased (List (Bool)) y) (erased (Rp b u r y) q) (erased (Rp b c y x) q2))
  (let-match erased a (AddSucc c1 _ w1 a1) ((AddZero _) (values x p (RpZ b x))))
  (let-match erased p (RpS _ _ _ x1 p1))
  (let ((erased y) (erased q) (erased q2)) (rp-split b c1 u w1 r x1 a1 p1))
  (values y q (RpS b c1 y x1 q2)))

(def-adts
  ((Strip : ((List (Bool)) u x) -> Type)
    enum
    (many StOk : (erased (List (Bool)) u x y) (many (List (Rn)) L) (erased (Den L y) d) (erased (Cat (Bool) u y x) c) -> (Strip u x))
    (many StNo : (erased (List (Bool)) u x) -> (Strip u x))))

(def-fns _ $ (many strip : (subterm many (List (Bool)) u) (many (List (Rn)) L) (erased (List (Bool)) x) (erased (Den L x) d) -> (many (Strip u x) s))
  (let-match many u (Cons _ b u1) ((Nil _) (StOk u x x L d (CatN _ x))))
  (let-match many L (Cons _ _ _) ((Nil _) (StNo u x)))
  (let ((many h) (many L1) (erased x1) (many pp) (erased d1)) (rpop L x d))
  (let-match many pp (PullCons _ _) ((PullNil) (StNo u x)))
  (let-match many (eq-bit b h) (ESome _ e) ((ENone _) (StNo u x)))
  (let-match erased e (Refl _ _))
  (let-match many (notail $ strip u1 L1 x1 d1) (StOk _ _ y L2 d2 c) ((StNo _ _) (StNo u x)))
  (StOk u x y L2 d2 (CatC _ b u1 y x1 c)))

(def-adts
  ((StripZ : ((Nat) w) ((List (Bool)) x) -> Type)
    enum
    (many SzOk : (erased (Nat) w) (erased (List (Bool)) x y) (many (List (Rn)) L) (erased (Den L y) d) (erased (Rp (BFalse) w y x) p) -> (StripZ w x))
    (many SzNo : (erased (Nat) w) (erased (List (Bool)) x) -> (StripZ w x))))

(def-fns _ $ (many stripz : (many (Nat) w) (subterm many (List (Rn)) L) (erased (List (Bool)) x) (erased (Den L x) d) -> (many (StripZ w x) s))
  (let-match many (nat-zero-dec w) (IsSucc _) ((IsZero) (SzOk w x x L d (RpZ _ x))))
  (let-match many L (Cons _ rn L1) ((Nil _) (SzNo w x)))
  (let-match many rn (MkRn b n))
  (let-match erased d (DeC _ _ _ t _ d1 p))
  (let-match many b (BFalse) ((BTrue) (SzNo w x)))
  (let-match many (nat-cmp w n) (CGt _ _ _ _ gt)
    ((CEq _ _ _) (SzOk w x t L1 d1 p))
    ((CLt _ _ _ _ lt)
      (let ((many k) (erased a)) (sub n w (lt-weaken w n lt)))
      (let ((erased y) (erased q2) (erased q1)) (rp-split (BFalse) w k n t x a p))
      (SzOk w x y (Cons _ (MkRn (BFalse) k) L1) (DeC (BFalse) k L1 t y d1 q2) q1)))
  (let ((many k) (erased a)) (sub w n (lt-weaken n w gt)))
  (let-match many (notail $ stripz k L1 t d1) (SzOk _ _ y L2 d2 q) ((SzNo _ _) (SzNo w x)))
  (SzOk w x y L2 d2 (rp-add (BFalse) n k w y t x p q a)))

(def-fns _ $ (many pushbits : (subterm many (List (Bool)) u) (many (List (Rn)) L) (erased (List (Bool)) r) (erased (Den L r) d)
    -> (many (List (Rn)) L2) (erased (List (Bool)) x) (erased (Den L2 x) d2) (erased (Cat (Bool) u r x) c))
  (let-match many u (Cons _ b u1) ((Nil _) (values L r d (CatN _ r))))
  (let ((many L1) (erased x1) (erased d1) (erased c1)) (notail $ pushbits u1 L r d))
  (let ((many L2) (erased d2)) (push b L1 x1 d1))
  (values L2 (Cons (Bool) b x1) d2 (CatC _ b u1 r x1 c1)))

(def-fns _ $ (many ones : (many (List (Rn)) L) (erased (List (Bool)) x) (erased (Den L x) d) -> (many (Nat) n) (erased (List (Bool)) t) (erased (Rp (BTrue) n t x) p))
  (let-match many L (Cons _ rn L1) ((Nil _) (values (Zero) x (RpZ _ x))))
  (let-match many rn (MkRn b n))
  (let-match many b (BTrue) ((BFalse) (values (Zero) x (RpZ _ x))))
  (let-match erased d (DeC _ _ _ t _ d1 p))
  (values n t p))
