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

(def-adts $ (Rc : -> Type)
  enum
  (many MkRc : (many (Nat) q) (many (List (Rn)) L) (many (Bool) h) (many (List (Rn)) R) -> (Rc)))

(def-adts
  ((Dc : ((Rc) e) ((Conf) c) -> Type)
    enum
    (many MkDc : (erased (Nat) q) (erased (List (Rn)) L R) (erased (Bool) h) (erased (List (Bool)) l r) (erased (Den L l) dl) (erased (Den R r) dr)
       -> (Dc (MkRc q L h R) (MkConf q l h r)))))

(def-adts
  ((Rch : ((List (Tr)) m) ((Conf) c0) ((Rc) e) -> Type)
    enum
    (many MkRch : (erased (List (Tr)) m) (erased (Conf) c0 a c) (erased (Rc) e) (erased (Nat) t) (erased (Run m c0 t a) r) (erased (Dc e c) d)
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
    (many RsOk : (erased (List (Tr)) m) (erased (Conf) c0) (many (Rc) e) (erased (Rch m c0 e) ch) -> (Rs m c0))
    (many RsNo : (erased (List (Tr)) m) (erased (Conf) c0) (many (Rc) e) (erased (Rch m c0 e) ch) -> (Rs m c0))))

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

(def-fns _ $ (erased dc-fn : (erased (Rc) e) (erased (Conf) c d) (erased (Dc e c) p) (erased (Dc e d) q) -> (erased (Eq (Conf) c d) r))
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

(def-fns _ $ (erased rch-run : (erased (List (Tr)) m) (erased (Conf) c0 c d) (erased (Rc) e e2) (erased (Nat) s)
    (erased (Rch m c0 e) ch) (erased (Dc e c) dc) (erased (Run m c s d) r) (erased (Dc e2 d) dc2) -> (erased (Rch m c0 e2) ch2))
  (let-match erased ch (MkRch _ _ a c1 _ t r0 dc1 z))
  (let-match erased (dc-fn e c c1 dc dc1) (Refl _ _))
  (let ((erased a2) (erased r2) (erased z2)) (run-eqz m c d a s r z))
  (let ((erased u) (erased r3)) (run-cat m c0 a a2 t s r0 r2))
  (MkRch m c0 a2 d e2 u r3 dc2 z2))

(def-fns _ $ (erased rch-stp : (erased (List (Tr)) m) (erased (Conf) c0 c d) (erased (Rc) e e2)
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

(def-fns _ $ (many pop : (subterm many (List (Rn)) L) (erased (List (Bool)) x) (erased (Den L x) d) ->
    (many (Bool) h) (many (List (Rn)) L2) (erased (List (Bool)) y) (erased (Pull x h y) pp) (erased (Den L2 y) d2))
  (let-match many L (Cons _ rn L1) ((Nil _) (let-match erased d (DeN)) (values (BFalse) L (Nil (Bool)) (PullNil) (DeN))))
  (let-match many rn (MkRn b n))
  (let-match erased d (DeC _ _ _ t _ d1 p))
  (match many n _
    ((Zero) (let-match erased p (RpZ _ _)) (tail $ pop L1 x d1))
    ((Succ n1)
      (let-match erased p (RpS _ _ _ x1 p1))
      (let-match many (nat-zero-dec n1) (IsZero) ((IsSucc _) (values b (Cons _ (MkRn b n1) L1) x1 (PullCons b x1) (DeC b n1 L1 t x1 d1 p1))))
      (let-match erased p1 (RpZ _ _))
      (values b L1 x1 (PullCons b x1) d1))))

(def-fns _ $ (many rstep : (many (List (Tr)) m) (erased (Conf) c0) (many (Rc) e) (erased (Rch m c0 e) ch) -> (many (Rs m c0) r))
  (let-match erased ch (MkRch _ _ a c _ t r0 dc z))
  (let-match many e (MkRc q L h R))
  (let-match erased dc (MkDc _ _ _ _ l r dl dr))
  (let-match many (tlook m q h) (LkOk _ _ _ tr lk) ((LkNo _ _ _) (RsNo m c0 e ch)))
  (let-match many tr (Mov w d q2) ((Hlt) (RsNo m c0 e ch)))
  (match many d _
    ((DR)
      (let ((many L2) (erased dl2)) (push w L l dl))
      (let ((many h2) (many R2) (erased r2) (erased pp) (erased dr2)) (pop R r dr))
      (let ((many e2)) (MkRc q2 L2 h2 R2))
      (RsOk m c0 e2 (rch-stp m c0 c _ e e2 ch dc (StepR m q q2 l r r2 h w h2 lk pp) (MkDc q2 L2 R2 h2 (Cons (Bool) w l) r2 dl2 dr2))))
    ((DL)
      (let ((many R2) (erased dr2)) (push w R r dr))
      (let ((many h2) (many L2) (erased l2) (erased pp) (erased dl2)) (pop L l dl))
      (let ((many e2)) (MkRc q2 L2 h2 R2))
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

(def-fns _ $ (erased trim-len : (erased (List (Bool)) x y) (erased (Nat) n k) (erased (Eqz x y) e) (erased (Trim x) tr)
    (erased (Length (Bool) x n) lx) (erased (Length (Bool) y k) ly) -> (erased (Lt n (Succ k)) r))
  (let-match erased tr (TrL _ l) ((TrN) (let-match erased lx (LengthNil _)) (LtZ k)))
  (eqz-len x y n k e l lx ly))

(def-fns _ $ (many trim : (subterm many (List (Rn)) L) (erased (List (Bool)) x) (erased (Den L x) d) ->
    (many (List (Rn)) L2) (erased (List (Bool)) y) (erased (Den L2 y) d2) (erased (Eqz x y) ez) (many (Trim y) tr))
  (let-match many L (Cons _ rn L1) ((Nil _) (let-match erased d (DeN)) (values L (Nil (Bool)) (DeN) (EZ _ _ (ZN) (ZN)) (TrN))))
  (let-match many rn (MkRn b n))
  (let-match erased d (DeC _ _ _ t _ d1 p))
  (let ((many L3) (erased y1) (erased d3) (erased e1) (many tr1)) (notail $ trim L1 t d1))
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

(def-fns _ $ (many span-check : (erased (List (Tr)) m) (many (Nat) N) (many (Rc) e) (erased (Rch m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) e) ch)
    -> (many (SpanR m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) N) r))
  (let-match erased ch (MkRch _ c0 a c _ t r0 dc z))
  (let-match many e (MkRc q L h R))
  (let-match erased dc (MkDc _ _ _ _ l r dl dr))
  (let-match erased z (MkCEz _ _ _ la ra _ el er))
  (let ((many L2) (erased yl) (erased dl2) (erased e1) (many t1)) (trim L l dl))
  (let ((many R2) (erased yr) (erased dr2) (erased e2) (many t2)) (trim R r dr))
  (let ((many nl) (erased ll)) (rsum L2 yl dl2))
  (let ((many nr) (erased lr)) (rsum R2 yr dr2))
  (let ((many n) (erased an)) (add nl nr))
  (let-match many (lt-dec N (Succ n)) (Yes _ _ _ _ big) ((No _ _ _ _ _) (SpLow m c0 N n)))
  (let ((erased kl) (erased lla)) (len-ex (Bool) la))
  (let ((erased kr) (erased lra)) (len-ex (Bool) ra))
  (let ((erased S) (erased aS)) (add-ex kl kr))
  (let ((erased S2) (erased z2) (erased le2)) (run-csz m c0 a t r0 (MkCsz (Zero) (Nil (Bool)) (Nil (Bool)) (BFalse) (Zero) (Zero) (Zero) (LengthNil _) (LengthNil _) (AddZero (Zero)))))
  (let-match erased (csz-fn a S S2 (MkCsz q la ra h kl kr S lla lra aS) z2) (Refl _ _))
  (let ((erased gl)) (trim-len yl la nl kl (eqz-trans yl l la (eqz-sym l yl e1) el) t1 ll lla))
  (let ((erased gr)) (trim-len yr ra nr kr (eqz-trans yr r ra (eqz-sym r yr e2) er) t2 lr lra))
  (let ((erased M) (erased aM)) (add-ex kl nr))
  (let ((erased gn)) (le-tr n M S (add-mono nl kl nr n M an aM gl) (add-mono nr kr kl M S (add-comm kl nr M aM) (add-comm kl kr S aS) gr)))
  (SpOk m c0 N (MkSpan m c0 a N t r0 (le-tr N n t big (le-tr n S t gn le2)))))

(def-fns _ $ (erased rch0 : (erased (List (Tr)) m) -> (erased (Rch m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) (MkRc (Zero) (Nil (Rn)) (BFalse) (Nil (Rn)))) ch))
  (let ((erased c0)) (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))))
  (MkRch m c0 c0 c0 _ (Zero) (RNil m c0) (MkDc (Zero) (Nil (Rn)) (Nil (Rn)) (BFalse) (Nil (Bool)) (Nil (Bool)) (DeN) (DeN))
    (MkCEz (Zero) (Nil (Bool)) (Nil (Bool)) (Nil (Bool)) (Nil (Bool)) (BFalse) (EZ _ _ (ZN) (ZN)) (EZ _ _ (ZN) (ZN)))))

(def-fns _ $ (many rrun : (many (List (Tr)) m) (erased (Conf) c0) (subterm many (Nat) fuel) (many (Rc) e) (erased (Rch m c0 e) ch)
    -> (many (Rc) e2) (erased (Rch m c0 e2) ch2))
  (let-match many fuel (Succ f) ((Zero) (values e ch)))
  (let-match many (rstep m c0 e ch) (RsOk _ _ e1 ch1) ((RsNo _ _ e1 ch1) (values e1 ch1)))
  (tail $ rrun m c0 f e1 ch1))
