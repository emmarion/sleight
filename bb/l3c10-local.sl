(def-adts
  ((Dx : ((Rq) e) ((List (Bool)) X) ((Conf) c) -> Type)
    enum
    (many MkDx : (erased (Nat) q) (erased (List (Rn)) L R) (erased (Bool) h) (erased (List (Bool)) l r X rx) (erased (Den L l) dl) (erased (Den R r) dr)
       (erased (Cat (Bool) r X rx) cx) -> (Dx (MkRq q L h R) X (MkConf q l h rx)))))

(def-fns _ $ (erased rp-catx : (erased (Bool) b) (erased (Nat) w) (erased (List (Bool)) r y X yX) (subterm erased (Rp b w r y) p) (erased (Cat (Bool) y X yX) c)
    -> (erased (List (Bool)) rX) (erased (Cat (Bool) r X rX) c2) (erased (Rp b w rX yX) q))
  (let-match erased p (RpS _ w1 _ y1 p1) ((RpZ _ _) (values yX c (RpZ b yX))))
  (let-match erased c (CatC _ _ _ _ y1X c1))
  (let ((erased rX) (erased c2) (erased q1)) (rp-catx b w1 r y1 X y1X p1 c1))
  (values rX c2 (RpS b w1 rX y1X q1)))

(def-lvl LF)

(def-adts
  ((FR : ((Rq) e e2) -> Type)
    enum
    (many MkFR : (erased (Rq) e e2)
       (erased (Fn LF (erased (List (Bool)) X) (erased (Conf) c) (erased (Dx e X c) d)
           -> (erased (Conf) a c2) (erased (Nat) t) (erased (Run l3 c t a) r) (erased (Dx e2 X c2) d2) (erased (CEz c2 a) z)) f)
       -> (FR e e2))))

(def-adts
  ((FRs : ((Rq) e) -> Type)
    enum
    (many FOk : (erased (Rq) e) (many (Rq) e2) (erased (FR e e2) p) -> (FRs e))
    (many FNo : (erased (Rq) e) -> (FRs e))))

(def-adts
  ((FSq : ((Rq) e e2) -> Type)
    enum
    (many FsN : (erased (Rq) e) -> (FSq e e))
    (many FsC : (erased (Rq) e e1 e2) (erased (FSq e e1) s) (erased (FR e1 e2) p) -> (FSq e e2))))

(def-fns _ $ (erased fsq-run : (erased (Rq) e e2) (subterm erased (FSq e e2) s) (erased (List (Bool)) X) (erased (Conf) c) (erased (Dx e X c) d)
    -> (erased (Conf) a c2) (erased (Nat) t) (erased (Run l3 c t a) r) (erased (Dx e2 X c2) d2) (erased (CEz c2 a) z))
  (let-match erased s (FsC _ e1 _ s1 p) ((FsN _) (values c c (Zero) (RNil l3 c) d (cez-refl c))))
  (let ((erased a1) (erased c1) (erased t1) (erased r1) (erased d1) (erased z1)) (fsq-run e e1 s1 X c d))
  (let-match erased p (MkFR _ _ f))
  (let ((erased a2) (erased c3) (erased t2) (erased r2) (erased d2) (erased z2)) (f X c1 d1))
  (let ((erased a3) (erased r3) (erased z3)) (run-eqz l3 c1 a2 a1 t2 r2 z1))
  (let ((erased t) (erased r)) (run-cat l3 c a1 a3 t1 t2 r1 r3))
  (values a3 c3 t r d2 (cez-trans c3 a2 a3 z2 z3)))

(def-fns _ $ (many f-step : (many (Rq) e) -> (many (FRs e) res))
  (let ((many no)) (FNo e))
  (let-match many e (MkRq q L h R))
  (let-match many (tlook l3 q h) (LkOk _ _ _ tr lk) ((LkNo _ _ _) no))
  (let-match many tr (Mov w d q2) ((Hlt) no))
  (let ((erased l) (erased dl)) (den-ex L))
  (let ((erased r) (erased dr)) (den-ex R))
  (match many d _
    ((DL)
      (let ((many h2) (many L2) (erased l2) (many pp) (erased dl2)) (rpop L l dl))
      (let ((many R2) (erased dr2)) (push w R r dr))
      (def-fns LF $ (erased pf : (erased (List (Bool)) X) (erased (Conf) c) (erased (Dx e X c) dx)
          -> (erased (Conf) a c2) (erased (Nat) t) (erased (Run l3 c t a) run) (erased (Dx (MkRq q2 L2 h2 R2) X c2) d2) (erased (CEz c2 a) z))
        (let-match erased dx (MkDx _ _ _ _ l1 r1 _ rx dl1 dr1 cx))
        (let-match erased (den-fn L l l1 dl dl1) (Refl _ _))
        (let-match erased (den-fn R r r1 dr dr1) (Refl _ _))
        (let ((erased a)) (MkConf q2 l2 h2 (Cons (Bool) w rx)))
        (values a a (Succ (Zero)) (RSnoc l3 c c a (Zero) (RNil l3 c) (StepL l3 q q2 l rx l2 h w h2 lk pp))
          (MkDx q2 L2 R2 h2 l2 (Cons (Bool) w r) X (Cons (Bool) w rx) dl2 dr2 (CatC _ w r X rx cx)) (cez-refl a)))
      (FOk e (MkRq q2 L2 h2 R2) (MkFR e _ pf)))
    ((DR)
      (let ((many h2) (many R2) (erased r2) (many pp) (erased dr2)) (rpop R r dr))
      (let-match many pp (PullCons _ _) ((PullNil) no))
      (let ((many L2) (erased y) (erased z2) (erased dl2) (erased p) (erased ez)) (cpushn w (Succ (Zero)) L l dl))
      (let-match erased p (RpS _ _ _ _ p1))
      (let-match erased p1 (RpZ _ _))
      (def-fns LF $ (erased pf : (erased (List (Bool)) X) (erased (Conf) c) (erased (Dx e X c) dx)
          -> (erased (Conf) a c2) (erased (Nat) t) (erased (Run l3 c t a) run) (erased (Dx (MkRq q2 L2 h2 R2) X c2) d2) (erased (CEz c2 a) z))
        (let-match erased dx (MkDx _ _ _ _ l1 r1 _ rx dl1 dr1 cx))
        (let-match erased (den-fn L l l1 dl dl1) (Refl _ _))
        (let-match erased (den-fn R r r1 dr dr1) (Refl _ _))
        (let-match erased cx (CatC _ _ _ _ r2X cx2))
        (let ((erased a)) (MkConf q2 (Cons (Bool) w l) h2 r2X))
        (values a (MkConf q2 y h2 r2X) (Succ (Zero)) (RSnoc l3 c c a (Zero) (RNil l3 c) (StepR l3 q q2 l rx r2X h w h2 lk (PullCons h2 r2X)))
          (MkDx q2 L2 R2 h2 y r2 X r2X dl2 dr2 cx2) (MkCEz q2 y r2X (Cons (Bool) w l) r2X h2 ez (eqz-refl r2X))))
      (FOk e (MkRq q2 L2 h2 R2) (MkFR e _ pf)))))
