
(def-adts
  ((PStep : ((List (PT)) p) ((Conf) c) ((Conf) d) -> Type)
    enum
    (many PStepL : (erased (List (PT)) p) (erased (Nat) q q2) (erased (List (Bool)) l r l2) (erased (Bool) h w h2)
       (erased (PLook p q h (Def (Mov w (DL) q2))) pl) (erased (Pull l h2 l2) pp)
       -> (PStep p (MkConf q l h r) (MkConf q2 l2 h2 (Cons (Bool) w r))))
    (many PStepR : (erased (List (PT)) p) (erased (Nat) q q2) (erased (List (Bool)) l r r2) (erased (Bool) h w h2)
       (erased (PLook p q h (Def (Mov w (DR) q2))) pl) (erased (Pull r h2 r2) pp)
       -> (PStep p (MkConf q l h r) (MkConf q2 (Cons (Bool) w l) h2 r2)))))

(def-adts
  ((PRunTo : ((List (PT)) p) ((Conf) c0) ((Nat) t) ((Conf) c) -> Type)
    enum
    (many PRNil : (erased (List (PT)) p) (erased (Conf) c0) -> (PRunTo p c0 (Zero) c0))
    (many PRSnoc : (erased (List (PT)) p) (erased (Conf) c0 c d) (erased (Nat) t)
       (erased (PRunTo p c0 t c) r) (erased (PStep p c d) st) -> (PRunTo p c0 (Succ t) d))))

(def-fns _ $ (erased prun-run : (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Ext p m) ex) (erased (Conf) c0 c) (erased (Nat) t)
    (subterm erased (PRunTo p c0 t c) pr) -> (erased (Run m c0 t c) r))
  (let-match erased pr (PRSnoc _ _ c1 _ t1 pr1 st) ((PRNil _ _) (RNil m c0)))
  (let ((erased r1)) (prun-run p m ex c0 c1 t1 pr1))
  (match erased st _
    ((PStepL _ q q2 l rr l2 h w h2 pl pp) (RSnoc m c0 c1 c t1 r1 (StepL m q q2 l rr l2 h w h2 (ext-look p m q h _ ex pl) pp)))
    ((PStepR _ q q2 l rr r2 h w h2 pl pp) (RSnoc m c0 c1 c t1 r1 (StepR m q q2 l rr r2 h w h2 (ext-look p m q h _ ex pl) pp)))))

(def-adts
  ((Cat : (Type A) ((List A) xs) ((List A) ys) ((List A) zs) -> Type)
    enum
    (many CatN : (erased Type A) (erased (List A) ys) -> (Cat A (Nil A) ys ys))
    (many CatC : (erased Type A) (erased A x) (erased (List A) xs ys zs) (erased (Cat A xs ys zs) c)
       -> (Cat A (Cons A x xs) ys (Cons A x zs)))))

(def-fns _ $ (erased cat-assoc : (erased Type A) (erased (List A) x w x2 y z) (subterm erased (Cat A x w x2) c1) (erased (Cat A x2 y z) c2)
    -> (erased (List A) wy) (erased (Cat A w y wy) c3) (erased (Cat A x wy z) c4))
  (let-match erased c1 (CatC _ a xs _ zs c) ((CatN _ _) (values z c2 (CatN A z))))
  (let-match erased c2 (CatC _ _ _ _ z1 c5))
  (let ((erased wy) (erased c3) (erased c4)) (cat-assoc A xs w zs y z1 c c5))
  (values wy c3 (CatC A a xs wy z1 c4)))

(def-adts
  ((LStep : ((List (PT)) p) ((Conf) c) ((Conf) d) -> Type)
    enum
    (many LStepL : (erased (List (PT)) p) (erased (Nat) q q2) (erased (List (Bool)) l r) (erased (Bool) h w h2)
       (erased (PLook p q h (Def (Mov w (DL) q2))) pl)
       -> (LStep p (MkConf q (Cons (Bool) h2 l) h r) (MkConf q2 l h2 (Cons (Bool) w r))))
    (many LStepR : (erased (List (PT)) p) (erased (Nat) q q2) (erased (List (Bool)) l r r2) (erased (Bool) h w h2)
       (erased (PLook p q h (Def (Mov w (DR) q2))) pl) (erased (Pull r h2 r2) pp)
       -> (LStep p (MkConf q l h r) (MkConf q2 (Cons (Bool) w l) h2 r2)))))

(def-adts
  ((LRun : ((List (PT)) p) ((Conf) c) ((Nat) t) ((Conf) d) -> Type)
    enum
    (many LRNil : (erased (List (PT)) p) (erased (Conf) c) -> (LRun p c (Zero) c))
    (many LRCons : (erased (List (PT)) p) (erased (Conf) c c1 d) (erased (Nat) t) (erased (LStep p c c1) st) (erased (LRun p c1 t d) r)
       -> (LRun p c (Succ t) d))))

(def-fns _ $ (erased lstep-step : (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Ext p m) ex) (erased (Conf) c d)
    (erased (LStep p c d) st) -> (erased (Stp m c d) st2))
  (match erased st _
    ((LStepL _ q q2 l r h w h2 pl) (StepL m q q2 (Cons (Bool) h2 l) r l h w h2 (ext-look p m q h _ ex pl) (PullCons h2 l)))
    ((LStepR _ q q2 l r r2 h w h2 pl pp) (StepR m q q2 l r r2 h w h2 (ext-look p m q h _ ex pl) pp))))

(def-fns _ $ (erased lrun-frame : (erased (List (PT)) p) (erased (Nat) t q q2) (erased (List (Bool)) x r x2 r2 y xy) (erased (Bool) h h2)
    (subterm erased (LRun p (MkConf q x h r) t (MkConf q2 x2 h2 r2)) lr) (erased (Cat (Bool) x y xy) c)
    -> (erased (List (Bool)) xy2) (erased (Cat (Bool) x2 y xy2) c2) (erased (LRun p (MkConf q xy h r) t (MkConf q2 xy2 h2 r2)) lr2))
  (let-match erased lr (LRCons _ _ c1 _ t1 st rest) ((LRNil _ _) (values xy c (LRNil p (MkConf q xy h r)))))
  (match erased st _
    ((LStepL _ _ q3 l _ _ w h3 pl)
      (let-match erased c (CatC _ _ _ _ ly cl))
      (let ((erased xy2) (erased c2) (erased lr2)) (lrun-frame p t1 q3 q2 l (Cons (Bool) w r) x2 r2 y ly h3 h2 rest cl))
      (values xy2 c2 (LRCons p _ _ _ t1 (LStepL p q q3 ly r h w h3 pl) lr2)))
    ((LStepR _ _ q3 _ _ r3 _ w h3 pl pp)
      (let ((erased xy2) (erased c2) (erased lr2))
        (lrun-frame p t1 q3 q2 (Cons (Bool) w x) r3 x2 r2 y (Cons (Bool) w xy) h3 h2 rest (CatC (Bool) w x y xy c)))
      (values xy2 c2 (LRCons p _ _ _ t1 (LStepR p q q3 xy r r3 h w h3 pl pp) lr2)))))

(def-fns _ $ (erased absurd no-step : (erased (List (Tr)) m) (erased (Nat) q) (erased (List (Bool)) l r) (erased (Bool) h) (erased (Conf) d)
    (erased (Look m q h (Hlt)) lk) (erased (Stp m (MkConf q l h r) d) st) -> (erased (False) f))
  (match erased st _
    (absurd (StepL _ _ _ _ _ _ _ _ _ lk2 _) (look-fn m q h _ _ lk lk2))
    (absurd (StepR _ _ _ _ _ _ _ _ _ lk2 _) (look-fn m q h _ _ lk lk2))))

(def-fns _ $ (erased halts-run : (erased (List (Tr)) m) (erased (Conf) c d) (erased (Nat) t s) (subterm erased (Run m c t d) r)
    (erased (HaltsAt m c s) hs) -> (erased (Nat) v) (erased (HaltsAt m d v) hd))
  (let-match erased r (RSnoc _ _ c1 _ t1 r1 st) ((RNil _ _) (values s hs)))
  (let ((erased v1) (erased h1)) (halts-run m c c1 t1 s r1 hs))
  (let-match erased h1 (HMove _ _ d2 v2 st2 h2) (absurd (HStop _ q l rr h lk) (no-step m q l rr h d lk st)))
  (let-match erased (step-fn m c1 d d2 st st2) (Refl _ _))
  (values v2 h2))

(def-fns _ $ (erased halts-lrun : (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Ext p m) ex) (erased (Conf) c d) (erased (Nat) t u)
    (subterm erased (LRun p c t d) lr) (erased (HaltsAt m c u) hs) -> (erased (Nat) v) (erased (Add t v u) a) (erased (HaltsAt m d v) hd))
  (let-match erased lr (LRCons _ _ c1 _ t1 st rest) ((LRNil _ _) (values u (AddZero u) hs)))
  (let ((erased s1)) (lstep-step p m ex c c1 st))
  (let-match erased hs (HMove _ _ d2 u1 st2 hs2) (absurd (HStop _ q l r h lk) (no-step m q l r h c1 lk s1)))
  (let-match erased (step-fn m c c1 d2 s1 st2) (Refl _ _))
  (let ((erased v) (erased a) (erased hd)) (halts-lrun p m ex c1 d t1 u1 rest hs2))
  (values v (AddSucc t1 v u1 a) hd))

(def-adts
  ((Cyc : ((List (PT)) p) -> Type)
    enum
    (many MkCyc : (erased (List (PT)) p) (erased (Nat) t1 T q) (erased (List (Bool)) x w x2 r y lc) (erased (Bool) h)
       (erased (PRunTo p (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) t1 (MkConf q lc h r)) pr) (erased (Cat (Bool) x y lc) c)
       (erased (LRun p (MkConf q x h r) (Succ T) (MkConf q x2 h r)) lr) (erased (Cat (Bool) x w x2) cw) -> (Cyc p))))

(def-fns _ $ (erased absurd cyc-loop : (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Ext p m) ex) (erased (Nat) T q)
    (erased (List (Bool)) x w x2 r y xy) (erased (Bool) h) (erased (LRun p (MkConf q x h r) (Succ T) (MkConf q x2 h r)) lr)
    (erased (Cat (Bool) x w x2) cw) (erased (Cat (Bool) x y xy) c) (subterm erased (Nat) u) (erased (HaltsAt m (MkConf q xy h r) u) hs)
    -> (erased (False) f))
  (let ((erased xy2) (erased c2) (erased lr2)) (lrun-frame p (Succ T) q q x r x2 r y xy h h lr c))
  (let ((erased v) (erased a) (erased hd)) (halts-lrun p m ex _ _ (Succ T) u lr2 hs))
  (let ((erased wy) (erased c3) (erased c4)) (cat-assoc (Bool) x w x2 y xy2 cw c2))
  (let ((erased lt)) (add-pos-lt v (Succ T) u (add-comm (Succ T) v u a) (LtZ T)))
  (cyc-loop p m ex T q x w x2 r wy xy2 h lr cw c4 (subterm (lt-subterm v u lt)) v hd))

(def-fns _ $ (erased absurd never-cyc : (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Cyc p) cy) (erased (Ext p m) ex)
    (erased (Nat) s) (erased (HaltsAt m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) hs) -> (erased (False) f))
  (let-match erased cy (MkCyc _ t1 T q x w x2 r y lc h pr c lr cw))
  (let ((erased v) (erased hd)) (halts-run m _ _ t1 s (prun-run p m ex _ _ t1 pr) hs))
  (cyc-loop p m ex T q x w x2 r y lc h lr cw c v hd))

(def-adts
  ((XP : ((List (PT)) p) ((List (PT)) p2) -> Type)
    enum
    (many XPNil : -> (XP (Nil (PT)) (Nil (PT))))
    (many XPU : (erased (List (PT)) p p2) (erased (XP p p2) x) -> (XP (Cons (PT) (Undef) p) (Cons (PT) (Undef) p2)))
    (many XPD : (erased (Tr) t u) (erased (List (PT)) p p2) (erased (XT (BTrue) (Zero) (Zero) t u) e) (erased (XP p p2) x)
       -> (XP (Cons (PT) (Def t) p) (Cons (PT) (Def u) p2)))))

(def-fns _ $ (erased flip-fn : (erased (Bool) f) (erased (Mv) d e e2) (erased (Flip f d e) a) (erased (Flip f d e2) b) -> (erased (Eq (Mv) e e2) r))
  (match erased a _
    ((FlN _) (let-match erased b (FlN _)) (Refl (Mv) e))
    ((FlL) (let-match erased b (FlL)) (Refl (Mv) e))
    ((FlR) (let-match erased b (FlR)) (Refl (Mv) e))))

(def-fns _ $ (erased xt-fn : (erased (Tr) t u u2) (erased (XT (BTrue) (Zero) (Zero) t u) a) (erased (XT (BTrue) (Zero) (Zero) t u2) b)
    -> (erased (Eq (Tr) u u2) r))
  (let-match erased a (XTG _ _ _ w d e q q2 fl s) ((XTH _ _ _) (let-match erased b (XTH _ _ _)) (Refl (Tr) u)))
  (let-match erased b (XTG _ _ _ _ _ e2 _ q3 fl2 s2))
  (let-match erased (flip-fn (BTrue) d e e2 fl fl2) (Refl _ _))
  (let-match erased (swap-same (Zero) q q2 s) (Refl _ _))
  (let-match erased (swap-same (Zero) q q3 s2) (Refl _ _))
  (Refl (Tr) u))

(def-fns _ $ (erased ext-xp : (erased (List (PT)) p p2) (erased (List (Tr)) m v) (subterm erased (Ext p m) ex)
    (erased (XM (BTrue) (Zero) (Zero) m v) x) (erased (XP p p2) xp) -> (erased (Ext p2 v) ex2))
  (match erased ex _
    ((ExNil) (let-match erased x (XMNil _ _ _)) (let-match erased xp (XPNil)) (ExNil))
    ((ExU t p1 m1 ex1)
      (let-match erased x (XMCons _ _ _ _ u _ v1 _ x1))
      (let-match erased xp (XPU _ p21 xp1))
      (ExU u p21 v1 (ext-xp p1 p21 m1 v1 ex1 x1 xp1)))
    ((ExD t p1 m1 ex1)
      (let-match erased x (XMCons _ _ _ _ u _ v1 e x1))
      (let-match erased xp (XPD _ u2 _ p21 e2 xp1))
      (let-match erased (xt-fn t u u2 e e2) (Refl _ _))
      (ExD u p21 v1 (ext-xp p1 p21 m1 v1 ex1 x1 xp1)))))

(def-adts
  ((XE : ((PT) x) ((PT) y) -> Type)
    enum
    (many XEU : -> (XE (Undef) (Undef)))
    (many XED : (erased (Tr) t u) (erased (XT (BTrue) (Zero) (Zero) t u) e) -> (XE (Def t) (Def u)))))

(def-fns _ $ (erased xp-cons : (erased (PT) x) (erased (List (PT)) rest p2) (erased (XP (Cons (PT) x rest) p2) xp)
    -> (erased (PT) y) (erased (List (PT)) rest2) (erased (Eq (List (PT)) p2 (Cons (PT) y rest2)) eq) (erased (XE x y) xe) (erased (XP rest rest2) xr))
  (match erased xp _
    ((XPU _ r1 x1) (values (Undef) r1 (Refl (List (PT)) p2) (XEU) x1))
    ((XPD t u _ r1 e x1) (values (Def u) r1 (Refl (List (PT)) p2) (XED t u e) x1))))

(def-fns _ $ (erased xp-pair : (erased (PT) x0 x1) (erased (List (PT)) rest p2) (erased (XP (Cons (PT) x0 (Cons (PT) x1 rest)) p2) xp)
    -> (erased (PT) y0 y1) (erased (List (PT)) rest2) (erased (Eq (List (PT)) p2 (Cons (PT) y0 (Cons (PT) y1 rest2))) eq)
    (erased (XE x0 y0) e0) (erased (XE x1 y1) e1) (erased (XP rest rest2) xr))
  (let ((erased y0) (erased p21) (erased eq0) (erased e0) (erased xp1)) (xp-cons x0 (Cons (PT) x1 rest) p2 xp))
  (let-match erased eq0 (Refl _ _))
  (let ((erased y1) (erased r2) (erased eq1) (erased e1) (erased xr)) (xp-cons x1 rest p21 xp1))
  (let-match erased eq1 (Refl _ _))
  (values y0 y1 r2 (Refl (List (PT)) p2) e0 e1 xr))

(def-fns _ $ (erased xe-mov : (erased (Bool) w) (erased (Mv) d) (erased (Nat) q) (erased (PT) y) (erased (XE (Def (Mov w d q)) y) xe)
    -> (erased (Mv) e) (erased (Flip (BTrue) d e) fl) (erased (Eq (PT) y (Def (Mov w e q))) eq))
  (let-match erased xe (XED _ u xt))
  (let-match erased xt (XTG _ _ _ _ _ e _ q2 fl s))
  (let-match erased (swap-same (Zero) q q2 s) (Refl _ _))
  (values e fl (Refl _ _)))

(def-fns _ $ (erased plook-xp : (erased (List (PT)) p p2) (erased (Nat) q q2) (erased (Bool) h w) (erased (Mv) d) (erased (XP p p2) xp)
    (subterm erased (PLook p q h (Def (Mov w d q2))) pl) -> (erased (Mv) e) (erased (Flip (BTrue) d e) fl) (erased (PLook p2 q h (Def (Mov w e q2))) pl2))
  (match erased pl _
    ((PL0 x0 x1 rest)
      (let ((erased y0) (erased y1) (erased r2) (erased eq) (erased e0) (erased e1) (erased xr)) (xp-pair x0 x1 rest p2 xp))
      (let-match erased eq (Refl _ _))
      (let ((erased e) (erased fl) (erased eq2)) (xe-mov w d q2 y0 e0))
      (let-match erased eq2 (Refl _ _))
      (values e fl (PL0 y0 y1 r2)))
    ((PL1 x0 x1 rest)
      (let ((erased y0) (erased y1) (erased r2) (erased eq) (erased e0) (erased e1) (erased xr)) (xp-pair x0 x1 rest p2 xp))
      (let-match erased eq (Refl _ _))
      (let ((erased e) (erased fl) (erased eq2)) (xe-mov w d q2 y1 e1))
      (let-match erased eq2 (Refl _ _))
      (values e fl (PL1 y0 y1 r2)))
    ((PLS x0 x1 rest q1 _ _ pl1)
      (let ((erased y0) (erased y1) (erased r2) (erased eq) (erased e0) (erased e1) (erased xr)) (xp-pair x0 x1 rest p2 xp))
      (let-match erased eq (Refl _ _))
      (let ((erased e) (erased fl) (erased pl3)) (plook-xp rest r2 q1 q2 h w d xr pl1))
      (values e fl (PLS y0 y1 r2 q1 h _ pl3)))))

(def-fns _ $ (erased prun-flip : (erased (List (PT)) p p2) (erased (Nat) qz q t) (erased (List (Bool)) lz rz l r) (erased (Bool) hz h) (erased (XP p p2) xp)
    (subterm erased (PRunTo p (MkConf qz lz hz rz) t (MkConf q l h r)) pr) -> (erased (PRunTo p2 (MkConf qz rz hz lz) t (MkConf q r h l)) r2))
  (let-match erased pr (PRSnoc _ _ _ _ t1 pr1 st) ((PRNil _ _) (PRNil p2 _)))
  (match erased st _
      ((PStepL _ q1 q2 l1 r1 l2 h1 w h2 pl pp)
        (let ((erased e) (erased fl) (erased pl2)) (plook-xp p p2 q1 q2 h1 w (DL) xp pl))
        (let-match erased fl (FlL))
        (PRSnoc p2 _ _ _ t1 (prun-flip p p2 qz q1 t1 lz rz l1 r1 hz h1 xp pr1) (PStepR p2 q1 q2 r1 l1 l2 h1 w h2 pl2 pp)))
      ((PStepR _ q1 q2 l1 r1 r2 h1 w h2 pl pp)
        (let ((erased e) (erased fl) (erased pl2)) (plook-xp p p2 q1 q2 h1 w (DR) xp pl))
        (let-match erased fl (FlR))
        (PRSnoc p2 _ _ _ t1 (prun-flip p p2 qz q1 t1 lz rz l1 r1 hz h1 xp pr1) (PStepL p2 q1 q2 r1 l1 r2 h1 w h2 pl2 pp)))))

(def-adts
  ((Mir : ((Bool) f) ((List (PT)) p) ((List (PT)) p2) -> Type)
    enum
    (many MirN : (erased (List (PT)) p) -> (Mir (BFalse) p p))
    (many MirY : (erased (List (PT)) p p2) (erased (XP p p2) xp) -> (Mir (BTrue) p p2))))

(def-fns _ $ (erased absurd never-flip : (erased (List (PT)) p p2) (erased (List (Tr)) m) (erased (XP p p2) xp) (erased (Cyc p2) cy)
    (erased (Ext p m) ex) (erased (Nat) s) (erased (HaltsAt m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) hs) -> (erased (False) f))
  (let ((erased v) (erased x)) (xm-of (BTrue) (Zero) (Zero) m))
  (let ((erased pm)) (PMId (BTrue) (Zero) m v x))
  (never-cyc p2 v cy (ext-xp p p2 m v ex x xp) s
    (pm-halts (BTrue) (Zero) (Zero) m v (Zero) (Zero) (Nil (Bool)) (Nil (Bool)) (Nil (Bool)) (Nil (Bool)) (BFalse) s hs pm (SwA (Zero) (Zero))
      (FC1 (Nil (Bool)) (Nil (Bool))))))

(def-fns _ $ (erased absurd never-mir : (erased (Bool) f) (erased (List (PT)) p p2) (erased (List (Tr)) m) (erased (Mir f p p2) mi) (erased (Cyc p2) cy)
    (erased (Ext p m) ex) (erased (Nat) s) (erased (HaltsAt m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) hs) -> (erased (False) f2))
  (match erased mi _
    (absurd (MirN _) (never-cyc p m cy ex s hs))
    (absurd (MirY _ _ xp) (never-flip p p2 m xp cy ex s hs))))
