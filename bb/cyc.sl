
(def-adts
  ((PStep : ((List (PT)) p) ((Cfg) c) ((Cfg) d) -> Type)
    enum
    (many PStepL : (erased (List (PT)) p) (erased (Nat) q q2) (erased (List (Bool)) l r l2) (erased (Bool) h w h2)
       (erased (PLook p q h (Def (Go w (DL) q2))) pl) (erased (Pop l h2 l2) pp)
       -> (PStep p (MkCfg q l h r) (MkCfg q2 l2 h2 (Cons (Bool) w r))))
    (many PStepR : (erased (List (PT)) p) (erased (Nat) q q2) (erased (List (Bool)) l r r2) (erased (Bool) h w h2)
       (erased (PLook p q h (Def (Go w (DR) q2))) pl) (erased (Pop r h2 r2) pp)
       -> (PStep p (MkCfg q l h r) (MkCfg q2 (Cons (Bool) w l) h2 r2)))))

(def-adts
  ((PRunTo : ((List (PT)) p) ((Cfg) c0) ((Nat) t) ((Cfg) c) -> Type)
    enum
    (many PRNil : (erased (List (PT)) p) (erased (Cfg) c0) -> (PRunTo p c0 (Zero) c0))
    (many PRSnoc : (erased (List (PT)) p) (erased (Cfg) c0 c d) (erased (Nat) t)
       (erased (PRunTo p c0 t c) r) (erased (PStep p c d) st) -> (PRunTo p c0 (Succ t) d))))

(def-fns _ $ (erased prun-run : (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Ext p m) ex) (erased (Cfg) c0 c) (erased (Nat) t)
    (subterm erased (PRunTo p c0 t c) pr) -> (erased (Run m c0 t c) r))
  (match erased pr _
    ((PRNil _ _) (RNil m c0))
    ((PRSnoc _ _ c1 _ t1 pr1 st)
      (let ((erased r1)) (prun-run p m ex c0 c1 t1 pr1))
      (match erased st _
        ((PStepL _ q q2 l rr l2 h w h2 pl pp) (RSnoc m c0 c1 c t1 r1 (StepL m q q2 l rr l2 h w h2 (ext-look p m q h _ ex pl) pp)))
        ((PStepR _ q q2 l rr r2 h w h2 pl pp) (RSnoc m c0 c1 c t1 r1 (StepR m q q2 l rr r2 h w h2 (ext-look p m q h _ ex pl) pp)))))))

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
  ((LStep : ((List (PT)) p) ((Cfg) c) ((Cfg) d) -> Type)
    enum
    (many LStepL : (erased (List (PT)) p) (erased (Nat) q q2) (erased (List (Bool)) l r) (erased (Bool) h w h2)
       (erased (PLook p q h (Def (Go w (DL) q2))) pl)
       -> (LStep p (MkCfg q (Cons (Bool) h2 l) h r) (MkCfg q2 l h2 (Cons (Bool) w r))))
    (many LStepR : (erased (List (PT)) p) (erased (Nat) q q2) (erased (List (Bool)) l r r2) (erased (Bool) h w h2)
       (erased (PLook p q h (Def (Go w (DR) q2))) pl) (erased (Pop r h2 r2) pp)
       -> (LStep p (MkCfg q l h r) (MkCfg q2 (Cons (Bool) w l) h2 r2)))))

(def-adts
  ((LRun : ((List (PT)) p) ((Cfg) c) ((Nat) t) ((Cfg) d) -> Type)
    enum
    (many LRNil : (erased (List (PT)) p) (erased (Cfg) c) -> (LRun p c (Zero) c))
    (many LRCons : (erased (List (PT)) p) (erased (Cfg) c c1 d) (erased (Nat) t) (erased (LStep p c c1) st) (erased (LRun p c1 t d) r)
       -> (LRun p c (Succ t) d))))

(def-fns _ $ (erased lstep-step : (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Ext p m) ex) (erased (Cfg) c d)
    (erased (LStep p c d) st) -> (erased (Step m c d) st2))
  (match erased st _
    ((LStepL _ q q2 l r h w h2 pl) (StepL m q q2 (Cons (Bool) h2 l) r l h w h2 (ext-look p m q h _ ex pl) (PopCons h2 l)))
    ((LStepR _ q q2 l r r2 h w h2 pl pp) (StepR m q q2 l r r2 h w h2 (ext-look p m q h _ ex pl) pp))))

(def-fns _ $ (erased lrun-frame : (erased (List (PT)) p) (erased (Nat) t q q2) (erased (List (Bool)) x r x2 r2 y xy) (erased (Bool) h h2)
    (subterm erased (LRun p (MkCfg q x h r) t (MkCfg q2 x2 h2 r2)) lr) (erased (Cat (Bool) x y xy) c)
    -> (erased (List (Bool)) xy2) (erased (Cat (Bool) x2 y xy2) c2) (erased (LRun p (MkCfg q xy h r) t (MkCfg q2 xy2 h2 r2)) lr2))
  (let-match erased lr (LRCons _ _ c1 _ t1 st rest) ((LRNil _ _) (values xy c (LRNil p (MkCfg q xy h r)))))
  (match erased st _
    ((LStepL _ _ q3 l _ _ w h3 pl)
      (let-match erased c (CatC _ _ _ _ ly cl))
      (let ((erased xy2) (erased c2) (erased lr2)) (lrun-frame p t1 q3 q2 l (Cons (Bool) w r) x2 r2 y ly h3 h2 rest cl))
      (values xy2 c2 (LRCons p _ _ _ t1 (LStepL p q q3 ly r h w h3 pl) lr2)))
    ((LStepR _ _ q3 _ _ r3 _ w h3 pl pp)
      (let ((erased xy2) (erased c2) (erased lr2))
        (lrun-frame p t1 q3 q2 (Cons (Bool) w x) r3 x2 r2 y (Cons (Bool) w xy) h3 h2 rest (CatC (Bool) w x y xy c)))
      (values xy2 c2 (LRCons p _ _ _ t1 (LStepR p q q3 xy r r3 h w h3 pl pp) lr2)))))

(def-fns _ $ (erased absurd no-step : (erased (List (Tr)) m) (erased (Nat) q) (erased (List (Bool)) l r) (erased (Bool) h) (erased (Cfg) d)
    (erased (Look m q h (Halt)) lk) (erased (Step m (MkCfg q l h r) d) st) -> (erased (False) f))
  (match erased st _
    (absurd (StepL _ _ _ _ _ _ _ _ _ lk2 _) (look-fn m q h _ _ lk lk2))
    (absurd (StepR _ _ _ _ _ _ _ _ _ lk2 _) (look-fn m q h _ _ lk lk2))))

(def-fns _ $ (erased halts-run : (erased (List (Tr)) m) (erased (Cfg) c d) (erased (Nat) t s) (subterm erased (Run m c t d) r)
    (erased (HaltsIn m c s) hs) -> (erased (Nat) v) (erased (HaltsIn m d v) hd))
  (let-match erased r (RSnoc _ _ c1 _ t1 r1 st) ((RNil _ _) (values s hs)))
  (let ((erased v1) (erased h1)) (halts-run m c c1 t1 s r1 hs))
  (let-match erased h1 (HMove _ _ d2 v2 st2 h2) (absurd (HStop _ q l rr h lk) (no-step m q l rr h d lk st)))
  (let-match erased (step-fn m c1 d d2 st st2) (Refl _ _))
  (values v2 h2))

(def-fns _ $ (erased halts-lrun : (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Ext p m) ex) (erased (Cfg) c d) (erased (Nat) t u)
    (subterm erased (LRun p c t d) lr) (erased (HaltsIn m c u) hs) -> (erased (Nat) v) (erased (Add t v u) a) (erased (HaltsIn m d v) hd))
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
       (erased (PRunTo p (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) t1 (MkCfg q lc h r)) pr) (erased (Cat (Bool) x y lc) c)
       (erased (LRun p (MkCfg q x h r) (Succ T) (MkCfg q x2 h r)) lr) (erased (Cat (Bool) x w x2) cw) -> (Cyc p))))

(def-fns _ $ (erased absurd cyc-loop : (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Ext p m) ex) (erased (Nat) T q)
    (erased (List (Bool)) x w x2 r y xy) (erased (Bool) h) (erased (LRun p (MkCfg q x h r) (Succ T) (MkCfg q x2 h r)) lr)
    (erased (Cat (Bool) x w x2) cw) (erased (Cat (Bool) x y xy) c) (subterm erased (Nat) u) (erased (HaltsIn m (MkCfg q xy h r) u) hs)
    -> (erased (False) f))
  (let ((erased xy2) (erased c2) (erased lr2)) (lrun-frame p (Succ T) q q x r x2 r y xy h h lr c))
  (let ((erased v) (erased a) (erased hd)) (halts-lrun p m ex _ _ (Succ T) u lr2 hs))
  (let ((erased wy) (erased c3) (erased c4)) (cat-assoc (Bool) x w x2 y xy2 cw c2))
  (let ((erased lt)) (add-pos-lt v (Succ T) u (add-comm (Succ T) v u a) (LtZ T)))
  (cyc-loop p m ex T q x w x2 r wy xy2 h lr cw c4 (subterm (lt-subterm v u lt)) v hd))

(def-fns _ $ (erased absurd never-cyc : (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Cyc p) cy) (erased (Ext p m) ex)
    (erased (Nat) s) (erased (HaltsIn m (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) hs) -> (erased (False) f))
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

(def-fns _ $ (erased flip-fn : (erased (Bool) f) (erased (Dir) d e e2) (erased (Flip f d e) a) (erased (Flip f d e2) b) -> (erased (Eq (Dir) e e2) r))
  (match erased a _
    ((FlN _) (let-match erased b (FlN _)) (Refl (Dir) e))
    ((FlL) (let-match erased b (FlL)) (Refl (Dir) e))
    ((FlR) (let-match erased b (FlR)) (Refl (Dir) e))))

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
  ((Mir : ((Bool) f) ((List (PT)) p) ((List (PT)) p2) -> Type)
    enum
    (many MirN : (erased (List (PT)) p) -> (Mir (BFalse) p p))
    (many MirY : (erased (List (PT)) p p2) (erased (XP p p2) xp) -> (Mir (BTrue) p p2))))

(def-fns _ $ (erased absurd never-flip : (erased (List (PT)) p p2) (erased (List (Tr)) m) (erased (XP p p2) xp) (erased (Cyc p2) cy)
    (erased (Ext p m) ex) (erased (Nat) s) (erased (HaltsIn m (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) hs) -> (erased (False) f))
  (let ((erased v) (erased x)) (xm-of (BTrue) (Zero) (Zero) m))
  (let ((erased pm)) (PMId (BTrue) (Zero) m v x))
  (never-cyc p2 v cy (ext-xp p p2 m v ex x xp) s
    (pm-halts (BTrue) (Zero) (Zero) m v (Zero) (Zero) (Nil (Bool)) (Nil (Bool)) (Nil (Bool)) (Nil (Bool)) (BFalse) s hs pm (SwA (Zero) (Zero))
      (FC1 (Nil (Bool)) (Nil (Bool))))))

(def-fns _ $ (erased absurd never-mir : (erased (Bool) f) (erased (List (PT)) p p2) (erased (List (Tr)) m) (erased (Mir f p p2) mi) (erased (Cyc p2) cy)
    (erased (Ext p m) ex) (erased (Nat) s) (erased (HaltsIn m (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) hs) -> (erased (False) f2))
  (match erased mi _
    (absurd (MirN _) (never-cyc p m cy ex s hs))
    (absurd (MirY _ _ xp) (never-flip p p2 m xp cy ex s hs))))
