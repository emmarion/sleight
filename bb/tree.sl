
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
  ((PSet : ((List (PT)) p) ((Nat) q) ((Bool) b) ((PT) y) ((List (PT)) p2) -> Type)
    enum
    (many PS0 : (erased (PT) x0 x1 y) (erased (List (PT)) rest) -> (PSet (Cons (PT) x0 (Cons (PT) x1 rest)) (Zero) (BFalse) y (Cons (PT) y (Cons (PT) x1 rest))))
    (many PS1 : (erased (PT) x0 x1 y) (erased (List (PT)) rest) -> (PSet (Cons (PT) x0 (Cons (PT) x1 rest)) (Zero) (BTrue) y (Cons (PT) x0 (Cons (PT) y rest))))
    (many PSS : (erased (PT) x0 x1 y) (erased (List (PT)) rest rest2) (erased (Nat) q) (erased (Bool) b) (erased (PSet rest q b y rest2) p)
       -> (PSet (Cons (PT) x0 (Cons (PT) x1 rest)) (Succ q) b y (Cons (PT) x0 (Cons (PT) x1 rest2))))))

(def-fns _ $ (erased ext-look-any : (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Nat) q) (erased (Bool) b) (erased (PT) x)
    (erased (Ext p m) e) (subterm erased (PLook p q b x) pl) -> (erased (Tr) t) (erased (Look m q b t) lk))
  (match erased pl _
    ((PL0 x0 x1 rest)
      (let ((erased t0) (erased t1) (erased m2) (erased eq) (erased e2)) (ext-pair x0 x1 rest m e))
      (let-match erased eq (Refl _ _))
      (values t0 (Look0 t0 t1 m2)))
    ((PL1 x0 x1 rest)
      (let ((erased t0) (erased t1) (erased m2) (erased eq) (erased e2)) (ext-pair x0 x1 rest m e))
      (let-match erased eq (Refl _ _))
      (values t1 (Look1 t0 t1 m2)))
    ((PLS x0 x1 rest q1 _ _ pl1)
      (let ((erased t0) (erased t1) (erased m2) (erased eq) (erased e2)) (ext-pair x0 x1 rest m e))
      (let-match erased eq (Refl _ _))
      (let ((erased t) (erased lk1)) (ext-look-any rest m2 q1 b x e2 pl1))
      (values t (LookS t0 t1 m2 q1 b t lk1)))))

(def-fns _ $ (erased ext-set : (erased (List (PT)) p p2) (erased (List (Tr)) m) (erased (Nat) q) (erased (Bool) b) (erased (Tr) t)
    (erased (Ext p m) e) (subterm erased (PSet p q b (Def t) p2) ps) (erased (Look m q b t) lk) -> (erased (Ext p2 m) e2))
  (match erased ps _
    ((PS0 x0 x1 _ rest)
      (let ((erased t0) (erased m1) (erased eq) (erased e1)) (ext-tail x0 (Cons (PT) x1 rest) m e))
      (let-match erased eq (Refl _ _))
      (let-match erased lk (Look0 _ t1 m2))
      (ExD t (Cons (PT) x1 rest) m1 e1))
    ((PS1 x0 x1 _ rest)
      (let ((erased t0) (erased m1) (erased eq) (erased e1)) (ext-tail x0 (Cons (PT) x1 rest) m e))
      (let-match erased eq (Refl _ _))
      (let ((erased t1) (erased m2) (erased eq2) (erased e2)) (ext-tail x1 rest m1 e1))
      (let-match erased eq2 (Refl _ _))
      (let-match erased lk (Look1 _ _ _))
      (ext-retail x0 (Cons (PT) x1 rest) (Cons (PT) (Def t) rest) t0 m1 m1 e (ExD t rest m2 e2)))
    ((PSS x0 x1 _ rest rest2 q1 _ ps1)
      (let ((erased t0) (erased m1) (erased eq) (erased e1)) (ext-tail x0 (Cons (PT) x1 rest) m e))
      (let-match erased eq (Refl _ _))
      (let ((erased t1) (erased m2) (erased eq2) (erased e2)) (ext-tail x1 rest m1 e1))
      (let-match erased eq2 (Refl _ _))
      (let-match erased lk (LookS _ _ _ _ _ _ lk1))
      (let ((erased e3)) (ext-set rest rest2 m2 q1 b t e2 ps1 lk1))
      (ext-retail x0 (Cons (PT) x1 rest) (Cons (PT) x1 rest2) t0 m1 (Cons (Tr) t1 m2) e (ext-retail x1 rest rest2 t1 m2 m2 e1 e3)))))

(def-adts
  ((AllGo : ((List (PT)) p) -> Type)
    enum
    (many AGNil : -> (AllGo (Nil (PT))))
    (many AGCons : (erased (Bool) w) (erased (Dir) d) (erased (Nat) q) (erased (List (PT)) p) (erased (AllGo p) g)
       -> (AllGo (Cons (PT) (Def (Go w d q)) p)))))

(def-adts
  ((AllGoM : ((List (Tr)) m) -> Type)
    enum
    (many AGMNil : -> (AllGoM (Nil (Tr))))
    (many AGMCons : (erased (Bool) w) (erased (Dir) d) (erased (Nat) q) (erased (List (Tr)) m) (erased (AllGoM m) g)
       -> (AllGoM (Cons (Tr) (Go w d q) m)))))

(def-fns _ $ (erased ag-m : (erased (List (PT)) p) (erased (List (Tr)) m) (erased (AllGo p) g) (subterm erased (Ext p m) ex) -> (erased (AllGoM m) gm))
  (match erased ex _
    ((ExNil) (AGMNil))
    (absurd (ExU _ _ _ _) (match erased g _))
    ((ExD t p1 m1 e1) (let-match erased g (AGCons w d q _ g1)) (AGMCons w d q m1 (ag-m p1 m1 g1 e1)))))

(def-fns _ $ (erased absurd go-no-halt : (erased (List (Tr)) m) (erased (Nat) q) (erased (Bool) b) (erased (AllGoM m) g)
    (subterm erased (Look m q b (Halt)) lk) -> (erased (False) f))
  (match erased lk _
    (absurd (Look0 _ _ _) (match erased g _))
    (absurd (Look1 _ _ _) (let-match erased g (AGMCons _ _ _ _ g1)) (match erased g1 _))
    (absurd (LookS _ _ rest q1 _ _ lk1)
      (let-match erased g (AGMCons _ _ _ _ g1))
      (let-match erased g1 (AGMCons _ _ _ _ g2))
      (go-no-halt rest q1 b g2 lk1))))

(def-fns _ $ (erased absurd never-full : (erased (List (Tr)) m) (erased (Cfg) c) (erased (Nat) s) (erased (AllGoM m) g)
    (subterm erased (HaltsIn m c s) hs) -> (erased (False) f))
  (match erased hs _
    (absurd (HStop _ q _ _ h lk) (go-no-halt m q h g lk))
    (absurd (HMove _ _ d s1 _ rest) (never-full m d s1 g rest))))

(def-adts
  ((TNode : ((Nat) n) ((Nat) k) ((List (PT)) p) -> Type)
    enum
    (many TH : (erased (Nat) n k) (erased (List (PT)) p) (erased (Nat) t q) (erased (List (Bool)) l r) (erased (Bool) h)
       (erased (PRunTo p (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) t (MkCfg q l h r)) pr) (erased (PLook p q h (Def (Halt))) pl)
       (erased (Lt (Succ t) (Succ k)) lt) -> (TNode n k p))
    (many TN : (erased (Nat) n k) (erased (List (PT)) p)
       (erased (List (Bool)) sy) (erased (List (Edge)) es) (erased (List (Nat)) acc) (erased (List (ACN)) S)
       (erased (ClosedN p sy es S S) cl) (erased (AccAll sy es acc acc) aa) (erased (ACN) a0) (erased (Mem (ACN) a0 S) ma)
       (erased (GCN sy es acc a0 (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool)))) g) -> (TNode n k p))
    (many TS : (erased (Nat) n k) (erased (List (PT)) p) (erased (Nat) t q) (erased (List (Bool)) l r) (erased (Bool) h)
       (erased (PRunTo p (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) t (MkCfg q l h r)) pr) (erased (PLook p q h (Undef)) pl)
       (erased (Nat) c c2) (erased (List (Nat)) xs) (erased (List (Tr)) os) (erased (Range c2 xs) rg) (erased (Opts xs os) op)
       (erased (NextC n c c2) nc) (erased (UF c p) uf) (erased (Below c p) bl) (erased (Lt q c) lq)
       (erased (TAll n k p q h os) ta) -> (TNode n k p))
    (many TF : (erased (Nat) n k) (erased (List (PT)) p) (erased (AllGo p) g) -> (TNode n k p)))
  ((TAll : ((Nat) n) ((Nat) k) ((List (PT)) p) ((Nat) q) ((Bool) h) ((List (Tr)) os) -> Type)
    enum
    (many TANil : (erased (Nat) n k) (erased (List (PT)) p) (erased (Nat) q) (erased (Bool) h) -> (TAll n k p q h (Nil (Tr))))
    (many TACons : (erased (Nat) n k) (erased (List (PT)) p p2) (erased (Nat) q) (erased (Bool) h) (erased (Tr) x) (erased (List (Tr)) os)
       (erased (PSet p q h (Def x) p2) ps) (erased (TNode n k p2) tn) (erased (TAll n k p q h os) rest) -> (TAll n k p q h (Cons (Tr) x os)))))

(def-fns _
  ((erased tn-good : (erased (Nat) n k) (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Nat) s)
       (subterm erased (TNode n k p) tn) (erased (Ext p m) ex) (erased (Rows n n m) wf)
       (erased (HaltsIn m (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) hs) -> (erased (Lt s (Succ k)) r))
    (match erased tn _
      ((TH _ _ _ t q l r h pr pl lt)
        (let ((erased run)) (prun-run p m ex _ _ t pr))
        (let ((erased h1)) (run-add m _ (MkCfg q l h r) t (Succ (Zero)) (Succ t) run (HStop m q l r h (ext-look p m q h _ ex pl))
          (add-succ-right t (Zero) t (add-zero-right t))))
        (let-match erased (halts-fn m _ s (Succ t) hs h1) (Refl _ _))
        lt)
      (absurd (TN _ _ _ sy es acc S cl aa a0 ma g) (never-n p m ex sy es acc S cl aa a0 ma _ g s hs))
      (absurd (TF _ _ _ g) (never-full m _ s (ag-m p m g ex) hs))
      ((TS _ _ _ t q l r h pr pl c c2 xs os rg op nc uf bl lq ta)
        (let ((erased tq) (erased lkq)) (ext-look-any p m q h _ ex pl))
        (let ((erased m2) (erased ex2) (erased wf2) (erased hs2) (erased tq2) (erased lk2) (erased mm) (erased _) (erased _) (erased _))
          (fit n c c2 q s xs os p m h tq rg op nc uf bl lq ex wf hs lkq))
        (ta-pick n k p m2 s q h tq2 os ta mm ex2 pl lk2 wf2 hs2))))
  ((erased ta-pick : (erased (Nat) n k) (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Nat) s q) (erased (Bool) h) (erased (Tr) tq)
       (erased (List (Tr)) os) (subterm erased (TAll n k p q h os) ta) (erased (Mem (Tr) tq os) mm) (erased (Ext p m) ex)
       (erased (PLook p q h (Undef)) pl) (erased (Look m q h tq) lkq) (erased (Rows n n m) wf)
       (erased (HaltsIn m (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) hs) -> (erased (Lt s (Succ k)) r))
    (match erased mm _
      ((MemHere _ _ os1)
        (let-match erased ta (TACons _ _ _ p2 _ _ _ _ ps tn _))
        (tn-good n k p2 m s tn (ext-set p p2 m q h tq ex ps lkq) wf hs))
      ((MemThere _ _ y os1 mm1)
        (let-match erased ta (TACons _ _ _ _ _ _ _ _ _ _ ta1))
        (ta-pick n k p m s q h tq os1 ta1 mm1 ex pl lkq wf hs)))))
