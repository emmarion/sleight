
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

(def-fns _ $ (erased ext-pair : (erased (PT) x0 x1) (erased (List (PT)) rest) (erased (List (Tr)) m)
    (erased (Ext (Cons (PT) x0 (Cons (PT) x1 rest)) m) e) ->
    (erased (Tr) t0 t1) (erased (List (Tr)) m2) (erased (Eq (List (Tr)) m (Cons (Tr) t0 (Cons (Tr) t1 m2))) eq) (erased (Ext rest m2) e2))
  (let ((erased t0) (erased m1) (erased e1) (erased eq0))
    (match erased e (((Tr) t0) ((List (Tr)) m1) ((Ext (Cons (PT) x1 rest) m1) e1) ((Eq (List (Tr)) m (Cons (Tr) t0 m1)) eq0))
      ((ExU t0 _ m1 e1) (values t0 m1 e1 (Refl _ m)))
      ((ExD t0 _ m1 e1) (values t0 m1 e1 (Refl _ m)))))
  (let-match erased eq0 (Refl _ _))
  (let ((erased t1) (erased m2) (erased e2) (erased eq))
    (match erased e1 (((Tr) t1) ((List (Tr)) m2) ((Ext rest m2) e2) ((Eq (List (Tr)) m1 (Cons (Tr) t1 m2)) eq))
      ((ExU t1 _ m2 e2) (values t1 m2 e2 (Refl _ m1)))
      ((ExD t1 _ m2 e2) (values t1 m2 e2 (Refl _ m1)))))
  (let-match erased eq (Refl _ _))
  (values t0 t1 m2 (Refl _ m) e2))

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

(def-fns _ $ (erased ext-tail : (erased (PT) x) (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Ext (Cons (PT) x p) m) e) ->
    (erased (Tr) t) (erased (List (Tr)) m1) (erased (Eq (List (Tr)) m (Cons (Tr) t m1)) eq) (erased (Ext p m1) e1))
  (match erased e _
    ((ExU t _ m1 e1) (values t m1 (Refl _ m) e1))
    ((ExD t _ m1 e1) (values t m1 (Refl _ m) e1))))

(def-fns _ $ (erased ext-retail : (erased (PT) x) (erased (List (PT)) p p2) (erased (Tr) t) (erased (List (Tr)) m m2)
    (erased (Ext (Cons (PT) x p) (Cons (Tr) t m)) e) (erased (Ext p2 m2) e2) -> (erased (Ext (Cons (PT) x p2) (Cons (Tr) t m2)) e3))
  (match erased e _
    ((ExU _ _ _ _) (ExU t p2 m2 e2))
    ((ExD _ _ _ _) (ExD t p2 m2 e2))))

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
  ((TNode : ((Nat) k) ((List (Tr)) O) ((List (PT)) p) -> Type)
    enum
    (many TH : (erased (Nat) k) (erased (List (Tr)) O) (erased (List (PT)) p) (erased (Nat) t q) (erased (List (Bool)) l r) (erased (Bool) h)
       (erased (PRunTo p (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) t (MkCfg q l h r)) pr) (erased (PLook p q h (Def (Halt))) pl)
       (erased (Lt (Succ t) (Succ k)) lt) -> (TNode k O p))
    (many TN : (erased (Nat) k) (erased (List (Tr)) O) (erased (List (PT)) p)
       (erased (List (Bool)) sy) (erased (List (Edge)) es) (erased (List (Nat)) acc) (erased (List (ACN)) S)
       (erased (ClosedN p sy es S S) cl) (erased (AccAll sy es acc acc) aa) (erased (ACN) a0) (erased (Mem (ACN) a0 S) ma)
       (erased (GCN sy es acc a0 (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool)))) g) -> (TNode k O p))
    (many TS : (erased (Nat) k) (erased (List (Tr)) O) (erased (List (PT)) p) (erased (Nat) t q) (erased (List (Bool)) l r) (erased (Bool) h)
       (erased (PRunTo p (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) t (MkCfg q l h r)) pr) (erased (PLook p q h (Undef)) pl)
       (erased (TAll k O p q h O) ta) -> (TNode k O p)))
  ((TAll : ((Nat) k) ((List (Tr)) O) ((List (PT)) p) ((Nat) q) ((Bool) h) ((List (Tr)) os) -> Type)
    enum
    (many TANil : (erased (Nat) k) (erased (List (Tr)) O) (erased (List (PT)) p) (erased (Nat) q) (erased (Bool) h) -> (TAll k O p q h (Nil (Tr))))
    (many TACons : (erased (Nat) k) (erased (List (Tr)) O) (erased (List (PT)) p p2) (erased (Nat) q) (erased (Bool) h) (erased (Tr) x) (erased (List (Tr)) os)
       (erased (PSet p q h (Def x) p2) ps) (erased (TNode k O p2) tn) (erased (TAll k O p q h os) rest) -> (TAll k O p q h (Cons (Tr) x os)))))

(def-fns _
  ((erased tn-good : (erased (Nat) n k) (erased (List (Nat)) xs) (erased (List (Tr)) O) (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Nat) s)
       (subterm erased (TNode k O p) tn) (erased (Ext p m) ex) (erased (Rows n n m) wf) (erased (Range n xs) rg) (erased (Opts xs O) op)
       (erased (HaltsIn m (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) hs) -> (erased (Lt s (Succ k)) r))
    (match erased tn _
      ((TH _ _ _ t q l r h pr pl lt)
        (let ((erased run)) (prun-run p m ex _ _ t pr))
        (let ((erased h1)) (run-add m _ (MkCfg q l h r) t (Succ (Zero)) (Succ t) run (HStop m q l r h (ext-look p m q h _ ex pl))
          (add-succ-right t (Zero) t (add-zero-right t))))
        (let-match erased (halts-fn m _ s (Succ t) hs h1) (Refl _ _))
        lt)
      (absurd (TN _ _ _ sy es acc S cl aa a0 ma g) (never-n p m ex sy es acc S cl aa a0 ma _ g s hs))
      ((TS _ _ _ t q l r h pr pl ta)
        (let ((erased tq) (erased lkq)) (ext-look-any p m q h _ ex pl))
        (let ((erased mm)) (tr-mem n xs O tq (look-ok n n q m h tq wf lkq) rg op))
        (ta-pick n k xs O p m s q h tq O ta mm ex pl lkq wf rg op hs))))
  ((erased ta-pick : (erased (Nat) n k) (erased (List (Nat)) xs) (erased (List (Tr)) O) (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Nat) s q)
       (erased (Bool) h) (erased (Tr) tq) (erased (List (Tr)) os)
       (subterm erased (TAll k O p q h os) ta) (erased (Mem (Tr) tq os) mm) (erased (Ext p m) ex) (erased (PLook p q h (Undef)) pl)
       (erased (Look m q h tq) lkq) (erased (Rows n n m) wf) (erased (Range n xs) rg) (erased (Opts xs O) op)
       (erased (HaltsIn m (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) hs) -> (erased (Lt s (Succ k)) r))
    (match erased mm _
      ((MemHere _ _ os1)
        (let-match erased ta (TACons _ _ _ p2 _ _ _ _ ps tn _))
        (tn-good n k xs O p2 m s tn (ext-set p p2 m q h tq ex ps lkq) wf rg op hs))
      ((MemThere _ _ y os1 mm1)
        (let-match erased ta (TACons _ _ _ _ _ _ _ _ _ _ ta1))
        (ta-pick n k xs O p m s q h tq os1 ta1 mm1 ex pl lkq wf rg op hs)))))
