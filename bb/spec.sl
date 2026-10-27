(def-adts
  ((SB : ((Sym) s) ((Bool) b) -> Type)
    enum
    (many SB0 : -> (SB (Sym0) (BFalse)))
    (many SB1 : -> (SB (Sym1) (BTrue)))))

(def-adts
  ((LB : ((List (Sym)) zs) ((List (Bool)) ys) -> Type)
    enum
    (many LBNil : -> (LB (Nil (Sym)) (Nil (Bool))))
    (many LBCons : (erased (Sym) x) (erased (Bool) y) (erased (List (Sym)) zs) (erased (List (Bool)) ys) (erased (SB x y) e)
       (erased (LB zs ys) r) -> (LB (Cons (Sym) x zs) (Cons (Bool) y ys)))))

(def-adts
  ((DM : ((Dir) d) ((Mv) e) -> Type)
    enum
    (many DML : -> (DM (Left) (DL)))
    (many DMR : -> (DM (Right) (DR)))))

(def-adts
  ((ET : ((Nat) n) ((Entry n) e) ((Tr) t) -> Type)
    enum
    (many ETH : (erased (Nat) n) -> (ET n (Halt n) (Hlt)))
    (many ETG : (erased (Nat) n) (erased (Sym) w) (erased (Bool) b) (erased (Dir) d) (erased (Mv) e) (erased (Nat) q) (erased (Lt q n) bl)
       (erased (SB w b) sb) (erased (DM d e) dm) -> (ET n (Go n w d q bl) (Mov b e q)))))

(def-adts
  ((RT : ((Nat) n) ((List (Row n)) rows) ((List (Tr)) m) -> Type)
    enum
    (many RTNil : (erased (Nat) n) -> (RT n (Nil (Row n)) (Nil (Tr))))
    (many RTCons : (erased (Nat) n) (erased (Entry n) e0 e1) (erased (Tr) t0 t1) (erased (List (Row n)) rows) (erased (List (Tr)) m)
       (erased (ET n e0 t0) x0) (erased (ET n e1 t1) x1) (erased (RT n rows m) r)
       -> (RT n (Cons (Row n) (MkRow n e0 e1) rows) (Cons (Tr) t0 (Cons (Tr) t1 m))))))

(def-fns _ $ (erased sb-of : (erased (Sym) s) -> (erased (Bool) b) (erased (SB s b) e))
  (match erased s _ ((Sym0) (values (BFalse) (SB0))) ((Sym1) (values (BTrue) (SB1)))))

(def-fns _ $ (erased dm-of : (erased (Dir) d) -> (erased (Mv) e) (erased (DM d e) x))
  (match erased d _ ((Left) (values (DL) (DML))) ((Right) (values (DR) (DMR)))))

(def-fns _ $ (erased et-of : (erased (Nat) n) (erased (Entry n) e) -> (erased (Tr) t) (erased (ET n e t) x))
  (let-match erased e (Go _ w d q bl) ((Halt _) (values (Hlt) (ETH n))))
  (let ((erased b) (erased sb)) (sb-of w))
  (let ((erased f) (erased dm)) (dm-of d))
  (values (Mov b f q) (ETG n w b d f q bl sb dm)))

(def-fns _ $ (erased rt-of : (erased (Nat) n) (subterm erased (List (Row n)) rows) -> (erased (List (Tr)) m) (erased (RT n rows m) r))
  (let-match erased rows (Cons _ row rest) ((Nil _) (values (Nil (Tr)) (RTNil n))))
  (let-match erased row (MkRow _ e0 e1))
  (let ((erased t0) (erased x0)) (et-of n e0))
  (let ((erased t1) (erased x1)) (et-of n e1))
  (let ((erased m) (erased r)) (rt-of n rest))
  (values (Cons (Tr) t0 (Cons (Tr) t1 m)) (RTCons n e0 e1 t0 t1 rest m x0 x1 r)))

(def-fns _ $ (erased et-ok : (erased (Nat) n) (erased (Entry n) e) (erased (Tr) t) (erased (ET n e t) x) -> (erased (TrOK n t) o))
  (match erased x _ ((ETH _) (OKHalt n)) ((ETG _ w b d f q bl _ _) (OKGo n q b f bl))))

(def-fns _ $ (erased rt-rows : (erased (Nat) n k) (erased (List (Row n)) rows) (erased (List (Tr)) m) (subterm erased (RT n rows m) r)
    (erased (Length (Row n) rows k) len) -> (erased (Rows n k m) w))
  (let-match erased r (RTCons _ e0 e1 t0 t1 rest m1 x0 x1 r1) ((RTNil _) (let-match erased len (LengthNil _)) (RowsZ n)))
  (let-match erased len (LengthCons _ _ _ lk1 len1))
  (RowsS n lk1 t0 t1 m1 (et-ok n e0 t0 x0) (et-ok n e1 t1 x1) (rt-rows n lk1 rest m1 r1 len1)))

(def-fns _ $ (erased nth-rows : (erased (Nat) n q) (erased (List (Row n)) rows) (erased (List (Tr)) m) (erased (Entry n) e0 e1)
    (subterm erased (Nth (Row n) rows q (MkRow n e0 e1)) nth) (erased (RT n rows m) r) ->
    (erased (Tr) t0 t1) (erased (ET n e0 t0) x0) (erased (ET n e1 t1) x1) (erased (Look m q (BFalse) t0) look0) (erased (Look m q (BTrue) t1) look1))
  (let-match erased r (RTCons _ f0 f1 u0 u1 rest m1 y0 y1 r1) (absurd (RTNil _) nth))
  (let-match erased nth (NthThere _ _ _ q1 _ nth1) ((NthHere _ _ _) (values u0 u1 y0 y1 (Look0 u0 u1 m1) (Look1 u0 u1 m1))))
  (let ((erased t0) (erased t1) (erased x0) (erased x1) (erased lk0) (erased lk1)) (nth-rows n q1 rest m1 e0 e1 nth1 r1))
  (values t0 t1 x0 x1 (LookS u0 u1 m1 q1 (BFalse) t0 lk0) (LookS u0 u1 m1 q1 (BTrue) t1 lk1)))

(def-fns _ $ (erased lookup-look : (erased (Nat) n q) (erased (List (Row n)) rows) (erased (Length (Row n) rows n) len) (erased (List (Tr)) m)
    (erased (Sym) s) (erased (Bool) b) (erased (Entry n) e) (erased (Lookup n (MkMachine n rows len) q s e) lk) (erased (RT n rows m) r)
    (erased (SB s b) sb) -> (erased (Tr) t) (erased (ET n e t) x) (erased (Look m q b t) lk2))
  (match erased lk _
    ((LookupSym0 _ _ _ _ e0 e1 nth)
      (let-match erased sb (SB0))
      (let ((erased t0) (erased t1) (erased x0) (erased x1) (erased lk0) (erased lk1)) (nth-rows n q rows m e0 e1 nth r))
      (values t0 x0 lk0))
    ((LookupSym1 _ _ _ _ e0 e1 nth)
      (let-match erased sb (SB1))
      (let ((erased t0) (erased t1) (erased x0) (erased x1) (erased lk0) (erased lk1)) (nth-rows n q rows m e0 e1 nth r))
      (values t1 x1 lk1))))

(def-fns _ $ (erased pop-tr : (erased (List (Sym)) ls ls2) (erased (Sym) h) (erased (List (Bool)) bs) (erased (Pop ls h ls2) pp) (erased (LB ls bs) e)
    -> (erased (Bool) h2) (erased (List (Bool)) bs2) (erased (Pull bs h2 bs2) pp2) (erased (SB h h2) sb) (erased (LB ls2 bs2) e2))
  (match erased pp _
    ((PopNil) (let-match erased e (LBNil)) (values (BFalse) (Nil (Bool)) (PullNil) (SB0) (LBNil)))
    ((PopCons x zs) (let-match erased e (LBCons _ y _ ys sb e1)) (values y ys (PullCons y ys) sb e1))))

(def-fns _ $ (erased halts-tr : (erased (Nat) n) (erased (List (Row n)) rows) (erased (Length (Row n) rows n) len) (erased (List (Tr)) m)
    (erased (RT n rows m) rt) (erased (Nat) q k) (erased (List (Sym)) ls rs) (erased (Sym) h) (erased (List (Bool)) bl br) (erased (Bool) bh)
    (erased (LB ls bl) el) (erased (SB h bh) eh) (erased (LB rs br) er)
    (subterm erased (HaltsIn n (MkMachine n rows len) (MkCfg q ls h rs) k) hs) -> (erased (HaltsAt m (MkConf q bl bh br) k) hr))
  (match erased hs _
    ((HaltNow _ _ _ _ _ _ look)
      (let ((erased t) (erased x) (erased lk)) (lookup-look n q rows len m h bh (Halt n) look rt eh))
      (let-match erased x (ETH _))
      (HStop m q bl br bh lk))
    ((HaltLater _ _ _ c2 st lk1 rest)
      (match erased st _
        ((StepLeft _ _ _ _ _ _ w q2 below look h2 ls2 spp)
          (let ((erased t) (erased x) (erased lk)) (lookup-look n q rows len m h bh _ look rt eh))
          (let-match erased x (ETG _ _ b _ _ _ _ sb dm))
          (let-match erased dm (DML))
          (let ((erased bh2) (erased bl2) (erased pp) (erased sb2) (erased el2)) (pop-tr ls ls2 h2 bl spp el))
          (HMove m _ _ lk1 (StepL m q q2 bl br bl2 bh b bh2 lk pp)
            (halts-tr n rows len m rt q2 lk1 ls2 (Cons (Sym) w rs) h2 bl2 (Cons (Bool) b br) bh2 el2 sb2 (LBCons w b rs br sb er) rest)))
        ((StepRight _ _ _ _ _ _ w q2 below look h2 rs2 spp)
          (let ((erased t) (erased x) (erased lk)) (lookup-look n q rows len m h bh _ look rt eh))
          (let-match erased x (ETG _ _ b _ _ _ _ sb dm))
          (let-match erased dm (DMR))
          (let ((erased bh2) (erased br2) (erased pp) (erased sb2) (erased er2)) (pop-tr rs rs2 h2 br spp er))
          (HMove m _ _ lk1 (StepR m q q2 bl br br2 bh b bh2 lk pp)
            (halts-tr n rows len m rt q2 lk1 (Cons (Sym) w ls) rs2 h2 (Cons (Bool) b bl) br2 bh2 (LBCons w b ls bl sb el) sb2 er2 rest)))))))

(def-adts
  ((NthRowR : ((Nat) n) ((List (Row n)) rows) ((Nat) q) -> Type)
    enum
    (many NROk : (erased (Nat) n) (erased (List (Row n)) rows) (erased (Nat) q) (many (Entry n) e0 e1)
       (erased (Nth (Row n) rows q (MkRow n e0 e1)) nth) -> (NthRowR n rows q))
    (many NRNo : (erased (Nat) n) (erased (List (Row n)) rows) (erased (Nat) q) -> (NthRowR n rows q))))

(def-fns _ $ (many nth-row : (erased (Nat) n) (subterm many (List (Row n)) rows) (many (Nat) q) -> (many (NthRowR n rows q) r))
  (let-match many rows (Cons _ row rest) ((Nil _) (NRNo n rows q)))
  (let-match many row (MkRow _ e0 e1))
  (let-match many q (Succ q1) ((Zero) (NROk n rows q e0 e1 (NthHere (Row n) row rest))))
  (let-match many (notail $ nth-row n rest q1) (NROk _ _ _ f0 f1 nth) ((NRNo _ _ _) (NRNo n rows q)))
  (NROk n rows q f0 f1 (NthThere (Row n) row rest q1 _ nth)))

(def-adts
  ((SimS : ((Nat) n) ((Machine n) m) ((Cfg) c) -> Type)
    enum
    (many SSHalt : (erased (Nat) n) (erased (Machine n) m) (erased (Cfg) c) (many (Nat) k) (erased (HaltsIn n m c k) h) -> (SimS n m c))
    (many SSNo : (erased (Nat) n) (erased (Machine n) m) (erased (Cfg) c) -> (SimS n m c))))

(def-fns _ $ (many spop : (many (List (Sym)) zs) -> (many (Sym) h) (many (List (Sym)) ys) (erased (Pop zs h ys) p))
  (match many zs _ ((Nil _) (values (Sym0) zs (PopNil))) ((Cons _ x ys) (values x ys (PopCons x ys)))))

(def-fns _ $ (many spec-sim : (erased (Nat) n) (many (List (Row n)) rows) (erased (Length (Row n) rows n) len) (subterm many (Nat) fuel)
    (many (Nat) q) (many (List (Sym)) ls) (many (Sym) h) (many (List (Sym)) rs) -> (many (SimS n (MkMachine n rows len) (MkCfg q ls h rs)) r))
  (let ((many mm)) (MkMachine n rows len))
  (let ((many no)) (SSNo n mm (MkCfg q ls h rs)))
  (let-match many fuel (Succ f) ((Zero) no))
  (let-match many (nth-row n rows q) (NROk _ _ _ e0 e1 nth) ((NRNo _ _ _) no))
  (let ((many e) (erased look))
    (match many h (((Entry n) e) ((Lookup n mm q h e) lk))
      ((Sym0) (values e0 (LookupSym0 n rows len q e0 e1 nth)))
      ((Sym1) (values e1 (LookupSym1 n rows len q e0 e1 nth)))))
  (let-match many e (Go _ w d q2 bl) ((Halt _) (SSHalt n mm _ (Succ (Zero)) (HaltNow n mm q ls h rs look))))
  (match many d _
    ((Left)
      (let ((many h2) (many ls2) (erased pp)) (spop ls))
      (let-match many (notail $ spec-sim n rows len f q2 ls2 h2 (Cons (Sym) w rs)) (SSHalt _ _ _ k hs) ((SSNo _ _ _) no))
      (SSHalt n mm _ (Succ k) (HaltLater n mm _ _ (StepLeft n mm q ls h rs w q2 bl look h2 ls2 pp) k hs)))
    ((Right)
      (let ((many h2) (many rs2) (erased pp)) (spop rs))
      (let-match many (notail $ spec-sim n rows len f q2 (Cons (Sym) w ls) h2 rs2) (SSHalt _ _ _ k hs) ((SSNo _ _ _) no))
      (SSHalt n mm _ (Succ k) (HaltLater n mm _ _ (StepRight n mm q ls h rs w q2 bl look h2 rs2 pp) k hs)))))
