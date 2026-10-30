; The certified reducibility check, over the initial trees of init.sl.

(def-adts $ (AnyT : ((List (Col)) et) -> Type)
  enum
  (many MkAnyT : (erased (List (Col)) et) -> (AnyT et)))

(def-fns _ $ (erased capp-any : (subterm erased (Ctree) t) (erased (List (Col)) pre) -> (erased (CtAllP AnyT t pre) a))
  (let-match erased t (CLeaf lf)
    ((CEmpty) (CAPE AnyT pre))
    ((CNode t1 t2 t3) (CAPN AnyT t1 t2 t3 pre (capp-any t1 (Cons _ (C1) pre)) (capp-any t2 (Cons _ (C2) pre)) (capp-any t3 (Cons _ (C3) pre)))))
  (let ((erased et) (erased r)) (revapp-exists (Col) pre (Nil _)))
  (let ((erased ct) (erased c)) (ctr-exists (C0) et))
  (CAPL AnyT lf pre et ct r c (MkAnyT ct)))

(def-adts $ (InitFor : ((Nat) h) -> Type)
  enum
  (many IFYes : (erased (Nat) h) (many (Ctree) ctu) (many (Gtree) gtu) (erased (CEv ctu (ESStart)) ce)
      (erased (GE ctu (Cons RS (MkRx (GSet) (BS0) (GSG gtu)) (Nil RS)) (ESStart) (Succ h)) ge) (erased (GCov (GSG gtu) (Zero) (BFalse) (Succ h)) gc)
      (erased (CtH (Succ h) ctu) hc) -> (InitFor h)))

(def-adts $ (InitE : -> Type)
  enum
  (many MkInitE : (many (Nat) h) (many (InitFor h) i) -> (InitE)))

(def-fns _ $ (many init-lookup : (many (Nat) h) (subterm many (List (InitE)) cache) -> (many (Maybe (InitFor h)) r))
  (let-match many cache (Cons _ x rest) ((Nil _) (None _)))
  (let-match many x (MkInitE h2 i))
  (match many (nat-eq h2 h) _ ((Equal _ _ _) (Some _ i)) ((Unequal _ _ _ _ _) (tail $ init-lookup h rest))))

(def-fns _ $ (many init-for : (many (Nat) h) (many (List (InitE)) cache) -> (many (InitFor h) i) (many (List (InitE)) cache2))
  (let-match many (init-lookup h cache) (None _) ((Some _ i) (values i cache)))
  (let ((many gtu) (erased gc)) (gtree-full h))
  (let ((many ctu) (erased ge) (erased ce) (erased hc)) (ctree-full h gtu))
  (let ((many i)) (IFYes h ctu gtu ce ge gc hc))
  (values i (Cons _ (MkInitE h i) cache)))

(def-fns _ $ (many kempe-tree-chk : (many (List (Step)) cp) (many (List (InitE)) cache) -> (many (Ctree) kt) (many (List (InitE)) cache2))
  (let-match many (cprsize cp) (Succ n1) ((Zero) (values (CEmpty) cache)))
  (let-match many n1 (Succ h) ((Zero) (values (CEmpty) cache)))
  (let ((many i) (many cache2)) (init-for h cache))
  (let-match many i (IFYes _ ctu gtu ce ge gc hc))
  (let ((many ctr)) (cpcolor cp))
  (let ((many kt) (erased ks)) (kempe-tree-c AnyT h ctu ctr gtu ce ge gc (capp-any ctr (Nil _)) hc))
  (values kt cache2))

(def-fns _ $ (many check-reducible-c : (many (Config) cf) (many (List (InitE)) cache) -> (many (Bool) b) (many (List (InitE)) cache2))
  (let-match many cf (MkConfig _ _ cp))
  (let-match many (contract-ctree cf) (Some _ ct) ((None _) (values (BFalse) cache)))
  (let ((many kt) (many cache2)) (kempe-tree-chk cp cache))
  (match many (ctree-disjoint kt ct) _ ((DjYes _ _ _) (values (BTrue) cache2)) ((DjNo _ _ _) (values (BFalse) cache2))))

(def-fns _ $ (many check-all-c : (subterm many (List (Config)) cfs) (many (List (InitE)) cache) -> (many (Bool) b))
  (let-match many cfs (Cons _ cf rest) ((Nil _) (BTrue)))
  (let ((many b) (many cache2)) (check-reducible-c cf cache))
  (match many b _ ((BTrue) (tail $ check-all-c rest cache2)) ((BFalse) (BFalse))))
