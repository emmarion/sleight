; The certified reducibility check, over the initial trees of init.sl.

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

; The Kempe tree kt of cp, whose ring has h + 2 darts, is sound for the ring traces of cp's map.
(def-adts $ (KChk : ((List (Step)) cp) -> Type)
  enum
  (many KCYes : (erased (List (Step)) cp) (erased (Nat) h) (many (Ctree) kt) (erased (KSound (MkPred (List (Step)) cp CpColR) h kt) ks)
      (erased (Cprsize cp (Succ (Succ h))) cs) (erased (NoA cp) na) -> (KChk cp))
  (many KCNo : (erased (List (Step)) cp) -> (KChk cp)))

(def-fns _ $ (many kempe-tree-chk : (many (List (Step)) cp) (many (List (InitE)) cache) -> (many (KChk cp) k) (many (List (InitE)) cache2))
  (let-match many (noa-dec cp) (NoAYes _ na) ((NoANo _) (values (KCNo cp) cache)))
  (let ((many d) (many e) (many f) (many r) (erased cm)) (cpmap-c cp na))
  (let ((erased k) (erased lk) (erased cs)) (cpmap-size cp d e f r cm))
  (let ((many m) (erased lm)) (size-c _ r))
  (let-match erased (length-fn _ r k m lk lm) (Refl _ _))
  (let-match many m (Succ m1) ((Zero) (values (KCNo cp) cache)))
  (let-match many m1 (Succ h) ((Zero) (values (KCNo cp) cache)))
  (let ((many i) (many cache2)) (init-for h cache))
  (let-match many i (IFYes _ ctu gtu ce ge gc hc))
  (let ((many ctr) (erased ht) (erased rt)) (cpcolor-c h cp cs na))
  (let ((many kt) (erased ks)) (kempe-tree-c (MkPred (List (Step)) cp CpColR) h ctu ctr gtu ce ge gc (ctring-allp cp ctr (Nil _) rt) hc))
  (values (KCYes cp h kt ks cs na) cache2))
