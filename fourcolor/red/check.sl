(def-adts $ (InitFor : ((Nat) h) -> Type)
  enum
  (many IFYes : (erased (Nat) h) (erased (Ctree) ctu) (erased (Gtree) gtu) (erased (CEv ctu (ESStart)) ce)
      (erased (GE ctu (Cons RS (MkRx (GSet) (BS0) (GSG gtu)) (Nil RS)) (ESStart) (Succ h)) ge) (erased (GCov (GSG gtu) (Zero) (BFalse) (Succ h)) gc)
      (erased (CtH (Succ h) ctu) hc) (many (Maybe (FlatIn h ctu gtu)) fl) -> (InitFor h)))

(def-adts $ (InitE : -> Type)
  enum
  (many MkInitE : (many (Nat) h) (many (InitFor h) i) -> (InitE)))

(def-fns _ $ (many init-lookup : (many (Nat) h) (subterm many (List (InitE)) cache) -> (many (Maybe (InitFor h)) r))
  (let-match many cache (Cons _ x rest) ((Nil _) (None _)))
  (let-match many x (MkInitE h2 i))
  (match many (nat-eq h2 h) _ ((Equal _ _ _) (Some _ i)) ((Unequal _ _ _ _ _) (tail $ init-lookup h rest))))

(def-fns _ $ (many init-for : (many (Nat) h) (many (List (InitE)) cache) -> (many (InitFor h) i) (many (List (InitE)) cache2))
  (let-match many (init-lookup h cache) (None _) ((Some _ i) (values i cache)))
  (let ((many gtu) (erased gc) (erased _) (erased _)) (gtree-full h))
  (let ((many i))
    (match many (flat-in h gtu) (((InitFor h) i))
      ((Some _ fo) (let-match many fo (MkFlatOut _ _ ctu ce ge hc fi)) (IFYes h ctu gtu ce ge gc hc (Some _ fi)))
      ((None _) (let ((many ctu) (erased ge) (erased ce) (erased hc)) (ctree-full h gtu)) (IFYes h ctu gtu ce ge gc hc (None _)))))
  (values i (Cons _ (MkInitE h i) cache)))

(def-adts $ (EngE : -> Type)
  enum
  (many MkEngE : (many (Nat) h) (many (Maybe (Eng h)) e) -> (EngE)))

(def-fns _ $ (many r4-eng-lookup : (many (Nat) h) (subterm many (List (EngE)) cache) -> (many (Maybe (Maybe (Eng h))) r))
  (let-match many cache (Cons _ x rest) ((Nil _) (None _)))
  (let-match many x (MkEngE h2 e))
  (match many (nat-eq h2 h) _ ((Equal _ _ _) (Some _ e)) ((Unequal _ _ _ _ _) (tail $ r4-eng-lookup h rest))))

; red4's cached fcache h make_eng.
(def-fns _ $ (many r4-eng-for : (many (Nat) h) (many (List (EngE)) cache) (erased (List (MaybeUninit (WRow))) rp rb) (erased (List (Copy (Nat))) ns)
    (unique (Array (MaybeUninit (WRow)) rp) lp) (unique (Array (MaybeUninit (WRow)) rb) lb) (unique (Array (Copy (Nat)) ns) ln) (erased (WSt rp rb ns) st) ->
    (erased (List (MaybeUninit (WRow))) rp2 rb2) (erased (List (Copy (Nat))) ns2) (unique (Array (MaybeUninit (WRow)) rp2) lp2 at lp)
    (unique (Array (MaybeUninit (WRow)) rb2) lb2 at lb) (unique (Array (Copy (Nat)) ns2) ln2 at ln) (erased (WSt rp2 rb2 ns2) st2) (many (Maybe (Eng h)) e)
    (many (List (EngE)) cache2))
  (let-match many (r4-eng-lookup h cache) (None _) ((Some _ e) (values rp rb ns lp lb ln st e cache)))
  (let ((erased rp2) (erased rb2) (erased ns2) (unique lp2) (unique lb2) (unique ln2) (erased st2) (many e)) (r4-make-eng h rp rb ns lp lb ln st))
  (values rp2 rb2 ns2 lp2 lb2 ln2 st2 e (Cons _ (MkEngE h e) cache)))

; The Kempe tree kt of cp, whose ring has h + 2 darts, is sound for the ring traces of cp's map.
(def-adts $ (KChk : ((List (Step)) cp) -> Type)
  enum
  (many KCYes : (erased (List (Step)) cp) (erased (Nat) h) (erased (Ctree) kt) (many (KtA kt) ka) (erased (KSound (MkPred (List (Step)) cp CpColR) h kt) ks)
      (erased (Cprsize cp (Succ (Succ h))) cs) (erased (NoA cp) na) -> (KChk cp))
  (many KCNo : (erased (List (Step)) cp) -> (KChk cp)))

(def-fns _ $ (many kempe-tree-chk : (many (List (Step)) cp) (many (List (InitE)) cache) -> (many (KChk cp) k) (many (List (InitE)) cache2))
  (let-match many (noa-dec cp) (NoAYes _ na) ((NoANo _) (values (KCNo cp) cache)))
  (let ((erased d) (erased e) (erased f) (many r) (erased cm)) (cpmap-c cp na))
  (let ((erased k) (erased lk) (erased cs)) (cpmap-size cp d e f r cm))
  (let ((many m) (erased lm)) (size-c _ r))
  (let-match erased (length-fn _ r k m lk lm) (Refl _ _))
  (let-match many m (Succ m1) ((Zero) (values (KCNo cp) cache)))
  (let-match many m1 (Succ h) ((Zero) (values (KCNo cp) cache)))
  (let ((many i) (many cache2)) (init-for h cache))
  (let-match many i (IFYes _ ctu gtu ce ge gc _ fl))
  (let-match many fl (Some _ fi) ((None _) (values (KCNo cp) cache2)))
  (let ((many ctr) (erased hr) (erased rt) (erased _)) (cpcolor-c h cp cs na))
  (let-match many (kempe-tree-f (MkPred (List (Step)) cp CpColR) h ctu ctr gtu ce ge gc (ctring-allp cp ctr (Nil _) rt) hr fi) (KtYes _ _ kt ka ks)
    ((KtNo _ _) (values (KCNo cp) cache2)))
  (values (KCYes cp h kt ka ks cs na) cache2))
