(def-adts $ (CtA : ((Nat) h) ((Nat) len) ((Ctree) ctu) -> Type)
  enum
  (many MkCtA : (erased (Nat) h len) (erased (Ctree) ctu) (erased (List Cnt) us) (unique (Array Cnt us) a) (erased (Tally us (Succ h) (Zero) ctu) tb)
      (erased (Length Cnt us len) lu) (many (Nat) L) (erased (NzCnt us L) z) -> (CtA h len ctu)))

(def-adts $ (Rm : ((Nat) h) ((Ctree) ctr) -> Type)
  enum
  (many MkRm : (erased (Nat) h) (erased (Ctree) ctr) (erased (List Cnt) ms) (unique (Array Cnt ms) m) (erased (Room ms (Succ h)) rm)
      (erased (Flags ms (Succ h) (Zero) ctr) f) -> (Rm h ctr)))

(def-adts $ (KEnv : ((Nat) h) ((Nat) len) -> Type)
  enum
  (many MkKEnv : (erased (Nat) h len) (erased (Lt len u62-modulus) lb) (erased (List Cnt) us) (erased (Ctree) t) (erased (Tally us (Succ h) (Zero) t) tb)
      (erased (Length Cnt us len) lu) (many len is n) -> (KEnv h len)))

(def-adts $ (KdF : ((Nat) h) ((Nat) len) ((Ctree) c0 r0) ((Gtree) g0) -> Type)
  enum
  (many MkKdF : (erased (Nat) h len) (erased (Ctree) c0 r0) (erased (Gtree) g0) (erased (Ctree) ctu) (unique (CtA h len ctu) ca) (many (KeepE ctu) e)
      (many (Gtree) gtr) (unique (UGtree) gu) (erased (Gtree) gtu) (many (GKeep gtu) ge) (erased (KR h c0 r0 g0 ctu gtr gtu) kr) (erased (UG gu gtu) ug)
      (erased (Ctree) ctr) (unique (Rm h ctr) rf) -> (KdF h len c0 r0 g0)))

(def-adts $ (KgF : ((Nat) h) ((Nat) len) ((Ctree) c0 r0) ((Gtree) g0) -> Type)
  enum
  (many MkKgF : (erased (Nat) h len) (erased (Ctree) c0 r0) (erased (Gtree) g0) (erased (Ctree) ctu) (unique (CtA h len ctu) ca) (many (KeepE ctu) e)
      (unique (UGtree) gu) (erased (Gtree) gtu) (many (GKeep gtu) ge) (erased (KR h c0 r0 g0 ctu (GEmpty) gtu) kr) (erased (UG gu gtu) ug)
      (erased (Ctree) ctr) (erased (CR h c0 r0 g0 ctr) cr) (unique (Rm h ctr) rf) -> (KgF h len c0 r0 g0)))

(def-adts $ (KrF : ((Nat) h) ((Nat) len) ((Ctree) c0 r0) ((Gtree) g0) -> Type)
  enum
  (many KDoneF : (erased (Nat) h len) (erased (Ctree) c0 r0) (erased (Gtree) g0) (unique (KdF h len c0 r0 g0) s) -> (KrF h len c0 r0 g0))
  (many KGoF : (erased (Nat) h len) (erased (Ctree) c0 r0) (erased (Gtree) g0) (unique (KgF h len c0 r0 g0) s) -> (KrF h len c0 r0 g0)))

(def-fns _ $ (many ktf-step : (erased (Ctree) c0 r0) (erased (Gtree) g0) (many (Nat) h) (erased (Nat) len) (many (KEnv h len) env)
    (unique (KdF h len c0 r0 g0) s) -> (unique (KrF h len c0 r0 g0) k))
  (let-match unique s (MkKdF _ _ _ _ _ ctu ca e gtr gu gtu ge kr ug ctr rf))
  (let-match many e (KLive _) ((KEmpty) (KDoneF h len c0 r0 g0 (MkKdF h len c0 r0 g0 ctu ca e gtr gu gtu ge kr ug ctr rf))))
  (let-match many gtr (GEmpty) (else
    (let-match many env (MkKEnv _ _ lb us0 t0 tb0 lu0 n))
    (let ((erased ws) (unique g) (erased rp)) (array-make (U62) n (MkU62 (Zero) u62-modulus-pos)))
    (let ((erased wz) (erased lw)) (values (tally-zeros us0 ws (Succ h) (Zero) len t0 tb0 lu0 rp) (repeat-length _ len _ ws rp)))
    (let-match many ge (GKLive _) ((GKEmpty)
      (let ((many L) (erased z) (unique g2)) (live-loop ws g (Zero) ws (SfZ ws) n lw))
      (KDoneF h len c0 r0 g0 (MkKdF h len c0 r0 g0 (CEmpty) (MkCtA h len (CEmpty) ws g2 wz lw L z) (KEmpty) (GEmpty) (UGEmpty) (GEmpty) (GKEmpty)
        (KREmpty h c0 r0 g0 ctu gtr kr) (UGE) ctr rf))))
    (let-match unique ca (MkCtA _ _ _ us a tb lu L z))
    (let ((erased keep) (erased gone) (erased c) (erased hk) (erased hg) (many e2) (erased us2) (unique a2) (erased tk) (erased lu2) (erased _) (many L2)
        (erased z2) (erased ws2) (unique g2) (erased tg) (erased _) (erased fg) (many _))
      (srestrict h gtr ctu len lb us a tb lu L z ws g wz lw))
    (let-match unique rf (MkRm _ _ ms m rm _))
    (let ((unique _) (erased ms2) (unique m2) (erased rm2) (erased ctr2) (erased rl) (erased f)) (ctr-flags h ws2 g2 fg gone tg ms m rm))
    (let ((erased hc)) (canon-h (Succ h) ctu (tally-canon us (Succ h) (Zero) ctu tb)))
    (KGoF h len c0 r0 g0 (MkKgF h len c0 r0 g0 keep (MkCtA h len keep us2 a2 tk lu2 L2 z2) e2 gu gtu ge (KRRestr h c0 r0 g0 ctu keep gone gtr gtu kr hc hk c) ug
      ctr2 (CRGone h c0 r0 g0 ctu keep gone ctr2 gtr gtu kr hc hg c rl) (MkRm h ctr2 ms2 m2 rm2 f)))))
  (KDoneF h len c0 r0 g0 (MkKdF h len c0 r0 g0 ctu ca e gtr gu gtu ge kr ug ctr rf)))

(def-fns _ $ (many ktf-u : (erased (Ctree) c0 r0) (erased (Gtree) g0) (subterm many (Nat) d) (many (Nat) h) (erased (Nat) len) (many (KEnv h len) env)
    (unique (KgF h len c0 r0 g0) s) -> (unique (KdF h len c0 r0 g0) r))
  (let-match many d (Succ d1)
    ((Zero)
      (let-match unique s (MkKgF _ _ _ _ _ ctu ca e gu gtu ge kr ug ctr cr rf))
      (let-match unique rf (MkRm _ _ ms m rm f))
      (let ((unique m2) (many hit) (unique mu) (erased miss) (erased um) (erased pt) (erased hs) (many me))
        (ctr-gsplit gu gtu ug h ms m (room-fit ms (Succ h) rm) ctr f))
      (MkKdF h len c0 r0 g0 ctu ca e hit mu miss (gk-drop miss _ _ me) (KRSplit h c0 r0 g0 ctu ctr gtu hit miss kr cr pt hs) um ctr (MkRm h ctr ms m2 rm f))))
  (let ((unique s1)) (notail $ ktf-u c0 r0 g0 d1 h len env s))
  (let ((unique s2))
    (match unique (ktf-step c0 r0 g0 h len env s1) (((KdF h len c0 r0 g0) r))
      ((KDoneF _ _ _ _ _ x) x)
      ((KGoF _ _ _ _ _ x) (notail $ ktf-u c0 r0 g0 d1 h len env x))))
  (match unique (ktf-step c0 r0 g0 h len env s2) _
    ((KDoneF _ _ _ _ _ x) x)
    ((KGoF _ _ _ _ _ x) (tail $ ktf-u c0 r0 g0 d1 h len env x))))

(def-adts $ (FlatIn : ((Nat) h) ((Ctree) ctu) -> Type)
  enum
  (many MkFlatIn : (erased (Nat) h) (erased (Ctree) ctu) (erased (List Cnt) us ws ms) (many (Array Cnt us) a) (many (Nat) L)
      (erased (SInit h ctu us ws L) si) (many (Array Cnt ms) m) (erased (Room ms (Succ h)) rm) -> (FlatIn h ctu)))

(def-fns _ $ (many flat-in : (many (Nat) h) (many (Ctree) ctu) (erased (CtH (Succ h) ctu) hc) -> (many (Maybe (FlatIn h ctu)) r))
  (let ((erased us) (erased ws) (unique a) (unique _) (many L) (many t)) (sinit h ctu hc))
  (let-match many t (TryOk _ si) ((TryNo _) (None _)))
  (let ((erased ms) (unique m) (many q)) (room-new (Succ h)))
  (let-match many q (TryOk _ rm) ((TryNo _) (None _)))
  (Some _ (MkFlatIn h ctu us ws ms (share a) L si (share m) rm)))

(def-fns _ $ (many kempe-tree-f : (erased Pred P) (many (Nat) h) (erased (Ctree) ctu) (many (Ctree) ctr) (many (Gtree) gtu)
    (erased (CEv ctu (ESStart)) ce) (erased (GE ctu (Cons RS (MkRx (GSet) (BS0) (GSG gtu)) (Nil RS)) (ESStart) (Succ h)) ge)
    (erased (GCov (GSG gtu) (Zero) (BFalse) (Succ h)) gc) (erased (CtAllP P ctr (Nil (Col))) ca) (erased (CtH (Succ h) ctr) hr) (many (FlatIn h ctu) fi) ->
    (many (Ctree) ct) (many (Try (KSound P h ct)) ks))
  (let-match many fi (MkFlatIn _ _ us _ ms a L si m rm))
  (let-match erased si (MkSInit _ _ _ _ len _ lb tb lu z _ _))
  (let ((many n) (erased ln)) (array-length-many _ us a))
  (let-match erased (length-fn _ us len n lu ln) (Refl _ _))
  (let ((unique m1)) (array-copy _ _ m))
  (let ((erased ms2) (unique m2) (erased rm2) (many tf)) (room-flags (Succ h) ctr hr ms m1 rm))
  (let-match many tf (TryOk _ f) ((TryNo _) (values ctr (TryNo _))))
  (let ((unique gu) (erased ug) (many ge2)) (ug-of gtu))
  (let ((unique a1)) (array-copy _ _ a))
  (let-match unique
    (ktf-u ctu ctr gtu (Succ $ Succ h) h len (MkKEnv h len lb us ctu tb lu n)
      (MkKgF h len ctu ctr gtu ctu (MkCtA h len ctu us a1 tb lu L z) (KLive ctu) gu gtu ge2 (KRBase h ctu ctr gtu) ug ctr (CRBase h ctu ctr gtu)
        (MkRm h ctr ms2 m2 rm2 f)))
    (MkKdF _ _ _ _ _ c2 ca2 _ gtr _ gtu2 _ kr _ _ _))
  (let-match unique ca2 (MkCtA _ _ _ us2 a2 tb2 lu2 _ _))
  (let ((many ct)) (tally-tree (Succ h) (Zero) us2 (share a2) (MkFit us2 len lu2 lb) c2 tb2))
  (values ct (TryOk _ (MkKSound P h ct gtr gtu2 (kr-kv P h ctu ctr gtu (KVBase P h ctu gtu ce ge gc) (CKBase P h ctr ca) ct gtr gtu2 kr)))))
