; No minimal counterexample, from unavoidability (UnavE), reducibility (AllRedC) and two open steps, each a level factory:
; minimal_counter_example_is_plain_cubic_pentagonal of birkhoff.v (BirkGeo) and not_embed_reducible of embed.v (NotEmbed).
; Load after unav/unave.sl, in the chain that PLAN.md gives.

(def-fns _ $ (erased perm-unique : (erased (Nat) d) (erased (List (Nat)) p q1 q2) (erased (HPerm d p q1) pm1) (erased (HPerm d p q2) pm2)
    -> (erased (Eq (List (Nat)) q1 q2) r))
  (let-match erased pm1 (HMkPerm _ _ _ ids io lp q1p pq1))
  (let-match erased pm2 (HMkPerm _ _ _ ids2 io2 lp2 q2p pq2))
  (let-match erased (iota-fn d ids ids2 io io2) (Refl _ _))
  (let ((erased lq1)) (perm-length d q1 p (perm-sym d p q1 pm1)))
  (respects-fn ids q2 q1 q2
    (respects-assoc q2 p q1 ids ids q1 d pq2 (respects-id-right d ids q1 io lq1) q1p (iota-length d ids io) lp)
    (respects-id-left d ids q2 io (perm-under d q2 p (perm-sym d p q2 pm2)))))

; minimal_counter_example_mirror of coloring.v, for the mirror (fn, ni, fi) of MapOrMirror.
(def-fns _ $ (erased mce-mirror : (erased (Level) L1) -> (erased (Level) M1 M2)
    (erased (Fn M2 (erased (Level) L2) (erased (Nat) d) (erased (List (Nat)) e n f fn ni fi) (erased (MinimalCounterExample L1 L2 d e n f) mce)
        (erased (Respects f n fn) rfn) (erased (HPerm d n ni) pn) (erased (HPerm d f fi) pf) -> (erased (MinimalCounterExample M1 L2 d fn ni fi) r)) mm))
  (def-lvl M1)
  (def-lvl M2)
  (def-fns M2 $ (erased mm : (erased (Level) L2) (erased (Nat) d) (erased (List (Nat)) e n f fn ni fi) (erased (MinimalCounterExample L1 L2 d e n f) mce)
      (erased (Respects f n fn) rfn) (erased (HPerm d n ni) pn) (erased (HPerm d f fi) pf) -> (erased (MinimalCounterExample M1 L2 d fn ni fi) r))
    (let-match erased mce (MkMinimalCounterExample _ _ _ _ _ _ h g b pl pc noncol minimal))
    (let ((erased fn2) (erased ni2) (erased fi2) (erased h2) (erased rfn2) (erased pn2) (erased pf2) (erased g2)) (genus-mirror d (Zero) e n f h g))
    (let-match erased (respects-fn f n fn2 fn rfn2 rfn) (Refl _ _))
    (let-match erased (perm-unique d n ni2 ni pn2 pn) (Refl _ _))
    (let-match erased (perm-unique d f fi2 fi pf2 pf) (Refl _ _))
    (let-match erased pc (MkPrecubic _ _ ks ol u))
    (let-match erased ol (MkOrderList _ _ ids _ io os))
    (def-fns M1 $ (erased noncol2 : (erased (List (Nat)) ks2) (erased (FourColoring fn fi ks2) c) -> (erased (False) r))
      (noncol ks2 (coloring-mirror d e n f fn fi ks2 h rfn pf c)))
    (MkMinimalCounterExample M1 L2 d fn ni fi h2 g2 (bridgeless-mirror d e n f fn ni fi h b rfn pf) (plain-mirror d e n f fn h pl rfn)
      (MkPrecubic d ni ks (MkOrderList d ni ids ks io (orders-inv d n ni ids ks pn os)) u) noncol2 minimal))
  (values M1 M2 mm))

; css concatenated is cfs.
(def-adts $ (ConcatL : ((List (List (Config))) css) ((List (Config)) cfs) -> Type)
  enum
  (many CLNil : -> (ConcatL (Nil (List (Config))) (Nil (Config))))
  (many CLSkip : (erased (List (List (Config))) css) (erased (List (Config)) cfs) (erased (ConcatL css cfs) p)
      -> (ConcatL (Cons (List (Config)) (Nil (Config)) css) cfs))
  (many CLCons : (erased (Config) cf) (erased (List (Config)) cs cfs) (erased (List (List (Config))) css) (erased (ConcatL (Cons (List (Config)) cs css) cfs) p)
      -> (ConcatL (Cons (List (Config)) (Cons (Config) cf cs) css) (Cons (Config) cf cfs))))

(def-fns _ $ (many concat-one : (subterm many (List (Config)) cs) (erased (List (List (Config))) css) (many (List (Config)) cfs) (erased (ConcatL css cfs) p)
    -> (many (List (Config)) cfs2) (erased (ConcatL (Cons (List (Config)) cs css) cfs2) p2))
  (let-match many cs (Cons _ cf cs1) ((Nil _) (values cfs (CLSkip css cfs p))))
  (let ((many cfs3) (erased p3)) (concat-one cs1 css cfs p))
  (values (Cons _ cf cfs3) (CLCons cf cs1 cfs3 css p3)))

(def-fns _ $ (many concat-c : (subterm many (List (List (Config))) css) -> (many (List (Config)) cfs) (erased (ConcatL css cfs) p))
  (let-match many css (Cons _ cs rest) ((Nil _) (values (Nil _) (CLNil))))
  (let ((many cfs) (erased p)) (concat-c rest))
  (concat-one cs rest cfs p))

(def-fns _ $ (erased allred-concat : (erased (List (List (Config))) css) (erased (List (Config)) cfs) (subterm erased (ConcatL css cfs) p)
    (erased (AllRedC css) a) -> (erased (AllRed cfs) r))
  (match erased p _
    ((CLNil) (ARNil))
    ((CLSkip css1 _ p1) (let-match erased a (ARCCons _ _ _ a1)) (allred-concat css1 cfs p1 a1))
    ((CLCons cf cs cfs1 css1 p1)
      (let-match erased a (ARCCons _ _ ar a1))
      (let-match erased ar (ARCons _ _ rd ar1))
      (ARCons cf cfs1 rd (allred-concat (Cons _ cs css1) cfs1 p1 (ARCCons cs css1 ar1 a1))))))

(def-fns _ $ (erased reducible-mem : (erased (Config) cf) (erased (List (Config)) cfs) (subterm erased (AllRed cfs) a) (erased (Mem (Config) cf cfs) m)
    -> (erased (Reducible cf) r))
  (let-match erased a (ARCons _ rest rd a1) (absurd (ARNil) m))
  (match erased m _
    ((MemHere _ _ _) rd)
    ((MemThere _ _ _ _ m1) (reducible-mem cf rest a1 m1))))

; minimal_counter_example_is_plain_cubic_pentagonal of birkhoff.v, with Coq's cubic part from coloring.v's
; minimal_counter_example_is_cubic: a minimal counterexample is plain cubic with every face above four darts.
(def-adts $ (BirkGeo : -> Type)
  enum
  (many MkBirkGeo : (erased (Level) F)
      (erased (Fn F (erased (Level) L1 L2) -> (erased (Level) M)
          (erased (Fn M (erased (Nat) d) (erased (List (Nat)) e n f) (erased (MinimalCounterExample L1 L2 d e n f) mce) -> (erased (List (Nat)) ks)
              (erased (Geo d e n f ks) g)) r)) fac)
      -> (BirkGeo)))

; not_embed_reducible of embed.v, for the configurations of cfs: a configuration of cfs, C-reducible with contract cc, whose
; kernel preembeds in a minimal counterexample, as CfEmbed states it, gives False. Coq's embeddable, which the quiz checks of
; cfquiz.v establish there, is part of what this leaves open.
(def-adts $ (NotEmbed : ((List (Config)) cfs) -> Type)
  enum
  (many MkNotEmbed : (erased (List (Config)) cfs) (erased (Level) F)
      (erased (Fn F (erased (Level) L1 L2) -> (erased (Level) M)
          (erased (Fn M (erased (Bool) sym) (erased (List (Nat)) cci cc) (erased (List (Step)) cp) (erased (Nat) dm dc x0c x0m)
              (erased (List (Nat)) em nm fm ksm ec nc fc rc ksc as hl) (erased (Mem (Config) (MkConfig sym cci cp) cfs) m)
              (erased (MinimalCounterExample L1 L2 dm em nm fm) mce) (erased (Geo dm em nm fm ksm) g) (erased (Cpmap cp dc ec fc rc) c)
              (erased (PointedMap dc ec nc fc rc) pm) (erased (OrderList dc fc ksc) ol) (erased (KernelList dc fc rc as) kl)
              (erased (Preembedding ec nc fc ksc em fm ksm as hl) pe) (erased (Nth (Nat) hl x0c x0m) h0) (erased (Lt x0m dm) lx) (erased (CRed cp cc) cr)
              -> (erased (False) r)) r)) fac)
      -> (NotEmbed cfs)))

; present.v's no_fit_the_redpart and the use of unavoidability in four_color_hypermap: no minimal counterexample, for the
; minimal counterexamples at any levels L1 and L2.
(def-fns _ $ (erased no-mce : (erased (List (List (Config))) css) (erased (List (Config)) cfs) (erased (ConcatL css cfs) cl) (erased (AllRedC css) ar)
    (erased (UnavE cfs) u) (erased (BirkGeo) bg) (erased (NotEmbed cfs) ne) -> (erased (Level) G)
    (erased (Fn G (erased (Level) L1 L2) -> (erased (Level) M)
        (erased (Fn M (erased (Nat) d) (erased (List (Nat)) e n f) (erased (MinimalCounterExample L1 L2 d e n f) mce) -> (erased (False) r)) r)) fac))
  (let-match erased u (MkUnavE _ lv every))
  (let-match erased bg (MkBirkGeo Fg geo))
  (let-match erased ne (MkNotEmbed _ Fe emb))
  (let ((erased all)) (allred-concat css cfs cl ar))
  (def-lvl G)
  (def-fns G $ (erased fac : (erased (Level) L1 L2) -> (erased (Level) M)
      (erased (Fn M (erased (Nat) d) (erased (List (Nat)) e n f) (erased (MinimalCounterExample L1 L2 d e n f) mce) -> (erased (False) r)) r))
    (let ((erased Mc) (erased conn)) (mce-connected L1 L2))
    (let ((erased Mg) (erased gf)) (geo L1 L2))
    (let ((erased Ms) (erased same)) (emb L1 L2))
    (let ((erased M1) (erased M2) (erased mir)) (mce-mirror L1))
    (let ((erased Mr) (erased flip)) (emb M1 L2))
    (def-lvl M)
    (def-fns M $ (erased r : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (MinimalCounterExample L1 L2 d e n f) mce) -> (erased (False) r))
      (let ((erased ks) (erased g)) (gf d e n f mce))
      (let-match erased mce (MkMinimalCounterExample _ _ _ _ _ _ _ gen _ _ _ _ _))
      (let-match erased (every d e n f ks g (conn d e n f mce) gen)
        (MkCfEmbed _ sym cci cp _ dc x0c x0m _ _ _ _ em2 nm2 fm2 ec nc fc rc ksc as hl m c pm ol mo g2 kl pe h0 lx))
      (let-match erased (reducible-mem (MkConfig sym cci cp) cfs all m) (MkReducible _ _ cc _ _ cr))
      (match erased mo _
        ((MoSame _ _ _ _) (same sym cci cc cp d dc x0c x0m e n f ks ec nc fc rc ksc as hl m mce g2 c pm ol kl pe h0 lx cr))
        ((MoMirror _ _ _ _ _ _ _ rfn pn pf)
          (flip sym cci cc cp d dc x0c x0m em2 nm2 fm2 ks ec nc fc rc ksc as hl m (mir L2 d e n f em2 nm2 fm2 mce rfn pn pf) g2 c pm ol kl pe h0 lx cr))))
    (values M r))
  (values G fac))
