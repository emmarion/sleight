; An Analysis, from unavoidability (UnavE), reducibility (AllRedC) and two open steps with minimality as data:
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

; minimal_counter_example_mirror of coloring.v, with minimality as data: the mirror (fn, ni, fi) of MapOrMirror is planar,
; bridgeless, plain and precubic and is uncolourable, and its reductions give reductions of the map.
(def-fns _ $ (erased pbpp-mirror : (erased (Nat) d) (erased (List (Nat)) e n f fn ni fi) (erased (Pbpp d e n f) p) (erased (Respects f n fn) rfn)
    (erased (HPerm d n ni) pn) (erased (HPerm d f fi) pf) -> (erased (Pbpp d fn ni fi) r))
  (let-match erased p (MkPbpp _ _ _ _ h g b pl pc))
  (let ((erased fn2) (erased ni2) (erased fi2) (erased h2) (erased rfn2) (erased pn2) (erased pf2) (erased g2)) (genus-mirror d (Zero) e n f h g))
  (let-match erased (respects-fn f n fn2 fn rfn2 rfn) (Refl _ _))
  (let-match erased (perm-unique d n ni2 ni pn2 pn) (Refl _ _))
  (let-match erased (perm-unique d f fi2 fi pf2 pf) (Refl _ _))
  (let-match erased pc (MkPrecubic _ _ ks ol u))
  (let-match erased ol (MkOrderList _ _ ids _ io os))
  (MkPbpp d fn ni fi h2 g2 (bridgeless-mirror d e n f fn ni fi h b rfn pf) (plain-mirror d e n f fn h pl rfn)
    (MkPrecubic d ni ks (MkOrderList d ni ids ks io (orders-inv d n ni ids ks pn os)) u)))

(def-fns _ $ (erased nocol-mirror : (erased (Nat) d) (erased (List (Nat)) e n f fn ni fi) (erased (Hypermap d e n f) h) (erased (Hypermap d fn ni fi) hm)
    (erased (Respects f n fn) rfn) (erased (HPerm d f fi) pf) (erased (NoColoring e f) ncol) -> (erased (NoColoring fn fi) r))
  (let-match erased (color-dec d fn ni fi hm) (NoColors _ _ ncol2)
    (absurd (Colors _ _ ks c) (no-coloring e f ks ncol (coloring-mirror d e n f fn fi ks h rfn pf c))))
  ncol2)

(def-fns _ $ (erased reduces-mirror : (erased (Level) Lo) -> (erased (Level) Hi)
    (erased (Fn Hi (erased (Nat) d) (erased (List (Nat)) e n f fn ni fi) (erased (Hypermap d e n f) h) (erased (Respects f n fn) rfn)
        (erased (HPerm d f fi) pf) (erased (Reduces Lo d fn ni fi) r) -> (erased (Reduces Hi d e n f) r2)) rm))
  (def-adts $ (MirrorW : ((Nat) dw) ((List (Nat)) ew nw fw) ((List (Mp)) mw) -> Type)
    enum
    (many MkMirrorW : (erased (Nat) d) (erased (List (Nat)) e n f fn ni fi) (erased (List (Mp)) ms) (erased (Hypermap d e n f) h)
        (erased (Respects f n fn) rfn) (erased (HPerm d f fi) pf) (erased (ColorFrom Lo d fn ni fi ms) g) -> (MirrorW d e n f ms)))
  (def-lvl M)
  (let ((erased pm)) (prove-predates Lo M))
  (def-fns M $ (erased mirror-glue : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (List (Mp)) ms) (erased (MirrorW d e n f ms) w)
      (erased (MpCols ms) cs) -> (erased (List (Nat)) ks) (erased (FourColoring e f ks) c))
    (let-match erased w (MkMirrorW _ _ _ _ fn ni fi _ h rfn pf g))
    (let-match erased g (MkColorFrom _ K _ _ _ _ _ W wm pk glue))
    (let ((erased ks) (erased c)) (glue (predates (predates-trans pk pm)) d fn ni fi ms wm cs))
    (values ks (coloring-mirror d e n f fn fi ks h rfn pf c)))
  (def-lvl Hi)
  (let ((erased ph)) (prove-predates M Hi))
  (def-fns Hi $ (erased rm : (erased (Nat) d) (erased (List (Nat)) e n f fn ni fi) (erased (Hypermap d e n f) h) (erased (Respects f n fn) rfn)
      (erased (HPerm d f fi) pf) (erased (Reduces Lo d fn ni fi) r) -> (erased (Reduces Hi d e n f) r2))
    (let-match erased r (MkReduces _ _ _ _ _ ms sm g))
    (MkReduces Hi d e n f ms sm (MkColorFrom Hi M d e n f ms MirrorW (MkMirrorW d e n f fn ni fi ms h rfn pf g) ph mirror-glue)))
  (values Hi rm))

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

(def-fns _ $ (erased allred-concat : (erased (Level) X) (erased (List (List (Config))) css) (erased (List (Config)) cfs) (subterm erased (ConcatL css cfs) p)
    (erased (AllRedC X css) a) -> (erased (AllRed X cfs) r))
  (match erased p _
    ((CLNil) (ARNil X))
    ((CLSkip css1 _ p1) (let-match erased a (ARCCons _ _ _ _ a1)) (allred-concat X css1 cfs p1 a1))
    ((CLCons cf cs cfs1 css1 p1)
      (let-match erased a (ARCCons _ _ _ ar a1))
      (let-match erased ar (ARCons _ _ _ rd ar1))
      (ARCons X cf cfs1 rd (allred-concat X (Cons _ cs css1) cfs1 p1 (ARCCons X cs css1 ar1 a1))))))

(def-fns _ $ (erased reducible-mem : (erased (Level) X) (erased (Config) cf) (erased (List (Config)) cfs) (subterm erased (AllRed X cfs) a)
    (erased (Mem (Config) cf cfs) m) -> (erased (Reducible X cf) r))
  (let-match erased a (ARCons _ _ rest rd a1) (absurd (ARNil _) m))
  (match erased m _
    ((MemHere _ _ _) rd)
    ((MemThere _ _ _ _ m1) (reducible-mem X cf rest a1 m1))))

; minimal_counter_example_is_plain_cubic_pentagonal of birkhoff.v, with Coq's cubic part from coloring.v's
; minimal_counter_example_is_cubic, and minimality as data: a connected planar bridgeless plain precubic map that the search
; finds uncolourable is plain cubic with every face above four darts (Geo), or reduces.
(def-adts $ (BirkGeo : -> Type)
  enum
  (many MkBirkGeo : (erased (Level) F B)
      (erased (Fn F (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Pbpp d e n f) p) (erased (NoColoring e f) ncol) (erased (Connected d e n f) conn)
          -> (erased (List (Nat)) ks) (erased (HOr (Geo d e n f ks) (Reduces B d e n f)) r)) geo)
      -> (BirkGeo)))

; not_embed_reducible of embed.v, for the configurations of cfs, with minimality as data: a map as BirkGeo takes it, Geo, in
; which the kernel of a configuration of cfs, C-reducible at X with contract cc, preembeds as CfEmbed states it, reduces. Coq's
; embeddable, which the quiz checks of cfquiz.v establish there, is part of what this leaves open.
(def-adts $ (NotEmbed : ((Level) X) ((List (Config)) cfs) -> Type)
  enum
  (many MkNotEmbed : (erased (Level) X) (erased (List (Config)) cfs) (erased (Level) F B)
      (erased (Fn F (erased (Bool) sym) (erased (List (Nat)) cci cc) (erased (List (Step)) cp) (erased (Nat) dm dc x0c x0m)
          (erased (List (Nat)) em nm fm ksm ec nc fc rc ksc as hl) (erased (Mem (Config) (MkConfig sym cci cp) cfs) m)
          (erased (Pbpp dm em nm fm) p) (erased (NoColoring em fm) ncol) (erased (Geo dm em nm fm ksm) g) (erased (Cpmap cp dc ec fc rc) c)
          (erased (PointedMap dc ec nc fc rc) pm) (erased (OrderList dc fc ksc) ol) (erased (KernelList dc fc rc as) kl)
          (erased (Preembedding ec nc fc ksc em fm ksm as hl) pe) (erased (Nth (Nat) hl x0c x0m) h0) (erased (Lt x0m dm) lx) (erased (CRed X cp cc) cr)
          -> (erased (Reduces B dm em nm fm) r)) emb)
      -> (NotEmbed X cfs)))

; present.v's no_fit_the_redpart and the use of unavoidability in four_color_hypermap, with minimality as data: a map with no
; dart is coloured, a disconnected one splits (split-reduces), and a connected one reduces through BirkGeo, or through
; unavoidability, a configuration of cfs and NotEmbed, on the map or its mirror.
(def-fns _ $ (erased embed-analysis : (erased (Level) X) (erased (List (List (Config))) css) (erased (List (Config)) cfs) (erased (ConcatL css cfs) cl)
    (erased (AllRedC X css) ar) (erased (UnavE cfs) u) (erased (BirkGeo) bg) (erased (NotEmbed X cfs) ne) -> (erased (Analysis) an))
  (let-match erased u (MkUnavE _ lv every))
  (let-match erased bg (MkBirkGeo Fg Bg geo))
  (let-match erased ne (MkNotEmbed _ _ Fe Be emb))
  (let ((erased all)) (allred-concat X css cfs cl ar))
  (let ((erased Bm) (erased mirror)) (reduces-mirror Be))
  (def-lvl B)
  (let ((erased qg) (erased qe) (erased qm) (erased qs)) (values (prove-predates Bg B) (prove-predates Be B) (prove-predates Bm B) (prove-predates (level-of split-glue) B)))
  (def-fns _ $ (erased analyse : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Pbpp d e n f) p) (erased (NoColoring e f) ncol)
      -> (erased (Reduces B d e n f) r))
    (let-match erased p (MkPbpp _ _ _ _ h gen _ _ _))
    (match erased d _
      (absurd (Zero)
        (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
        (let-match erased le (LengthNil _))
        (let-match erased lf (LengthNil _))
        (no-coloring (Nil _) (Nil _) (Nil _) ncol
          (MkFourColoring (Nil _) (Nil _) (Nil _) (Nil _) (RespNil (Nil _)) (RespNil (Nil _)) (DifferNil) (UnderNil _))))
      ((Succ d1)
        (let-match erased (split-reduces B qs d e n f p (LtZ d1)) (OrL _ _ conn) ((OrR _ _ r) r))
        (let ((erased ks) (erased gr)) (geo d e n f p ncol conn))
        (let-match erased gr (OrL _ _ g) ((OrR _ _ r) (reduces-lift Bg B d e n f r qg)))
        (let-match erased (every d e n f ks g conn gen)
          (MkCfEmbed _ sym cci cp _ dc x0c x0m _ _ _ _ em2 nm2 fm2 ec nc fc rc ksc as hl m c pm ol mo gm kl pe h0 lx))
        (let-match erased (reducible-mem X (MkConfig sym cci cp) cfs all m) (MkReducible _ _ _ cc _ _ cr))
        (let-match erased mo (MoMirror _ _ _ _ _ _ _ rfn pn pf)
          ((MoSame _ _ _ _) (reduces-lift Be B d e n f (emb sym cci cc cp d dc x0c x0m e n f ks ec nc fc rc ksc as hl m p ncol gm c pm ol kl pe h0 lx cr) qe)))
        (let ((erased p2)) (pbpp-mirror d e n f em2 nm2 fm2 p rfn pn pf))
        (let-match erased p2 (MkPbpp _ _ _ _ h2 _ _ _ _))
        (let ((erased ncol2)) (nocol-mirror d e n f em2 nm2 fm2 h h2 rfn pf ncol))
        (reduces-lift Bm B d e n f
          (mirror d e n f em2 nm2 fm2 h rfn pf (emb sym cci cc cp d dc x0c x0m em2 nm2 fm2 ks ec nc fc rc ksc as hl m p2 ncol2 gm c pm ol kl pe h0 lx cr))
          qm))))
  (MkAnalysis (level-of analyse) B analyse))
