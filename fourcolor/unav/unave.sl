; (e2, n2, f2): (e, n, f) or its mirror.
(def-adts $ (MapOrMirror : ((Nat) d) ((List (Nat)) e n f e2 n2 f2) -> Type)
  enum
  (many MoSame : (erased (Nat) d) (erased (List (Nat)) e n f) -> (MapOrMirror d e n f e n f))
  (many MoMirror : (erased (Nat) d) (erased (List (Nat)) e n f fn ni fi) (erased (Respects f n fn) rfn) (erased (HPerm d n ni) pn) (erased (HPerm d f fi) pf)
      -> (MapOrMirror d e n f fn ni fi)))

; A configuration of cfs whose kernel has a preembedding into (em, nm, fm) or its mirror.
(def-adts $ (CfEmbed : ((List (Config)) cfs) ((Nat) dm) ((List (Nat)) em nm fm ksm) -> Type)
  enum
  (many MkCfEmbed : (erased (List (Config)) cfs) (erased (Bool) sym) (erased (List (Nat)) cci) (erased (List (Step)) cp) (erased (Nat) dm dc x0c x0m)
      (erased (List (Nat)) em nm fm ksm em2 nm2 fm2 ec nc fc rc ksc as hl) (erased (Mem (Config) (MkConfig sym cci cp) cfs) m) (erased (Cpmap cp dc ec fc rc) c)
      (erased (PointedMap dc ec nc fc rc) pm) (erased (OrderList dc fc ksc) ol) (erased (MapOrMirror dm em nm fm em2 nm2 fm2) mo) (erased (Geo dm em2 nm2 fm2 ksm) g2)
      (erased (KernelList dc fc rc as) kl) (erased (Preembedding ec nc fc ksc em2 fm2 ksm as hl) pe) (erased (Nth (Nat) hl x0c x0m) h0) (erased (Lt x0m dm) lx)
      -> (CfEmbed cfs dm em nm fm ksm)))

(def-fns _ $ (erased hit-embed : (erased (List (Config)) cfs) (erased (Nat) d) (erased (List (Nat)) e n f ks) (erased (Geo d e n f ks) g)
    (erased (QzHit cfs d e n ks) hit) -> (erased (CfEmbed cfs d e n f ks) r))
  (let-match erased hit (MkQzHit _ _ y _ _ _ _ qz qz2 m c v fz ly))
  (let-match erased c (MkCfQz sym cci cp dc x0c ec nc fc rc ksc _ cm pm qc))
  (let-match erased qc (MkQzCert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ olc _ _ _ _ _ _ _ _ _))
  (match erased v _
    ((VSame _)
      (let ((erased as) (erased hl) (erased kl) (erased pe) (erased h0)) (quiz-preembedding dc x0c d y ec nc fc ksc rc e n f ks qz qc g ly fz))
      (MkCfEmbed cfs sym cci cp d dc x0c y e n f ks e n f ec nc fc rc ksc as hl m cm pm olc (MoSame d e n f) g kl pe h0 ly))
    ((VFlip _ _ fl)
      (let ((erased fn) (erased ni) (erased fi) (erased g2) (erased rfn) (erased pn) (erased pf)) (geo-mirror d e n f ks g))
      (let ((erased w) (erased fz2) (erased lw)) (fitz-flip d y e n f ks fn ni qz qz2 g rfn pn ly fl fz))
      (let ((erased as) (erased hl) (erased kl) (erased pe) (erased h0)) (quiz-preembedding dc x0c d w ec nc fc ksc rc fn ni fi ks qz qc g2 lw fz2))
      (MkCfEmbed cfs sym cci cp d dc x0c w e n f ks fn ni fi ec nc fc rc ksc as hl m cm pm olc (MoMirror d e n f fn ni fi rfn pn pf) g2 kl pe h0 lw))))

(def-adts $ (UnavE : ((List (Config)) cfs) -> Type)
  enum
  (many MkUnavE : (erased (List (Config)) cfs) (erased (Level) lv)
      (erased (Fn lv (erased (Nat) d) (erased (List (Nat)) e n f ks) (erased (Geo d e n f ks) g) (erased (Connected d e n f) cc)
          (erased (Genus d e n f (Zero)) gen) -> (erased (CfEmbed cfs d e n f ks) r)) every)
      -> (UnavE cfs)))
