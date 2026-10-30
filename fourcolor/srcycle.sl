; srcycleI of geometry.v, on the rings of snip.sl. Load after snip.sl.

; No dart of zs is on the face of x, each told apart from x by a labelling constant on the faces (the bonds gf).
(def-adts $ (FaceApart : ((List (Bond)) gf) ((Nat) x) ((List (Nat)) zs) -> Type)
  enum
  (many FANil : (erased (List (Bond)) gf) (erased (Nat) x) -> (FaceApart gf x (Nil (Nat))))
  (many FACons : (erased (List (Bond)) gf) (erased (Nat) x z) (erased (List (Nat)) zs) (erased (Sep gf x z) s) (erased (FaceApart gf x zs) rest)
      -> (FaceApart gf x (Cons (Nat) z zs))))

; srpath of geometry.v: from x the darts p, each on the face of the edge image of the one before and on no face of the
; darts before that one, the edge image of the last on the face of x0; gf holds the bonds of the face permutation.
(def-adts $ (SRPath : ((List (Nat)) e f) ((List (Bond)) gf) ((Nat) x0 x) ((List (Nat)) p) -> Type)
  enum
  (many SRNil : (erased (List (Nat)) e f) (erased (List (Bond)) gf) (erased (Nat) x0 x ex) (erased (Nth (Nat) e x ex) pe) (erased (SomePath f (Nil (Nat)) ex x0) w)
      -> (SRPath e f gf x0 x (Nil (Nat))))
  (many SRCons : (erased (List (Nat)) e f p) (erased (List (Bond)) gf) (erased (Nat) x0 x ex y) (erased (Nth (Nat) e x ex) pe)
      (erased (SomePath f (Nil (Nat)) ex y) w) (erased (FaceApart gf x p) sa) (erased (SRPath e f gf x0 y p) rest) -> (SRPath e f gf x0 x (Cons (Nat) y p))))

; The class labels of darts told apart are apart.
(def-fns _ $ (erased sep-lab : (erased (Nat) d a b la lb) (erased (List (Nat)) lab rs ids) (erased (List (Bond)) g) (erased (Iota d ids) io) (erased (Rooted g rs ids lab) ro)
    (erased (Sep g a b) s) (erased (Nth (Nat) lab a la) pa) (erased (Nth (Nat) lab b lb) pb) (erased (Length (Nat) lab d) ll) -> (erased (Apart (Nat) Lt la lb) r))
  (match erased (nat-cmp la lb) _
    ((CLt _ _ _ _ lt) (ApLt _ _ la lb lt))
    ((CGt _ _ _ _ gt) (ApGt _ _ la lb gt))
    (absurd (CEq _ _ _)
      (let ((erased _) (erased ca)) (classes-root g d ids lab rs a la io ro pa (nth-lt-length _ lab a d la pa ll)))
      (let ((erased _) (erased cb)) (classes-root g d ids lab rs b la io ro pb (nth-lt-length _ lab b d la pb ll)))
      (sep-conn g a b s (conn-cat g a la b (conn-sym g la a ca) cb)))))

(def-fns _ $ (erased seps-notin : (erased (Nat) d x lx) (erased (List (Nat)) lab rs ids zs ls) (erased (List (Bond)) g) (erased (Iota d ids) io)
    (erased (Rooted g rs ids lab) ro) (erased (Length (Nat) lab d) ll) (erased (Nth (Nat) lab x lx) px) (subterm erased (FaceApart g x zs) sa)
    (erased (Respects lab zs ls) rl) -> (erased (NotIn lx ls) r))
  (let-match erased sa (FACons _ _ z zs1 s sa1) ((FANil _ _) (let-match erased rl (RespNil _)) (NotInNil lx)))
  (let-match erased rl (RespCons _ _ ls1 _ lz pz rl1))
  (NotInCons lx lz ls1 (sep-lab d x z lx lz lab rs ids g io ro s px pz ll) (seps-notin d x lx lab rs ids zs1 ls1 g io ro ll px sa1 rl1)))

(def-fns _ $ (erased sr-walk : (erased (Nat) d x0 x) (erased (List (Nat)) e ei f p lab rs ids) (erased (List (Bond)) gf ge) (erased (Graph d e ge) gre)
    (erased (AllSep gf ge) as) (erased (Iota d ids) io) (erased (Length (Nat) lab d) ll) (erased (Rooted gf rs ids lab) ro) (erased (Respects lab f lab) rf)
    (erased (Length (Nat) e d) le) (erased (HPerm d e ei) pm) (subterm erased (SRPath e f gf x0 x p) sp)
    -> (erased (Nat) y ey) (erased (RPath e f x p y) rp) (erased (Nth (Nat) e y ey) pe) (erased (SomePath f (Nil (Nat)) ey x0) w)
    (erased (List (Nat)) ls) (erased (Respects lab (Cons (Nat) x p) ls) rl) (erased (Distinct ls) dl))
  (let ((erased lx) (erased plx)) (nth-exists _ lab d x ll
    (match erased sp _
      ((SRNil _ _ _ _ _ ex pex _) (nth-lt-length _ e x d ex pex le))
      ((SRCons _ _ _ _ _ _ ex _ pex _ _ _) (nth-lt-length _ e x d ex pex le)))))
  (match erased sp _
    ((SRNil _ _ _ _ _ ex pex wx)
      (values x ex (RPNil e f x) pex wx (Cons (Nat) lx (Nil (Nat))) (RespCons lab (Nil (Nat)) (Nil (Nat)) x lx plx (RespNil lab))
        (DistCons lx (Nil (Nat)) (NotInNil lx) (DistNil))))
    ((SRCons _ _ p1 _ _ _ ex y1 pex wy sa sp1)
      (let ((erased y) (erased ey) (erased rp1) (erased pe) (erased w) (erased ls1) (erased rl1) (erased dl1))
        (sr-walk d x0 y1 e ei f p1 lab rs ids gf ge gre as io ll ro rf le pm sp1))
      (let-match erased rl1 (RespCons _ _ ls2 _ ly py rl2))
      (let ((erased lex) (erased plex)) (nth-exists _ lab d ex ll (perm-val d x ex e ei pm pex)))
      (let-match erased wy (MkSomePath _ _ xs _ _ pth))
      (let-match erased (nth-fn _ lab y1 ly lex py (path-label f lab (Nil _) xs ex y1 lex pth rf plex)) (Refl _ _))
      (let ((erased ne)) (sep-lab d x ex lx lex lab rs ids gf io ro (allsep-adj gf ge x ex (graph-adj d x ex e ge gre pex) as) plx plex ll))
      (values y ey (RPCons e f p1 x ex y1 y pex wy rp1) pe w (Cons (Nat) lx ls1) (RespCons lab (Cons (Nat) y1 p1) ls1 x lx plx rl1)
        (DistCons lx ls1 (NotInCons lx ly ls2 ne (seps-notin d x lx lab rs ids p1 ls2 gf io ro ll plx sa rl2)) dl1)))))

; srcycleI of geometry.v, from srcycle to scycle rlink: in a bridgeless map an srcycle x0 :: p is a ring.
(def-fns _ $ (erased srcycle-ring : (erased (Nat) d x0) (erased (List (Nat)) e n f p) (erased (List (Bond)) gf) (erased (Hypermap d e n f) h)
    (erased (Bridgeless d e n f) br) (erased (Graph d f gf) gr) (erased (SRPath e f gf x0 x0 p) sp) -> (erased (Ring e f x0 p) r))
  (let-match erased br (MkBridgeless _ _ _ _ ge gf2 gre grf as))
  (let-match erased (graph-fn d f gf gf2 gr grf) (Refl _ _))
  (let ((erased nf) (erased ni) (erased fi) (erased _) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased k) (erased cs)) (classes-exists gf d (graph-below d f fi gf (graph-fun d f gf gr) pf)))
  (let-match erased cs (MkClasses _ _ _ ids lab rs io ll lr dr fix cl ro))
  (let-match erased gr (MkGraph _ _ ids2 _ io2 _ z))
  (let-match erased (iota-fn d ids ids2 io io2) (Refl _ _))
  (let ((erased rf)) (const-respects lab ids f lab gf z cl (respects-id-right d ids lab io ll)))
  (let ((erased y) (erased ey) (erased rp) (erased pey) (erased w) (erased ls) (erased rl) (erased dl)) (sr-walk d x0 x0 e nf f p lab rs ids gf ge gre as io ll ro rf le pe sp))
  (MkRing e f p x0 y ey rp pey w (MkSimple f (Cons (Nat) x0 p) lab ls rf rl dl)))
