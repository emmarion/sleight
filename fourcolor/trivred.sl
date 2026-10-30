; fullred.sl's TrivRed: trivial_hom_ring of embed.v, its use on the reversed ring, and the five-dart case. Load after fullred.sl,
; in its chain. That these statements match Coq's has been checked only by reading.

; What the lemmas here read off the two maps: embed3.sl's EEnv with GcOK and FunctorAll, and the map as Spk of minarity.sl.
(def-adts $ (TCx : ((Nat) dc) ((List (Nat)) ec nc fc ksc rc) ((Nat) dm) ((List (Nat)) em nm fm ksm as hl fe lab) -> Type)
  enum
  (many MkTCx : (erased (Nat) dc) (erased (List (Nat)) ec nc fc ksc rc) (erased (Nat) dm) (erased (List (Nat)) em nm fm ksm as hl fe lab)
      (erased (EEnv dc ec nc fc ksc rc dm em nm fm ksm as hl) en) (erased (GcOK dc ec nc rc as) ok) (erased (FunctorAll ec em as hl as) fu)
      (erased (Spk dm em nm fm fe lab) sp) (erased (Connected dm em nm fm) cn) -> (TCx dc ec nc fc ksc rc dm em nm fm ksm as hl fe lab)))

(def-fns _ $ (erased tm : (erased (Nat) dc dm) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl fe lab) (erased (TCx dc ec nc fc ksc rc dm em nm fm ksm as hl fe lab) cx)
    -> (erased (Hypermap dm em nm fm) h) (erased (Genus dm em nm fm (Zero)) gen) (erased (Bridgeless dm em nm fm) bl) (erased (AllOrder dm em (Succ (Succ (Zero)))) pl)
    (erased (AllOrder dm nm (Succ (Succ (Succ (Zero))))) cu) (erased (FaceLab dm fm lab) fl) (erased (Connected dm em nm fm) cn)
    (erased (List (Nat)) nfm nim fim) (erased (HPerm dm em nfm) qem) (erased (HPerm dm nm nim) qnm) (erased (HPerm dm fm fim) qfm))
  (let-match erased cx (MkTCx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ en ok fu sp cn))
  (let-match erased sp (MkSpk _ _ _ _ _ _ ids h gen bl pl cu rfe kfe io ufe lfe fl rl))
  (let ((erased nfm) (erased nim) (erased fim) (erased rnf) (erased qem) (erased qnm) (erased qfm)) (hyper-core dm em nm fm h))
  (values h gen bl pl cu fl cn nfm nim fim qem qnm qfm))

(def-fns _ $ (erased allab-in : (erased (List (Nat)) lab L) (erased (Nat) x) (subterm erased (List (Nat)) xs) (erased (AllLab lab L xs) al) (erased (In x xs) ix)
    -> (erased (Nat) l) (erased (Nth (Nat) lab x l) pl) (erased (In l L) il))
  (let-match erased al (AlCons _ _ xs1 y l pl il al1) (absurd (AlNil _ _) ix))
  (match erased ix _ ((InHere _ _) (values l pl il)) ((InThere _ _ _ ix1) (allab-in lab L x xs1 al1 ix1))))

; t is on a face of R or on none, told apart by the labels.
(def-fns _ $ (erased lab-dec : (erased (Nat) d t) (erased (List (Nat)) f lab R lr) (erased (FaceLab d f lab) fl) (erased (Respects lab R lr) rl) (erased (Lt t d) lt)
    -> (erased (Or (Fband f R t) (Kernel f R t)) r))
  (let ((erased fl2)) fl)
  (let-match erased fl2 (MkFaceLab _ k _ fi _ ids rs gf pf gr io ro cl ll))
  (let ((erased l) (erased pl)) (nth-exists _ lab d t ll lt))
  (match erased (in-dec l lr) _
    ((OrL _ _ il)
      (let ((erased j) (erased ij) (erased pj)) (respects-in lab R lr l rl il))
      (OrL _ _ (MkFband f R t j ij (facelab-same d t j l f lab fl pl pj))))
    ((OrR _ _ ol) (OrR _ _ (MkKernel f R lab lr t l (facelab-rf d f lab fl) rl pl ol)))))

(def-fns _ $ (erased rp-unsnoc : (erased (List (Nat)) e f P) (erased (Nat) x a y) (subterm erased (RPath e f x (Cons (Nat) a P) y) rp)
    -> (erased (List (Nat)) Q) (erased (Nat) c ec) (erased (RPath e f x Q c) r1) (erased (Nth (Nat) e c ec) pc) (erased (SomePath f (Nil (Nat)) ec y) sc)
    (erased (AppN Q (Cons (Nat) y (Nil (Nat))) (Cons (Nat) a P)) ap))
  (let-match erased rp (RPCons _ _ _ _ ex _ _ pe sp rp1))
  (let-match erased rp1 (RPCons _ _ P1 _ ea b _ pa sa rp2) ((RPNil _ _ _) (values (Nil _) x ex (RPNil e f x) pe sp (AppNil _))))
  (let ((erased Q1) (erased c) (erased ec) (erased r1) (erased pc) (erased sc) (erased ap1)) (rp-unsnoc e f P1 a b y rp1))
  (values (Cons _ a Q1) c ec (RPCons e f Q1 x ex a c pe sp r1) pc sc (AppCons Q1 _ _ a ap1)))

(def-fns _ $ (erased resp-end : (erased (List (Nat)) ec fc em fm hl hp) (erased (Nat) x y hx w) (subterm erased (List (Nat)) p) (erased (RPath ec fc x p y) rp)
    (erased (RPath em fm hx hp w) rq) (erased (Respects hl (Cons (Nat) x p) (Cons (Nat) hx hp)) rh) -> (erased (Nth (Nat) hl y w) r))
  (let-match erased rh (RespCons _ _ _ _ _ px rh1))
  (let-match erased rp (RPCons _ _ p1 _ ex z _ pe sp rp1)
    ((RPNil _ _ _) (let-match erased rh1 (RespNil _)) (let-match erased rq (RPNil _ _ _)) px))
  (let-match erased rh1 (RespCons _ _ hp1 _ hz pz rh2))
  (let-match erased rq (RPCons _ _ _ _ eh _ _ _ _ rq1))
  (resp-end ec fc em fm hl hp1 z y hz w p1 rp1 rq1 rh1))

(def-fns _ $ (erased sub-rot : (erased (List (Nat)) X Y) (erased (Nat) a) (erased (AppN X (Cons (Nat) a (Nil (Nat))) Y) ap)
    -> (erased (WSub (Cons (Nat) a X) Y) s1) (erased (WSub Y (Cons (Nat) a X)) s2))
  (values (HSubCons a X Y (app-in-r X _ Y a ap (InHere a (Nil _))) (app-sub-l X _ Y X ap (sub-refl X)))
    (app-sub X _ Y (Cons _ a X) ap (sub-cons a X X (sub-refl X)) (HSubCons a (Nil _) (Cons _ a X) (InHere a X) (HSubNil _)))))

(def-fns _ $ (erased dist-unrot : (erased (List (Nat)) X Y) (erased (Nat) a) (erased (AppN X (Cons (Nat) a (Nil (Nat))) Y) ap) (erased (Distinct Y) dy)
    -> (erased (Distinct (Cons (Nat) a X)) r))
  (let ((erased oa) (erased ob)) (app-mid-notin (Nil _) Y X a ap dy))
  (let ((erased dx) (erased da)) (app-parts _ Y X ap dy))
  (DistCons a X oa dx))

(def-fns _ $ (erased dist-rot : (erased (List (Nat)) X Y) (erased (Nat) a) (erased (AppN X (Cons (Nat) a (Nil (Nat))) Y) ap) (erased (Distinct (Cons (Nat) a X)) da)
    -> (erased (Distinct Y) r))
  (let-match erased da (DistCons _ _ oa dx))
  (app-distinct X _ Y ap dx (DistCons a (Nil _) (NotInNil a) (DistNil)) (disj-one a X oa)))

; A ring a :: b :: P read from b.
(def-fns _ $ (erased ring-rot1 : (erased (List (Nat)) e f P) (erased (Nat) a b) (erased (Ring e f a (Cons (Nat) b P)) rg)
    -> (erased (List (Nat)) Q) (erased (AppN P (Cons (Nat) a (Nil (Nat))) Q) ap) (erased (Ring e f b Q) r))
  (let-match erased rg (MkRing _ _ _ _ w ew rp pw sw sm))
  (let-match erased rp (RPCons _ _ _ _ ea _ _ pa sa rp1))
  (let ((erased Q) (erased rq) (erased ap)) (rpath-join e f (Nil _) P b w ew a a rp1 pw sw (RPNil e f a)))
  (let-match erased sm (MkSimple _ _ lab ls rf rl dl))
  (let-match erased rl (RespCons _ _ ls1 _ la pla rl1))
  (let-match erased rl1 (RespCons _ _ lP _ lb plb rlP))
  (let ((erased LQ) (erased rLQ) (erased al)) (resp-app lab _ Q _ P ap lP rlP (RespCons lab (Nil _) (Nil _) a la pla (RespNil lab))))
  (values Q ap (MkRing e f Q b a ea rq pa sa (MkSimple f (Cons _ b Q) lab (Cons _ lb LQ) rf (RespCons lab Q LQ b lb plb rLQ)
    (dist-rot (Cons _ lb lP) (Cons _ lb LQ) la (AppCons lP _ LQ lb al) dl)))))

; diskF S is empty: every dart of diskN S is on a face of S, read off a ring S0 with the darts of S.
(def-adts $ (FEmpty : ((Nat) d) ((List (Nat)) e n f lab S) -> Type)
  enum
  (many MkFEmpty : (erased (Nat) d x0) (erased (List (Nat)) e n f lab S p hd zs lr) (erased (Ring e f x0 p) rg) (erased (WSub S (Cons (Nat) x0 p)) s1)
      (erased (WSub (Cons (Nat) x0 p) S) s2) (erased (DiskSplit d e n (Cons (Nat) x0 p) hd zs) ds) (erased (Respects lab (Cons (Nat) x0 p) lr) rl)
      (erased (AllLab lab lr hd) al) -> (FEmpty d e n f lab S)))

(def-fns _ $ (erased fe-band : (erased (Nat) d t) (erased (List (Nat)) e n f lab S) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) gen)
    (erased (FaceLab d f lab) fl) (erased (FEmpty d e n f lab S) fm) (erased (DiskN n f S t) dn) (erased (Lt t d) lt) -> (erased (Fband f S t) r))
  (let-match erased fm (MkFEmpty _ x0 _ _ _ _ _ p hd zs lr rg s1 s2 ds rl al))
  (let ((erased dn0)) (disk-move n f S (Cons _ x0 p) t dn s1 s2))
  (let ((erased it)) (ds-mem d t x0 e n f p hd zs h gen rg (ring-under d x0 e n f p h rg) ds dn0 lt))
  (let ((erased l) (erased pl) (erased il)) (allab-in lab lr t hd al it))
  (let ((erased j) (erased ij) (erased pj)) (respects-in lab (Cons _ x0 p) lr l rl il))
  (fband-move f (Cons _ x0 p) S t (MkFband f _ t j ij (facelab-same d t j l f lab fl pl pj)) s2))

(def-fns _ $ (erased fe-move : (erased (Nat) d) (erased (List (Nat)) e n f lab S S2) (erased (FEmpty d e n f lab S) fm) (erased (WSub S S2) a) (erased (WSub S2 S) b)
    -> (erased (FEmpty d e n f lab S2) r))
  (let-match erased fm (MkFEmpty _ x0 _ _ _ _ _ p hd zs lr rg s1 s2 ds rl al))
  (MkFEmpty d x0 e n f lab S2 p hd zs lr rg (sub-trans S2 S _ b s1) (sub-trans _ S S2 s2 a) ds rl al))
