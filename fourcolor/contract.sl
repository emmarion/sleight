; contract_coloring of contract.v with minimality as data, and the trace equations of embed_contract of embed.v. Load after
; embed2.sl and traceconv.sl.

(def-fns _ $ (erased resp-pt : (erased (List (Nat)) kc p ks) (erased (Nat) x u) (erased (Respects kc p ks) rk) (erased (Nth (Nat) p x u) pu)
    -> (erased (Nat) a) (erased (Nth (Nat) kc u a) pa) (erased (Nth (Nat) ks x a) pk))
  (let ((erased a) (erased pa) (erased ia)) (respects-val kc p ks u rk (nth-in p x u pu)))
  (values a pa (respects-at kc p ks x u a rk pu pa)))

; Over the bonds x-y of g, with p a dart map into (e2, f2): the images of x and y are on one face when x is in ins, and the
; image of y is the edge image of that of x otherwise.
(def-adts $ (LiftE : ((List (Nat)) ins p e2 f2) ((List (Bond)) g) -> Type)
  enum
  (many LENil : (erased (List (Nat)) ins p e2 f2) -> (LiftE ins p e2 f2 (Nil (Bond))))
  (many LEIn : (erased (List (Nat)) ins p e2 f2) (erased (List (Bond)) g) (erased (Nat) x y u v) (erased (In x ins) i) (erased (Nth (Nat) p x u) pu)
      (erased (Nth (Nat) p y v) pv) (erased (SomePath f2 (Nil (Nat)) u v) w) (erased (LiftE ins p e2 f2 g) rest)
      -> (LiftE ins p e2 f2 (Cons (Bond) (MkBond x y) g)))
  (many LEOut : (erased (List (Nat)) ins p e2 f2) (erased (List (Bond)) g) (erased (Nat) x y u v) (erased (NotIn x ins) o) (erased (Nth (Nat) p x u) pu)
      (erased (Nth (Nat) p y v) pv) (erased (Nth (Nat) e2 u v) pe) (erased (LiftE ins p e2 f2 g) rest)
      -> (LiftE ins p e2 f2 (Cons (Bond) (MkBond x y) g))))

(def-fns _ $ (erased lift-ecc : (erased (List (Nat)) ins p e2 f2 kc ke ks) (erased (List (Bond)) g) (subterm erased (LiftE ins p e2 f2 g) lf)
    (erased (Respects kc f2 kc) rf) (erased (Respects kc e2 ke) re) (erased (Differ ke kc) df) (erased (Respects kc p ks) rk) -> (erased (EdgeCC ins ks g) r))
  (match erased lf _
    ((LENil _ _ _ _) (ECNil ins ks))
    ((LEIn _ _ _ _ g1 x y u v i pu pv w lf1)
      (let ((erased a) (erased pa) (erased px)) (resp-pt kc p ks x u rk pu))
      (let ((erased b) (erased pb) (erased py)) (resp-pt kc p ks y v rk pv))
      (let-match erased w (MkSomePath _ _ ws _ _ pw))
      (let-match erased (nth-fn _ kc v a b (path-col kc f2 (Nil _) ws u v a rf pw pa) pb) (Refl _ _))
      (ECIn ins ks g1 x y a i px py (lift-ecc ins p e2 f2 kc ke ks g1 lf1 rf re df rk)))
    ((LEOut _ _ _ _ g1 x y u v o pu pv pe lf1)
      (let ((erased a) (erased pa) (erased px)) (resp-pt kc p ks x u rk pu))
      (let ((erased b) (erased pb) (erased py)) (resp-pt kc p ks y v rk pv))
      (ECOut ins ks g1 x y a b o px py (apart-sym b a (differ-nth ke kc u b a df (respects-at kc e2 ke u v b re pe pb) pa))
        (lift-ecc ins p e2 f2 kc ke ks g1 lf1 rf re df rk)))))

; The colouring k0 = k . h of contract_coloring: a four-colouring kc of (e2, f2) gives the contract colouring kc . p of
; (d, e, f) for cc when p sends each face along faces (pf is p . f) and the edge links as LiftE says.
(def-fns _ $ (erased cc-lift : (erased (Nat) d d2) (erased (List (Nat)) e f ccx ins e2 f2 kc p pf) (erased (List (Bond)) ge) (erased (InsertE e ccx ins) ie)
    (erased (Graph d e ge) gr) (erased (FourColoring e2 f2 kc) c) (erased (Length (Nat) kc d2) lk) (erased (Length (Nat) p d) lp) (erased (Under p d2) up)
    (erased (Respects p f pf) rpf) (erased (Reach f2 p pf) rc) (erased (LiftE ins p e2 f2 ge) le)
    -> (erased (List (Nat)) ks) (erased (Respects kc p ks) rk) (erased (CCColoring d e f ccx ks) r))
  (let-match erased c (MkFourColoring _ _ _ ke rf re df u))
  (let ((erased ks) (erased rk)) (respects-exists kc p d2 up lk))
  (let ((erased lks)) (respects-length kc p ks d rk lp))
  (values ks rk
    (MkCCColoring d e f ccx ks ins ge ie gr (respects-assoc f p kc pf ks ks d rpf (reach-resp kc f2 p pf ks rf rc rk) rk lks lp)
      (lift-ecc ins p e2 f2 kc ke ks ge le rf re df rk) (respects-under-vals kc p ks 4 rk u) lks)))

; The map of (d, e, n, f) contracted along cc (contract_coloring's G2): the one map of ms, smaller, planar, bridgeless, plain
; and precubic, with a dart map p from (d, e, n, f) for cc-lift.
(def-adts $ (Contraction : ((Nat) d) ((List (Nat)) e n f ccx) ((List (Mp)) ms) -> Type)
  enum
  (many MkContraction : (erased (Nat) d d2) (erased (List (Nat)) e n f ccx e2 n2 f2 ins p pf) (erased (List (Bond)) ge) (erased (Pbpp d2 e2 n2 f2) pb)
      (erased (Lt d2 d) lt) (erased (InsertE e ccx ins) ie) (erased (Graph d e ge) gr) (erased (Length (Nat) p d) lp) (erased (Under p d2) up)
      (erased (Respects p f pf) rpf) (erased (Reach f2 p pf) rc) (erased (LiftE ins p e2 f2 ge) le)
      -> (Contraction d e n f ccx (Cons (Mp) (MkMp d2 e2 n2 f2) (Nil (Mp))))))

(def-fns _ $ (erased contraction-smaller : (erased (Nat) d) (erased (List (Nat)) e n f ccx) (erased (List (Mp)) ms) (erased (Contraction d e n f ccx ms) ct)
    -> (erased (Smaller d ms) r))
  (let-match erased ct (MkContraction _ d2 _ _ _ _ e2 n2 f2 ins p pf ge pb lt ie gr lp up rpf rc le))
  (SmallerCons d d2 e2 n2 f2 (Nil _) pb lt (SmallerNil d)))

; contract_coloring, given the contracted map: a four-colouring of it gives a contract colouring for cc.
(def-fns _ $ (erased contraction-lift : (erased (Nat) d) (erased (List (Nat)) e n f ccx) (erased (List (Mp)) ms) (erased (Contraction d e n f ccx ms) ct)
    (erased (MpCols ms) cs) -> (erased (List (Nat)) ks) (erased (CCColoring d e f ccx ks) r))
  (let-match erased ct (MkContraction _ d2 _ _ _ _ e2 n2 f2 ins p pf ge pb lt ie gr lp up rpf rc le))
  (let-match erased cs (MpcCons _ _ _ _ kc _ col _))
  (let-match erased pb (MkPbpp _ _ _ _ h _ _ _ _))
  (let ((erased le2) (erased ln2) (erased lf2)) (hyper-lengths d2 e2 n2 f2 h))
  (let-match erased col (MkFourColoring _ _ _ _ rf _ _ _))
  (let ((erased ks) (erased rk) (erased r)) (cc-lift d d2 e f ccx ins e2 f2 kc p pf ge ie gr col (respects-length kc f2 kc d2 rf lf2) lp up rpf rc le))
  (values ks r))

; The trace equations of embed_contract: with k constant on the faces fm, kc = k . h1 a contract colouring of a configuration
; map and kr = k . hr a four-colouring of a remainder map, and the images under h1 of the configuration's ring a :: p each
; reaching along fm the image under hr of the dart of R at its place, the colours of kc on a :: p and of kr on R have one
; trace et: a contract ring trace (CcCol) of the configuration and a ring trace of the remainder map on R.
(def-fns _ $ (erased embed-contract-trace : (erased (List (Step)) cp) (erased (Nat) dm dc dr a) (erased (List (Nat)) fm k h1 hr ec fc p ccx kc er fr R kr A B)
    (erased (Cpmap cp dc ec fc (Cons (Nat) a p)) cm) (erased (CcColoring ec fc ccx kc) c) (erased (FourColoring er fr kr) cr)
    (erased (Respects k fm k) rf) (erased (Length (Nat) k dm) lk) (erased (Respects k h1 kc) rk1) (erased (Respects k hr kr) rk2)
    (erased (Length (Nat) h1 dc) l1) (erased (Under h1 dm) u1) (erased (Length (Nat) hr dr) l2)
    (erased (Respects h1 (Cons (Nat) a p) A) ra) (erased (Respects hr R B) rb) (erased (Reach fm A B) rc)
    -> (erased (List (Col)) et) (erased (CcCol cp ccx et) cc1) (erased (RingTrace er fr R et) rt))
  (let ((erased L) (erased rl)) (respects-exists k A dm (respects-under-vals h1 (Cons _ a p) A dm ra u1) lk))
  (let ((erased rr)) (respects-assoc R hr k B kr L dr rb (reach-resp k fm A B L rf rc rl) rk2 (respects-length k hr kr dr rk2 l2) l2))
  (let ((erased rr1)) (respects-assoc (Cons _ a p) h1 k A kc L dc ra rl rk1 (respects-length k h1 kc dc rk1 l1) l1))
  (let-match erased c (MkCcColoring _ _ _ _ ie ke pi face ce edge four))
  (let ((erased cs) (erased co)) (cols-exists L (respects-under-out kc (Cons _ a p) L 4 rr1 four)))
  (let-match erased rr1 (RespCons _ _ L1 _ l0 pl0 rr2))
  (let-match erased co (All2Cons _ _ _ _ c0 _ cs1 pc0 co1))
  (let ((erased et) (erased t)) (trace-exists cs))
  (let-match erased t (TrCons _ _ _ tf))
  (values et (MkCcCol cp ccx dc ec fc (Cons _ a p) kc L cs et cm c rr1 (ncols-of L cs co) (MkTrace c0 cs1 et (ctr-of-tf c0 c0 cs1 et tf)))
    (MkRingTrace er fr R kr L cs et cr rr co t)))
