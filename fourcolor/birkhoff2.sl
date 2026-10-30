; The uses of minimality in birkhoff.v and coloring.v, with the minimality of the map entering as data: each step that Coq
; proves by colouring smaller maps here returns a Plan, which names the smaller maps; plan-false takes four-colourings of
; them and a search certificate that the map has none (NoExt), and gives False. Load after birkhoff.sl.

(def-fns _ $ (erased noext-col : (erased (Nat) d) (erased (List (Nat)) e n f ks) (erased (Hypermap d e n f) hm)
    (erased (NoExt d e f (Nil (Nat)) (Nil (Nat)) (Nil (Nat))) nce) (erased (FourColoring e f ks) c) -> (erased (False) r))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f hm))
  (let ((erased c2)) c)
  (let-match erased c2 (MkFourColoring _ _ _ _ rf _ _ _))
  (noext-sound d e f (Nil _) (Nil _) (Nil _) ks ks nce (JoinNil ks) (respects-length ks f ks d rf lf) c (RespNil ks)))

; The maps of ms are each planar, bridgeless, plain, precubic and smaller than d darts.
(def-adts $ (Smaller : ((Nat) d) ((List (Mp)) ms) -> Type)
  enum
  (many SmNil : (erased (Nat) d) -> (Smaller d (Nil (Mp))))
  (many SmCons : (erased (Nat) d d2) (erased (List (Nat)) e2 n2 f2) (erased (List (Mp)) ms) (erased (Hypermap d2 e2 n2 f2) h2)
      (erased (Genus d2 e2 n2 f2 (Zero)) g2) (erased (Bridgeless d2 e2 n2 f2) b2) (erased (AllOrder d2 e2 (Succ (Succ (Zero)))) pl2)
      (erased (Precubic d2 n2) pc2) (erased (Lt d2 d) lt2) (erased (Smaller d ms) rest) -> (Smaller d (Cons (Mp) (MkMp d2 e2 n2 f2) ms))))

; What a step needs coloured to refute the map: a colouring of the map itself, two parts it is patched from along empty rings
; (minimal_counter_example_is_connected), or the maps of the Birkhoff check for a ring of h + 2 darts nontrivial for m.
(def-adts $ (Plan : ((Nat) d) ((List (Nat)) e n f) ((List (Mp)) ms) -> Type)
  enum
  (many PCol : (erased (Nat) d) (erased (List (Nat)) e n f ks) (erased (FourColoring e f ks) c) -> (Plan d e n f (Nil (Mp))))
  (many PSplit : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr)
      (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr (Nil (Nat)) (Nil (Nat))) pt)
      (erased (Genus dd ed nd fd (Zero)) gd) (erased (Bridgeless dd ed nd fd) bd) (erased (AllOrder dd ed (Succ (Succ (Zero)))) pld) (erased (Precubic dd nd) pcd)
      (erased (Lt dd d) ltd)
      (erased (Genus dr er nr fr (Zero)) gr) (erased (Bridgeless dr er nr fr) br) (erased (AllOrder dr er (Succ (Succ (Zero)))) plr) (erased (Precubic dr nr) pcr)
      (erased (Lt dr d) ltr)
      -> (Plan d e n f (Cons (Mp) (MkMp dd ed nd fd) (Cons (Mp) (MkMp dr er nr fr) (Nil (Mp))))))
  (many PBirk : (erased (Nat) d x0 h m n0 dd1 dd2) (erased (List (Nat)) e n f p ed1 nd1 fd1 bd1 ed2 nd2 fd2 bd2) (erased (List (Ctree)) ts)
      (erased (List (Mp)) ms1 ms2 ms) (erased (Ctree) ctu) (erased (Gtree) gtu) (erased (Genus d e n f (Zero)) gen)
      (erased (AllOrder d e (Succ (Succ (Zero)))) pl) (erased (AllOrder d n (Succ (Succ (Succ (Zero))))) cu) (erased (Connected d e n f) cn)
      (erased (Length (Nat) (Cons (Nat) x0 p) (Succ (Succ h))) lr)
      (erased (CEv ctu (ESStart)) ce) (erased (GE ctu (Cons RS (MkRx (GSet) (BS0) (GSG gtu)) (Nil RS)) (ESStart) (Succ h)) ge)
      (erased (GCov (GSG gtu) (Zero) (BFalse) (Succ h)) gc) (erased (BK h ts ctu gtu n0 ctu gtu) bk)
      (erased (BRing d e n f x0 p dd1 dd2 ed1 nd1 fd1 bd1 ed2 nd2 fd2 bd2) br) (erased (BNeed d dd1 h m ed1 nd1 fd1 bd1 ts ms1) n1)
      (erased (BNeed d dd2 h m ed2 nd2 fd2 bd2 ts ms2) n2) (erased (App (Mp) ms1 ms2 ms) ap) -> (Plan d e n f ms)))

; A plan with the list of maps it names.
(def-adts $ (Planned : ((Nat) d) ((List (Nat)) e n f) -> Type)
  enum
  (many MkPlanned : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (List (Mp)) ms) (erased (Plan d e n f ms) pl) -> (Planned d e n f)))

(def-fns _ $ (erased mp-app : (subterm erased (List (Mp)) xs) (erased (List (Mp)) ys) -> (erased (List (Mp)) zs) (erased (App (Mp) xs ys zs) r))
  (let-match erased xs (Cons _ x xs1) ((Nil _) (values ys (CatNil _ ys))))
  (let ((erased zs1) (erased r1)) (mp-app xs1 ys))
  (values (Cons _ x zs1) (CatCons _ x xs1 ys zs1 r1)))

(def-fns _ $ (erased mpcols-split : (erased (List (Mp)) xs ys zs) (subterm erased (App (Mp) xs ys zs) ap) (erased (MpCols zs) c)
    -> (erased (MpCols xs) cx) (erased (MpCols ys) cy))
  (match erased ap _
    ((CatNil _ _) (values (MCNil) c))
    ((CatCons _ x xs1 _ zs1 ap1)
      (let-match erased c (MCCons d e n f ks _ cl c1))
      (let ((erased cx) (erased cy)) (mpcols-split xs1 ys zs1 ap1 c1))
      (values (MCCons d e n f ks xs1 cl cx) cy))))

(def-fns _ $ (erased smaller-app : (erased (Nat) d) (erased (List (Mp)) xs ys zs) (subterm erased (App (Mp) xs ys zs) ap) (erased (Smaller d xs) sx)
    (erased (Smaller d ys) sy) -> (erased (Smaller d zs) r))
  (match erased ap _
    ((CatNil _ _) sy)
    ((CatCons _ x xs1 _ zs1 ap1)
      (let-match erased sx (SmCons _ d2 e2 n2 f2 _ h2 g2 b2 pl2 pc2 lt2 sx1))
      (SmCons d d2 e2 n2 f2 zs1 h2 g2 b2 pl2 pc2 lt2 (smaller-app d xs1 ys zs1 ap1 sx1 sy)))))

(def-fns _ $ (erased bneed-smaller : (erased (Nat) d dd h m) (erased (List (Nat)) ed nd fd bd) (erased (List (Ctree)) ts) (erased (List (Mp)) ms)
    (subterm erased (BNeed d dd h m ed nd fd bd ts ms) bn) -> (erased (Smaller d ms) r))
  (match erased bn _
    ((BNNil _ _ _ _ _ _ _ _) (SmNil d))
    ((BNCons _ _ _ _ d2 _ _ _ _ e2 n2 f2 cp t ts1 ms1 bp h2 g2 b2 pl2 pc2 lt2 ss bn1)
      (SmCons d d2 e2 n2 f2 ms1 h2 g2 b2 pl2 pc2 lt2 (bneed-smaller d dd h m ed nd fd bd ts1 ms1 bn1)))))

; The maps a plan names are smaller planar bridgeless plain precubic maps.
(def-fns _ $ (erased plan-smaller : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (List (Mp)) ms) (erased (Plan d e n f ms) pa)
    -> (erased (Smaller d ms) r))
  (match erased pa _
    ((PCol _ _ _ _ _ _) (SmNil d))
    ((PSplit _ dd dr _ _ _ ed nd fd er nr fr hd hr pt gd bd pld pcd ltd gr br plr pcr ltr)
      (let ((erased pt2)) pt)
      (let-match erased pt2 (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids idd idr bG bGr h hmd hmr io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
      (SmCons d dd ed nd fd _ hmd gd bd pld pcd ltd (SmCons d dr er nr fr _ hmr gr br plr pcr ltr (SmNil d))))
    ((PBirk _ x0 h m n0 dd1 dd2 _ _ _ p ed1 nd1 fd1 bd1 ed2 nd2 fd2 bd2 ts ms1 ms2 _ ctu gtu gen pl cu cn lr ce ge gc bk br n1 n2 ap)
      (smaller-app d ms1 ms2 ms ap (bneed-smaller d dd1 h m ed1 nd1 fd1 bd1 ts ms1 n1) (bneed-smaller d dd2 h m ed2 nd2 fd2 bd2 ts ms2 n2)))))

; A plan, the four-colourings of the maps it names, and a certificate that the map has none give False.
(def-fns _ $ (erased plan-false : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (List (Mp)) ms) (erased (Hypermap d e n f) hm)
    (erased (NoExt d e f (Nil (Nat)) (Nil (Nat)) (Nil (Nat))) nce) (erased (Plan d e n f ms) pa) (erased (MpCols ms) mc) -> (erased (False) r))
  (match erased pa _
    ((PCol _ _ _ _ ks c) (noext-col d e n f ks hm nce c))
    ((PSplit _ dd dr _ _ _ ed nd fd er nr fr hd hr pt gd bd pld pcd ltd gr br plr pcr ltr)
      (let-match erased mc (MCCons _ _ _ _ kd _ cd mc1))
      (let-match erased mc1 (MCCons _ _ _ _ kr _ cr _))
      (let ((erased ks) (erased c)) (patch-colorable-nil d dd dr e n f ed nd fd er nr fr hd hr kd kr pt cd cr))
      (noext-col d e n f ks hm nce c))
    ((PBirk _ x0 h m n0 dd1 dd2 _ _ _ p ed1 nd1 fd1 bd1 ed2 nd2 fd2 bd2 ts ms1 ms2 _ ctu gtu gen pl cu cn lr ce ge gc bk br n1 n2 ap)
      (let ((erased c1) (erased c2)) (mpcols-split ms1 ms2 ms ap mc))
      (birkhoff-ring d x0 h m n0 dd1 dd2 e n f p ed1 nd1 fd1 bd1 ed2 nd2 fd2 bd2 ts ms1 ms2 ctu gtu hm gen pl cu cn nce lr ce ge gc bk br n1 n2 c1 c2))))

; minimal_counter_example_is_connected: a planar bridgeless plain precubic map with a dart is connected, or has a plan.
(def-fns _ $ (erased mce-connected-plan : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) hm) (erased (Genus d e n f (Zero)) gen)
    (erased (Bridgeless d e n f) bl) (erased (AllOrder d e (Succ (Succ (Zero)))) pl) (erased (Precubic d n) pc) (erased (Lt (Zero) d) ld)
    -> (erased (HOr (Connected d e n f) (Planned d e n f)) r))
  (let-match erased (gcomp-split d e n f hm gen bl pl pc ld) (OrR _ _ sp) ((OrL _ _ cn) (OrL _ _ cn)))
  (let-match erased sp (MkGcompSplit _ dd dr _ _ _ ed nd fd er nr fr hd hr pt gd bd pld pcd ltd gr br plr pcr ltr))
  (OrR _ _ (MkPlanned d e n f _ (PSplit d dd dr e n f ed nd fd er nr fr hd hr pt gd bd pld pcd ltd gr br plr pcr ltr))))

(def-fns _ $ (erased lt-succ-of : (erased (Nat) a b) (erased (Lt a b) p) -> (erased (Nat) b1) (erased (Eq (Nat) b (Succ b1)) e))
  (match erased p _ ((LtZ b1) (values b1 (Refl _ b))) ((LtS _ b1 _) (values b1 (Refl _ b)))))

(def-fns _ $ (erased lt-ls : (erased (Nat) a c b) (subterm erased (Lt a c) p) (erased (Lt c (Succ b)) q) -> (erased (Lt a b) r))
  (match erased p _
    ((LtZ c1)
      (let-match erased q (LtS _ _ q1))
      (let ((erased b1) (erased eb)) (lt-succ-of c1 b q1))
      (let-match erased eb (Refl _ _))
      (LtZ b1))
    ((LtS a1 c1 p1)
      (let-match erased q (LtS _ _ q1))
      (let ((erased b1) (erased eb)) (lt-succ-of c1 b q1))
      (let-match erased eb (Refl _ _))
      (LtS a1 b1 (lt-ls a1 c1 b1 p1 q1)))))

(def-fns _ $ (erased lt-tr : (erased (Nat) a c b) (erased (Lt a c) p) (erased (Lt c b) q) -> (erased (Lt a b) r))
  (let ((erased b1) (erased eb)) (lt-succ-of c b q))
  (let-match erased eb (Refl _ _))
  (lt-succ-left a b (LtS a b1 (lt-ls a c b1 p q))))

(def-fns _ $ (erased bkmode-fn : (erased (Nat) k m1 m2) (erased (BkMode k m1) b1) (erased (BkMode k m2) b2) -> (erased (Eq (Nat) m1 m2) r))
  (match erased b1 _
    ((BMLow _ l1) (match erased b2 _ ((BMLow _ _) (Refl _ m1)) (absurd (BMFive) (lt-irrefl k l1))))
    ((BMFive) (match erased b2 _ (absurd (BMLow _ l2) (lt-irrefl k l2)) ((BMFive) (Refl _ m1))))))

; The theorem Birkhoff of birkhoff.v for a planar bridgeless plain cubic connected map: a ring of k darts, k below 6, nontrivial
; for the m of BkMode k m, has a plan. The induction on the ring size follows birkhoff-maps' Shorter rings until birkhoff-maps
; names the maps of the check, so one plan names every map needed.
(def-fns _ $ (erased birkhoff-go : (erased (Nat) d x0 k m) (erased (List (Nat)) e n f p) (subterm erased (Nat) b) (erased (Lt k b) lb)
    (erased (BirkhoffChecks) bks) (erased (Hypermap d e n f) hm) (erased (Genus d e n f (Zero)) gen) (erased (Bridgeless d e n f) bl)
    (erased (AllOrder d e (Succ (Succ (Zero)))) pl) (erased (AllOrder d n (Succ (Succ (Succ (Zero))))) cu) (erased (Connected d e n f) cn)
    (erased (Ring e f x0 p) rg) (erased (Length (Nat) (Cons (Nat) x0 p) k) lr) (erased (Lt k 6) l6) (erased (BkMode k m) md)
    (erased (NonTrivial d e n f (Cons (Nat) x0 p) m) nt) -> (erased (Planned d e n f) r))
  (unary 6)
  (let ((erased h) (erased m2) (erased eq) (erased bc) (erased md2)) (birkhoff-check-at k bks (ring-two d x0 k e n f p hm bl rg lr) l6))
  (let-match erased eq (Refl _ _))
  (let-match erased (bkmode-fn k m m2 md md2) (Refl _ _))
  (let-match erased bc (MkBirkhoffCheck _ _ n0 cps ts ctu gtu ce ge gc bb bk))
  (match erased (birkhoff-maps d h m x0 e n f p cps ts hm gen bl pl cu cn rg lr nt bb) _
    ((BKShort _ _ _ _ _ _ _ _ _ sh)
      (let-match erased sh (MkShorter _ _ y0 k2 _ _ _ Q rq nq lq lt))
      (let-match erased lb (LtS _ b1 lb1))
      (birkhoff-go d y0 k2 (Zero) e n f Q b1 (lt-ls k2 k b1 lt lb) bks hm gen bl pl cu cn rq lq (lt-tr k2 k 6 lt l6)
        (BMLow k2 (lt-ls k2 k (Succ (Succ (Succ (Succ (Succ (Zero)))))) lt l6)) nq))
    ((BKMaps _ _ _ _ dd1 dd2 _ _ _ _ ed1 nd1 fd1 bd1 ed2 nd2 fd2 bd2 _ ms1 ms2 br n1 n2)
      (let ((erased ms) (erased ap)) (mp-app ms1 ms2))
      (MkPlanned d e n f ms (PBirk d x0 h m n0 dd1 dd2 e n f p ed1 nd1 fd1 bd1 ed2 nd2 fd2 bd2 ts ms1 ms2 ms ctu gtu gen pl cu cn lr ce ge gc bk br n1 n2 ap)))))

(def-fns _ $ (erased birkhoff-plan : (erased (Nat) d x0 k m) (erased (List (Nat)) e n f p) (erased (BirkhoffChecks) bks) (erased (Hypermap d e n f) hm)
    (erased (Genus d e n f (Zero)) gen) (erased (Bridgeless d e n f) bl) (erased (AllOrder d e (Succ (Succ (Zero)))) pl)
    (erased (AllOrder d n (Succ (Succ (Succ (Zero))))) cu) (erased (Connected d e n f) cn) (erased (Ring e f x0 p) rg)
    (erased (Length (Nat) (Cons (Nat) x0 p) k) lr) (erased (Lt k 6) l6) (erased (BkMode k m) md) (erased (NonTrivial d e n f (Cons (Nat) x0 p) m) nt)
    -> (erased (Planned d e n f) r))
  (birkhoff-go d x0 k m e n f p 6 l6 bks hm gen bl pl cu cn rg lr l6 md nt))
