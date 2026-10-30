; not_embed_reducible of embed.v with minimality as data: embed.sl's NotEmbed CRX cfs, from embed5.sl's FullRed and
; PatchOpen and three open steps taken as hypotheses (GcFun, EmbedValid, ContractStep). Load after embed5.sl, with
; iealias.sl loaded after red/cfred.sl. That these statements match Coq's has been checked only by reading.

(def-fns _ $ (erased ie-conv : (erased (List (Nat)) e cc ie) (subterm erased (CInsertE e cc ie) p) -> (erased (InsertE e cc ie) r))
  (let-match erased p (CIECons _ cc1 ie1 y z pz p1) ((CIENil _) (IENil e)))
  (IECons e cc1 ie1 y z pz (ie-conv e cc1 ie1 p1)))

(def-fns _ $ (erased under-nth : (erased (List (Nat)) ks) (erased (Nat) b i k) (subterm erased (Under ks b) u) (erased (Nth (Nat) ks i k) p) -> (erased (Lt k b) r))
  (let-match erased u (UnderCons ks1 k0 _ l u1) (absurd (UnderNil _) p))
  (match erased p _ ((NthHere _ _ _) l) ((NthThere _ _ _ i1 _ p1) (under-nth ks1 b i1 k u1 p1))))

(def-fns _ $ (erased ie-under : (erased (Nat) d) (erased (List (Nat)) e cc ie) (subterm erased (InsertE e cc ie) p) (erased (Length (Nat) e d) le)
    (erased (Under e d) ue) -> (erased (Under cc d) u1) (erased (Under ie d) u2))
  (let-match erased p (IECons _ cc1 ie1 y z pz p1) ((IENil _) (values (UnderNil d) (UnderNil d))))
  (let ((erased u1) (erased u2)) (ie-under d e cc1 ie1 p1 le ue))
  (let ((erased ly)) (nth-lt-length _ e y d z pz le))
  (values (UnderCons cc1 y d ly u1) (UnderCons (Cons _ z ie1) y d ly (UnderCons ie1 z d (under-nth e d y z ue pz) u2))))

(def-fns _ $ (erased inserte-exists : (erased (List (Nat)) e) (erased (Nat) d) (subterm erased (List (Nat)) cc) (erased (Under cc d) u) (erased (Length (Nat) e d) le)
    -> (erased (List (Nat)) ins) (erased (InsertE e cc ins) r))
  (let-match erased u (UnderCons cc1 y _ ly u1) ((UnderNil _) (values (Nil _) (IENil e))))
  (let ((erased z) (erased pz)) (nth-exists _ e d y le ly))
  (let ((erased ins) (erased r)) (inserte-exists e d cc1 u1 le))
  (values (Cons _ y (Cons _ z ins)) (IECons e cc1 ins y z pz r)))

(def-fns _ $ (erased reach-at : (erased (List (Nat)) f xs ys) (erased (Nat) i x y) (subterm erased (Reach f xs ys) rc) (erased (Nth (Nat) xs i x) px)
    (erased (Nth (Nat) ys i y) py) -> (erased (SomePath f (Nil (Nat)) x y) r))
  (let-match erased rc (ReachCons _ xs1 ys1 x0 y0 w rc1) (absurd (ReachNil _) px))
  (match erased px _
    ((NthHere _ _ _) (let-match erased py (NthHere _ _ _)) w)
    ((NthThere _ _ _ i1 _ px1) (let-match erased py (NthThere _ _ _ _ _ py1)) (reach-at f xs1 ys1 i1 x y rc1 px1 py1))))

(def-fns _ $ (erased reach-flip : (erased (Nat) d) (erased (List (Nat)) f fi xs ys) (erased (HPerm d f fi) pf) (erased (Under xs d) u)
    (subterm erased (Reach f xs ys) rc) -> (erased (Reach f ys xs) r))
  (let-match erased rc (ReachCons _ xs1 ys1 x y w rc1) ((ReachNil _) (ReachNil f)))
  (let-match erased u (UnderCons _ _ _ lx u1))
  (ReachCons f ys1 xs1 y x (some-sym d x y f fi pf w lx) (reach-flip d f fi xs1 ys1 pf u1 rc1)))

; With h1 sending each face step along fm (Reach fm h1 h1f), A = h1 xs and B = h1 (f xs) are paired along fm.
(def-fns _ $ (erased reach-map : (erased (List (Nat)) fm f h1 h1f xs ys A B) (subterm erased (Respects h1 xs A) ra) (erased (Respects f xs ys) ry)
    (erased (Respects h1 ys B) rb) (erased (Respects h1 f h1f) rf) (erased (Reach fm h1 h1f) rc) -> (erased (Reach fm A B) r))
  (let-match erased ra (RespCons _ xs1 A1 x u pu ra1) ((RespNil _) (let-match erased ry (RespNil _)) (let-match erased rb (RespNil _)) (ReachNil fm)))
  (let-match erased ry (RespCons _ _ ys1 _ y py ry1))
  (let-match erased rb (RespCons _ _ B1 _ v pv rb1))
  (ReachCons fm A1 B1 u v (reach-at fm h1 h1f x u v rc pu (respects-at h1 f h1f x y v rf py pv)) (reach-map fm f h1 h1f xs1 ys1 A1 B1 ra1 ry1 rb1 rf rc)))

(def-fns _ $ (erased reach-unsnoc : (erased (List (Nat)) f X0 X Y0 Y) (erased (Nat) x y) (subterm erased (HSnoc (Nat) X0 x X) sx) (erased (HSnoc (Nat) Y0 y Y) sy)
    (erased (Reach f X Y) rc) -> (erased (Reach f X0 Y0) r0) (erased (SomePath f (Nil (Nat)) x y) w))
  (match erased sx _
    ((SnocNil _ _)
      (let-match erased rc (ReachCons _ _ Y1 _ y1 w1 rc1))
      (let-match erased rc1 (ReachNil _))
      (let-match erased sy (SnocNil _ _) (absurd (SnocCons _ _ _ _ _ s1) s1))
      (values (ReachNil f) w1))
    ((SnocCons _ x0 _ X1 Xs s1)
      (let-match erased rc (ReachCons _ _ Y1 _ y0 w0 rc1))
      (let-match erased sy (SnocCons _ _ _ Y01 _ s2)
        (absurd (SnocNil _ _) (match erased s1 _ (absurd (SnocNil _ _) rc1) (absurd (SnocCons _ _ _ _ _ _) rc1))))
      (let ((erased r0) (erased w)) (reach-unsnoc f X1 Xs Y01 Y1 x y s1 s2 rc1))
      (values (ReachCons f X1 Y01 x0 y0 w0 r0) w))))

; k constant on faces takes the colours L of f xs on xs.
(def-fns _ $ (erased resp-face-back : (erased (List (Nat)) k f xs ys L) (subterm erased (Respects f xs ys) ry) (erased (Respects k ys L) rl)
    (erased (Respects k f k) rf) -> (erased (Respects k xs L) r))
  (let-match erased ry (RespCons _ xs1 ys1 x y py ry1) ((RespNil _) (let-match erased rl (RespNil _)) (RespNil k)))
  (let-match erased rl (RespCons _ _ L1 _ v pv rl1))
  (RespCons k xs1 L1 x v (respects-at k f k x y v rf py pv) (resp-face-back k f xs1 ys1 L1 ry1 rl1 rf)))

(def-fns _ $ (erased resp-comp : (erased (List (Nat)) h g hg xs ys zs) (erased (Respects h g hg) rh) (subterm erased (Respects g xs ys) rg)
    (erased (Respects hg xs zs) rz) -> (erased (Respects h ys zs) r))
  (let-match erased rg (RespCons _ xs1 ys1 u x pu rg1) ((RespNil _) (let-match erased rz (RespNil _)) (RespNil h)))
  (let-match erased rz (RespCons _ _ zs1 _ y py rz1))
  (RespCons h ys1 zs1 x y (respects-nth h g hg u x y rh pu py) (resp-comp h g hg xs1 ys1 zs1 rh rg1 rz1)))

; n z = x gives f (e x) = z.
(def-fns _ $ (erased fe-step : (erased (Nat) d x z) (erased (List (Nat)) e n f fe) (erased (Respects f e fe) rfe) (erased (HPerm d n fe) pm)
    (erased (Length (Nat) e d) le) (erased (Nth (Nat) n z x) pz) -> (erased (Nat) ex) (erased (Nth (Nat) e x ex) pex) (erased (Nth (Nat) f ex z) r))
  (let ((erased ex) (erased pex)) (nth-exists _ e d x le (perm-val d z x n fe pm pz)))
  (values ex pex (respects-nth f e fe x ex z rfe pex (perm-inv d z x n fe pm pz))))

; The ring x :: p of cpring, read backwards along n, with n t = y for its last dart y: f sends its edge images es to the
; ring rotated by one, p followed by t.
(def-fns _ $ (erased ring-fe : (erased (Nat) d x y t) (erased (List (Nat)) e n f fe p) (erased (Respects f e fe) rfe) (erased (HPerm d n fe) pm)
    (erased (Length (Nat) e d) le) (subterm erased (CRPath n x p y) rp) (erased (Nth (Nat) n t y) pt)
    -> (erased (List (Nat)) es rs) (erased (Respects e (Cons (Nat) x p) es) r1) (erased (HSnoc (Nat) p t rs) sn) (erased (Respects f es rs) r2))
  (match erased rp _
    ((CRPNil _ _)
      (let ((erased ex) (erased pex) (erased pf)) (fe-step d x t e n f fe rfe pm le pt))
      (values (Cons _ ex (Nil _)) (Cons _ t (Nil _)) (RespCons e (Nil _) (Nil _) x ex pex (RespNil e)) (SnocNil _ t) (RespCons f (Nil _) (Nil _) ex t pf (RespNil f))))
    ((CRPCons _ p1 _ z _ pz rp1)
      (let ((erased ex) (erased pex) (erased pf)) (fe-step d x z e n f fe rfe pm le pz))
      (let ((erased es) (erased rs) (erased r1) (erased sn) (erased r2)) (ring-fe d z y t e n f fe p1 rfe pm le rp1 pt))
      (values (Cons _ ex es) (Cons _ z rs) (RespCons e (Cons _ z p1) es x ex pex r1) (SnocCons _ z t p1 rs sn) (RespCons f es rs ex z pf r2)))))

(def-fns _ $ (erased ieither-at : (erased (List (Nat)) r s xs) (erased (Nat) x) (subterm erased (InEither r s xs) ie) (erased (In x xs) ix)
    -> (erased (HOr (In x r) (In x s)) res))
  (let-match erased ie (IeCons _ _ xs1 y p ie1) (absurd (IeNil _ _) ix))
  (match erased ix _ ((InHere _ _) p) ((InThere _ _ _ ix1) (ieither-at r s xs1 x ie1 ix1))))

; ins = insertE (map h1 cc) is map h1 (insertE cc).
(def-fns _ $ (erased ins-map : (erased (Nat) dc) (erased (List (Nat)) ec em h1 ids cc ie ccr ins) (subterm erased (InsertE ec cc ie) iec) (erased (Respects h1 cc ccr) rcc)
    (erased (InsertE em ccr ins) iem) (erased (MorphOff h1 ec em (Nil (Nat)) ids) me) (erased (Iota dc ids) io) (erased (Length (Nat) ec dc) le)
    -> (erased (Respects h1 ie ins) r))
  (let-match erased iec (IECons _ cc1 ie1 y z pz iec1) ((IENil _) (let-match erased rcc (RespNil _)) (let-match erased iem (IENil _)) (RespNil h1)))
  (let-match erased rcc (RespCons _ _ ccr1 _ u pu rcc1))
  (let-match erased iem (IECons _ _ ins1 _ v pv iem1))
  (let-match erased (morph-at h1 ec em (Nil _) ids y me (iota-in dc y ids io (nth-lt-length _ ec y dc z pz le))) (InR _ _ ma) (absurd (InL _ _ ib) ib))
  (let-match erased ma (MkMorphAt _ _ _ _ z2 u2 w2 pz2 pu2 pw2 pv2))
  (let-match erased (nth-fn _ ec y z z2 pz pz2) (Refl _ _))
  (let-match erased (nth-fn _ h1 y u u2 pu pu2) (Refl _ _))
  (let-match erased (nth-fn _ em u v w2 pv pv2) (Refl _ _))
  (RespCons h1 (Cons _ z ie1) (Cons _ v ins1) y u pu (RespCons h1 ie1 ins1 z v pw2 (ins-map dc ec em h1 ids cc1 ie1 ccr1 ins1 iec1 rcc1 iem1 me io le))))

; A dart of ie = insertE cc is not in erc = rev (map edge rc).
(def-fns _ $ (erased ie-off-erc : (erased (Nat) dc dm x) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl cc ie erc0 erc)
    (erased (EEnv dc ec nc fc ksc rc dm em nm fm ksm as hl) en) (erased (GcOK dc ec nc rc as) ok) (erased (InsertE ec cc ie) iec) (erased (Under cc dc) uc)
    (erased (Disj ie rc) dj) (erased (Length (Nat) ec dc) le) (erased (Respects ec rc erc0) re) (erased (RevApp (Nat) erc0 (Nil (Nat)) erc) rv)
    (erased (In x ie) ix) -> (erased (NotIn x erc) r))
  (match erased (in-dec x erc) _
    ((OrR _ _ o) o)
    (absurd (OrL _ _ i)
      (let ((erased i0)) (revapp-in erc (Nil _) erc0 x (revapp-flip (Nat) erc0 (Nil _) erc erc0 rv (RANil _ erc0)) (OrL _ _ i)))
      (let ((erased r) (erased ir) (erased pr)) (respects-in ec rc erc0 x re i0))
      (let-match erased (gc-at dc r ec nc rc as ok (nth-lt-length _ ec r dc x pr le)) (MkGcAt _ _ _ _ _ ex nx pex pxe pnx rs ep cl cs))
      (let-match erased (nth-fn _ ec r x ex pr pex) (Refl _ _))
      (in-notin r rc ir (disj-notin r ie rc dj (gc-img dc dm x r ec nc fc ksc rc em nm fm ksm as hl cc ie en ok iec uc ix pxe))))))

; A dart of ins is the image under hd of a disk dart off bd, so it is not in hr.
(def-fns _ $ (erased ins-off : (erased (Nat) dc dm dd dr y) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl cc ie erc0 erc h1 ins idc
    ed nd fd er nr fr hd hr bd br embd)
    (erased (EEnv dc ec nc fc ksc rc dm em nm fm ksm as hl) en) (erased (GcOK dc ec nc rc as) ok) (erased (InsertE ec cc ie) iec) (erased (Under cc dc) uc)
    (erased (Under ie dc) uie) (erased (Disj ie rc) dj) (erased (Length (Nat) ec dc) le) (erased (Respects ec rc erc0) re)
    (erased (RevApp (Nat) erc0 (Nil (Nat)) erc) rv) (erased (Respects h1 ie ins) rie) (erased (Under h1 dm) uh) (erased (Iota dc idc) ioc)
    (erased (InEither rc embd idc) cv) (erased (Respects embd bd erc) reb) (erased (Respects h1 embd hd) rh)
    (erased (Patch dm dd dr em nm fm ed nd fd er nr fr hd hr bd br) pt) (erased (In y ins) iy) -> (erased (NotIn y hr) r))
  (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids idd idr bG bGr h hd2 hr2 io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rvp pp med mnd mer mnr))
  (let ((erased x) (erased ix) (erased px)) (respects-in h1 ie ins y rie iy))
  (let ((erased oe)) (ie-off-erc dc dm x ec nc fc ksc rc em nm fm ksm as hl cc ie erc0 erc en ok iec uc dj le re rv ix))
  (let ((erased j) (erased pj)) (in-nth x ie ix))
  (let-match erased (ieither-at rc embd idc x cv (iota-in dc x idc ioc (under-nth ie dc j x uie pj))) (OrR _ _ ie2)
    (absurd (OrL _ _ ir) (in-notin x rc ir (disj-notin x ie rc dj ix))))
  (let ((erased u) (erased pu)) (in-nth x embd ie2))
  (let ((erased ou))
    (match erased (in-dec u bd) (((NotIn u bd) o))
      ((OrR _ _ o) o)
      (absurd (OrL _ _ iu)
        (let ((erased x2) (erased p2) (erased i2)) (respects-val embd bd erc u reb iu))
        (let-match erased (nth-fn _ embd u x x2 pu p2) (Refl _ _))
        (in-notin x erc i2 oe))))
  (let ((erased phu)) (respects-at h1 embd hd u x y rh pu px))
  (match erased (parts-at hd hr bd ids y pp (iota-in dm y ids io (under-nth h1 dm x y uh px))) _
    ((PtDisk _ _ _ _ xd px2 out outr) outr)
    (absurd (PtRing _ _ _ _ xd xr px2 pin pr) (let-match erased (distinct-nth hd xd u y dhd px2 phu) (Refl _ _)) (in-notin u bd pin ou))
    (absurd (PtRest _ _ _ _ xr pr outd) (in-notin y hd (nth-in hd u y phu) outd))))

(def-fns _ $ (erased ins-hr : (erased (Nat) dc dm dd dr) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl cc ie erc0 erc h1 ins idc
    ed nd fd er nr fr hd hr bd br embd)
    (erased (EEnv dc ec nc fc ksc rc dm em nm fm ksm as hl) en) (erased (GcOK dc ec nc rc as) ok) (erased (InsertE ec cc ie) iec) (erased (Under cc dc) uc)
    (erased (Under ie dc) uie) (erased (Disj ie rc) dj) (erased (Length (Nat) ec dc) le) (erased (Respects ec rc erc0) re)
    (erased (RevApp (Nat) erc0 (Nil (Nat)) erc) rv) (erased (Respects h1 ie ins) rie) (erased (Under h1 dm) uh) (erased (Iota dc idc) ioc)
    (erased (InEither rc embd idc) cv) (erased (Respects embd bd erc) reb) (erased (Respects h1 embd hd) rh)
    (erased (Patch dm dd dr em nm fm ed nd fd er nr fr hd hr bd br) pt) (subterm erased (List (Nat)) zs) (erased (WSub zs ins) sb) -> (erased (Disj zs hr) r))
  (let-match erased sb (HSubCons y zs1 _ iy sb1) ((HSubNil _) (DisjNil hr)))
  (DisjCons y zs1 hr
    (ins-off dc dm dd dr y ec nc fc ksc rc em nm fm ksm as hl cc ie erc0 erc h1 ins idc ed nd fd er nr fr hd hr bd br embd en ok iec uc uie dj le re rv rie uh ioc
      cv reb rh pt iy)
    (ins-hr dc dm dd dr ec nc fc ksc rc em nm fm ksm as hl cc ie erc0 erc h1 ins idc ed nd fd er nr fr hd hr bd br embd en ok iec uc uie dj le re rv rie uh ioc
      cv reb rh pt zs1 sb1)))

; kempemap.sl's kempe-closed at a level L the caller gives, after KCA.
(def-lvl KCA)

(def-fns _ $ (erased kclosed-at : (erased (Level) L) (erased (Predates (Level) KCA L) pl) (erased (Nat) d) (erased (List (Nat)) e n f r) (erased (KempeRing d e n f r) kr)
    -> (erased (KClosed L (MkPred (RArgs) (MkRArgs d e n f r) RTP) (MkRel (RArgs) (MkRArgs d e n f r) RKP)) cl))
  (let ((erased a)) (MkRArgs d e n f r))
  (let ((erased P2)) (MkPred (RArgs) a RTP))
  (let ((erased R)) (MkRel (RArgs) a RKP))
  (let-match erased kr (MkKempeRing _ _ _ _ _ h g pl2 qc nc ds))
  (let ((erased q1) (erased q2) (erased q3))
    (values (predates-trans (prove-predates (level-of ring-trace-perm) KCA) pl) (predates-trans (prove-predates (level-of kempe-map) KCA) pl)
      (predates-trans (prove-predates (level-of kempe-map-sound) KCA) pl)))
  (def-fns L
    ((erased cp : (erased (List (Col)) ct ct2) (erased (Perm) gp) (erased (IsPerm gp) ip) (erased (PermT gp ct ct2) pt) (erased (Holds P2 ct) p)
        -> (erased (Holds P2 ct2) q))
      (let-match erased p (MkHolds _ _ _ _ h0))
      (let-match erased h0 (MkRTP _ _ _ _ _ _ rt))
      (MkHolds (RArgs) a RTP ct2 (MkRTP d e n f r ct2 (ring-trace-perm (predates q1) e f r ct ct2 gp ip pt rt))))
    ((erased cg : (erased (List (Col)) ct) (erased (Holds P2 ct) p) -> (erased (List (Gsym)) w) (erased (MatchG (BS0) ct w) m) (erased (HoldsR R ct w) q))
      (let-match erased p (MkHolds _ _ _ _ h0))
      (let-match erased h0 (MkRTP _ _ _ _ _ _ rt))
      (let ((erased w) (erased m) (erased kg)) (kempe-map (predates q2) d e n f r ct h g pl2 qc nc ds rt))
      (values w m (MkHoldsR (RArgs) a RKP ct w (MkRKP d e n f r ct w kg))))
    ((erased cm : (erased (List (Col)) ct ct2) (erased (List (Gsym)) w) (erased (HoldsR R ct w) q) (erased (MatchG (BS0) ct2 w) m) -> (erased (Holds P2 ct2) p))
      (let-match erased q (MkHoldsR _ _ _ _ _ h0))
      (let-match erased h0 (MkRKP _ _ _ _ _ _ _ kg))
      (MkHolds (RArgs) a RTP ct2 (MkRTP d e n f r ct2 (kempe-map-sound (predates q3) d e n f r w ct2 kg m)))))
  (MkKClosed L P2 R cp cg cm))

; The last step of not_embed_reducible: a ring trace et of the configuration map on its ring a :: p, of which f sends the
; edge images erc0 to the ring rotated by one, and a ring trace et of the remainder map on its ring l :: init, the ring br =
; init ++ [l] rotated by one, give a four-colouring of the map through embed2.sl's embed-color.
(def-fns _ $ (erased ne-finish : (erased (Nat) dm dd dr dc a l) (erased (List (Nat)) em nm fm ed nd fd er nr fr hd hr bd br ec nc fc p embd q1 q2 q3 erc0 erc rs init)
    (erased (List (Col)) et) (erased (Patch dm dd dr em nm fm ed nd fd er nr fr hd hr bd br) pt) (erased (Hypermap dc ec nc fc) hc)
    (erased (Length (Nat) embd dd) lem) (erased (Under embd dc) uem) (erased (Respects embd fd q1) r1) (erased (Reach fc embd q1) rc1) (erased (Respects ec embd q2) r2)
    (erased (Respects embd ed q3) r3) (erased (Reach fc q2 q3) rc2) (erased (Respects embd bd erc) reb) (erased (RevApp (Nat) erc0 (Nil (Nat)) erc) rv)
    (erased (Respects fc erc0 rs) rfs) (erased (HSnoc (Nat) p a rs) snp) (erased (HSnoc (Nat) init l br) sn)
    (erased (RingTrace ec fc (Cons (Nat) a p) et) tc) (erased (RingTrace er fr (Cons (Nat) l init) et) tr)
    -> (erased (List (Nat)) ks) (erased (FourColoring em fm ks) r))
  (let-match erased tc (MkRingTrace _ _ _ kc lc cs _ col rl co t))
  (let-match erased rl (RespCons _ _ lp _ la pla rlp))
  (let-match erased co (All2Cons _ _ _ _ c0 _ cs1 pc0 co1))
  (let ((erased col2)) col)
  (let-match erased col2 (MkFourColoring _ _ _ ke rf re df u))
  (let ((erased lcr) (erased slc)) (snoc-exists (Nat) lp la))
  (let ((erased rlr)) (respects-snoc kc p rs lp lcr a la rlp pla snp slc))
  (let ((erased csr) (erased scs) (erased cor)) (cols-snoc lp lcr cs1 la c0 co1 slc pc0))
  (let ((erased s) (erased E) (erased et3) (erased eq) (erased se) (erased t3)) (trace-rot c0 cs1 csr et t scs))
  (let ((erased lce) (erased rvl) (erased rle)) (respects-revapp kc erc0 (Nil _) erc lcr (Nil _) (resp-face-back kc fc erc0 rs lcr rfs rlr rf) (RespNil kc) rv))
  (let ((erased cse) (erased rvc) (erased coe)) (all2-revapp (Nat) (Col) ColOf lcr (Nil _) lce csr (Nil _) cor (All2Nil _ _ ColOf) rvl))
  (let ((erased w) (erased rrw)) (rotrev-exists et3))
  (let ((erased s2) (erased E2) (erased et4) (erased eq2) (erased se2) (erased tr4)) (rt-rot er fr init br l et sn tr))
  (let-match erased eq (Refl _ _))
  (let-match erased eq2 (Refl _ _))
  (let-match erased (hsnoc-fn (Col) E et3 et4 s se se2) (Refl _ _))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths dc ec nc fc hc))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pme) (erased pmn) (erased pmf)) (hyper-core dc ec nc fc hc))
  (embed-color dm dd dr dc em nm fm ed nd fd er nr fr hd hr bd br ec fc kc embd q1 q2 q3 erc lce cse w et3 pt col le (respects-length kc fc kc dc rf lf)
    (perm-under dc ec nf pme) lem uem r1 rc1 r2 r3 rc2 reb rle coe (trace-rev csr cse et3 w t3 rvc rrw) (rotrev-sym et3 w rrw) tr4))
