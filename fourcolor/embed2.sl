; First-order pieces of not_embed_reducible of embed.v: colourings carried through the patch that embed_patch builds.
; Load after embed.sl, in its chain.

; Each dart of ys is reached from the dart of xs at the same position along f (cface, read as f steps forward).
(def-adts $ (Reach : ((List (Nat)) f xs ys) -> Type)
  enum
  (many ReachNil : (erased (List (Nat)) f) -> (Reach f (Nil (Nat)) (Nil (Nat))))
  (many ReachCons : (erased (List (Nat)) f xs ys) (erased (Nat) x y) (erased (SomePath f (Nil (Nat)) x y) w) (erased (Reach f xs ys) rest)
      -> (Reach f (Cons (Nat) x xs) (Cons (Nat) y ys))))

(def-fns _ $ (erased path-col : (erased (List (Nat)) ks f s xs) (erased (Nat) x y l) (erased (Respects ks f ks) rf) (subterm erased (Path f s x y xs) w)
    (erased (Nth (Nat) ks x l) px) -> (erased (Nth (Nat) ks y l) r))
  (let-match erased w (PathStep _ _ xs1 _ z _ pz _ w1) ((PathHere _ _ _) px))
  (path-col ks f s xs1 z y l rf w1 (respects-nth ks f ks x z l rf pz px)))

(def-fns _ $ (erased reach-resp : (erased (List (Nat)) ks f xs ys L) (erased (Respects ks f ks) rf) (subterm erased (Reach f xs ys) rc)
    (erased (Respects ks xs L) rx) -> (erased (Respects ks ys L) r))
  (let-match erased rc (ReachCons _ xs1 ys1 x y w rc1) ((ReachNil _) (let-match erased rx (RespNil _)) (RespNil ks)))
  (let-match erased rx (RespCons _ _ L1 _ l p rx1))
  (let-match erased w (MkSomePath _ _ ps _ _ pa))
  (RespCons ks ys1 L1 y l (path-col ks f (Nil _) ps x y l rf pa p) (reach-resp ks f xs1 ys1 L1 rf rc1 rx1)))

(def-fns _ $ (erased differ-resp : (erased (List (Nat)) ke ks h A B) (erased (Differ ke ks) df) (subterm erased (Respects ke h A) ra)
    (erased (Respects ks h B) rb) -> (erased (Differ A B) r))
  (let-match erased ra (RespCons _ h1 A1 j a pa ra1) ((RespNil _) (let-match erased rb (RespNil _)) (DifferNil)))
  (let-match erased rb (RespCons _ _ Bt _ b pb rb1))
  (DifferCons A1 Bt a b (differ-nth ke ks j a b df pa pb) (differ-resp ke ks h1 A1 Bt df ra1 rb1)))

; A four-colouring ks of (e, f) gives the four-colouring ks . h of (e2, f2) when h sends the face and edge images of each dart
; of (e2, f2) to darts reached along f from the face and edge images of its image (the colouring kc . embd of not_embed_reducible).
(def-fns _ $ (erased pull-col : (erased (Nat) d d2) (erased (List (Nat)) e f e2 f2 h ks hf2 eh he2 kd) (erased (FourColoring e f ks) c)
    (erased (Length (Nat) e d) le) (erased (Length (Nat) ks d) lk) (erased (Under e d) ue) (erased (Length (Nat) h d2) lh)
    (erased (Respects h f2 hf2) r1) (erased (Reach f h hf2) rc1) (erased (Respects e h eh) r2) (erased (Respects h e2 he2) r3) (erased (Reach f eh he2) rc2)
    (erased (Respects ks h kd) rk) -> (erased (FourColoring e2 f2 kd) r))
  (let-match erased c (MkFourColoring _ _ _ ke rf re df u))
  (let ((erased lkd)) (respects-length ks h kd d2 rk lh))
  (let ((erased A) (erased rA)) (respects-exists ks eh d (respects-under-vals e h eh d r2 ue) lk))
  (MkFourColoring e2 f2 kd A
    (respects-assoc f2 h ks hf2 kd kd d2 r1 (reach-resp ks f h hf2 kd rf rc1 rk) rk lkd lh)
    (respects-assoc e2 h ks he2 kd A d2 r3 (reach-resp ks f eh he2 A rf rc2 rA) rk lkd lh)
    (differ-resp ke ks h A kd df (respects-assoc h e ks eh ke A d r2 rA re (respects-length ks e ke d re le) le) rk)
    (respects-under-vals ks h kd 4 rk u)))

; The last step of not_embed_reducible: a patch of the map from a disk map whose darts embd sends into a configuration map
; (ec, fc) as pull-col asks, with its ring bd sent to erc, a four-colouring kc of the configuration map whose colours on erc
; have the trace et, and a ring trace rot 1 (rev et) of the remainder map on br, give a four-colouring of the map.
(def-fns _ $ (erased embed-color : (erased (Nat) d dd dr dc) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br ec fc kc embd q1 q2 q3 erc lc)
    (erased (List (Col)) cs et et2) (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (FourColoring ec fc kc) c)
    (erased (Length (Nat) ec dc) le) (erased (Length (Nat) kc dc) lk) (erased (Under ec dc) ue) (erased (Length (Nat) embd dd) lh) (erased (Under embd dc) uh)
    (erased (Respects embd fd q1) r1) (erased (Reach fc embd q1) rc1) (erased (Respects ec embd q2) r2) (erased (Respects embd ed q3) r3)
    (erased (Reach fc q2 q3) rc2) (erased (Respects embd bd erc) rb) (erased (Respects kc erc lc) rl) (erased (All2 (Nat) (Col) ColOf lc cs) co)
    (erased (Trace cs et) t) (erased (RotRev et et2) rr) (erased (RingTrace er fr br et2) tr) -> (erased (List (Nat)) ks) (erased (FourColoring e f ks) r))
  (let ((erased kd) (erased rk)) (respects-exists kc embd dc uh lk))
  (let ((erased cd)) (pull-col dc dd ec fc ed fd embd kc q1 q2 q3 kd c le lk ue lh r1 rc1 r2 r3 rc2 rk))
  (let ((erased rlb)) (respects-assoc bd embd kc erc kd lc dd rb rl rk (respects-length kc embd kd dd rk lh) lh))
  (patch-colorable d dd dr e n f ed nd fd er nr fr hd hr bd br et et2 pt (MkRingTrace ed fd bd kd lc cs et cd rlb co t) rr tr))

(def-fns _ $ (erased ecc-rest : (erased (List (Nat)) ins ks) (erased (List (Bond)) g) (erased (Bond) b) (erased (EdgeCC ins ks (Cons (Bond) b g)) ec)
    -> (erased (EdgeCC ins ks g) r))
  (match erased ec _ ((ECIn _ _ _ _ _ _ _ _ _ r) r) ((ECOut _ _ _ _ _ _ _ _ _ _ _ r) r)))

; A contract colouring gives different colours to the ends of the edge link from a dart off ins.
(def-fns _ $ (erased ecc-zip : (erased (List (Nat)) xs ys ins ks) (erased (List (Bond)) g) (erased (Nat) j x y a b) (subterm erased (Zip xs ys g) z)
    (erased (EdgeCC ins ks g) ec) (erased (Nth (Nat) xs j x) px) (erased (Nth (Nat) ys j y) py) (erased (NotIn x ins) o) (erased (Nth (Nat) ks x a) pa)
    (erased (Nth (Nat) ks y b) pb) -> (erased (Apart (Nat) Lt a b) r))
  (let-match erased z (ZipCons xs1 ys1 g1 x0 y0 z1) (absurd (ZipNil) px))
  (match erased px _
    ((NthHere _ _ _)
      (let-match erased py (NthHere _ _ _))
      (let-match erased ec (ECOut _ _ _ _ _ l1 l2 _ p1 p2 ne _) (absurd (ECIn _ _ _ _ _ _ i _ _ _) (apart-irrefl x (notin-in x x ins o i))))
      (let-match erased (nth-fn _ ks x l1 a p1 pa) (Refl _ _))
      (let-match erased (nth-fn _ ks y l2 b p2 pb) (Refl _ _))
      ne)
    ((NthThere _ _ _ j1 _ px1)
      (let-match erased py (NthThere _ _ _ _ _ py1))
      (ecc-zip xs1 ys1 ins ks g1 j1 x y a b z1 (ecc-rest ins ks g1 (MkBond x0 y0) ec) px1 py1 o pa pb))))

(def-fns _ $ (erased diff-cc : (erased (Nat) d) (erased (List (Nat)) e ids ins ks h eh A B) (erased (List (Bond)) ge) (erased (Zip ids e ge) z)
    (erased (Iota d ids) io) (erased (EdgeCC ins ks ge) ec) (erased (Respects e h eh) re) (erased (Respects ks eh A) ra) (subterm erased (Respects ks h B) rb)
    (erased (Disj h ins) dj) (erased (Under h d) uh) -> (erased (Differ A B) r))
  (let-match erased rb (RespCons _ h1 Bt x b pb rb1) ((RespNil _) (let-match erased re (RespNil _)) (let-match erased ra (RespNil _)) (DifferNil)))
  (let-match erased re (RespCons _ _ eh1 _ y py re1))
  (let-match erased ra (RespCons _ _ A1 _ a pa ra1))
  (let-match erased dj (DisjCons _ _ _ o dj1))
  (let-match erased uh (UnderCons _ _ _ lx uh1))
  (DifferCons A1 Bt a b (apart-sym b a (ecc-zip ids e ins ks ge x x y b a z ec (iota-nth d x ids io lx) py o pb pa))
    (diff-cc d e ids ins ks h1 eh1 A1 Bt ge z io ec re1 ra1 rb1 dj1 uh1)))

(def-fns _ $ (erased ccins-fn : (erased (List (Nat)) e cc a b) (subterm erased (InsertE e cc a) ia) (erased (InsertE e cc b) ib) -> (erased (Eq (List (Nat)) a b) r))
  (let-match erased ia (IECons _ cc1 a1 x y px ia1) ((IENil _) (let-match erased ib (IENil _)) (Refl _ a)))
  (let-match erased ib (IECons _ _ b1 _ y2 px2 ib1))
  (let-match erased (nth-fn _ e x y y2 px px2) (Refl _ _))
  (let-match erased (ccins-fn e cc1 a1 b1 ia1 ib1) (Refl _ _))
  (Refl _ a))

; Over the darts xs, h (p x) = q (h x): both sides listed as L.
(def-fns _ $ (erased morph-lists : (erased (List (Nat)) h p q xs) (subterm erased (MorphOff h p q (Nil (Nat)) xs) mo)
    -> (erased (List (Nat)) Pxs Hxs L) (erased (Respects p xs Pxs) rp) (erased (Respects h xs Hxs) rh) (erased (Respects h Pxs L) r1) (erased (Respects q Hxs L) r2))
  (let-match erased mo (MOAt _ _ _ _ xs1 x y z w px hx hy qz mo1)
    ((MONil _ _ _ _) (values (Nil _) (Nil _) (Nil _) (RespNil p) (RespNil h) (RespNil h) (RespNil q)))
    (absurd (MOSkip _ _ _ _ _ _ ib _) ib))
  (let ((erased P1) (erased Hh1) (erased L1) (erased rp1) (erased rh1) (erased r11) (erased r21)) (morph-lists h p q xs1 mo1))
  (values (Cons _ y P1) (Cons _ z Hh1) (Cons _ w L1) (RespCons p xs1 P1 x y px rp1) (RespCons h xs1 Hh1 x z hx rh1) (RespCons h P1 L1 y w hy r11)
    (RespCons q Hh1 L1 z w qz r21)))

; A contract colouring ks of the map whose contract darts ins miss the remainder map gives the four-colouring ks . hr of the
; remainder map (the colouring k . embr of embed_contract).
(def-fns _ $ (erased rem-col : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br cc ks ins)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (CCColoring d e f cc ks) c) (erased (InsertE e cc ins) ie0)
    (erased (Disj hr ins) dj) -> (erased (List (Nat)) kr) (erased (Respects ks hr kr) rkr) (erased (FourColoring er fr kr) r))
  (let ((erased pt2)) pt)
  (let-match erased pt2 (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids idd idr bG bGr h hd2 hr2 io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
  (let-match erased c (MkCCColoring _ _ _ _ _ ins2 ge ie gr rf ec u lks))
  (let-match erased (ccins-fn e cc ins2 ins ie ie0) (Refl _ _))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pme) (erased pmn) (erased pmf)) (hyper-core d e n f h))
  (let ((erased nfr) (erased nri) (erased fri) (erased rnfr) (erased pmer) (erased pmnr) (erased pmfr)) (hyper-core dr er nr fr hr2))
  (let ((erased ler) (erased lnr) (erased lfr)) (hyper-lengths dr er nr fr hr2))
  (let ((erased gf) (erased grf)) (perm-graph d f fi pmf))
  (let ((erased gfr) (erased grfr)) (perm-graph dr fr fri pmfr))
  (let ((erased kr) (erased rkr)) (respects-exists ks hr d uhr lks))
  (let ((erased lkr)) (respects-length ks hr kr dr rkr lhr))
  (let ((erased clr)) (color-const-r d dd dr e n f ed nd fd er nr fr hd hr bd br fi fri ks kr gf gfr pt pmf pmfr grf
    (resp-const d ks f gf (graph-fun d f gf grf) rf lks) lks lhr uhr rkr (graph-fun dr fr gfr grfr)))
  (let ((erased Px) (erased Hx) (erased L) (erased rp) (erased rh) (erased r1) (erased r2)) (morph-lists hr er e idr mer))
  (let-match erased (respects-fn er idr Px er rp (respects-id-right dr idr er ior ler)) (Refl _ _))
  (let-match erased (respects-fn hr idr Hx hr rh (respects-id-right dr idr hr ior lhr)) (Refl _ _))
  (let-match erased gr (MkGraph _ _ ids2 _ io2 le z))
  (let-match erased (iota-fn d ids ids2 io io2) (Refl _ _))
  (let ((erased A) (erased rA)) (respects-exists ks L d (respects-under-vals e hr L d r2 (perm-under d e nf pme)) lks))
  (values kr rkr
    (MkFourColoring er fr kr A
      (const-respects kr idr fr kr gfr (graph-zip dr fr idr gfr grfr ior) clr (respects-id-right dr idr kr ior lkr))
      (respects-assoc er hr ks L kr A dr r1 rA rkr lkr lhr)
      (diff-cc d e ids ins ks hr L A kr ge z io ec r2 rA rkr dj uhr)
      (respects-under-vals ks hr kr 4 rkr u))))

; The remainder map of a patch of a planar plain cubic map, with its ring b0 :: B read from its last dart l (rotr 1), has
; the hypotheses of Kempe_map (embed_closure).
(def-fns _ $ (erased rem-kempe : (erased (Nat) d dd dr b0) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd B)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd (Cons (Nat) b0 B)) pt) (erased (Genus d e n f (Zero)) gen)
    (erased (AllOrder d e (Succ (Succ (Zero)))) pl) (erased (AllOrder d n (Succ (Succ (Succ (Zero))))) cu)
    -> (erased (List (Nat)) init) (erased (Nat) l) (erased (HSnoc (Nat) init l (Cons (Nat) b0 B)) sn) (erased (KempeRing dr er nr fr (Cons (Nat) l init)) kr))
  (let ((erased br)) (Cons (Nat) b0 B))
  (let ((erased pt2)) pt)
  (let-match erased pt2 (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids idd idr bG bGr h hdm hrm io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
  (let ((erased gd) (erased gr)) (patch-parts-planar d dd dr e n f ed nd fd er nr fr hd hr bd br pt gen))
  (let ((erased od) (erased plr)) (edge-order-patch d dd dr (Succ (Succ (Zero))) e n f ed nd fd er nr fr hd hr bd br pt pl idd iod))
  (let ((erased an) (erased onr)) (node-order-patch d dd dr (Succ (Succ (Succ (Zero)))) e n f ed nd fd er nr fr hd hr bd br pt cu idr ior))
  (let ((erased init) (erased l) (erased sn)) (unsnoc-exists (Nat) b0 B))
  (let ((erased R1)) (Cons (Nat) l init))
  (let ((erased ii) (erased j0)) (join-exists init (Nil _)))
  (let-match erased (join-nil-r init ii j0) (Refl _ _))
  (let-match erased (ring-turn nr (Nil _) init (Cons _ l (Nil _)) br R1 idr (join-snoc-r init (Nil _) init (Cons _ l (Nil _)) br l j0 (SnocNil _ l) sn)
      (JoinCons (Nil _) init init l (JoinNil init)) (MkRingOK nr (Nil _) br idr cyr dbr (off-nil br) (oo-qcubic nr br br idr onr (sub-refl br))))
    (MkRingOK _ _ _ _ nc1 ds3 av1 qc1))
  (values init l sn (MkKempeRing dr er nr fr R1 hrm gr plr (MkQuasiCubic dr nr R1 idr ior qc1) nc1 ds3)))
