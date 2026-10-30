; Parts of the embedding construction of embed.v (from a preembedding of a configuration's kernel to an embedding), with
; minimality as data. Load after embed2.sl, in its chain.

; What the lemmas of embed.v read off the configuration map (ec, nc, fc) with ring rc and arities ksc, its kernel as, the
; map (em, nm, fm) with arities ksm, and the preembedding hl.
(def-adts $ (EEnv : ((Nat) dc) ((List (Nat)) ec nc fc ksc rc) ((Nat) dm) ((List (Nat)) em nm fm ksm as hl) -> Type)
  enum
  (many MkEEnv : (erased (Nat) dc) (erased (List (Nat)) ec nc fc ksc rc) (erased (Nat) dm) (erased (List (Nat)) em nm fm ksm as hl)
      (erased (Hypermap dc ec nc fc) hc) (erased (OrderList dc fc ksc) olc) (erased (KernelList dc fc rc as) kl) (erased (Geo dm em nm fm ksm) g)
      (erased (Preembedding ec nc fc ksc em fm ksm as hl) pe) -> (EEnv dc ec nc fc ksc rc dm em nm fm ksm as hl)))

(def-fns _ $ (erased kerall-in : (erased (List (Nat)) f r as) (erased (Nat) x) (subterm erased (KerAll f r as) ka) (erased (In x as) ix)
    -> (erased (Kernel f r x) k))
  (let-match erased ka (KACons _ _ as1 y ky ka1) (absurd (KANil _ _) ix))
  (match erased ix _ ((InHere _ _) ky) ((InThere _ _ _ ix1) (kerall-in f r as1 x ka1 ix1))))

(def-fns _ $ (erased cover-in : (erased (List (Nat)) f r as xs) (erased (Nat) x) (subterm erased (KerCover f r as xs) cv) (erased (In x xs) ix)
    -> (erased (Or (In x as) (Fband f r x)) res))
  (match erased cv _
    (absurd (KvNil _ _ _) ix)
    ((KvIn _ _ _ xs1 y iy cv1) (match erased ix _ ((InHere _ _) (OrL _ _ iy)) ((InThere _ _ _ ix1) (cover-in f r as xs1 x cv1 ix1))))
    ((KvBand _ _ _ xs1 y b cv1) (match erased ix _ ((InHere _ _) (OrR _ _ b)) ((InThere _ _ _ ix1) (cover-in f r as xs1 x cv1 ix1))))))

; A dart on no face of r is listed by as.
(def-fns _ $ (erased ker-in : (erased (Nat) d x) (erased (List (Nat)) f r as) (erased (KernelList d f r as) kl) (erased (Kernel f r x) k) (erased (Lt x d) lx)
    -> (erased (In x as) res))
  (let-match erased kl (MkKernelList _ _ _ _ ids io ka cv))
  (let-match erased (cover-in f r as ids x cv (iota-in d x ids io lx)) (OrL _ _ i) (absurd (OrR _ _ b) (fband-kernel f r x b k)))
  i)

(def-fns _ $ (erased ker-of : (erased (Nat) d x) (erased (List (Nat)) f r as) (erased (KernelList d f r as) kl) (erased (In x as) ix) -> (erased (Kernel f r x) k))
  (let-match erased kl (MkKernelList _ _ _ _ ids io ka cv))
  (kerall-in f r as x ka ix))

; The kernel is closed under face, both ways.
(def-fns _ $ (erased ker-face : (erased (Nat) dc dm x y) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl) (erased (EEnv dc ec nc fc ksc rc dm em nm fm ksm as hl) en)
    (erased (In x as) ix) (erased (Nth (Nat) fc x y) pfx) -> (erased (In y as) res))
  (let-match erased en (MkEEnv _ _ _ _ _ _ _ _ _ _ _ _ _ hc olc kl g pe))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased qe) (erased qn) (erased qf)) (hyper-core dc ec nc fc hc))
  (ker-in dc y fc rc as kl (kernel-face fc rc x y (ker-of dc x fc rc as kl ix) pfx) (perm-val dc x y fc fi qf pfx)))

(def-fns _ $ (erased ker-face-inv : (erased (Nat) dc dm x y) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl) (erased (EEnv dc ec nc fc ksc rc dm em nm fm ksm as hl) en)
    (erased (In y as) iy) (erased (Nth (Nat) fc x y) pfx) -> (erased (In x as) res))
  (let-match erased en (MkEEnv _ _ _ _ _ _ _ _ _ _ _ _ _ hc olc kl g pe))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths dc ec nc fc hc))
  (ker-in dc x fc rc as kl (kernel-face-inv dc x y fc rc lf (ker-of dc y fc rc as kl iy) pfx) (nth-lt-length _ fc x dc y pfx lf)))

(def-fns _ $ (erased peall-of : (erased (List (Nat)) ec nc fc ksc em fm ksm as hl xs) (erased (Nat) x) (subterm erased (PeAll ec nc fc ksc em fm ksm as hl xs) pa)
    (erased (In x xs) ix) -> (erased (PeAt ec nc fc ksc em fm ksm as hl x) r))
  (let-match erased pa (PeCons _ _ _ _ _ _ _ _ _ xs1 y py pa1) (absurd (PeNil _ _ _ _ _ _ _ _ _) ix))
  (match erased ix _ ((InHere _ _) py) ((InThere _ _ _ ix1) (peall-of ec nc fc ksc em fm ksm as hl xs1 x pa1 ix1))))

(def-fns _ $ (erased pe-of : (erased (Nat) dc dm x) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl) (erased (EEnv dc ec nc fc ksc rc dm em nm fm ksm as hl) en)
    (erased (In x as) ix) -> (erased (PeAt ec nc fc ksc em fm ksm as hl x) r))
  (let-match erased en (MkEEnv _ _ _ _ _ _ _ _ _ _ _ _ _ hc olc kl g pe))
  (let-match erased pe (MkPreembedding _ _ _ _ _ _ _ _ _ pa))
  (peall-of ec nc fc ksc em fm ksm as hl as x pa ix))

; At a kernel dart x, h (face x) = face (h x) (hF of embed.v).
(def-fns _ $ (erased h-face : (erased (Nat) dc dm x x1 w) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl) (erased (EEnv dc ec nc fc ksc rc dm em nm fm ksm as hl) en)
    (erased (In x as) ix) (erased (Nth (Nat) fc x x1) px) (erased (Nth (Nat) hl x w) pw) -> (erased (Nat) w1) (erased (Nth (Nat) hl x1 w1) pw1) (erased (Nth (Nat) fm w w1) pfx))
  (let-match erased (pe-of dc dm x ec nc fc ksc rc em nm fm ksm as hl en ix) (MkPeAt _ _ _ _ _ _ _ _ _ _ x2 w2 w12 a y z px2 pw2 pw12 pf2 pa2 pma py cy pz rl))
  (let-match erased (nth-fn _ fc x x1 x2 px px2) (Refl _ _))
  (let-match erased (nth-fn _ hl x w w2 pw pw2) (Refl _ _))
  (values w12 pw12 pf2))

(def-fns _ $ (erased some-cons : (erased (List (Nat)) f) (erased (Nat) x y z) (erased (Nth (Nat) f x y) pfx) (erased (SomePath f (Nil (Nat)) y z) sp)
    -> (erased (SomePath f (Nil (Nat)) x z) r))
  (let-match erased sp (MkSomePath _ _ ps _ _ w))
  (MkSomePath f (Nil _) (Cons _ x ps) x z (PathStep f (Nil _) ps x y z pfx (NotInNil x) w)))

; cface_ac_h: h sends a face path from a kernel dart to a face path of the map.
(def-fns _ $ (erased face-h : (erased (Nat) dc dm x y w) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl s xs)
    (erased (EEnv dc ec nc fc ksc rc dm em nm fm ksm as hl) en) (erased (In x as) ix) (subterm erased (Path fc s x y xs) p) (erased (Nth (Nat) hl x w) pw)
    -> (erased (Nat) v) (erased (Nth (Nat) hl y v) pv) (erased (SomePath fm (Nil (Nat)) w v) sp))
  (let-match erased p (PathStep _ _ xs1 _ z _ pz _ p1) ((PathHere _ _ _) (values w pw (MkSomePath fm (Nil _) (Nil _) w w (PathHere fm (Nil _) w)))))
  (let ((erased w1) (erased pw1) (erased pfx)) (h-face dc dm x z w ec nc fc ksc rc em nm fm ksm as hl en ix pz pw))
  (let ((erased v) (erased pv) (erased sp)) (face-h dc dm z y w1 ec nc fc ksc rc em nm fm ksm as hl s xs1 en (ker-face dc dm x z ec nc fc ksc rc em nm fm ksm as hl en ix pz) p1 pw1))
  (values v pv (some-cons fm w w1 v pfx sp)))

; cface_h_ac: a face path of the map from h x, x in the kernel, follows a face path from x.
(def-fns _ $ (erased h-face-back : (erased (Nat) dc dm x w u) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl s us)
    (erased (EEnv dc ec nc fc ksc rc dm em nm fm ksm as hl) en) (erased (In x as) ix) (erased (Nth (Nat) hl x w) pw) (subterm erased (Path fm s w u us) p)
    -> (erased (Nat) y) (erased (SomePath fc (Nil (Nat)) x y) sp) (erased (Nth (Nat) hl y u) pu))
  (let-match erased p (PathStep _ _ us1 _ w2 _ pw2 _ p1) ((PathHere _ _ _) (values x (MkSomePath fc (Nil _) (Nil _) x x (PathHere fc (Nil _) x)) pw)))
  (let ((erased en2)) en)
  (let-match erased en2 (MkEEnv _ _ _ _ _ _ _ _ _ _ _ _ _ hc olc kl g pe))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths dc ec nc fc hc))
  (let ((erased xe) (erased xn) (erased x1) (erased pxe) (erased lxe) (erased pxn) (erased lxn) (erased px1) (erased lx1))
    (hyper-step dc x ec nc fc hc (kernel-lt dc x fc rc lf (ker-of dc x fc rc as kl ix))))
  (let ((erased w1) (erased pw1) (erased pfx)) (h-face dc dm x x1 w ec nc fc ksc rc em nm fm ksm as hl en ix px1 pw))
  (let-match erased (nth-fn _ fm w w1 w2 pfx pw2) (Refl _ _))
  (let ((erased y) (erased sp) (erased pu))
    (h-face-back dc dm x1 w1 u ec nc fc ksc rc em nm fm ksm as hl s us1 en (ker-face dc dm x x1 ec nc fc ksc rc em nm fm ksm as hl en ix px1) pw1 p1))
  (values y (some-cons fc x x1 y px1 sp) pu))

(def-fns _ $ (erased iter-h : (erased (Nat) dc dm k x y w) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl) (erased (EEnv dc ec nc fc ksc rc dm em nm fm ksm as hl) en)
    (erased (In x as) ix) (subterm erased (Iter fc k x y) it) (erased (Nth (Nat) hl x w) pw) -> (erased (Nat) v) (erased (Nth (Nat) hl y v) pv) (erased (Iter fm k w v) itm))
  (let-match erased it (ItS _ k1 _ z _ pz it1) ((ItZ _ _) (values w pw (ItZ fm w))))
  (let ((erased w1) (erased pw1) (erased pfx)) (h-face dc dm x z w ec nc fc ksc rc em nm fm ksm as hl en ix pz pw))
  (let ((erased v) (erased pv) (erased itm)) (iter-h dc dm k1 z y w1 ec nc fc ksc rc em nm fm ksm as hl en (ker-face dc dm x z ec nc fc ksc rc em nm fm ksm as hl en ix pz) it1 pw1))
  (values v pv (ItS fm k1 w w1 v pfx itm)))

; An iterate of a dart of order a is one of fewer than a steps.
(def-fns _ $ (erased iter-below : (erased (List (Nat)) f) (erased (Nat) a x y) (subterm erased (Nat) k) (erased (Order f x a) o) (erased (Iter f k x y) it)
    -> (erased (Nat) r) (erased (Lt r a) lr) (erased (Iter f r x y) it2))
  (let ((erased o2)) o)
  (let-match erased o2 (MkOrder _ xs _ x1 a1 px w l))
  (let-match erased k (Succ k1) ((Zero) (let-match erased it (ItZ _ _)) (values (Zero) (LtZ a1) (ItZ f x))))
  (let ((erased u) (erased it1) (erased pu)) (iter-last f k1 x y it))
  (let ((erased r1) (erased lr1) (erased it3)) (iter-below f a x u k1 o it1))
  (let ((erased it4)) (iter-snoc f r1 x u y it3 pu))
  (let-match erased (nat-cmp (Succ r1) a) (CEq _ _ _) ((CLt _ _ _ _ lt) (values (Succ r1) lt it4)) (absurd (CGt _ _ _ _ gt) (lt-asym r1 a lr1 gt)))
  (let-match erased (iter-fn f a x y x it4 (order-iter f x a o)) (Refl _ _))
  (values (Zero) (LtZ a1) (ItZ f x)))

; cface_inj_embed: two kernel darts on one face with one image are one dart.
(def-fns _ $ (erased cface-inj : (erased (Nat) dc dm x y w) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl s xs)
    (erased (EEnv dc ec nc fc ksc rc dm em nm fm ksm as hl) en) (erased (In x as) ix) (erased (Path fc s x y xs) p) (erased (Nth (Nat) hl x w) pw)
    (erased (Nth (Nat) hl y w) pw2) -> (erased (Eq (Nat) x y) r))
  (let ((erased en2)) en)
  (let-match erased en2 (MkEEnv _ _ _ _ _ _ _ _ _ _ _ _ _ hc olc kl g pe))
  (let-match erased g (MkGeo _ _ _ _ _ hm pem cnm olm pam))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths dc ec nc fc hc))
  (let ((erased lem) (erased lnm) (erased lfm)) (hyper-lengths dm em nm fm hm))
  (let-match erased (pe-of dc dm x ec nc fc ksc rc em nm fm ksm as hl en ix) (MkPeAt _ _ _ _ _ _ _ _ _ _ x2 w2 w12 a y0 z0 px2 pw0 pw12 pf2 pa2 pma py cy pz rl))
  (let-match erased (nth-fn _ hl x w w2 pw pw0) (Refl _ _))
  (let ((erased a0) (erased pa0) (erased oc)) (arity-at dc x fc ksc olc (kernel-lt dc x fc rc lf (ker-of dc x fc rc as kl ix))))
  (let-match erased (nth-fn _ ksc x a a0 pa2 pa0) (Refl _ _))
  (let ((erased am) (erased pam0) (erased om)) (arity-at dm w fm ksm olm (nth-lt-length _ fm w dm w12 pf2 lfm)))
  (let-match erased (nth-fn _ ksm w a am pma pam0) (Refl _ _))
  (let ((erased k) (erased lk)) (length-exists _ xs))
  (let ((erased r0) (erased lr) (erased itc)) (iter-below fc a x y k oc (path-iter fc s xs x y k p lk)))
  (let ((erased v) (erased pv) (erased itm)) (iter-h dc dm r0 x y w ec nc fc ksc rc em nm fm ksm as hl en ix itc pw))
  (let-match erased (nth-fn _ hl y v w pv pw2) (Refl _ _))
  (match erased r0 _
    ((Zero) (let-match erased itc (ItZ _ _)) (Refl _ x))
    (absurd (Succ r1)
      (let-match erased om (MkOrder _ xs3 _ w3 a3 pw3 wm l3))
      (let-match erased itm (ItS _ _ _ w4 _ pw4 itm1))
      (let-match erased (nth-fn _ fm w w3 w4 pw3 pw4) (Refl _ _))
      (let-match erased lr (LtS _ _ lr1))
      (path-iter-short fm xs3 w3 w a3 r1 wm l3 itm1 lr1))))
