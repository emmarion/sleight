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

; The identities of a plain cubic map that the case analyses below use: e (e w) = w, n (f (e v)) = v and f (e z) = n (n z).
(def-fns _ $ (erased gm-ee : (erased (Nat) dm w a) (erased (List (Nat)) em nm fm ksm) (erased (Geo dm em nm fm ksm) g) (erased (Nth (Nat) em w a) pa)
    -> (erased (Nth (Nat) em a w) r))
  (let-match erased g (MkGeo _ _ _ _ _ hm pem cnm olm pam))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths dm em nm fm hm))
  (let ((erased r) (erased _)) (plain-eq dm w a em pem (nth-lt-length _ em w dm a pa le) pa))
  r)

(def-fns _ $ (erased gm-nfe : (erased (Nat) dm v a u) (erased (List (Nat)) em nm fm ksm) (erased (Geo dm em nm fm ksm) g) (erased (Nth (Nat) em v a) pa)
    (erased (Nth (Nat) fm a u) pu) -> (erased (Nth (Nat) nm u v) r))
  (let-match erased g (MkGeo _ _ _ _ _ hm pem cnm olm pam))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased qe) (erased qn) (erased qf)) (hyper-core dm em nm fm hm))
  (let ((erased t) (erased pt) (erased lt)) (perm-nth dm u nm ni qn (perm-val dm a u fm fi qf pu)))
  (let ((erased a2) (erased pa2) (erased la2)) (perm-nth dm t em nf qe lt))
  (let-match erased (perm-inj dm a a2 u fm fi qf pu (hyper-third dm a2 t u em nm fm hm pa2 pt)) (Refl _ _))
  (let-match erased (perm-inj dm v t a em nf qe pa pa2) (Refl _ _))
  pt)

(def-fns _ $ (erased gm-fe : (erased (Nat) dm z a b) (erased (List (Nat)) em nm fm ksm) (erased (Geo dm em nm fm ksm) g) (erased (Nth (Nat) em z a) pa)
    (erased (Nth (Nat) fm a b) pb) -> (erased (Nat) z1) (erased (Nth (Nat) nm z z1) p1) (erased (Nth (Nat) nm z1 b) p2))
  (let-match erased g (MkGeo _ _ _ _ _ hm pem cnm olm pam))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased qe) (erased qn) (erased qf)) (hyper-core dm em nm fm hm))
  (let ((erased lz)) (perm-val dm a z em nf qe (gm-ee dm z a em nm fm ksm g pa)))
  (let ((erased z1) (erased p1) (erased _)) (perm-nth dm z nm ni qn lz))
  (let ((erased z2) (erased p2) (erased p3) (erased _) (erased _)) (cubic-eq dm z z1 nm cnm lz p1))
  (let-match erased (nth-fn _ fm a b z2 pb (hyper-third dm a z z2 em nm fm hm pa p3)) (Refl _ _))
  (values z1 p1 p2))

; What a run checks of the configuration map at a dart x, after embeddable and the lemmas of embed.v about the perimeter rc:
; edge is an involution, node keeps rc and has order 3 off it, x or edge x is off rc (edge_perimeter), two darts off rc
; joined by an edge are not both off the kernel (chordless_perimeter), and x, edge x, node x or node (edge x) is in the
; kernel (embed_cases).
(def-adts $ (RingSide : ((List (Nat)) nc rc) ((Nat) x nx) -> Type)
  enum
  (many RsOn : (erased (List (Nat)) nc rc) (erased (Nat) x nx) (erased (In x rc) ix) (erased (In nx rc) inx) -> (RingSide nc rc x nx))
  (many RsOff : (erased (List (Nat)) nc rc) (erased (Nat) x nx nnx) (erased (NotIn x rc) ox) (erased (NotIn nx rc) onx) (erased (Nth (Nat) nc nx nnx) p1)
      (erased (Nth (Nat) nc nnx x) p2) -> (RingSide nc rc x nx)))

(def-adts $ (NodeIn : ((List (Nat)) nc as) ((Nat) y) -> Type)
  enum
  (many MkNodeIn : (erased (List (Nat)) nc as) (erased (Nat) y z) (erased (Nth (Nat) nc y z) pz) (erased (In z as) iz) -> (NodeIn nc as y)))

(def-adts $ (GcAt : ((List (Nat)) ec nc rc as) ((Nat) x) -> Type)
  enum
  (many MkGcAt : (erased (List (Nat)) ec nc rc as) (erased (Nat) x ex nx) (erased (Nth (Nat) ec x ex) pe) (erased (Nth (Nat) ec ex x) pe2)
      (erased (Nth (Nat) nc x nx) pn) (erased (RingSide nc rc x nx) rs) (erased (Or (NotIn x rc) (NotIn ex rc)) ep)
      (erased (Or (In x rc) (Or (In ex rc) (Or (In x as) (In ex as)))) cl) (erased (Or (In x as) (Or (In ex as) (Or (In nx as) (NodeIn nc as ex)))) cs)
      -> (GcAt ec nc rc as x)))

(def-adts $ (GcAll : ((List (Nat)) ec nc rc as xs) -> Type)
  enum
  (many GcNil : (erased (List (Nat)) ec nc rc as) -> (GcAll ec nc rc as (Nil (Nat))))
  (many GcCons : (erased (List (Nat)) ec nc rc as xs) (erased (Nat) x) (erased (GcAt ec nc rc as x) p) (erased (GcAll ec nc rc as xs) rest)
      -> (GcAll ec nc rc as (Cons (Nat) x xs))))

(def-adts $ (GcOK : ((Nat) dc) ((List (Nat)) ec nc rc as) -> Type)
  enum
  (many MkGcOK : (erased (Nat) dc) (erased (List (Nat)) ec nc rc as ids) (erased (Iota dc ids) io) (erased (GcAll ec nc rc as ids) ga) -> (GcOK dc ec nc rc as)))

(def-fns _ $ (erased gcall-at : (erased (List (Nat)) ec nc rc as xs) (erased (Nat) x) (subterm erased (GcAll ec nc rc as xs) ga) (erased (In x xs) ix)
    -> (erased (GcAt ec nc rc as x) r))
  (let-match erased ga (GcCons _ _ _ _ xs1 y py ga1) (absurd (GcNil _ _ _ _) ix))
  (match erased ix _ ((InHere _ _) py) ((InThere _ _ _ ix1) (gcall-at ec nc rc as xs1 x ga1 ix1))))

(def-fns _ $ (erased gc-at : (erased (Nat) dc x) (erased (List (Nat)) ec nc rc as) (erased (GcOK dc ec nc rc as) ok) (erased (Lt x dc) lx) -> (erased (GcAt ec nc rc as x) r))
  (let-match erased ok (MkGcOK _ _ _ _ _ ids io ga))
  (gcall-at ec nc rc as ids x ga (iota-in dc x ids io lx)))

; embed_functor of embed.v, as a certificate: each kernel dart whose edge image is in the kernel is central.
(def-adts $ (EdgeOut : ((List (Nat)) ec as) ((Nat) x) -> Type)
  enum
  (many MkEdgeOut : (erased (List (Nat)) ec as) (erased (Nat) x y) (erased (Nth (Nat) ec x y) py) (erased (NotIn y as) oy) -> (EdgeOut ec as x)))

(def-adts $ (FunctorAll : ((List (Nat)) ec em as hl xs) -> Type)
  enum
  (many FaNil : (erased (List (Nat)) ec em as hl) -> (FunctorAll ec em as hl (Nil (Nat))))
  (many FaCons : (erased (List (Nat)) ec em as hl xs) (erased (Nat) x) (erased (Or (EdgeOut ec as x) (Central ec em hl x)) p)
      (erased (FunctorAll ec em as hl xs) rest) -> (FunctorAll ec em as hl (Cons (Nat) x xs))))

(def-fns _ $ (erased functor-at : (erased (List (Nat)) ec em as hl xs) (erased (Nat) x y w) (subterm erased (FunctorAll ec em as hl xs) fa) (erased (In x xs) ix)
    (erased (Nth (Nat) ec x y) py) (erased (In y as) iy) (erased (Nth (Nat) hl x w) pw) -> (erased (Nat) v) (erased (Nth (Nat) hl y v) pv) (erased (Nth (Nat) em w v) pm))
  (let-match erased fa (FaCons _ _ _ _ xs1 x1 p fa1) (absurd (FaNil _ _ _ _) ix))
  (let-match erased ix (InHere _ _) ((InThere _ _ _ ix1) (functor-at ec em as hl xs1 x y w fa1 ix1 py iy pw)))
  (let-match erased p (OrR _ _ c)
    (absurd (OrL _ _ eo) (let-match erased eo (MkEdgeOut _ _ _ y2 py2 oy)) (let-match erased (nth-fn _ ec x y y2 py py2) (Refl _ _)) (apart-irrefl y (notin-in y y as oy iy))))
  (let-match erased c (MkCentral _ _ _ _ y3 w3 v3 py3 pw3 pv3 pm3))
  (let-match erased (nth-fn _ ec x y y3 py py3) (Refl _ _))
  (let-match erased (nth-fn _ hl x w w3 pw pw3) (Refl _ _))
  (values v3 pv3 pm3))

; embed of embed.v at x: h x on the kernel, and otherwise read off edge x, node x or node (edge x), the first in it.
(def-adts $ (HEmb : ((List (Nat)) ec nc em nm fm as hl) ((Nat) x u) -> Type)
  enum
  (many HeK : (erased (List (Nat)) ec nc em nm fm as hl) (erased (Nat) x u) (erased (In x as) ix) (erased (Nth (Nat) hl x u) pu) -> (HEmb ec nc em nm fm as hl x u))
  (many HeE : (erased (List (Nat)) ec nc em nm fm as hl) (erased (Nat) x u y w) (erased (NotIn x as) ox) (erased (Nth (Nat) ec x y) py) (erased (In y as) iy)
      (erased (Nth (Nat) hl y w) pw) (erased (Nth (Nat) em w u) pu) -> (HEmb ec nc em nm fm as hl x u))
  (many HeN : (erased (List (Nat)) ec nc em nm fm as hl) (erased (Nat) x u y z w a) (erased (NotIn x as) ox) (erased (Nth (Nat) ec x y) py) (erased (NotIn y as) oy)
      (erased (Nth (Nat) nc x z) pz) (erased (In z as) iz) (erased (Nth (Nat) hl z w) pw) (erased (Nth (Nat) em w a) pa) (erased (Nth (Nat) fm a u) pu)
      -> (HEmb ec nc em nm fm as hl x u))
  (many HeEN : (erased (List (Nat)) ec nc em nm fm as hl) (erased (Nat) x u y z t w w1 w2) (erased (NotIn x as) ox) (erased (Nth (Nat) ec x y) py) (erased (NotIn y as) oy)
      (erased (Nth (Nat) nc x z) pz) (erased (NotIn z as) oz) (erased (Nth (Nat) nc y t) pt) (erased (In t as) it) (erased (Nth (Nat) hl t w) pw)
      (erased (Nth (Nat) nm w w1) p1) (erased (Nth (Nat) nm w1 w2) p2) (erased (Nth (Nat) em w2 u) pu) -> (HEmb ec nc em nm fm as hl x u)))

(def-fns _ $ (erased absurd in-notin : (erased (Nat) x) (erased (List (Nat)) s) (erased (In x s) i) (erased (NotIn x s) o) -> (erased (False) r))
  (apart-irrefl x (notin-in x x s o i)))

(def-fns _ $ (erased ker-off-ring : (erased (Nat) dc dm x) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl) (erased (EEnv dc ec nc fc ksc rc dm em nm fm ksm as hl) en)
    (erased (In x as) ix) -> (erased (NotIn x rc) r))
  (let-match erased en (MkEEnv _ _ _ _ _ _ _ _ _ _ _ _ _ hc olc kl g pe))
  (kernel-off fc rc x (ker-of dc x fc rc as kl ix)))

; A dart of the configuration map whose node image is in the kernel is off rc.
(def-fns _ $ (erased node-off-ring : (erased (Nat) dc dm x z) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl) (erased (EEnv dc ec nc fc ksc rc dm em nm fm ksm as hl) en)
    (erased (GcAt ec nc rc as x) gx) (erased (Nth (Nat) nc x z) pz) (erased (In z as) iz) -> (erased (NotIn x rc) r))
  (let-match erased gx (MkGcAt _ _ _ _ _ ex nx pe pe2 pn rs ep cl cs))
  (let-match erased (nth-fn _ nc x z nx pz pn) (Refl _ _))
  (match erased rs _
    (absurd (RsOn _ _ _ _ ix inx) (in-notin z rc inx (ker-off-ring dc dm z ec nc fc ksc rc em nm fm ksm as hl en iz)))
    ((RsOff _ _ _ _ _ ox _ _ _) ox)))

; embedE at a dart x off rc: h1 (edge x) = edge (h1 x).
(def-fns _ $ (erased embed-e-off : (erased (Nat) dc dm x y u v) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl) (erased (EEnv dc ec nc fc ksc rc dm em nm fm ksm as hl) en)
    (erased (GcOK dc ec nc rc as) ok) (erased (FunctorAll ec em as hl as) fa) (erased (NotIn x rc) ox) (erased (Nth (Nat) ec x y) py)
    (erased (HEmb ec nc em nm fm as hl x u) hx) (erased (HEmb ec nc em nm fm as hl y v) hy) -> (erased (Nth (Nat) em u v) r))
  (let ((erased en2)) en)
  (let-match erased en2 (MkEEnv _ _ _ _ _ _ _ _ _ _ _ _ _ hc olc kl g pe))
  (let ((erased nfc) (erased nic) (erased fic) (erased rnfc) (erased qe) (erased qn) (erased qf)) (hyper-core dc ec nc fc hc))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths dc ec nc fc hc))
  (let ((erased lx)) (nth-lt-length _ ec x dc y py le))
  (let ((erased gx)) (gc-at dc x ec nc rc as ok lx))
  (let ((erased gy)) (gc-at dc y ec nc rc as ok (perm-val dc x y ec nfc qe py)))
  (let-match erased gx (MkGcAt _ _ _ _ _ ex nx pex pyx pnx rsx epx clx csx))
  (let-match erased (nth-fn _ ec x y ex py pex) (Refl _ _))
  (match erased hx _
    ((HeK _ _ _ _ _ _ _ _ _ ix pu)
      (match erased hy _
        ((HeK _ _ _ _ _ _ _ _ _ iy pv)
          (let ((erased v2) (erased pv2) (erased pm)) (functor-at ec em as hl as x y u fa ix py iy pu))
          (let-match erased (nth-fn _ hl y v v2 pv pv2) (Refl _ _))
          pm)
        ((HeE _ _ _ _ _ _ _ _ _ q w oy pq iq pw pv)
          (let-match erased (nth-fn _ ec y x q pyx pq) (Refl _ _))
          (let-match erased (nth-fn _ hl x u w pu pw) (Refl _ _))
          pv)
        (absurd (HeN _ _ _ _ _ _ _ _ _ q z w a oy pq oq pz iz pw pa pv)
          (let-match erased (nth-fn _ ec y x q pyx pq) (Refl _ _)) (in-notin x as ix oq))
        (absurd (HeEN _ _ _ _ _ _ _ _ _ q z t w w1 w2 oy pq oq pz oz pt it pw p1 p2 pv)
          (let-match erased (nth-fn _ ec y x q pyx pq) (Refl _ _)) (in-notin x as ix oq))))
    ((HeE _ _ _ _ _ _ _ _ _ y1 w ox1 py1 iy1 pw pu)
      (let-match erased (nth-fn _ ec x y y1 py py1) (Refl _ _))
      (let-match erased hy (HeK _ _ _ _ _ _ _ _ _ iy pv)
        (absurd (HeE _ _ _ _ _ _ _ _ _ _ _ oy _ _ _ _) (in-notin y as iy1 oy))
        (absurd (HeN _ _ _ _ _ _ _ _ _ _ _ _ _ oy _ _ _ _ _ _ _) (in-notin y as iy1 oy))
        (absurd (HeEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ oy _ _ _ _ _ _ _ _ _ _) (in-notin y as iy1 oy)))
      (let-match erased (nth-fn _ hl y v w pv pw) (Refl _ _))
      (gm-ee dm w u em nm fm ksm g pu))
    ((HeN _ _ _ _ _ _ _ _ _ y1 z w a ox1 py1 oy1 pz iz pw pa pu)
      (let-match erased (nth-fn _ ec x y y1 py py1) (Refl _ _))
      (match erased hy _
        (absurd (HeK _ _ _ _ _ _ _ _ _ iy pv) (in-notin y as iy oy1))
        (absurd (HeE _ _ _ _ _ _ _ _ _ q w2 oy pq iq pw2 pv)
          (let-match erased (nth-fn _ ec y x q pyx pq) (Refl _ _)) (in-notin x as iq ox1))
        (absurd (HeN _ _ _ _ _ _ _ _ _ q z2 w2 a2 oy pq oq pz2 iz2 pw2 pa2 pv)
          (let ((erased oyr)) (node-off-ring dc dm y z2 ec nc fc ksc rc em nm fm ksm as hl en gy pz2 iz2))
          (match erased clx _
            (absurd (OrL _ _ i) (in-notin x rc i ox))
            (absurd (OrR _ _ c1)
              (match erased c1 _
                (absurd (OrL _ _ i) (in-notin y rc i oyr))
                (absurd (OrR _ _ c2) (match erased c2 _ (absurd (OrL _ _ i) (in-notin x as i ox1)) (absurd (OrR _ _ i) (in-notin y as i oy1))))))))
        ((HeEN _ _ _ _ _ _ _ _ _ q z2 t w2 w3 w4 oy pq oq pz2 oz2 pt it pw2 p1 p2 pv)
          (let-match erased (nth-fn _ ec y x q pyx pq) (Refl _ _))
          (let-match erased (nth-fn _ nc x z t pz pt) (Refl _ _))
          (let-match erased (nth-fn _ hl z w w2 pw pw2) (Refl _ _))
          (let ((erased z1) (erased q1) (erased q2)) (gm-fe dm w a u em nm fm ksm g pa pu))
          (let-match erased (nth-fn _ nm w z1 w3 q1 p1) (Refl _ _))
          (let-match erased (nth-fn _ nm z1 u w4 q2 p2) (Refl _ _))
          pv)))
    ((HeEN _ _ _ _ _ _ _ _ _ y1 z t w w1 w2 ox1 py1 oy1 pz oz pt it pw p1 p2 pu)
      (let-match erased (nth-fn _ ec x y y1 py py1) (Refl _ _))
      (match erased hy _
        (absurd (HeK _ _ _ _ _ _ _ _ _ iy pv) (in-notin y as iy oy1))
        (absurd (HeE _ _ _ _ _ _ _ _ _ q w5 oy pq iq pw5 pv)
          (let-match erased (nth-fn _ ec y x q pyx pq) (Refl _ _)) (in-notin x as iq ox1))
        ((HeN _ _ _ _ _ _ _ _ _ q z2 w5 a oy pq oq pz2 iz2 pw5 pa pv)
          (let-match erased (nth-fn _ nc y t z2 pt pz2) (Refl _ _))
          (let-match erased (nth-fn _ hl t w w5 pw pw5) (Refl _ _))
          (let ((erased z1) (erased q1) (erased q2)) (gm-fe dm w a v em nm fm ksm g pa pv))
          (let-match erased (nth-fn _ nm w w1 z1 p1 q1) (Refl _ _))
          (let-match erased (nth-fn _ nm w1 w2 v p2 q2) (Refl _ _))
          (gm-ee dm w2 u em nm fm ksm g pu))
        (absurd (HeEN _ _ _ _ _ _ _ _ _ q z2 t2 w5 w6 w7 oy pq oq pz2 oz2 pt2 it2 pw5 p5 p6 pv)
          (let-match erased (nth-fn _ nc y t z2 pt pz2) (Refl _ _)) (in-notin t as it oz2))))))

; embedE: h1 (edge x) = edge (h1 x) at every dart.
(def-fns _ $ (erased embed-e : (erased (Nat) dc dm x y u v) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl) (erased (EEnv dc ec nc fc ksc rc dm em nm fm ksm as hl) en)
    (erased (GcOK dc ec nc rc as) ok) (erased (FunctorAll ec em as hl as) fa) (erased (Nth (Nat) ec x y) py)
    (erased (HEmb ec nc em nm fm as hl x u) hx) (erased (HEmb ec nc em nm fm as hl y v) hy) -> (erased (Nth (Nat) em u v) r))
  (let ((erased en2)) en)
  (let-match erased en2 (MkEEnv _ _ _ _ _ _ _ _ _ _ _ _ _ hc olc kl g pe))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths dc ec nc fc hc))
  (let-match erased (gc-at dc x ec nc rc as ok (nth-lt-length _ ec x dc y py le)) (MkGcAt _ _ _ _ _ ex nx pex pyx pnx rsx epx clx csx))
  (let-match erased (nth-fn _ ec x y ex py pex) (Refl _ _))
  (match erased epx _
    ((OrL _ _ ox) (embed-e-off dc dm x y u v ec nc fc ksc rc em nm fm ksm as hl en ok fa ox py hx hy))
    ((OrR _ _ oy) (gm-ee dm v u em nm fm ksm g (embed-e-off dc dm y x v u ec nc fc ksc rc em nm fm ksm as hl en ok fa oy pyx hy hx)))))
