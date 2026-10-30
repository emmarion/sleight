; embed_functor of embed.v (embed3.sl's FunctorAll) and embed3.sl's GcOK on the configuration maps that cpmap.sl builds,
; from certificates that a run decides (embed4goal.sl). Load after embed3.sl.

(def-adts $ (NonCen : ((List (Nat)) ec em hl) ((Nat) x) -> Type)
  enum
  (many MkNonCen : (erased (List (Nat)) ec em hl) (erased (Nat) x y w v u) (erased (Nth (Nat) ec x y) py) (erased (Nth (Nat) hl x w) pw)
      (erased (Nth (Nat) hl y v) pv) (erased (Nth (Nat) em w u) pu) (erased (Apart (Nat) Lt u v) ne) -> (NonCen ec em hl x)))

(def-adts $ (CStat : ((List (Nat)) ec em hl) ((Bool) b) ((Nat) x) -> Type)
  enum
  (many CsCen : (erased (List (Nat)) ec em hl) (erased (Nat) x) (erased (Central ec em hl x) c) -> (CStat ec em hl (BTrue) x))
  (many CsNon : (erased (List (Nat)) ec em hl) (erased (Nat) x) (erased (NonCen ec em hl x) c) -> (CStat ec em hl (BFalse) x)))

(def-adts $ (AllCStat : ((List (Nat)) ec em hl) ((Bool) b) ((List (Nat)) xs) -> Type)
  enum
  (many AcNil : (erased (List (Nat)) ec em hl) (erased (Bool) b) -> (AllCStat ec em hl b (Nil (Nat))))
  (many AcCons : (erased (List (Nat)) ec em hl xs) (erased (Bool) b) (erased (Nat) x) (erased (CStat ec em hl b x) s) (erased (AllCStat ec em hl b xs) rest)
      -> (AllCStat ec em hl b (Cons (Nat) x xs))))

(def-adts $ (EIn : ((List (Nat)) ec l) ((Nat) x) -> Type)
  enum
  (many EiHere : (erased (List (Nat)) ec l) (erased (Nat) x) (erased (In x l) i) -> (EIn ec l x))
  (many EiEdge : (erased (List (Nat)) ec l) (erased (Nat) x y) (erased (Nth (Nat) ec x y) py) (erased (In y l) i) -> (EIn ec l x)))

(def-adts $ (Tri : ((List (Nat)) ec nc as) ((Nat) a b c) -> Type)
  enum
  (many MkTri : (erased (List (Nat)) ec nc as) (erased (Nat) a b c ea eb ecc) (erased (Nth (Nat) nc a b) pab) (erased (Nth (Nat) nc b c) pbc)
      (erased (Nth (Nat) nc c a) pca) (erased (Nth (Nat) ec a ea) pa) (erased (Nth (Nat) ec b eb) pb) (erased (Nth (Nat) ec c ecc) pcc) (erased (In a as) ia)
      (erased (In b as) ib) (erased (In c as) ic) (erased (In ea as) iea) (erased (In eb as) ieb) (erased (In ecc as) iec) -> (Tri ec nc as a b c)))

(def-adts $ (LabAt : ((List (Nat)) fid lab) ((Nat) x k) -> Type)
  enum
  (many MkLabAt : (erased (List (Nat)) fid lab) (erased (Nat) x k i) (erased (Nth (Nat) fid x i) pi) (erased (Nth (Nat) lab i k) pk) -> (LabAt fid lab x k)))

(def-adts $ (CrossAt : ((List (Nat)) ec as fid lab ns) ((Nat) z) -> Type)
  enum
  (many CxZero : (erased (List (Nat)) ec as fid lab ns) (erased (Nat) z) (erased (LabAt fid lab z (Zero)) l) -> (CrossAt ec as fid lab ns z))
  (many CxOut : (erased (List (Nat)) ec as fid lab ns) (erased (Nat) z y) (erased (Nth (Nat) ec z y) py) (erased (NotIn y as) o) -> (CrossAt ec as fid lab ns z))
  (many CxSame : (erased (List (Nat)) ec as fid lab ns) (erased (Nat) z y) (erased (Nth (Nat) ec z y) py) (erased (LabAt fid lab y (Succ (Zero))) l)
      -> (CrossAt ec as fid lab ns z))
  (many CxNon : (erased (List (Nat)) ec as fid lab ns) (erased (Nat) z) (erased (EIn ec ns z) i) -> (CrossAt ec as fid lab ns z)))

(def-adts $ (CrossAll : ((List (Nat)) ec as fid lab ns xs) -> Type)
  enum
  (many CaNil : (erased (List (Nat)) ec as fid lab ns) -> (CrossAll ec as fid lab ns (Nil (Nat))))
  (many CaCons : (erased (List (Nat)) ec as fid lab ns xs) (erased (Nat) z) (erased (CrossAt ec as fid lab ns z) c) (erased (CrossAll ec as fid lab ns xs) rest)
      -> (CrossAll ec as fid lab ns (Cons (Nat) z xs))))

; ns are darts not central and cs central darts, each up to edge.
(def-adts $ (Refut : ((List (Nat)) ec nc fid as ns cs) -> Type)
  enum
  (many RfSplit : (erased (List (Nat)) ec nc fid as ns cs) (erased (Nat) z y) (erased (Nth (Nat) ec z y) py) (erased (In z as) iz) (erased (In y as) iy)
      (erased (Refut ec nc fid as (Cons (Nat) z ns) cs) rn) (erased (Refut ec nc fid as ns (Cons (Nat) z cs)) rc) -> (Refut ec nc fid as ns cs))
  (many RfNode : (erased (List (Nat)) ec nc fid as ns cs) (erased (Nat) a b c) (erased (Tri ec nc as a b c) t) (erased (EIn ec cs b) ib) (erased (EIn ec cs c) ic)
      (erased (Refut ec nc fid as ns (Cons (Nat) a cs)) r) -> (Refut ec nc fid as ns cs))
  (many RfConf : (erased (List (Nat)) ec nc fid as ns cs) (erased (Nat) z) (erased (In z as) iz) (erased (EIn ec ns z) in1) (erased (EIn ec cs z) in2)
      -> (Refut ec nc fid as ns cs))
  (many RfCut : (erased (List (Nat)) ec nc fid as ns cs lab) (erased (Nat) x y) (erased (In x as) ix) (erased (LabAt fid lab x (Succ (Zero))) lx)
      (erased (In y as) iy) (erased (LabAt fid lab y (Zero)) ly) (erased (CrossAll ec as fid lab ns as) ca) -> (Refut ec nc fid as ns cs)))

(def-adts $ (FAt : ((List (Nat)) ec nc fid as) ((Nat) x) -> Type)
  enum
  (many FaOut : (erased (List (Nat)) ec nc fid as) (erased (Nat) x y) (erased (Nth (Nat) ec x y) py) (erased (NotIn y as) o) -> (FAt ec nc fid as x))
  (many FaRef : (erased (List (Nat)) ec nc fid as) (erased (Nat) x) (erased (Refut ec nc fid as (Cons (Nat) x (Nil (Nat))) (Nil (Nat))) r) -> (FAt ec nc fid as x)))

(def-adts $ (FAll : ((List (Nat)) ec nc fid as xs) -> Type)
  enum
  (many FsNil : (erased (List (Nat)) ec nc fid as) -> (FAll ec nc fid as (Nil (Nat))))
  (many FsCons : (erased (List (Nat)) ec nc fid as xs) (erased (Nat) x) (erased (FAt ec nc fid as x) p) (erased (FAll ec nc fid as xs) rest)
      -> (FAll ec nc fid as (Cons (Nat) x xs))))

; as0 is the kernel the certificates were checked on, fid labels the darts by their faces.
(def-adts $ (FEnv : ((Nat) dc) ((List (Nat)) ec nc fc ksc rc) ((Nat) dm) ((List (Nat)) em nm fm ksm as hl as0 fid) -> Type)
  enum
  (many MkFEnv : (erased (Nat) dc) (erased (List (Nat)) ec nc fc ksc rc) (erased (Nat) dm) (erased (List (Nat)) em nm fm ksm as hl as0 fid)
      (erased (EEnv dc ec nc fc ksc rc dm em nm fm ksm as hl) en) (erased (KernelList dc fc rc as0) kl0) (erased (GcOK dc ec nc rc as) ok)
      (erased (Respects fid fc fid) rf) -> (FEnv dc ec nc fc ksc rc dm em nm fm ksm as hl as0 fid)))

(def-adts $ (InAll : ((List (Nat)) xs s) -> Type)
  enum
  (many IaNil : (erased (List (Nat)) s) -> (InAll (Nil (Nat)) s))
  (many IaCons : (erased (Nat) x) (erased (List (Nat)) xs s) (erased (In x s) i) (erased (InAll xs s) rest) -> (InAll (Cons (Nat) x xs) s)))

(def-fns _ $ (erased ia-weaken : (erased (Nat) y) (erased (List (Nat)) xs s) (subterm erased (InAll xs s) ia) -> (erased (InAll xs (Cons (Nat) y s)) r))
  (match erased ia _
    ((IaNil _) (IaNil (Cons (Nat) y s)))
    ((IaCons x xs1 _ i ia1) (IaCons x xs1 (Cons (Nat) y s) (InThere x y s i) (ia-weaken y xs1 s ia1)))))

(def-fns _ $ (erased ia-self : (subterm erased (List (Nat)) xs) -> (erased (InAll xs xs) r))
  (let-match erased xs (Cons _ x xs1) ((Nil _) (IaNil (Nil (Nat)))))
  (IaCons x xs1 xs (InHere x xs1) (ia-weaken x xs1 xs1 (ia-self xs1))))

(def-fns _ $ (erased kl-move : (erased (Nat) d x) (erased (List (Nat)) f r as as2) (erased (Length (Nat) f d) lf) (erased (KernelList d f r as) kl)
    (erased (KernelList d f r as2) kl2) (erased (In x as) ix) -> (erased (In x as2) res))
  (let ((erased k)) (ker-of d x f r as kl ix))
  (ker-in d x f r as2 kl2 k (kernel-lt d x f r lf k)))

; Centrality is decided at a kernel dart whose edge image is in the kernel.
(def-fns _ $ (erased cstat-dec : (erased (Nat) dc dm z y) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl as0 fid)
    (erased (FEnv dc ec nc fc ksc rc dm em nm fm ksm as hl as0 fid) fe) (erased (In z as) iz) (erased (Nth (Nat) ec z y) py) (erased (In y as) iy)
    -> (erased (Or (CStat ec em hl (BTrue) z) (CStat ec em hl (BFalse) z)) r))
  (let-match erased fe (MkFEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ en kl0 ok rf))
  (let ((erased w) (erased pw) (erased lw)) (h-val dc dm z ec nc fc ksc rc em nm fm ksm as hl en iz))
  (let ((erased v) (erased pv) (erased _)) (h-val dc dm y ec nc fc ksc rc em nm fm ksm as hl en iy))
  (let ((erased en2)) en)
  (let-match erased en2 (MkEEnv _ _ _ _ _ _ _ _ _ _ _ _ _ hc olc kl g pe))
  (let ((erased u) (erased _) (erased _) (erased pu) (erased _) (erased _) (erased _) (erased _) (erased _)) (gm-step dm w em nm fm ksm g lw))
  (match erased (nat-eq u v) _
    ((Equal _ _ _) (OrL _ _ (CsCen ec em hl z (MkCentral ec em hl z y w v py pw pv pu))))
    ((Unequal _ _ _ _ ne) (OrR _ _ (CsNon ec em hl z (MkNonCen ec em hl z y w v u py pw pv pu ne))))))

; The status of y is that of its edge image x.
(def-fns _ $ (erased cstat-edge : (erased (Nat) dc dm x y) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl as0 fid) (erased (Bool) b)
    (erased (FEnv dc ec nc fc ksc rc dm em nm fm ksm as hl as0 fid) fe) (erased (In x as) ix) (erased (Nth (Nat) ec x y) py) (erased (CStat ec em hl b y) s)
    -> (erased (CStat ec em hl b x) r))
  (let-match erased fe (MkFEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ en kl0 ok rf))
  (let ((erased en2)) en)
  (let-match erased en2 (MkEEnv _ _ _ _ _ _ _ _ _ _ _ _ _ hc olc kl g pe))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths dc ec nc fc hc))
  (let-match erased (gc-at dc x ec nc rc as ok (nth-lt-length _ ec x dc y py le)) (MkGcAt _ _ _ _ _ ex nx pex pyx pnx rsx epx clx csx))
  (let-match erased (nth-fn _ ec x y ex py pex) (Refl _ _))
  (let ((erased v) (erased pv) (erased lv)) (h-val dc dm x ec nc fc ksc rc em nm fm ksm as hl en ix))
  (match erased s _
    ((CsCen _ _ _ _ c)
      (let-match erased c (MkCentral _ _ _ _ y2 w2 v2 py2 pw2 pv2 pm2))
      (let-match erased (nth-fn _ ec y x y2 pyx py2) (Refl _ _))
      (let-match erased (nth-fn _ hl x v v2 pv pv2) (Refl _ _))
      (CsCen ec em hl x (MkCentral ec em hl x y v w2 py pv pw2 (gm-ee dm w2 v em nm fm ksm g pm2))))
    ((CsNon _ _ _ _ c)
      (let-match erased c (MkNonCen _ _ _ _ y2 w2 v2 u2 py2 pw2 pv2 pu2 ne))
      (let-match erased (nth-fn _ ec y x y2 pyx py2) (Refl _ _))
      (let-match erased (nth-fn _ hl x v v2 pv pv2) (Refl _ _))
      (let ((erased u) (erased _) (erased _) (erased pu) (erased _) (erased _) (erased _) (erased _) (erased _)) (gm-step dm v em nm fm ksm g lv))
      (match erased (nat-eq u w2) _
        ((Unequal _ _ _ _ ne2) (CsNon ec em hl x (MkNonCen ec em hl x y v w2 u py pv pw2 pu ne2)))
        (absurd (Equal _ _ _)
          (let-match erased (nth-fn _ em w2 u2 v pu2 (gm-ee dm v w2 em nm fm ksm g pu)) (Refl _ _))
          (apart-irrefl v ne))))))

(def-fns _ $ (erased acs-in : (erased (List (Nat)) ec em hl l) (erased (Bool) b) (erased (Nat) z) (subterm erased (AllCStat ec em hl b l) a) (erased (In z l) iz)
    -> (erased (CStat ec em hl b z) r))
  (let-match erased a (AcCons _ _ _ l1 _ y s a1) (absurd (AcNil _ _ _ _) iz))
  (match erased iz _ ((InHere _ _) s) ((InThere _ _ _ iz1) (acs-in ec em hl l1 b z a1 iz1))))

(def-fns _ $ (erased cstat-of : (erased (Nat) dc dm z) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl as0 fid l) (erased (Bool) b)
    (erased (FEnv dc ec nc fc ksc rc dm em nm fm ksm as hl as0 fid) fe) (erased (In z as) iz) (erased (EIn ec l z) i) (erased (AllCStat ec em hl b l) a)
    -> (erased (CStat ec em hl b z) r))
  (match erased i _
    ((EiHere _ _ _ p) (acs-in ec em hl l b z a p))
    ((EiEdge _ _ _ y py p) (cstat-edge dc dm z y ec nc fc ksc rc em nm fm ksm as hl as0 fid b fe iz py (acs-in ec em hl l b y a p)))))

(def-fns _ $ (erased absurd cstat-clash : (erased (List (Nat)) ec em hl) (erased (Nat) z) (erased (CStat ec em hl (BTrue) z) s1) (erased (CStat ec em hl (BFalse) z) s2)
    -> (erased (False) r))
  (let-match erased s1 (CsCen _ _ _ _ c))
  (let-match erased s2 (CsNon _ _ _ _ n))
  (let-match erased c (MkCentral _ _ _ _ y w v py pw pv pm))
  (let-match erased n (MkNonCen _ _ _ _ y2 w2 v2 u py2 pw2 pv2 pu ne))
  (let-match erased (nth-fn _ ec z y y2 py py2) (Refl _ _))
  (let-match erased (nth-fn _ hl z w w2 pw pw2) (Refl _ _))
  (let-match erased (nth-fn _ hl y v v2 pv pv2) (Refl _ _))
  (let-match erased (nth-fn _ em w v u pm pu) (Refl _ _))
  (apart-irrefl v ne))

; For z central with edge image y in the kernel, and n z1 = z: n (h z1) = h z.
(def-fns _ $ (erased cen-pred : (erased (Nat) dc dm z z1 y) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl as0 fid)
    (erased (FEnv dc ec nc fc ksc rc dm em nm fm ksm as hl as0 fid) fe) (erased (Central ec em hl z) c) (erased (Nth (Nat) nc z1 z) pn)
    (erased (Nth (Nat) ec z y) py) (erased (In y as) iy)
    -> (erased (Nat) w1 w) (erased (Nth (Nat) hl z1 w1) pw1) (erased (Nth (Nat) hl z w) pw) (erased (Nth (Nat) nm w1 w) pm))
  (let-match erased fe (MkFEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ en kl0 ok rf))
  (let ((erased en2)) en)
  (let-match erased en2 (MkEEnv _ _ _ _ _ _ _ _ _ _ _ _ _ hc olc kl g pe))
  (let-match erased c (MkCentral _ _ _ _ y2 w v py2 pw pv pm))
  (let-match erased (nth-fn _ ec z y y2 py py2) (Refl _ _))
  (let ((erased w1) (erased pw1) (erased pfv)) (h-face dc dm y z1 v ec nc fc ksc rc em nm fm ksm as hl en iy (hyper-third dc y z z1 ec nc fc hc py pn) pv))
  (values w1 w pw1 pw (gm-nfe dm w v w1 em nm fm ksm g pm pfv)))

; At a node a, b = n a, c = n b of the kernel with every edge image in it, a is central when b and c are.
(def-fns _ $ (erased node-rule : (erased (Nat) dc dm a b c) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl as0 fid)
    (erased (FEnv dc ec nc fc ksc rc dm em nm fm ksm as hl as0 fid) fe) (erased (Tri ec nc as0 a b c) t) (erased (Central ec em hl b) cb)
    (erased (Central ec em hl c) cec) -> (erased (Central ec em hl a) r))
  (let ((erased fe2)) fe)
  (let-match erased fe2 (MkFEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ en kl0 ok rf))
  (let ((erased en2)) en)
  (let-match erased en2 (MkEEnv _ _ _ _ _ _ _ _ _ _ _ _ _ hc olc kl g pe))
  (let-match erased g (MkGeo _ _ _ _ _ hm pem cnm olm pam))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths dc ec nc fc hc))
  (let ((erased lem) (erased lnm) (erased lfm)) (hyper-lengths dm em nm fm hm))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased qe) (erased qn) (erased qf)) (hyper-core dm em nm fm hm))
  (let-match erased t (MkTri _ _ _ _ _ _ ea eb ecc pab pbc pca pa pb pcc ia ib ic iea ieb iec))
  (let ((erased wa) (erased wb) (erased pwa) (erased pwb) (erased nab))
    (cen-pred dc dm b a eb ec nc fc ksc rc em nm fm ksm as hl as0 fid fe cb pab pb (kl-move dc eb fc rc as0 as lf kl0 kl ieb)))
  (let ((erased wb2) (erased wc) (erased pwb2) (erased pwc) (erased nbc))
    (cen-pred dc dm c b ecc ec nc fc ksc rc em nm fm ksm as hl as0 fid fe cec pbc pcc (kl-move dc ecc fc rc as0 as lf kl0 kl iec)))
  (let-match erased (nth-fn _ hl b wb wb2 pwb pwb2) (Refl _ _))
  (let ((erased lwa)) (nth-lt-length _ nm wa dm wb nab lnm))
  (let ((erased z) (erased p1) (erased p2) (erased _) (erased _)) (cubic-eq dm wa wb nm cnm lwa nab))
  (let-match erased (nth-fn _ nm wb z wc p1 nbc) (Refl _ _))
  (let ((erased iea2)) (kl-move dc ea fc rc as0 as lf kl0 kl iea))
  (let ((erased wea) (erased pwea) (erased _)) (h-val dc dm ea ec nc fc ksc rc em nm fm ksm as hl en iea2))
  (let ((erased t1) (erased pt1) (erased pft))
    (h-face dc dm ea c wea ec nc fc ksc rc em nm fm ksm as hl en iea2 (hyper-third dc ea a c ec nc fc hc pa pca) pwea))
  (let-match erased (nth-fn _ hl c t1 wc pt1 pwc) (Refl _ _))
  (let ((erased u) (erased _) (erased _) (erased pu) (erased lu) (erased _) (erased _) (erased _) (erased _)) (gm-step dm wa em nm fm ksm g lwa))
  (let ((erased _) (erased _) (erased s) (erased _) (erased _) (erased _) (erased _) (erased ps) (erased _)) (gm-step dm u em nm fm ksm g lu))
  (let-match erased (perm-inj dm s z wa nm ni qn (gm-nfe dm wa u s em nm fm ksm g pu ps) p2) (Refl _ _))
  (let-match erased (perm-inj dm u wea z fm fi qf ps pft) (Refl _ _))
  (MkCentral ec em hl a ea wa u pa pwa pwea pu))

(def-fns _ $ (erased lab-path : (erased (List (Nat)) fid fc s xs lab) (erased (Nat) a b k) (erased (Respects fid fc fid) rf) (subterm erased (Path fc s a b xs) p)
    (erased (LabAt fid lab a k) la) -> (erased (LabAt fid lab b k) r))
  (let-match erased p (PathStep _ _ xs1 _ z _ pz _ p1) ((PathHere _ _ _) la))
  (let-match erased la (MkLabAt _ _ _ _ i pi pk))
  (lab-path fid fc s xs1 lab z b k rf p1 (MkLabAt fid lab z k i (respects-nth fid fc fid a z i rf pz pi) pk)))

(def-fns _ $ (erased lab-some : (erased (List (Nat)) fid fc lab) (erased (Nat) a b k) (erased (Respects fid fc fid) rf) (erased (SomePath fc (Nil (Nat)) a b) sp)
    (erased (LabAt fid lab a k) la) -> (erased (LabAt fid lab b k) r))
  (let-match erased sp (MkSomePath _ _ xs _ _ p))
  (lab-path fid fc (Nil (Nat)) xs lab a b k rf p la))

(def-fns _ $ (erased absurd lab-clash : (erased (List (Nat)) fid lab) (erased (Nat) x) (erased (LabAt fid lab x (Succ (Zero))) l1) (erased (LabAt fid lab x (Zero)) l0)
    -> (erased (False) r))
  (let-match erased l1 (MkLabAt _ _ _ _ i pi pk))
  (let-match erased l0 (MkLabAt _ _ _ _ j pi2 pk2))
  (let-match erased (nth-fn _ fid x i j pi pi2) (Refl _ _))
  (nth-fn _ lab i (Succ (Zero)) (Zero) pk pk2))

(def-fns _ $ (erased ker-back : (erased (Nat) dc dm a b) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl s xs) (erased (EEnv dc ec nc fc ksc rc dm em nm fm ksm as hl) en)
    (subterm erased (Path fc s a b xs) p) (erased (In b as) ib) -> (erased (In a as) r))
  (let-match erased p (PathStep _ _ xs1 _ z _ pz _ p1) ((PathHere _ _ _) ib))
  (ker-face-inv dc dm a z ec nc fc ksc rc em nm fm ksm as hl en (ker-back dc dm z b ec nc fc ksc rc em nm fm ksm as hl s xs1 en p1 ib) pz))

; The edge image of the start of a path of rlinks to a kernel dart is in the kernel.
(def-fns _ $ (erased rl-edge-in : (erased (Nat) dc dm t y te) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl p) (erased (EEnv dc ec nc fc ksc rc dm em nm fm ksm as hl) en)
    (erased (RlPath ec fc em hl as t p y) rp) (erased (In y as) iy) (erased (Nth (Nat) ec t te) pte) -> (erased (In te as) r))
  (match erased rp _
    ((RPLast _ _ _ _ _ _ _ l)
      (let-match erased l (MkRlink _ _ _ _ q pq w))
      (let-match erased (nth-fn _ ec t te q pte pq) (Refl _ _))
      (let-match erased w (MkSomePath _ _ ws _ _ pw))
      (ker-back dc dm te y ec nc fc ksc rc em nm fm ksm as hl (Nil (Nat)) ws en pw iy))
    ((RPStep _ _ _ _ _ p1 _ t2 _ l it2 _ _)
      (let-match erased l (MkRlink _ _ _ _ q pq w))
      (let-match erased (nth-fn _ ec t te q pte pq) (Refl _ _))
      (let-match erased w (MkSomePath _ _ ws _ _ pw))
      (ker-back dc dm te t2 ec nc fc ksc rc em nm fm ksm as hl (Nil (Nat)) ws en pw it2))))

(def-fns _ $ (erased crossall-at : (erased (List (Nat)) ec as fid lab ns xs) (erased (Nat) z) (subterm erased (CrossAll ec as fid lab ns xs) ca) (erased (In z xs) iz)
    -> (erased (CrossAt ec as fid lab ns z) r))
  (let-match erased ca (CaCons _ _ _ _ _ xs1 y c ca1) (absurd (CaNil _ _ _ _ _) iz))
  (match erased iz _ ((InHere _ _) c) ((InThere _ _ _ iz1) (crossall-at ec as fid lab ns xs1 z ca1 iz1))))

; A path of rlinks from the face of a dart labelled 1 to one labelled 0 leaves a face labelled 1 by the edge of a central
; dart to a face labelled 0, which the cut says is not central.
(def-fns _ $ (erased absurd path-cross : (erased (Nat) dc dm z q y) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl as0 fid lab ns p)
    (erased (FEnv dc ec nc fc ksc rc dm em nm fm ksm as hl as0 fid) fe) (erased (CrossAll ec as0 fid lab ns as0) ca) (erased (AllCStat ec em hl (BFalse) ns) an)
    (subterm erased (RlPath ec fc em hl as z p y) rp) (erased (In y as) iy) (erased (Nth (Nat) ec z q) pq) (erased (LabAt fid lab q (Succ (Zero))) lq)
    (erased (LabAt fid lab y (Zero)) ly) -> (erased (False) r))
  (let ((erased fe2)) fe)
  (let-match erased fe2 (MkFEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ en kl0 ok rf))
  (let ((erased en2)) en)
  (let-match erased en2 (MkEEnv _ _ _ _ _ _ _ _ _ _ _ _ _ hc olc kl g pe))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths dc ec nc fc hc))
  (match erased rp _
    (absurd (RPLast _ _ _ _ _ _ _ l)
      (let-match erased l (MkRlink _ _ _ _ q2 pq2 w))
      (let-match erased (nth-fn _ ec z q q2 pq pq2) (Refl _ _))
      (lab-clash fid lab y (lab-some fid fc lab q y (Succ (Zero)) rf w lq) ly))
    (absurd (RPStep _ _ _ _ _ p1 _ t _ l it ct rest)
      (let-match erased l (MkRlink _ _ _ _ q2 pq2 w))
      (let-match erased (nth-fn _ ec z q q2 pq pq2) (Refl _ _))
      (let ((erased lt)) (lab-some fid fc lab q t (Succ (Zero)) rf w lq))
      (match erased (crossall-at ec as0 fid lab ns as0 t ca (kl-move dc t fc rc as as0 lf kl kl0 it)) _
        (absurd (CxZero _ _ _ _ _ _ l0) (lab-clash fid lab t lt l0))
        (absurd (CxOut _ _ _ _ _ _ te pte o)
          (in-notin te as0 (kl-move dc te fc rc as as0 lf kl kl0 (rl-edge-in dc dm t y te ec nc fc ksc rc em nm fm ksm as hl p1 en rest iy pte)) o))
        (absurd (CxSame _ _ _ _ _ _ te pte l1) (path-cross dc dm t te y ec nc fc ksc rc em nm fm ksm as hl as0 fid lab ns p1 fe ca an rest iy pte l1 ly))
        (absurd (CxNon _ _ _ _ _ _ i)
          (cstat-clash ec em hl t (CsCen ec em hl t ct) (cstat-of dc dm t ec nc fc ksc rc em nm fm ksm as hl as0 fid ns (BFalse) fe it i an)))))))

(def-fns _ $ (erased rlto-at : (erased (List (Nat)) ec fc em hl as ys) (erased (Nat) x y) (subterm erased (RlTo ec fc em hl as x ys) rt) (erased (In y ys) iy)
    -> (erased (List (Nat)) p) (erased (RlPath ec fc em hl as x p y) r))
  (let-match erased rt (RTCons _ _ _ _ _ ys1 p1 _ y1 rp rt1) (absurd (RTNil _ _ _ _ _ _) iy))
  (match erased iy _ ((InHere _ _) (values p1 rp)) ((InThere _ _ _ iy1) (rlto-at ec fc em hl as ys1 x y rt1 iy1))))

; A cut of the kernel faces, labelled 1 and 0, with x and y on its two sides: the rlink path of the preembedding from the face
; of x to y crosses it.
(def-fns _ $ (erased absurd cut-sound : (erased (Nat) dc dm x y) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl as0 fid lab ns)
    (erased (FEnv dc ec nc fc ksc rc dm em nm fm ksm as hl as0 fid) fe) (erased (In x as0) ix) (erased (LabAt fid lab x (Succ (Zero))) lx)
    (erased (In y as0) iy) (erased (LabAt fid lab y (Zero)) ly) (erased (CrossAll ec as0 fid lab ns as0) ca) (erased (AllCStat ec em hl (BFalse) ns) an)
    -> (erased (False) r))
  (let ((erased fe2)) fe)
  (let-match erased fe2 (MkFEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ en kl0 ok rf))
  (let ((erased en2)) en)
  (let-match erased en2 (MkEEnv _ _ _ _ _ _ _ _ _ _ _ _ _ hc olc kl g pe))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths dc ec nc fc hc))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased qe) (erased qn) (erased qf)) (hyper-core dc ec nc fc hc))
  (let ((erased iy2)) (kl-move dc y fc rc as0 as lf kl0 kl iy))
  (let-match erased (pe-of dc dm x ec nc fc ksc rc em nm fm ksm as hl en (kl-move dc x fc rc as0 as lf kl0 kl ix))
    (MkPeAt _ _ _ _ _ _ _ _ _ _ x1 w w1 a y0 z px pw pw1 pfm pa pma py cy pz rl))
  (let ((erased p) (erased rp)) (rlto-at ec fc em hl as as z y rl iy2))
  (let ((erased t) (erased pt) (erased _)) (perm-nth dc z ec nf qe (perm-val dc x1 z nc ni qn pz)))
  (let-match erased (perm-inj dc t x x1 fc fi qf (hyper-third dc t z x1 ec nc fc hc pt pz) px) (Refl _ _))
  (path-cross dc dm z x y ec nc fc ksc rc em nm fm ksm as hl as0 fid lab ns p fe ca an rp iy2 pt lx ly))

(def-fns _ $ (erased absurd refut-sound : (erased (Nat) dc dm) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl as0 fid ns cs)
    (erased (FEnv dc ec nc fc ksc rc dm em nm fm ksm as hl as0 fid) fe) (subterm erased (Refut ec nc fid as0 ns cs) rr)
    (erased (AllCStat ec em hl (BFalse) ns) an) (erased (AllCStat ec em hl (BTrue) cs) ac) -> (erased (False) r))
  (let ((erased fe2)) fe)
  (let-match erased fe2 (MkFEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ en kl0 ok rf))
  (let ((erased en2)) en)
  (let-match erased en2 (MkEEnv _ _ _ _ _ _ _ _ _ _ _ _ _ hc olc kl g pe))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths dc ec nc fc hc))
  (match erased rr _
    (absurd (RfSplit _ _ _ _ _ _ z y py iz iy r1 r2)
      (match erased (cstat-dec dc dm z y ec nc fc ksc rc em nm fm ksm as hl as0 fid fe (kl-move dc z fc rc as0 as lf kl0 kl iz) py (kl-move dc y fc rc as0 as lf kl0 kl iy)) _
        (absurd (OrL _ _ s) (refut-sound dc dm ec nc fc ksc rc em nm fm ksm as hl as0 fid ns (Cons (Nat) z cs) fe r2 an (AcCons ec em hl cs (BTrue) z s ac)))
        (absurd (OrR _ _ s) (refut-sound dc dm ec nc fc ksc rc em nm fm ksm as hl as0 fid (Cons (Nat) z ns) cs fe r1 (AcCons ec em hl ns (BFalse) z s an) ac))))
    (absurd (RfNode _ _ _ _ _ _ a b c t ib ic r1)
      (let ((erased t2)) t)
      (let-match erased t2 (MkTri _ _ _ _ _ _ ea eb ecc pab pbc pca pa pb pcc ia ib0 ic0 iea ieb iec))
      (let-match erased (cstat-of dc dm b ec nc fc ksc rc em nm fm ksm as hl as0 fid cs (BTrue) fe (kl-move dc b fc rc as0 as lf kl0 kl ib0) ib ac) (CsCen _ _ _ _ cb))
      (let-match erased (cstat-of dc dm c ec nc fc ksc rc em nm fm ksm as hl as0 fid cs (BTrue) fe (kl-move dc c fc rc as0 as lf kl0 kl ic0) ic ac) (CsCen _ _ _ _ cec))
      (let ((erased cen)) (node-rule dc dm a b c ec nc fc ksc rc em nm fm ksm as hl as0 fid fe t cb cec))
      (refut-sound dc dm ec nc fc ksc rc em nm fm ksm as hl as0 fid ns (Cons (Nat) a cs) fe r1 an (AcCons ec em hl cs (BTrue) a (CsCen ec em hl a cen) ac)))
    (absurd (RfConf _ _ _ _ _ _ z iz j1 j2)
      (let ((erased iz2)) (kl-move dc z fc rc as0 as lf kl0 kl iz))
      (cstat-clash ec em hl z (cstat-of dc dm z ec nc fc ksc rc em nm fm ksm as hl as0 fid cs (BTrue) fe iz2 j2 ac)
        (cstat-of dc dm z ec nc fc ksc rc em nm fm ksm as hl as0 fid ns (BFalse) fe iz2 j1 an)))
    (absurd (RfCut _ _ _ _ _ _ lab x y ix lx iy ly ca) (cut-sound dc dm x y ec nc fc ksc rc em nm fm ksm as hl as0 fid lab ns fe ix lx iy ly ca an))))

(def-fns _ $ (erased fall-at : (erased (List (Nat)) ec nc fid as xs) (erased (Nat) x) (subterm erased (FAll ec nc fid as xs) fa) (erased (In x xs) ix)
    -> (erased (FAt ec nc fid as x) r))
  (let-match erased fa (FsCons _ _ _ _ xs1 y p fa1) (absurd (FsNil _ _ _ _) ix))
  (match erased ix _ ((InHere _ _) p) ((InThere _ _ _ ix1) (fall-at ec nc fid as xs1 x fa1 ix1))))

(def-fns _ $ (erased functor-x : (erased (Nat) dc dm x) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl as0 fid)
    (erased (FEnv dc ec nc fc ksc rc dm em nm fm ksm as hl as0 fid) fe) (erased (FAll ec nc fid as0 as0) fa) (erased (In x as) ix)
    -> (erased (Or (EdgeOut ec as x) (Central ec em hl x)) r))
  (let ((erased fe2)) fe)
  (let-match erased fe2 (MkFEnv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ en kl0 ok rf))
  (let ((erased en2)) en)
  (let-match erased en2 (MkEEnv _ _ _ _ _ _ _ _ _ _ _ _ _ hc olc kl g pe))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths dc ec nc fc hc))
  (let-match erased (gc-at dc x ec nc rc as ok (kernel-lt dc x fc rc lf (ker-of dc x fc rc as kl ix))) (MkGcAt _ _ _ _ _ y nx py pyx pnx rsx epx clx csx))
  (let-match erased (in-dec y as) (OrL _ _ iy) ((OrR _ _ oy) (OrL _ _ (MkEdgeOut ec as x y py oy))))
  (let-match erased (cstat-dec dc dm x y ec nc fc ksc rc em nm fm ksm as hl as0 fid fe ix py iy) (OrL _ _ s)
    (absurd (OrR _ _ s)
      (match erased (fall-at ec nc fid as0 as0 x fa (kl-move dc x fc rc as as0 lf kl kl0 ix)) _
        (absurd (FaOut _ _ _ _ _ y2 py2 o)
          (let-match erased (nth-fn _ ec x y y2 py py2) (Refl _ _))
          (in-notin y as0 (kl-move dc y fc rc as as0 lf kl kl0 iy) o))
        (absurd (FaRef _ _ _ _ _ rr)
          (refut-sound dc dm ec nc fc ksc rc em nm fm ksm as hl as0 fid (Cons (Nat) x (Nil (Nat))) (Nil (Nat)) fe rr
            (AcCons ec em hl (Nil (Nat)) (BFalse) x s (AcNil ec em hl (BFalse))) (AcNil ec em hl (BTrue)))))))
  (let-match erased s (CsCen _ _ _ _ c))
  (OrR _ _ c))

(def-fns _ $ (erased functor-list : (erased (Nat) dc dm) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl as0 fid)
    (erased (FEnv dc ec nc fc ksc rc dm em nm fm ksm as hl as0 fid) fe) (erased (FAll ec nc fid as0 as0) fa) (subterm erased (List (Nat)) xs) (erased (InAll xs as) ia)
    -> (erased (FunctorAll ec em as hl xs) r))
  (let-match erased xs (Cons _ x xs1) ((Nil _) (FaNil ec em as hl)))
  (let-match erased ia (IaCons _ _ _ ix ia1))
  (FaCons ec em as hl xs1 x (functor-x dc dm x ec nc fc ksc rc em nm fm ksm as hl as0 fid fe fa ix)
    (functor-list dc dm ec nc fc ksc rc em nm fm ksm as hl as0 fid fe fa xs1 ia1)))

(def-fns _ $ (erased nodein-move : (erased (Nat) dc x) (erased (List (Nat)) nc fc rc as0 as) (erased (Length (Nat) fc dc) lf) (erased (KernelList dc fc rc as0) kl0)
    (erased (KernelList dc fc rc as) kl) (erased (NodeIn nc as0 x) ni) -> (erased (NodeIn nc as x) r))
  (let-match erased ni (MkNodeIn _ _ _ z pz iz))
  (MkNodeIn nc as x z pz (kl-move dc z fc rc as0 as lf kl0 kl iz)))

(def-fns _ $ (erased gcat-move : (erased (Nat) dc x) (erased (List (Nat)) ec nc fc rc as0 as) (erased (Length (Nat) fc dc) lf) (erased (KernelList dc fc rc as0) kl0)
    (erased (KernelList dc fc rc as) kl) (erased (GcAt ec nc rc as0 x) gx) -> (erased (GcAt ec nc rc as x) r))
  (let-match erased gx (MkGcAt _ _ _ _ _ ex nx pe pe2 pn rs ep cl cs))
  (let ((erased (Or (In x rc) (Or (In ex rc) (Or (In x as) (In ex as)))) cl2))
    (match erased cl _
      ((OrL _ _ i) (OrL _ _ i))
      ((OrR _ _ c1) (OrR _ _ (match erased c1 _
        ((OrL _ _ i) (OrL _ _ i))
        ((OrR _ _ c2) (OrR _ _ (match erased c2 _
          ((OrL _ _ i) (OrL _ _ (kl-move dc x fc rc as0 as lf kl0 kl i)))
          ((OrR _ _ i) (OrR _ _ (kl-move dc ex fc rc as0 as lf kl0 kl i)))))))))))
  (let ((erased (Or (In x as) (Or (In ex as) (Or (In nx as) (NodeIn nc as ex)))) cs2))
    (match erased cs _
      ((OrL _ _ i) (OrL _ _ (kl-move dc x fc rc as0 as lf kl0 kl i)))
      ((OrR _ _ c1) (OrR _ _ (match erased c1 _
        ((OrL _ _ i) (OrL _ _ (kl-move dc ex fc rc as0 as lf kl0 kl i)))
        ((OrR _ _ c2) (OrR _ _ (match erased c2 _
          ((OrL _ _ i) (OrL _ _ (kl-move dc nx fc rc as0 as lf kl0 kl i)))
          ((OrR _ _ ni) (OrR _ _ (nodein-move dc ex nc fc rc as0 as lf kl0 kl ni)))))))))))
  (MkGcAt ec nc rc as x ex nx pe pe2 pn rs ep cl2 cs2))
(def-fns _ $ (erased gcall-move : (erased (Nat) dc) (erased (List (Nat)) ec nc fc rc as0 as xs) (erased (Length (Nat) fc dc) lf) (erased (KernelList dc fc rc as0) kl0)
    (erased (KernelList dc fc rc as) kl) (subterm erased (GcAll ec nc rc as0 xs) ga) -> (erased (GcAll ec nc rc as xs) r))
  (match erased ga _
    ((GcNil _ _ _ _) (GcNil ec nc rc as))
    ((GcCons _ _ _ _ xs1 x p rest)
      (GcCons ec nc rc as xs1 x (gcat-move dc x ec nc fc rc as0 as lf kl0 kl p) (gcall-move dc ec nc fc rc as0 as xs1 lf kl0 kl rest)))))

(def-fns _ $ (erased gcok-move : (erased (Nat) dc) (erased (List (Nat)) ec nc fc rc as0 as) (erased (Length (Nat) fc dc) lf) (erased (KernelList dc fc rc as0) kl0)
    (erased (KernelList dc fc rc as) kl) (erased (GcOK dc ec nc rc as0) ok) -> (erased (GcOK dc ec nc rc as) r))
  (let-match erased ok (MkGcOK _ _ _ _ _ ids io ga))
  (MkGcOK dc ec nc rc as ids io (gcall-move dc ec nc fc rc as0 as ids lf kl0 kl ga)))

; What a run decides of a configuration of red/configs.sl on the map cpmap.sl builds: its kernel as, the conditions GcOK, and
; for each kernel dart whose edge image is in the kernel a refutation of it not being central, with fid labelling the faces.
(def-adts $ (CfGc : ((Config) cf) -> Type)
  enum
  (many MkCfGc : (erased (Bool) sym) (erased (List (Nat)) cci) (erased (List (Step)) cp) (erased (Nat) dc) (erased (List (Nat)) ec nc fc rc as fid)
      (erased (Cpmap cp dc ec fc rc) cm) (erased (Hypermap dc ec nc fc) hc) (erased (KernelList dc fc rc as) kl) (erased (GcOK dc ec nc rc as) ok)
      (erased (Respects fid fc fid) rf) (erased (FAll ec nc fid as as) fa) -> (CfGc (MkConfig sym cci cp))))

(def-adts $ (AllGc : ((List (Config)) cfs) -> Type)
  enum
  (many AgNil : -> (AllGc (Nil (Config))))
  (many AgCons : (erased (List (Config)) cfs) (erased (Config) cf) (erased (CfGc cf) c) (erased (AllGc cfs) rest) -> (AllGc (Cons (Config) cf cfs))))

(def-fns _ $ (erased gc-lookup : (erased (List (Config)) cfs) (erased (Config) cf) (subterm erased (AllGc cfs) a) (erased (Mem (Config) cf cfs) m) -> (erased (CfGc cf) r))
  (let-match erased a (AgCons cfs1 cf1 c1 a1) (absurd (AgNil) m))
  (match erased m _ ((MemHere _ _ _) c1) ((MemThere _ _ _ _ m1) (gc-lookup cfs1 cf a1 m1))))

(def-fns _ $ (erased cfgc-at : (erased (Bool) sym) (erased (List (Nat)) cci) (erased (List (Step)) cp) (erased (Nat) dc) (erased (List (Nat)) ec nc fc rc)
    (erased (CfGc (MkConfig sym cci cp)) c) (erased (Cpmap cp dc ec fc rc) cm) (erased (Hypermap dc ec nc fc) h)
    -> (erased (List (Nat)) as0 fid) (erased (KernelList dc fc rc as0) kl0) (erased (GcOK dc ec nc rc as0) ok0) (erased (Respects fid fc fid) rf)
    (erased (FAll ec nc fid as0 as0) fa))
  (let-match erased c (MkCfGc _ _ _ dc0 ec0 nc0 fc0 rc0 as0 fid cm0 hc0 kl0 ok0 rf fa))
  (let-match erased (cpmap-fn cp dc0 dc ec0 fc0 rc0 ec fc rc cm0 cm) (Refl _ _))
  (let-match erased (hyper-node-unique dc ec nc0 fc nc hc0 h) (Refl _ _))
  (values as0 fid kl0 ok0 rf fa))

; GcOK for any kernel list of a configuration of cfs, on the map cpmap.sl builds.
(def-fns _ $ (erased cf-gcok : (erased (List (Config)) cfs) (erased (Bool) sym) (erased (List (Nat)) cci) (erased (List (Step)) cp) (erased (Nat) dc)
    (erased (List (Nat)) ec nc fc rc as) (erased (AllGc cfs) ag) (erased (Mem (Config) (MkConfig sym cci cp) cfs) m) (erased (Cpmap cp dc ec fc rc) cm)
    (erased (Hypermap dc ec nc fc) h) (erased (KernelList dc fc rc as) kl) -> (erased (GcOK dc ec nc rc as) r))
  (let ((erased as0) (erased fid) (erased kl0) (erased ok0) (erased rf) (erased fa)) (cfgc-at sym cci cp dc ec nc fc rc (gc-lookup cfs (MkConfig sym cci cp) ag m) cm h))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths dc ec nc fc h))
  (gcok-move dc ec nc fc rc as0 as lf kl0 kl ok0))

; embed_functor: FunctorAll for an EEnv on the map cpmap.sl builds of a configuration of cfs.
(def-fns _ $ (erased cf-functor : (erased (List (Config)) cfs) (erased (Bool) sym) (erased (List (Nat)) cci) (erased (List (Step)) cp) (erased (Nat) dc dm)
    (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl) (erased (AllGc cfs) ag) (erased (Mem (Config) (MkConfig sym cci cp) cfs) m) (erased (Cpmap cp dc ec fc rc) cm)
    (erased (EEnv dc ec nc fc ksc rc dm em nm fm ksm as hl) en) -> (erased (FunctorAll ec em as hl as) r))
  (let ((erased en2)) en)
  (let-match erased en2 (MkEEnv _ _ _ _ _ _ _ _ _ _ _ _ _ hc olc kl g pe))
  (let ((erased as0) (erased fid) (erased kl0) (erased ok0) (erased rf) (erased fa)) (cfgc-at sym cci cp dc ec nc fc rc (gc-lookup cfs (MkConfig sym cci cp) ag m) cm hc))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths dc ec nc fc hc))
  (let ((erased fe)) (MkFEnv dc ec nc fc ksc rc dm em nm fm ksm as hl as0 fid en kl0 (gcok-move dc ec nc fc rc as0 as lf kl0 kl ok0) rf))
  (functor-list dc dm ec nc fc ksc rc em nm fm ksm as hl as0 fid fe fa as (ia-self as)))

; The run. The kernel is labelled by a face walk to the ring; the refutations are found by a search on the statuses of the
; kernel darts (unknown, not central, central) that applies node-rule, splits on a dart, or closes with a cut of the kernel
; faces whose crossing darts are all not central, found by a flood fill over the other kernel edges.

(def-adts $ (KerOK : ((List (Nat)) f r as xs) -> Type)
  enum
  (many MkKerOK : (erased (List (Nat)) f r as xs) (erased (KerAll f r as) ka) (erased (KerCover f r as xs) kv) -> (KerOK f r as xs)))

(def-fns _ $ (erased kv-weaken : (erased (List (Nat)) f r as xs) (erased (Nat) y) (subterm erased (KerCover f r as xs) kv) -> (erased (KerCover f r (Cons (Nat) y as) xs) res))
  (match erased kv _
    ((KvNil _ _ _) (KvNil f r (Cons (Nat) y as)))
    ((KvIn _ _ _ xs1 x i kv1) (KvIn f r (Cons (Nat) y as) xs1 x (InThere x y as i) (kv-weaken f r as xs1 y kv1)))
    ((KvBand _ _ _ xs1 x b kv1) (KvBand f r (Cons (Nat) y as) xs1 x b (kv-weaken f r as xs1 y kv1)))))

(def-fns _ $ (many klab-c : (many (Nat) d) (many (List (Nat)) fc rc) (subterm many (List (Nat)) xs) -> (many (List (Nat)) lab))
  (let-match many xs (Cons _ x rest) ((Nil _) (Nil _)))
  (Cons _ (match many (fband-q fc rc x d) (((Nat) k)) ((ChkYes _ _) (Zero)) ((ChkNo _) (Succ (Zero)))) $ notail $ klab-c d fc rc rest))

(def-fns _ $ (many kern-c : (many (Nat) d) (many (List (Nat)) fc rc lab lr) (erased (Respects lab fc lab) rf) (erased (Respects lab rc lr) rp)
    (erased (NotIn (Succ (Zero)) lr) out) (subterm many (List (Nat)) xs) -> (many (List (Nat)) as) (many (Checked (KerOK fc rc as xs)) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (values (Nil _) (ChkYes _ (MkKerOK fc rc (Nil _) (Nil _) (KANil fc rc) (KvNil fc rc (Nil _)))))))
  (let ((many as1) (many c1)) (notail $ kern-c d fc rc lab lr rf rp out rest))
  (let-match many c1 (ChkYes _ ko) ((ChkNo _) (values (Nil _) (ChkNo _))))
  (let-match erased ko (MkKerOK _ _ _ _ ka kv))
  (let-match many (nat-at lab x (Succ (Zero))) (ChkNo _)
    ((ChkYes _ px)
      (values (Cons _ x as1) (ChkYes _ (MkKerOK fc rc (Cons _ x as1) xs (KACons fc rc as1 x (MkKernel fc rc lab lr x (Succ (Zero)) rf rp px out) ka)
        (KvIn fc rc (Cons _ x as1) rest x (InHere x as1) (kv-weaken fc rc as1 rest x kv)))))))
  (let-match many (fband-q fc rc x d) (ChkYes _ fb) ((ChkNo _) (values (Nil _) (ChkNo _))))
  (values as1 (ChkYes _ (MkKerOK fc rc as1 xs ka (KvBand fc rc as1 rest x fb kv)))))

(def-fns _ $ (many rs-off : (many (List (Nat)) nc rc) (many (Nat) x nx nnx) (erased (NotIn x rc) ox) (erased (Nth (Nat) nc nx nnx) pnn)
    -> (many (Checked (RingSide nc rc x nx)) r))
  (let-match many (in-q nx rc) (IQOut _ _ onx) ((IQIn _ _ _) (ChkNo _)))
  (let-match many (nat-at nc nnx x) (ChkYes _ p2) ((ChkNo _) (ChkNo _)))
  (ChkYes _ (RsOff nc rc x nx nnx ox onx pnn p2)))

(def-fns _ $ (many rs-c : (many (List (Nat)) nc rc) (many (Nat) x nx) -> (many (Checked (RingSide nc rc x nx)) r))
  (let-match many (nth-q (Nat) nc nx) (NQYes _ _ _ nnx pnn) ((NQNo _ _ _) (ChkNo _)))
  (match many (in-q x rc) _
    ((IQIn _ _ ix) (match many (in-q nx rc) _ ((IQIn _ _ inx) (ChkYes _ (RsOn nc rc x nx ix inx))) ((IQOut _ _ _) (ChkNo _))))
    ((IQOut _ _ ox) (rs-off nc rc x nx nnx ox pnn))))

(def-fns _ $ (many ep-c : (many (List (Nat)) rc) (many (Nat) x ex) -> (many (Checked (Or (NotIn x rc) (NotIn ex rc))) r))
  (let-match many (in-q x rc) (IQIn _ _ _) ((IQOut _ _ o) (ChkYes _ (OrL _ _ o))))
  (let-match many (in-q ex rc) (IQOut _ _ o) ((IQIn _ _ _) (ChkNo _)))
  (ChkYes _ (OrR _ _ o)))

(def-fns _ $ (many cl-c : (many (List (Nat)) rc as) (many (Nat) x ex) -> (many (Checked (Or (In x rc) (Or (In ex rc) (Or (In x as) (In ex as))))) r))
  (let-match many (in-q x rc) (IQOut _ _ _) ((IQIn _ _ i) (ChkYes _ (OrL _ _ i))))
  (let-match many (in-q ex rc) (IQOut _ _ _) ((IQIn _ _ i) (ChkYes _ (OrR _ _ (OrL _ _ i)))))
  (let-match many (in-q x as) (IQOut _ _ _) ((IQIn _ _ i) (ChkYes _ (OrR _ _ (OrR _ _ (OrL _ _ i))))))
  (let-match many (in-q ex as) (IQIn _ _ i) ((IQOut _ _ _) (ChkNo _)))
  (ChkYes _ (OrR _ _ (OrR _ _ (OrR _ _ i)))))

(def-fns _ $ (many cs-c : (many (List (Nat)) nc as) (many (Nat) x ex nx z) (erased (Nth (Nat) nc ex z) pz)
    -> (many (Checked (Or (In x as) (Or (In ex as) (Or (In nx as) (NodeIn nc as ex))))) r))
  (let-match many (in-q x as) (IQOut _ _ _) ((IQIn _ _ i) (ChkYes _ (OrL _ _ i))))
  (let-match many (in-q ex as) (IQOut _ _ _) ((IQIn _ _ i) (ChkYes _ (OrR _ _ (OrL _ _ i)))))
  (let-match many (in-q nx as) (IQOut _ _ _) ((IQIn _ _ i) (ChkYes _ (OrR _ _ (OrR _ _ (OrL _ _ i))))))
  (let-match many (in-q z as) (IQIn _ _ i) ((IQOut _ _ _) (ChkNo _)))
  (ChkYes _ (OrR _ _ (OrR _ _ (OrR _ _ (MkNodeIn nc as ex z pz i))))))

(def-fns _ $ (many gcat-c : (many (List (Nat)) ec nc rc as) (many (Nat) x) -> (many (Checked (GcAt ec nc rc as x)) r))
  (let-match many (nth-q (Nat) ec x) (NQYes _ _ _ ex pe) ((NQNo _ _ _) (ChkNo _)))
  (let-match many (nat-at ec ex x) (ChkYes _ pe2) ((ChkNo _) (ChkNo _)))
  (let-match many (nth-q (Nat) nc x) (NQYes _ _ _ nx pn) ((NQNo _ _ _) (ChkNo _)))
  (let-match many (nth-q (Nat) nc ex) (NQYes _ _ _ z pz) ((NQNo _ _ _) (ChkNo _)))
  (let-match many (rs-c nc rc x nx) (ChkYes _ rs) ((ChkNo _) (ChkNo _)))
  (let-match many (ep-c rc x ex) (ChkYes _ ep) ((ChkNo _) (ChkNo _)))
  (let-match many (cl-c rc as x ex) (ChkYes _ cl) ((ChkNo _) (ChkNo _)))
  (let-match many (cs-c nc as x ex nx z pz) (ChkYes _ cs) ((ChkNo _) (ChkNo _)))
  (ChkYes _ (MkGcAt ec nc rc as x ex nx pe pe2 pn rs ep cl cs)))

(def-fns _ $ (many gcall-c : (many (List (Nat)) ec nc rc as) (subterm many (List (Nat)) xs) -> (many (Checked (GcAll ec nc rc as xs)) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (ChkYes _ (GcNil ec nc rc as))))
  (let-match many (gcat-c ec nc rc as x) (ChkYes _ g) ((ChkNo _) (ChkNo _)))
  (let-match many (notail $ gcall-c ec nc rc as rest) (ChkYes _ gr) ((ChkNo _) (ChkNo _)))
  (ChkYes _ (GcCons ec nc rc as rest x g gr)))

(def-fns _ $ (many face-min : (many (List (Nat)) f) (many (Nat) x y m) (subterm many (Nat) left) -> (many (Nat) r))
  (let-match many left (Succ l1) ((Zero) m))
  (let ((many z)) (get-at _ f y 0))
  (match many (nat-eqb z x) _
    ((BTrue) m)
    ((BFalse) (tail $ face-min f x z (bif _ (nat-ltb z m) z m) l1))))

(def-fns _ $ (many fid-c : (many (List (Nat)) f) (many (Nat) d) (subterm many (List (Nat)) xs) -> (many (List (Nat)) fid))
  (let-match many xs (Cons _ x rest) ((Nil _) (Nil _)))
  (Cons _ (face-min f x x x d) $ notail $ fid-c f d rest))

(def-fns _ $ (erased tri-rot : (erased (List (Nat)) ec nc as) (erased (Nat) a b c) (erased (Tri ec nc as a b c) t) -> (erased (Tri ec nc as b c a) r))
  (let-match erased t (MkTri _ _ _ _ _ _ ea eb ecc pab pbc pca pa pb pcc ia ib ic iea ieb iec))
  (MkTri ec nc as b c a eb ecc ea pbc pca pab pb pcc pa ib ic ia ieb iec iea))

(def-adts $ (TriD : ((List (Nat)) ec nc as) -> Type)
  enum
  (many MkTriD : (erased (List (Nat)) ec nc as) (many (Nat) a b c ea eb ecc) (erased (Tri ec nc as a b c) t) (erased (Nth (Nat) ec a ea) pa)
      (erased (Nth (Nat) ec b eb) pb) (erased (Nth (Nat) ec c ecc) pcc) (erased (In a as) ia) (erased (In b as) ib) (erased (In c as) ic)
      (erased (In ea as) iea) (erased (In eb as) ieb) (erased (In ecc as) iec) -> (TriD ec nc as)))

; The three rotations of the node of a, when a is its least dart and the node and its edge images are in the kernel.
(def-fns _ $ (many tri3-c : (many (List (Nat)) ec nc as) (many (Nat) a) -> (many (List (TriD ec nc as)) ts))
  (let ((many (List (TriD ec nc as)) no)) (Nil _))
  (let-match many (nth-q (Nat) nc a) (NQYes _ _ _ b pab) ((NQNo _ _ _) no))
  (let-match many (nth-q (Nat) nc b) (NQYes _ _ _ c pbc) ((NQNo _ _ _) no))
  (let-match many (nat-at nc c a) (ChkYes _ pca) ((ChkNo _) no))
  (let-match many (andb (nat-ltb a b) (nat-ltb a c)) (BTrue) ((BFalse) no))
  (let-match many (nth-q (Nat) ec a) (NQYes _ _ _ ea pa) ((NQNo _ _ _) no))
  (let-match many (nth-q (Nat) ec b) (NQYes _ _ _ eb pb) ((NQNo _ _ _) no))
  (let-match many (nth-q (Nat) ec c) (NQYes _ _ _ ecc pcc) ((NQNo _ _ _) no))
  (let-match many (in-q a as) (IQIn _ _ ia) ((IQOut _ _ _) no))
  (let-match many (in-q b as) (IQIn _ _ ib) ((IQOut _ _ _) no))
  (let-match many (in-q c as) (IQIn _ _ ic) ((IQOut _ _ _) no))
  (let-match many (in-q ea as) (IQIn _ _ iea) ((IQOut _ _ _) no))
  (let-match many (in-q eb as) (IQIn _ _ ieb) ((IQOut _ _ _) no))
  (let-match many (in-q ecc as) (IQIn _ _ iec) ((IQOut _ _ _) no))
  (let ((erased t)) (MkTri ec nc as a b c ea eb ecc pab pbc pca pa pb pcc ia ib ic iea ieb iec))
  (let ((erased t2)) (tri-rot ec nc as a b c t))
  (Cons _ (MkTriD ec nc as a b c ea eb ecc t pa pb pcc ia ib ic iea ieb iec) $ Cons _ (MkTriD ec nc as b c a eb ecc ea t2 pb pcc pa ib ic ia ieb iec iea) $
    Cons _ (MkTriD ec nc as c a b ecc ea eb (tri-rot ec nc as b c a t2) pcc pa pb ic ia ib iec iea ieb) $ Nil _))

(def-fns _ $ (many tris-c : (many (List (Nat)) ec nc as) (subterm many (List (Nat)) xs) -> (many (List (TriD ec nc as)) ts))
  (let-match many xs (Cons _ x rest) ((Nil _) (Nil _)))
  (cat _ (tri3-c ec nc as x) $ notail $ tris-c ec nc as rest))

(def-adts $ (KEdge : -> Type)
  enum
  (many MkKEdge : (many (Nat) z y) -> (KEdge)))

(def-fns _ $ (many kes-c : (many (List (Nat)) ec as) (subterm many (List (Nat)) xs) -> (many (List (KEdge)) ks))
  (let-match many xs (Cons _ x rest) ((Nil _) (Nil _)))
  (let ((many y)) (get-at _ ec x 0))
  (let ((many ks)) (notail $ kes-c ec as rest))
  (bif _ (andb (mem-nat y as) (nat-ltb x y)) (Cons _ (MkKEdge x y) ks) ks))

(def-fns _ $ (many ein-c : (erased (List (Nat)) ec) (many (Nat) z y) (erased (Nth (Nat) ec z y) py) (many (List (Nat)) l) -> (many (Checked (EIn ec l z)) r))
  (let-match many (in-q z l) (IQOut _ _ _) ((IQIn _ _ i) (ChkYes _ (EiHere ec l z i))))
  (let-match many (in-q y l) (IQIn _ _ i) ((IQOut _ _ _) (ChkNo _)))
  (ChkYes _ (EiEdge ec l z y py i)))

(def-fns _ $ (erased ein-weaken : (erased (List (Nat)) ec l) (erased (Nat) z w) (erased (EIn ec l z) i) -> (erased (EIn ec (Cons (Nat) w l) z) r))
  (match erased i _
    ((EiHere _ _ _ p) (EiHere ec (Cons (Nat) w l) z (InThere z w l p)))
    ((EiEdge _ _ _ y py p) (EiEdge ec (Cons (Nat) w l) z y py (InThere y w l p)))))

(def-fns _ $ (many st-c : (many (Nat) z y) (many (List (Nat)) ns cs) -> (many (Nat) s))
  (bif _ (orb (mem-nat z ns) (mem-nat y ns)) 1 (bif _ (orb (mem-nat z cs) (mem-nat y cs)) 2 0)))

; Mode 0: a not central-known, b and c central; 1: a not central, b central, c unknown; 2: a not central, b and c unknown.
(def-fns _ $ (many fits : (many (Nat) mode sa sb sc) -> (many (Bool) r))
  (match many (nat-eqb mode 0) _
    ((BTrue) (andb (negb (nat-eqb sa 2)) (andb (nat-eqb sb 2) (nat-eqb sc 2))))
    ((BFalse) (andb (nat-eqb sa 1) (andb (nat-eqb sb (bif _ (nat-eqb mode 1) 2 0)) (nat-eqb sc 0))))))

(def-fns _ $ (many scan-c : (erased (List (Nat)) ec nc as) (many (Nat) mode) (many (List (Nat)) ns cs) (subterm many (List (TriD ec nc as)) ts)
    -> (many (Maybe (TriD ec nc as)) r))
  (let-match many ts (Cons _ td rest) ((Nil _) (None _)))
  (let-match many td (MkTriD _ _ _ a b c ea eb ecc _ _ _ _ _ _ _ _ _ _))
  (match many (fits mode (st-c a ea ns cs) (st-c b eb ns cs) (st-c c ecc ns cs)) _
    ((BTrue) (Some _ td))
    ((BFalse) (tail $ scan-c ec nc as mode ns cs rest))))

(def-fns _ $ (many alive-c : (many (List (Nat)) ns) (subterm many (List (KEdge)) ks) -> (many (List (KEdge)) r))
  (let-match many ks (Cons _ k rest) ((Nil _) (Nil _)))
  (let-match many k (MkKEdge z y))
  (let ((many r1)) (notail $ alive-c ns rest))
  (bif _ (orb (mem-nat z ns) (mem-nat y ns)) r1 (Cons _ k r1)))

(def-fns _ $ (many flood-pass : (many (List (Nat)) fid lab) (many (Bool) ch) (subterm many (List (KEdge)) ks) -> (many (List (Nat)) lab2) (many (Bool) ch2))
  (let-match many ks (Cons _ k rest) ((Nil _) (values lab ch)))
  (let-match many k (MkKEdge z y))
  (let ((many fz) (many fy)) (values (get-at _ fid z 0) (get-at _ fid y 0)))
  (match many (nat-eqb (get-at _ lab fz 0) (get-at _ lab fy 0)) _
    ((BTrue) (tail $ flood-pass fid lab ch rest))
    ((BFalse) (tail $ flood-pass fid (set-at _ (set-at _ lab fz 1) fy 1) (BTrue) rest))))

(def-fns _ $ (many flood : (many (List (Nat)) fid lab) (many (List (KEdge)) ks) (subterm many (Nat) fuel) -> (many (List (Nat)) lab2))
  (let-match many fuel (Succ f1) ((Zero) lab))
  (let ((many lab1) (many ch)) (flood-pass fid lab (BFalse) ks))
  (match many ch _ ((BTrue) (tail $ flood fid lab1 ks f1)) ((BFalse) lab1)))

(def-fns _ $ (many first-zero : (many (List (Nat)) fid lab) (subterm many (List (Nat)) xs) -> (many (Maybe (Nat)) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (None _)))
  (match many (nat-eqb (get-at _ lab (get-at _ fid x 0) 0) 0) _ ((BTrue) (Some _ x)) ((BFalse) (tail $ first-zero fid lab rest))))

(def-adts $ (Plan : ((List (Nat)) ec nc as) -> Type)
  enum
  (many PlNode : (erased (List (Nat)) ec nc as) (many (TriD ec nc as) t) -> (Plan ec nc as))
  (many PlSplitC : (erased (List (Nat)) ec nc as) (many (TriD ec nc as) t) -> (Plan ec nc as))
  (many PlSplit : (erased (List (Nat)) ec nc as) (many (TriD ec nc as) t) -> (Plan ec nc as))
  (many PlCut : (erased (List (Nat)) ec nc as) (many (List (Nat)) lab) (many (Nat) y) -> (Plan ec nc as))
  (many PlNone : (erased (List (Nat)) ec nc as) -> (Plan ec nc as)))

(def-fns _ $ (many plan-c : (many (Nat) d) (many (List (Nat)) fid as) (erased (List (Nat)) ec nc) (many (List (TriD ec nc as)) ts) (many (List (KEdge)) kes)
    (many (List (Nat)) ns cs) -> (many (Plan ec nc as) p))
  (let-match many (scan-c ec nc as 0 ns cs ts) (None _) ((Some _ td) (PlNode ec nc as td)))
  (let-match many (scan-c ec nc as 1 ns cs ts) (None _) ((Some _ td) (PlSplitC ec nc as td)))
  (let-match many as (Cons _ x0 _) ((Nil _) (PlNone ec nc as)))
  (let ((many lab)) (flood fid (set-at _ (nseq _ d 0) (get-at _ fid x0 0) 1) (alive-c ns kes) d))
  (let-match many (first-zero fid lab as) (None _) ((Some _ y) (PlCut ec nc as lab y)))
  (match many (scan-c ec nc as 2 ns cs ts) _ ((Some _ td) (PlSplit ec nc as td)) ((None _) (PlNone ec nc as))))

(def-fns _ $ (many labat-c : (many (List (Nat)) fid lab) (many (Nat) x k) -> (many (Checked (LabAt fid lab x k)) r))
  (let-match many (nth-q (Nat) fid x) (NQYes _ _ _ i pi) ((NQNo _ _ _) (ChkNo _)))
  (let-match many (nat-at lab i k) (ChkYes _ pk) ((ChkNo _) (ChkNo _)))
  (ChkYes _ (MkLabAt fid lab x k i pi pk)))

(def-fns _ $ (many cross-c : (many (List (Nat)) ec as fid lab ns) (subterm many (List (Nat)) xs) -> (many (Checked (CrossAll ec as fid lab ns xs)) r))
  (let-match many xs (Cons _ z rest) ((Nil _) (ChkYes _ (CaNil ec as fid lab ns))))
  (let-match many (notail $ cross-c ec as fid lab ns rest) (ChkYes _ cr) ((ChkNo _) (ChkNo _)))
  (let-match many (labat-c fid lab z (Zero)) (ChkNo _) ((ChkYes _ l0) (ChkYes _ (CaCons ec as fid lab ns rest z (CxZero ec as fid lab ns z l0) cr))))
  (let-match many (nth-q (Nat) ec z) (NQYes _ _ _ y py) ((NQNo _ _ _) (ChkNo _)))
  (let-match many (in-q y as) (IQIn _ _ _) ((IQOut _ _ o) (ChkYes _ (CaCons ec as fid lab ns rest z (CxOut ec as fid lab ns z y py o) cr))))
  (let-match many (labat-c fid lab y (Succ (Zero))) (ChkNo _) ((ChkYes _ l1) (ChkYes _ (CaCons ec as fid lab ns rest z (CxSame ec as fid lab ns z y py l1) cr))))
  (let-match many (ein-c ec z y py ns) (ChkYes _ i) ((ChkNo _) (ChkNo _)))
  (ChkYes _ (CaCons ec as fid lab ns rest z (CxNon ec as fid lab ns z i) cr)))

(def-fns _ $ (many refute-c : (many (Nat) d) (many (List (Nat)) ec fid as) (erased (List (Nat)) nc) (many (List (TriD ec nc as)) ts) (many (List (KEdge)) kes)
    (many (List (Nat)) ns cs) (subterm many (Nat) fuel) -> (many (Checked (Refut ec nc fid as ns cs)) r))
  (let-match many fuel (Succ fuel1) ((Zero) (ChkNo _)))
  (match many (plan-c d fid as ec nc ts kes ns cs) _
    ((PlNode _ _ _ td)
      (let-match many td (MkTriD _ _ _ a b c ea eb ecc t pa pb pcc ia ib ic iea ieb iec))
      (let-match many (ein-c ec b eb pb cs) (ChkYes _ ibc) ((ChkNo _) (ChkNo _)))
      (let-match many (ein-c ec c ecc pcc cs) (ChkYes _ icc) ((ChkNo _) (ChkNo _)))
      (let-match many (ein-c ec a ea pa ns) (ChkNo _)
        ((ChkYes _ ian) (ChkYes _ (RfNode ec nc fid as ns cs a b c t ibc icc (RfConf ec nc fid as ns (Cons _ a cs) a ia ian (EiHere ec (Cons _ a cs) a (InHere a cs)))))))
      (let-match many (notail $ refute-c d ec fid as nc ts kes ns (Cons _ a cs) fuel1) (ChkYes _ r1) ((ChkNo _) (ChkNo _)))
      (ChkYes _ (RfNode ec nc fid as ns cs a b c t ibc icc r1)))
    ((PlSplitC _ _ _ td)
      (let-match many td (MkTriD _ _ _ a b c ea eb ecc t pa pb pcc ia ib ic iea ieb iec))
      (let-match many (ein-c ec a ea pa ns) (ChkYes _ ian) ((ChkNo _) (ChkNo _)))
      (let-match many (ein-c ec b eb pb cs) (ChkYes _ ibc) ((ChkNo _) (ChkNo _)))
      (let-match many (notail $ refute-c d ec fid as nc ts kes (Cons _ c ns) cs fuel1) (ChkYes _ r1) ((ChkNo _) (ChkNo _)))
      (let ((erased cs2)) (Cons (Nat) c cs))
      (ChkYes _ (RfSplit ec nc fid as ns cs c ecc pcc ic iec r1
        (RfNode ec nc fid as ns cs2 a b c t (ein-weaken ec cs b c ibc) (EiHere ec cs2 c (InHere c cs))
          (RfConf ec nc fid as ns (Cons (Nat) a cs2) a ia ian (EiHere ec (Cons (Nat) a cs2) a (InHere a cs2)))))))
    ((PlSplit _ _ _ td)
      (let-match many td (MkTriD _ _ _ a b c ea eb ecc t pa pb pcc ia ib ic iea ieb iec))
      (let-match many (notail $ refute-c d ec fid as nc ts kes (Cons _ b ns) cs fuel1) (ChkYes _ r1) ((ChkNo _) (ChkNo _)))
      (let-match many (notail $ refute-c d ec fid as nc ts kes ns (Cons _ b cs) fuel1) (ChkYes _ r2) ((ChkNo _) (ChkNo _)))
      (ChkYes _ (RfSplit ec nc fid as ns cs b eb pb ib ieb r1 r2)))
    ((PlCut _ _ _ lab y)
      (let-match many as (Cons _ x0 as1) ((Nil _) (ChkNo _)))
      (let-match many (labat-c fid lab x0 (Succ (Zero))) (ChkYes _ lx) ((ChkNo _) (ChkNo _)))
      (let-match many (in-q y as) (IQIn _ _ iy) ((IQOut _ _ _) (ChkNo _)))
      (let-match many (labat-c fid lab y (Zero)) (ChkYes _ ly) ((ChkNo _) (ChkNo _)))
      (let-match many (cross-c ec as fid lab ns as) (ChkYes _ ca) ((ChkNo _) (ChkNo _)))
      (ChkYes _ (RfCut ec nc fid as ns cs lab x0 y (InHere x0 as1) lx iy ly ca)))
    ((PlNone _ _ _) (ChkNo _))))

(def-fns _ $ (many fall-c : (many (Nat) d) (many (List (Nat)) ec fid as) (erased (List (Nat)) nc) (many (List (TriD ec nc as)) ts) (many (List (KEdge)) kes)
    (subterm many (List (Nat)) xs) -> (many (Checked (FAll ec nc fid as xs)) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (ChkYes _ (FsNil ec nc fid as))))
  (let-match many (notail $ fall-c d ec fid as nc ts kes rest) (ChkYes _ fr) ((ChkNo _) (ChkNo _)))
  (let-match many (nth-q (Nat) ec x) (NQYes _ _ _ y py) ((NQNo _ _ _) (ChkNo _)))
  (let-match many (in-q y as) (IQIn _ _ _) ((IQOut _ _ o) (ChkYes _ (FsCons ec nc fid as rest x (FaOut ec nc fid as x y py o) fr))))
  (let-match many (refute-c d ec fid as nc ts kes (Cons _ x (Nil _)) (Nil _) (Succ d)) (ChkYes _ rr) ((ChkNo _) (ChkNo _)))
  (ChkYes _ (FsCons ec nc fid as rest x (FaRef ec nc fid as x rr) fr)))

(def-fns _ $ (many cfgc-c : (many (Config) cf) -> (many (Checked (CfGc cf)) r))
  (let-match many cf (MkConfig sym cci cp))
  (let-match many (noa-dec cp) (NoAYes _ na) ((NoANo _) (ChkNo _)))
  (let ((many d) (many e) (many f) (many r) (erased c)) (cpmap-c cp na))
  (let-match many (resp-q f e) (RQYes _ _ fe _) ((RQNo _ _) (ChkNo _)))
  (let ((many n)) (inv-from fe 0 d))
  (let ((many ids) (erased io)) (iota-c d))
  (let-match many (hyper-c d e n f ids io) (ChkYes _ hc) ((ChkNo _) (ChkNo _)))
  (let ((many lab)) (klab-c d f r ids))
  (let-match many (resp-to lab f lab) (ChkYes _ rf) ((ChkNo _) (ChkNo _)))
  (let-match many (resp-q lab r) (RQYes _ _ lr rp) ((RQNo _ _) (ChkNo _)))
  (let-match many (in-q (Succ (Zero)) lr) (IQOut _ _ out) ((IQIn _ _ _) (ChkNo _)))
  (let ((many as) (many ck)) (kern-c d f r lab lr rf rp out ids))
  (let-match many ck (ChkYes _ ko) ((ChkNo _) (ChkNo _)))
  (let-match erased ko (MkKerOK _ _ _ _ ka kv))
  (let-match many (gcall-c e n r as ids) (ChkYes _ ga) ((ChkNo _) (ChkNo _)))
  (let ((many fid)) (fid-c f d ids))
  (let-match many (resp-to fid f fid) (ChkYes _ rsp) ((ChkNo _) (ChkNo _)))
  (let-match many (fall-c d e fid as n (tris-c e n as as) (kes-c e as as) as) (ChkYes _ fa) ((ChkNo _) (ChkNo _)))
  (ChkYes _ (MkCfGc sym cci cp d e n f r as fid c hc (MkKernelList d f r as ids io ka kv) (MkGcOK d e n r as ids io ga) rsp fa)))

(def-fns _ $ (many allgc-c : (subterm many (List (Config)) cfs) -> (many (Checked (AllGc cfs)) r))
  (let-match many cfs (Cons _ cf rest) ((Nil _) (ChkYes _ (AgNil))))
  (let-match many (cfgc-c cf) (ChkYes _ c) ((ChkNo _) (ChkNo _)))
  (let-match many (notail $ allgc-c rest) (ChkYes _ a) ((ChkNo _) (ChkNo _)))
  (ChkYes _ (AgCons rest cf c a)))
