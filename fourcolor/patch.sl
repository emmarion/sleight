; Patching two maps to cover a larger one, after patch.v. The disk map (ed, nd, fd) and the remainder map (er, nr, fr)
; live on the darts 0..d-1 of the whole map (e, n, f), each with the darts of the other's inside kept as dead darts that
; its three permutations fix, in place of patch.v's injections hd and hr. Load after kempemap.sl.

(def-adts $ (Part : -> Type)
  enum
  (many PDisk : -> (Part))
  (many PRing : -> (Part))
  (many PRest : -> (Part)))

; The dart x in the part sd gives it: inside the disk, e and n are ed and nd and the remainder map fixes x; on the
; ring r, n is nd, e is er, and nr sends ed x back to x; in the rest, e and n are er and nr and the disk map fixes x.
(def-adts $ (PatchDart : ((List (Part)) sd) ((List (Nat)) e n ed nd er nr r) ((Nat) x) -> Type)
  enum
  (many PtDisk : (erased (List (Part)) sd) (erased (List (Nat)) e n ed nd er nr r) (erased (Nat) x a b)
      (erased (Nth (Part) sd x (PDisk)) ps) (erased (NotIn x r) out) (erased (Nth (Nat) e x a) pe) (erased (Nth (Nat) ed x a) ped)
      (erased (Nth (Nat) n x b) pn) (erased (Nth (Nat) nd x b) pnd) (erased (Nth (Nat) er x x) per) (erased (Nth (Nat) nr x x) pnr)
      -> (PatchDart sd e n ed nd er nr r x))
  (many PtRing : (erased (List (Part)) sd) (erased (List (Nat)) e n ed nd er nr r) (erased (Nat) x a b c)
      (erased (Nth (Part) sd x (PRing)) ps) (erased (In x r) pin) (erased (Nth (Nat) e x a) pe) (erased (Nth (Nat) er x a) per)
      (erased (Nth (Nat) n x b) pn) (erased (Nth (Nat) nd x b) pnd) (erased (Nth (Nat) ed x c) ped) (erased (Nth (Nat) nr c x) pnr)
      -> (PatchDart sd e n ed nd er nr r x))
  (many PtRest : (erased (List (Part)) sd) (erased (List (Nat)) e n ed nd er nr r) (erased (Nat) x a b)
      (erased (Nth (Part) sd x (PRest)) ps) (erased (NotIn x r) out) (erased (Nth (Nat) e x a) pe) (erased (Nth (Nat) er x a) per)
      (erased (Nth (Nat) n x b) pn) (erased (Nth (Nat) nr x b) pnr) (erased (Nth (Nat) ed x x) ped) (erased (Nth (Nat) nd x x) pnd)
      -> (PatchDart sd e n ed nd er nr r x)))

(def-adts $ (PatchDarts : ((List (Part)) sd) ((List (Nat)) e n ed nd er nr r xs) -> Type)
  enum
  (many PDNil : (erased (List (Part)) sd) (erased (List (Nat)) e n ed nd er nr r) -> (PatchDarts sd e n ed nd er nr r (Nil (Nat))))
  (many PDCons : (erased (List (Part)) sd) (erased (List (Nat)) e n ed nd er nr r xs) (erased (Nat) x)
      (erased (PatchDart sd e n ed nd er nr r x) p) (erased (PatchDarts sd e n ed nd er nr r xs) rest)
      -> (PatchDarts sd e n ed nd er nr r (Cons (Nat) x xs))))

; r is empty or a cycle of ed on distinct faces of fd (sfcycle edge).
(def-adts $ (ECycle : ((List (Nat)) ed fd r) -> Type)
  enum
  (many ECNil : (erased (List (Nat)) ed fd) -> (ECycle ed fd (Nil (Nat))))
  (many ECCons : (erased (List (Nat)) ed fd p) (erased (Nat) x) (erased (SCycle ed fd x p) c) -> (ECycle ed fd (Cons (Nat) x p))))

; patch: (e, n, f) is the disk map glued to the remainder map along the ring r, the darts parted by sd.
(def-adts $ (Patch : ((Nat) d) ((List (Nat)) e n f ed nd fd er nr fr) ((List (Part)) sd) ((List (Nat)) r) -> Type)
  enum
  (many MkPatch : (erased (Nat) d) (erased (List (Nat)) e n f ed nd fd er nr fr r ids) (erased (List (Part)) sd)
      (erased (Hypermap d e n f) h) (erased (Hypermap d ed nd fd) hd) (erased (Hypermap d er nr fr) hr) (erased (Iota d ids) io)
      (erased (PatchDarts sd e n ed nd er nr r ids) pd) (erased (ECycle ed fd r) cy) -> (Patch d e n f ed nd fd er nr fr sd r)))

(def-fns _ $ (erased pd-at : (erased (List (Part)) sd) (erased (List (Nat)) e n ed nd er nr r xs) (erased (Nat) x)
    (subterm erased (PatchDarts sd e n ed nd er nr r xs) pd) (erased (In x xs) ix) -> (erased (PatchDart sd e n ed nd er nr r x) res))
  (let-match erased pd (PDCons _ _ _ _ _ _ _ _ xs1 y p pd1) (absurd (PDNil _ _ _ _ _ _ _ _) ix))
  (match erased ix _
    ((InHere _ _) p)
    ((InThere _ _ _ ix1) (pd-at sd e n ed nd er nr r xs1 x pd1 ix1))))

(def-fns _ $ (erased patch-dart : (erased (Nat) d x) (erased (List (Nat)) e n f ed nd fd er nr fr r) (erased (List (Part)) sd)
    (erased (Patch d e n f ed nd fd er nr fr sd r) pt) (erased (Lt x d) lx) -> (erased (PatchDart sd e n ed nd er nr r x) res))
  (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ ids _ h hd hr io pd cy))
  (pd-at sd e n ed nd er nr r ids x pd (iota-in d x ids io lx)))

; The three hypermaps of a patch, and their permutations.
(def-fns _ $ (erased patch-perms : (erased (Nat) d) (erased (List (Nat)) e n f ed nd fd er nr fr r) (erased (List (Part)) sd)
    (erased (Patch d e n f ed nd fd er nr fr sd r) pt) -> (erased (Hypermap d e n f) h) (erased (Hypermap d ed nd fd) hd)
    (erased (Hypermap d er nr fr) hr) (erased (List (Nat)) ni ndi nri ei edi eri fi fdi fri) (erased (HPerm d n ni) pn) (erased (HPerm d nd ndi) pnd)
    (erased (HPerm d nr nri) pnr) (erased (HPerm d e ei) pe) (erased (HPerm d ed edi) ped) (erased (HPerm d er eri) per)
    (erased (HPerm d f fi) pf) (erased (HPerm d fd fdi) pfd) (erased (HPerm d fr fri) pfr))
  (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ ids _ h hd hr io pd cy))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (let ((erased nfd) (erased ndi) (erased fdi) (erased rnfd) (erased ped) (erased pnd) (erased pfd)) (hyper-core d ed nd fd hd))
  (let ((erased nfr) (erased nri) (erased fri) (erased rnfr) (erased per) (erased pnr) (erased pfr)) (hyper-core d er nr fr hr))
  (values h hd hr ni ndi nri nf nfd nfr fi fdi fri pn pnd pnr pe ped per pf pfd pfr))

(def-fns _ $ (erased patch-rest : (erased (Nat) d x) (erased (List (Nat)) e n f ed nd fd er nr fr r) (erased (List (Part)) sd)
    (erased (Patch d e n f ed nd fd er nr fr sd r) pt) (erased (Nth (Part) sd x (PRest)) px) (erased (Lt x d) lx)
    -> (erased (Nat) a b) (erased (Nth (Nat) e x a) pe) (erased (Nth (Nat) er x a) per) (erased (Nth (Nat) n x b) pn)
    (erased (Nth (Nat) nr x b) pnr) (erased (Nth (Nat) ed x x) ped) (erased (Nth (Nat) nd x x) pnd))
  (match erased (patch-dart d x e n f ed nd fd er nr fr r sd pt lx) _
    ((PtRest _ _ _ _ _ _ _ _ _ a b _ _ pe per pn pnr ped pnd) (values a b pe per pn pnr ped pnd))
    (absurd (PtDisk _ _ _ _ _ _ _ _ _ _ _ ps _ _ _ _ _ _ _) (nth-fn (Part) sd x (PDisk) (PRest) ps px))
    (absurd (PtRing _ _ _ _ _ _ _ _ _ _ _ _ ps _ _ _ _ _ _ _) (nth-fn (Part) sd x (PRing) (PRest) ps px))))

(def-fns _ $ (erased patch-disk : (erased (Nat) d x) (erased (List (Nat)) e n f ed nd fd er nr fr r) (erased (List (Part)) sd)
    (erased (Patch d e n f ed nd fd er nr fr sd r) pt) (erased (Nth (Part) sd x (PDisk)) px) (erased (Lt x d) lx)
    -> (erased (Nat) a b) (erased (Nth (Nat) e x a) pe) (erased (Nth (Nat) ed x a) ped) (erased (Nth (Nat) n x b) pn)
    (erased (Nth (Nat) nd x b) pnd) (erased (Nth (Nat) er x x) per) (erased (Nth (Nat) nr x x) pnr))
  (match erased (patch-dart d x e n f ed nd fd er nr fr r sd pt lx) _
    ((PtDisk _ _ _ _ _ _ _ _ _ a b _ _ pe ped pn pnd per pnr) (values a b pe ped pn pnd per pnr))
    (absurd (PtRest _ _ _ _ _ _ _ _ _ _ _ ps _ _ _ _ _ _ _) (nth-fn (Part) sd x (PRest) (PDisk) ps px))
    (absurd (PtRing _ _ _ _ _ _ _ _ _ _ _ _ ps _ _ _ _ _ _ _) (nth-fn (Part) sd x (PRing) (PDisk) ps px))))

; A dart before x under p, a permutation, is below d.
(def-fns _ $ (erased pre-lt : (erased (Nat) d x y) (erased (List (Nat)) p q) (erased (HPerm d p q) pm) (erased (Nth (Nat) p x y) px) -> (erased (Lt x d) r))
  (perm-val d y x q p (perm-sym d p q pm) (perm-inv d x y p q pm px)))

; The node of a dart of the rest is in the rest.
(def-fns _ $ (erased rest-node : (erased (Nat) d x y) (erased (List (Nat)) e n f ed nd fd er nr fr r) (erased (List (Part)) sd)
    (erased (Patch d e n f ed nd fd er nr fr sd r) pt) (erased (Nth (Part) sd x (PRest)) px) (erased (Nth (Nat) n x y) pn)
    -> (erased (Nth (Part) sd y (PRest)) res))
  (let ((erased h) (erased hd) (erased hr) (erased ni) (erased ndi) (erased nri) (erased ei) (erased edi) (erased eri) (erased fi) (erased fdi)
        (erased fri) (erased pmn) (erased pmnd) (erased pmnr) (erased pme) (erased pmed) (erased pmer) (erased pmf) (erased pmfd) (erased pmfr))
    (patch-perms d e n f ed nd fd er nr fr r sd pt))
  (let ((erased a) (erased b) (erased pex) (erased perx) (erased pnx) (erased pnrx) (erased pedx) (erased pndx))
    (patch-rest d x e n f ed nd fd er nr fr r sd pt px (pre-lt d x y n ni pmn pn)))
  (let-match erased (nth-fn (Nat) n x b y pnx pn) (Refl _ _))
  (match erased (patch-dart d y e n f ed nd fd er nr fr r sd pt (perm-val d x y n ni pmn pn)) _
    ((PtRest _ _ _ _ _ _ _ _ _ _ _ ps _ _ _ _ _ _ _) ps)
    (absurd (PtDisk _ _ _ _ _ _ _ _ _ _ _ ps _ _ _ _ _ _ pnry)
      (let-match erased (perm-inj d x y y nr nri pmnr pnrx pnry) (Refl _ _))
      (nth-fn (Part) sd x (PDisk) (PRest) ps px))
    (absurd (PtRing _ _ _ _ _ _ _ _ _ _ _ c ps _ _ _ _ _ pedy pnrc)
      (let-match erased (perm-inj d x c y nr nri pmnr pnrx pnrc) (Refl _ _))
      (let-match erased (perm-inj d y x x ed edi pmed pedy pedx) (Refl _ _))
      (nth-fn (Part) sd x (PRing) (PRest) ps px))))

; The node image of a dart is in the rest only for a dart of the rest (closed_Gd).
(def-fns _ $ (erased rest-node-back : (erased (Nat) d x y) (erased (List (Nat)) e n f ed nd fd er nr fr r) (erased (List (Part)) sd)
    (erased (Patch d e n f ed nd fd er nr fr sd r) pt) (erased (Nth (Part) sd y (PRest)) py) (erased (Nth (Nat) n x y) pn)
    -> (erased (Nth (Part) sd x (PRest)) res))
  (let ((erased h) (erased hd) (erased hr) (erased ni) (erased ndi) (erased nri) (erased ei) (erased edi) (erased eri) (erased fi) (erased fdi)
        (erased fri) (erased pmn) (erased pmnd) (erased pmnr) (erased pme) (erased pmed) (erased pmer) (erased pmf) (erased pmfd) (erased pmfr))
    (patch-perms d e n f ed nd fd er nr fr r sd pt))
  (let ((erased a) (erased b) (erased pey) (erased pery) (erased pny) (erased pnry) (erased pedy) (erased pndy))
    (patch-rest d y e n f ed nd fd er nr fr r sd pt py (perm-val d x y n ni pmn pn)))
  (match erased (patch-dart d x e n f ed nd fd er nr fr r sd pt (pre-lt d x y n ni pmn pn)) _
    ((PtRest _ _ _ _ _ _ _ _ _ _ _ ps _ _ _ _ _ _ _) ps)
    (absurd (PtDisk _ _ _ _ _ _ _ _ _ _ b2 ps _ _ _ pnx pndx _ _)
      (let-match erased (nth-fn (Nat) n x b2 y pnx pn) (Refl _ _))
      (let-match erased (perm-inj d x y y nd ndi pmnd pndx pndy) (Refl _ _))
      (nth-fn (Part) sd x (PDisk) (PRest) ps py))
    (absurd (PtRing _ _ _ _ _ _ _ _ _ _ b2 _ ps _ _ _ pnx pndx _ _)
      (let-match erased (nth-fn (Nat) n x b2 y pnx pn) (Refl _ _))
      (let-match erased (perm-inj d x y y nd ndi pmnd pndx pndy) (Refl _ _))
      (nth-fn (Part) sd x (PRing) (PRest) ps py))))

; The edge image of a dart is inside the disk only for a dart inside the disk (closed_Gr).
(def-fns _ $ (erased disk-edge-back : (erased (Nat) d x y) (erased (List (Nat)) e n f ed nd fd er nr fr r) (erased (List (Part)) sd)
    (erased (Patch d e n f ed nd fd er nr fr sd r) pt) (erased (Nth (Part) sd y (PDisk)) py) (erased (Nth (Nat) e x y) pe)
    -> (erased (Nth (Part) sd x (PDisk)) res))
  (let ((erased h) (erased hd) (erased hr) (erased ni) (erased ndi) (erased nri) (erased ei) (erased edi) (erased eri) (erased fi) (erased fdi)
        (erased fri) (erased pmn) (erased pmnd) (erased pmnr) (erased pme) (erased pmed) (erased pmer) (erased pmf) (erased pmfd) (erased pmfr))
    (patch-perms d e n f ed nd fd er nr fr r sd pt))
  (let ((erased a) (erased b) (erased pey) (erased pedy) (erased pny) (erased pndy) (erased pery) (erased pnry))
    (patch-disk d y e n f ed nd fd er nr fr r sd pt py (perm-val d x y e ei pme pe)))
  (match erased (patch-dart d x e n f ed nd fd er nr fr r sd pt (pre-lt d x y e ei pme pe)) _
    ((PtDisk _ _ _ _ _ _ _ _ _ _ _ ps _ _ _ _ _ _ _) ps)
    (absurd (PtRing _ _ _ _ _ _ _ _ _ a2 _ _ ps _ pex perx _ _ _ _)
      (let-match erased (nth-fn (Nat) e x a2 y pex pe) (Refl _ _))
      (let-match erased (perm-inj d x y y er eri pmer perx pery) (Refl _ _))
      (nth-fn (Part) sd x (PRing) (PDisk) ps py))
    (absurd (PtRest _ _ _ _ _ _ _ _ _ a2 _ ps _ pex perx _ _ _ _)
      (let-match erased (nth-fn (Nat) e x a2 y pex pe) (Refl _ _))
      (let-match erased (perm-inj d x y y er eri pmer perx pery) (Refl _ _))
      (nth-fn (Part) sd x (PRest) (PDisk) ps py))))

; Inside the disk the face permutation of the disk map is that of the whole map (hdF).
(def-fns _ $ (erased patch-face-d : (erased (Nat) d x y) (erased (List (Nat)) e n f ed nd fd er nr fr r) (erased (List (Part)) sd)
    (erased (Patch d e n f ed nd fd er nr fr sd r) pt) (erased (Nth (Part) sd x (PDisk)) px) (erased (Nth (Nat) f x y) pf)
    -> (erased (Nth (Nat) fd x y) res))
  (let ((erased h) (erased hd) (erased hr) (erased ni) (erased ndi) (erased nri) (erased ei) (erased edi) (erased eri) (erased fi) (erased fdi)
        (erased fri) (erased pmn) (erased pmnd) (erased pmnr) (erased pme) (erased pmed) (erased pmer) (erased pmf) (erased pmfd) (erased pmfr))
    (patch-perms d e n f ed nd fd er nr fr r sd pt))
  (let ((erased ly)) (perm-val d x y f fi pmf pf))
  (let ((erased b) (erased pny) (erased lb)) (perm-nth d y n ni pmn ly))
  (let ((erased peb)) (hyper-edge d b y x e n f h pny pf))
  (let ((erased pb)) (disk-edge-back d b x e n f ed nd fd er nr fr r sd pt px peb))
  (let ((erased a) (erased c) (erased peb2) (erased pedb) (erased pnb) (erased pndb) (erased perb) (erased pnrb))
    (patch-disk d b e n f ed nd fd er nr fr r sd pt pb lb))
  (let-match erased (nth-fn (Nat) e b a x peb2 peb) (Refl _ _))
  (let ((erased pndy)) (match erased (patch-dart d y e n f ed nd fd er nr fr r sd pt ly) (((Nth (Nat) nd y b) q))
    ((PtDisk _ _ _ _ _ _ _ _ _ _ b2 _ _ _ _ pn2 pnd2 _ _) (let-match erased (nth-fn (Nat) n y b2 b pn2 pny) (Refl _ _)) pnd2)
    ((PtRing _ _ _ _ _ _ _ _ _ _ b2 _ _ _ _ _ pn2 pnd2 _ _) (let-match erased (nth-fn (Nat) n y b2 b pn2 pny) (Refl _ _)) pnd2)
    (absurd (PtRest _ _ _ _ _ _ _ _ _ _ _ ps _ _ _ _ _ _ _)
      (nth-fn (Part) sd b (PRest) (PDisk) (rest-node d y b e n f ed nd fd er nr fr r sd pt ps pny) pb))))
  (hyper-third d x b y ed nd fd hd pedb pndy))

; Into the rest the face permutation of the remainder map is that of the whole map (hrF).
(def-fns _ $ (erased patch-face-r : (erased (Nat) d x y) (erased (List (Nat)) e n f ed nd fd er nr fr r) (erased (List (Part)) sd)
    (erased (Patch d e n f ed nd fd er nr fr sd r) pt) (erased (Nth (Part) sd y (PRest)) py) (erased (Nth (Nat) fr x y) pf)
    -> (erased (Nth (Nat) f x y) res))
  (let ((erased h) (erased hd) (erased hr) (erased ni) (erased ndi) (erased nri) (erased ei) (erased edi) (erased eri) (erased fi) (erased fdi)
        (erased fri) (erased pmn) (erased pmnd) (erased pmnr) (erased pme) (erased pmed) (erased pmer) (erased pmf) (erased pmfd) (erased pmfr))
    (patch-perms d e n f ed nd fd er nr fr r sd pt))
  (let ((erased a) (erased b) (erased pey) (erased pery) (erased pny) (erased pnry) (erased pedy) (erased pndy))
    (patch-rest d y e n f ed nd fd er nr fr r sd pt py (perm-val d x y fr fri pmfr pf)))
  (let ((erased perb)) (hyper-edge d b y x er nr fr hr pnry pf))
  (let ((erased a2) (erased b2) (erased peb) (erased perb2) (erased pnb) (erased pnrb) (erased pedb) (erased pndb))
    (patch-rest d b e n f ed nd fd er nr fr r sd pt (rest-node d y b e n f ed nd fd er nr fr r sd pt py pny) (perm-val d y b n ni pmn pny)))
  (let-match erased (nth-fn (Nat) er b a2 x perb2 perb) (Refl _ _))
  (hyper-third d x b y e n f h peb pny))
