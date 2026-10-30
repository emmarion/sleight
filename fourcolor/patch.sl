; Patching two maps to cover a larger one, after patch.v. The disk map (ed, nd, fd) on the darts 0..dd-1 and the
; remainder map (er, nr, fr) on 0..dr-1 are sent into the darts 0..d-1 of the whole map (e, n, f) by the injections hd
; and hr, listed by their images. Load after kempemap.sl.

; For each dart x of xs not in b, h (p x) = q (h x).
(def-adts $ (MorphOff : ((List (Nat)) h p q b xs) -> Type)
  enum
  (many MONil : (erased (List (Nat)) h p q b) -> (MorphOff h p q b (Nil (Nat))))
  (many MOSkip : (erased (List (Nat)) h p q b xs) (erased (Nat) x) (erased (In x b) ib) (erased (MorphOff h p q b xs) rest)
      -> (MorphOff h p q b (Cons (Nat) x xs)))
  (many MOAt : (erased (List (Nat)) h p q b xs) (erased (Nat) x y z w) (erased (Nth (Nat) p x y) px) (erased (Nth (Nat) h x z) hx)
      (erased (Nth (Nat) h y w) hy) (erased (Nth (Nat) q z w) qz) (erased (MorphOff h p q b xs) rest) -> (MorphOff h p q b (Cons (Nat) x xs))))

(def-adts $ (MorphAt : ((List (Nat)) h p q) ((Nat) x) -> Type)
  enum
  (many MkMorphAt : (erased (List (Nat)) h p q) (erased (Nat) x y z w) (erased (Nth (Nat) p x y) px) (erased (Nth (Nat) h x z) hx)
      (erased (Nth (Nat) h y w) hy) (erased (Nth (Nat) q z w) qz) -> (MorphAt h p q x)))

; The dart x of the whole map is the image of a dart of the disk map off its ring and of no dart of the remainder
; map, the image of a ring dart of each, or the image of a dart of the remainder map only.
(def-adts $ (PatchPart : ((List (Nat)) hd hr bd) ((Nat) x) -> Type)
  enum
  (many PtDisk : (erased (List (Nat)) hd hr bd) (erased (Nat) x xd) (erased (Nth (Nat) hd xd x) px) (erased (NotIn xd bd) out)
      (erased (NotIn x hr) outr) -> (PatchPart hd hr bd x))
  (many PtRing : (erased (List (Nat)) hd hr bd) (erased (Nat) x xd xr) (erased (Nth (Nat) hd xd x) px) (erased (In xd bd) pin)
      (erased (Nth (Nat) hr xr x) pr) -> (PatchPart hd hr bd x))
  (many PtRest : (erased (List (Nat)) hd hr bd) (erased (Nat) x xr) (erased (Nth (Nat) hr xr x) pr) (erased (NotIn x hd) outd)
      -> (PatchPart hd hr bd x)))

(def-adts $ (PatchParts : ((List (Nat)) hd hr bd xs) -> Type)
  enum
  (many PPNil : (erased (List (Nat)) hd hr bd) -> (PatchParts hd hr bd (Nil (Nat))))
  (many PPCons : (erased (List (Nat)) hd hr bd xs) (erased (Nat) x) (erased (PatchPart hd hr bd x) p) (erased (PatchParts hd hr bd xs) rest)
      -> (PatchParts hd hr bd (Cons (Nat) x xs))))

; patch hd hr bd br: bd is a simple edge cycle of the disk map, br a duplicate-free node cycle of the remainder map, hd
; and hr injective, map hr br = rev (map hd bd), the images cover the whole map and meet on map hd bd, hd keeps edges
; off bd and all nodes, and hr keeps all edges and nodes off br.
(def-adts $ (Patch : ((Nat) d dd dr) ((List (Nat)) e n f ed nd fd er nr fr hd hr bd br) -> Type)
  enum
  (many MkPatch : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br ids idd idr bG bGr)
      (erased (Hypermap d e n f) h) (erased (Hypermap dd ed nd fd) hdm) (erased (Hypermap dr er nr fr) hrm)
      (erased (Iota d ids) io) (erased (Iota dd idd) iod) (erased (Iota dr idr) ior) (erased (Length (Nat) hd dd) lhd) (erased (Length (Nat) hr dr) lhr)
      (erased (Distinct hd) dhd) (erased (Distinct hr) dhr) (erased (Under hd d) uhd) (erased (Under hr d) uhr)
      (erased (NCyc ed bd) cyd) (erased (Simple fd bd) sd) (erased (NCyc nr br) cyr) (erased (Distinct br) dbr)
      (erased (Respects hd bd bG) rbd) (erased (Respects hr br bGr) rbr) (erased (RevApp (Nat) bG (Nil (Nat)) bGr) rv)
      (erased (PatchParts hd hr bd ids) pp)
      (erased (MorphOff hd ed e bd idd) med) (erased (MorphOff hd nd n (Nil (Nat)) idd) mnd)
      (erased (MorphOff hr er e (Nil (Nat)) idr) mer) (erased (MorphOff hr nr n br idr) mnr)
      -> (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br)))

(def-fns _ $ (erased morph-at : (erased (List (Nat)) h p q b xs) (erased (Nat) x) (subterm erased (MorphOff h p q b xs) mo) (erased (In x xs) ix)
    -> (erased (Or (In x b) (MorphAt h p q x)) r))
  (match erased mo _
    (absurd (MONil _ _ _ _) ix)
    ((MOSkip _ _ _ _ xs1 y ib mo1)
      (match erased ix _ ((InHere _ _) (InL _ _ ib)) ((InThere _ _ _ ix1) (morph-at h p q b xs1 x mo1 ix1))))
    ((MOAt _ _ _ _ xs1 y y2 z w px hx hy qz mo1)
      (match erased ix _ ((InHere _ _) (InR _ _ (MkMorphAt h p q x y2 z w px hx hy qz))) ((InThere _ _ _ ix1) (morph-at h p q b xs1 x mo1 ix1))))))

; h (p x) = q (h x) for x off b, the darts of p below k and listed by ids.
(def-fns _ $ (erased morph : (erased (List (Nat)) h p q b ids) (erased (Nat) k x y z) (erased (MorphOff h p q b ids) mo) (erased (Iota k ids) io)
    (erased (Lt x k) lx) (erased (NotIn x b) out) (erased (Nth (Nat) p x y) px) (erased (Nth (Nat) h x z) hx)
    -> (erased (Nat) w) (erased (Nth (Nat) h y w) hy) (erased (Nth (Nat) q z w) qz))
  (match erased (morph-at h p q b ids x mo (iota-in k x ids io lx)) _
    (absurd (InL _ _ ib) (apart-irrefl x (notin-in x x b out ib)))
    ((InR _ _ ma)
      (let-match erased ma (MkMorphAt _ _ _ _ y2 z2 w px2 hx2 hy qz))
      (let-match erased (nth-fn (Nat) p x y2 y px2 px) (Refl _ _))
      (let-match erased (nth-fn (Nat) h x z2 z hx2 hx) (Refl _ _))
      (values w hy qz))))

; A dart before x under p, a permutation, is below d.
(def-fns _ $ (erased pre-lt : (erased (Nat) d x y) (erased (List (Nat)) p q) (erased (HPerm d p q) pm) (erased (Nth (Nat) p x y) px) -> (erased (Lt x d) r))
  (perm-val d y x q p (perm-sym d p q pm) (perm-inv d x y p q pm px)))

; Off the ring the disk map's faces are those of the whole map (hdF).
(def-fns _ $ (erased patch-face-d : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (Nat) xd yd x y) (erased (NotIn xd bd) out)
    (erased (Nth (Nat) fd xd yd) pf) (erased (Nth (Nat) hd xd x) hx) (erased (Nth (Nat) hd yd y) hy) -> (erased (Nth (Nat) f x y) res))
  (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids idd idr bG bGr h hd2 hr2 io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
  (let ((erased nfd) (erased ndi) (erased fdi) (erased rnf) (erased pmed) (erased pmnd) (erased pmfd)) (hyper-core dd ed nd fd hd2))
  (let ((erased ly)) (perm-val dd xd yd fd fdi pmfd pf))
  (let ((erased b) (erased pnb) (erased lb)) (perm-nth dd yd nd ndi pmnd ly))
  (let ((erased peb)) (hyper-edge dd b yd xd ed nd fd hd2 pnb pf))
  (let ((erased w) (erased hb) (erased pny)) (morph hd nd n (Nil (Nat)) idd dd yd b y mnd iod ly (NotInNil yd) pnb hy))
  (match erased (morph-at hd ed e bd idd b med (iota-in dd b idd iod lb)) _
    (absurd (InL _ _ ib) (apart-irrefl xd (notin-in xd xd bd out (ncyc-next ed bd b xd cyd ib peb))))
    ((InR _ _ ma)
      (let-match erased ma (MkMorphAt _ _ _ _ y2 z2 w2 py2 hz2 hw2 qz))
      (let-match erased (nth-fn (Nat) ed b y2 xd py2 peb) (Refl _ _))
      (let-match erased (nth-fn (Nat) hd b z2 w hz2 hb) (Refl _ _))
      (let-match erased (nth-fn (Nat) hd xd w2 x hw2 hx) (Refl _ _))
      (hyper-third d x w y e n f h qz pny))))

; Onto a dart off the ring the remainder map's faces are those of the whole map (hrF).
(def-fns _ $ (erased patch-face-r : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (Nat) xr yr x y) (erased (NotIn yr br) out)
    (erased (Nth (Nat) fr xr yr) pf) (erased (Nth (Nat) hr xr x) hx) (erased (Nth (Nat) hr yr y) hy) -> (erased (Nth (Nat) f x y) res))
  (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids idd idr bG bGr h hd2 hr2 io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
  (let ((erased nfr) (erased nri) (erased fri) (erased rnf) (erased pmer) (erased pmnr) (erased pmfr)) (hyper-core dr er nr fr hr2))
  (let ((erased ly)) (perm-val dr xr yr fr fri pmfr pf))
  (let ((erased b) (erased pnb) (erased lb)) (perm-nth dr yr nr nri pmnr ly))
  (let ((erased peb)) (hyper-edge dr b yr xr er nr fr hr2 pnb pf))
  (let ((erased w) (erased hb) (erased pny)) (morph hr nr n br idr dr yr b y mnr ior ly out pnb hy))
  (let ((erased w2) (erased hx2) (erased pew)) (morph hr er e (Nil (Nat)) idr dr b xr w mer ior lb (NotInNil b) peb hb))
  (let-match erased (nth-fn (Nat) hr xr w2 x hx2 hx) (Refl _ _))
  (hyper-third d x w y e n f h pew pny))
