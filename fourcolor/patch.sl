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

; The image of hr is closed under e (closed_Gr).
(def-fns _ $ (erased closed-gr : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (Nat) xr x y) (erased (Nth (Nat) hr xr x) hx) (erased (Nth (Nat) e x y) pe)
    -> (erased (Nat) yr) (erased (Nth (Nat) hr yr y) hy))
  (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids idd idr bG bGr h hd2 hr2 io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
  (let ((erased nfr) (erased nri) (erased fri) (erased rnf) (erased pmer) (erased pmnr) (erased pmfr)) (hyper-core dr er nr fr hr2))
  (let ((erased lx)) (nth-lt-length _ hr xr dr x hx lhr))
  (let ((erased yr) (erased pyr) (erased ly)) (perm-nth dr xr er nfr pmer lx))
  (let ((erased w) (erased hy) (erased pew)) (morph hr er e (Nil (Nat)) idr dr xr yr x mer ior lx (NotInNil xr) pyr hx))
  (let-match erased (nth-fn (Nat) e x w y pew pe) (Refl _ _))
  (values yr hy))

; The image of hd is closed under n (closed_Gd).
(def-fns _ $ (erased closed-gd : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (Nat) xd x y) (erased (Nth (Nat) hd xd x) hx) (erased (Nth (Nat) n x y) pn)
    -> (erased (Nat) yd) (erased (Nth (Nat) hd yd y) hy))
  (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids idd idr bG bGr h hd2 hr2 io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
  (let ((erased nfd) (erased ndi) (erased fdi) (erased rnf) (erased pmed) (erased pmnd) (erased pmfd)) (hyper-core dd ed nd fd hd2))
  (let ((erased lx)) (nth-lt-length _ hd xd dd x hx lhd))
  (let ((erased yd) (erased pyd) (erased ly)) (perm-nth dd xd nd ndi pmnd lx))
  (let ((erased w) (erased hy) (erased pnw)) (morph hd nd n (Nil (Nat)) idd dd xd yd x mnd iod lx (NotInNil xd) pyd hx))
  (let-match erased (nth-fn (Nat) n x w y pnw pn) (Refl _ _))
  (values yd hy))
(def-fns _ $ (erased revapp-in : (erased (List (Nat)) pre w r) (erased (Nat) x) (subterm erased (RevApp (Nat) pre w r) ra)
    (erased (HOr (In x pre) (In x w)) ix) -> (erased (In x r) res))
  (let-match erased ra (RACons _ s pre1 _ _ ra1)
    ((RANil _ _) (match erased ix _ (absurd (OrL _ _ i) i) ((OrR _ _ i) i))))
  (revapp-in pre1 (Cons _ s w) r x ra1
    (match erased ix _
      ((OrL _ _ i) (match erased i _ ((InHere _ _) (OrR _ _ (InHere x w))) ((InThere _ _ _ i1) (OrL _ _ i1))))
      ((OrR _ _ i) (OrR _ _ (InThere x s w i))))))

(def-fns _ $ (erased revapp-out : (erased (List (Nat)) pre w r) (erased (Nat) x) (subterm erased (RevApp (Nat) pre w r) ra) (erased (In x r) ix)
    -> (erased (HOr (In x pre) (In x w)) res))
  (let-match erased ra (RACons _ s pre1 _ _ ra1) ((RANil _ _) (OrR _ _ ix)))
  (match erased (revapp-out pre1 (Cons _ s w) r x ra1 ix) _
    ((OrL _ _ i) (OrL _ _ (InThere x s pre1 i)))
    ((OrR _ _ i) (match erased i _ ((InHere _ _) (OrL _ _ (InHere x pre1))) ((InThere _ _ _ i1) (OrR _ _ i1))))))

(def-fns _ $ (erased revapp-length : (erased (List (Nat)) pre w r) (erased (Nat) a b c) (subterm erased (RevApp (Nat) pre w r) ra) (erased (Length (Nat) pre a) la)
    (erased (Length (Nat) w b) lb) (erased (Add a b c) ab) -> (erased (Length (Nat) r c) res))
  (let-match erased ra (RACons _ s pre1 _ _ ra1)
    ((RANil _ _) (let-match erased la (LengthNil _)) (let-match erased ab (AddZero _)) lb))
  (let-match erased la (LengthCons _ _ _ a1 la1))
  (let-match erased ab (AddSucc _ _ c1 ab1))
  (revapp-length pre1 (Cons _ s w) r a1 (Succ b) c ra1 la1 (LengthCons _ s w b lb) (add-succ-right a1 b c1 ab1)))

(def-fns _ $ (erased parts-at : (erased (List (Nat)) hd hr bd xs) (erased (Nat) x) (subterm erased (PatchParts hd hr bd xs) pp) (erased (In x xs) ix)
    -> (erased (PatchPart hd hr bd x) r))
  (let-match erased pp (PPCons _ _ _ xs1 y p pp1) (absurd (PPNil _ _ _) ix))
  (match erased ix _ ((InHere _ _) p) ((InThere _ _ _ ix1) (parts-at hd hr bd xs1 x pp1 ix1))))

; Every dart is in hd, or in qs, the darts of hr not in hd.
(def-fns _ $ (erased parts-sub : (erased (List (Nat)) hd hr bd xs rs qs us) (subterm erased (PatchParts hd hr bd xs) pp) (erased (Split hd hr rs qs) sp)
    (erased (AppN hd qs us) ap) -> (erased (Sub xs us) r))
  (let-match erased pp (PPCons _ _ _ xs1 x p pp1) ((PPNil _ _ _) (HSubNil us)))
  (HSubCons x xs1 us
    (match erased p _
      ((PtDisk _ _ _ _ xd px out outr) (app-in-l hd qs us x ap (nth-in hd xd x px)))
      ((PtRing _ _ _ _ xd xr px pin pr) (app-in-l hd qs us x ap (nth-in hd xd x px)))
      ((PtRest _ _ _ _ xr pr outd)
        (match erased (split-cover hd hr rs qs x sp (nth-in hr xr x pr)) _
          (absurd (OrL _ _ i) (apart-irrefl x (notin-in x x hd outd (split-in hd hr rs qs x sp i))))
          ((OrR _ _ i) (app-in-r hd qs us x ap i)))))
    (parts-sub hd hr bd xs1 rs qs us pp1 sp ap)))

; A dart of both hd and hr is on the ring.
(def-fns _ $ (erased ring-sub : (erased (Nat) d) (erased (List (Nat)) hd hr bd bG bGr ids m) (erased (PatchParts hd hr bd ids) pp) (erased (Iota d ids) io)
    (erased (Under hr d) uhr) (erased (Respects hd bd bG) rbd) (erased (RevApp (Nat) bG (Nil (Nat)) bGr) rv) (subterm erased (Sub m hr) sr) (erased (Sub m hd) sd)
    -> (erased (Sub m bGr) r))
  (let-match erased sr (HSubCons y m1 _ iy sr1) ((HSubNil _) (HSubNil bGr)))
  (let-match erased sd (HSubCons _ _ _ jy sd1))
  (HSubCons y m1 bGr
    (match erased (parts-at hd hr bd ids y pp (iota-in d y ids io (under-in hr y d uhr iy))) _
      (absurd (PtDisk _ _ _ _ xd px out outr) (apart-irrefl y (notin-in y y hr outr iy)))
      ((PtRing _ _ _ _ xd xr px pin pr) (revapp-in bG (Nil _) bGr y rv (OrL _ _ (in-map hd bd bG xd y pin rbd px))))
      (absurd (PtRest _ _ _ _ xr pr outd) (apart-irrefl y (notin-in y y hd outd jy))))
    (ring-sub d hd hr bd bG bGr ids m1 pp io uhr rbd rv sr1 sd1)))

(def-fns _ $ (erased ring-sub-back : (erased (List (Nat)) hd hr bd br bG bGr rs qs m) (erased (Respects hd bd bG) rbd) (erased (Respects hr br bGr) rbr)
    (erased (RevApp (Nat) bG (Nil (Nat)) bGr) rv) (erased (Split hd hr rs qs) sp) (subterm erased (Sub m bGr) sb) -> (erased (Sub m rs) r))
  (let-match erased sb (HSubCons y m1 _ iy sb1) ((HSubNil _) (HSubNil rs)))
  (let ((erased jr) (erased ijr) (erased pjr)) (respects-in hr br bGr y rbr iy))
  (let ((erased ihr)) (nth-in hr jr y pjr))
  (let-match erased (revapp-out bG (Nil _) bGr y rv iy) (OrL _ _ ibg) (absurd (OrR _ _ i) i))
  (let ((erased jd) (erased ijd) (erased pjd)) (respects-in hd bd bG y rbd ibg))
  (HSubCons y m1 rs
    (match erased (split-cover hd hr rs qs y sp ihr) _
      ((OrL _ _ i) i)
      (absurd (OrR _ _ i) (apart-irrefl y (notin-in y y hd (split-out hd hr rs qs y sp i) (nth-in hd jd y pjd)))))
    (ring-sub-back hd hr bd br bG bGr rs qs m1 rbd rbr rv sp sb1)))

; #|Gd| + #|Gr| = size bG + #|G| (card_patch).
(def-fns _ $ (erased card-patch : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt)
    -> (erased (Nat) b s) (erased (Length (Nat) bd b) lb) (erased (Add dd dr s) a1) (erased (Add b d s) a2))
  (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids idd idr bG bGr h hd2 hr2 io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
  (let ((erased b) (erased lbd)) (length-exists _ bd))
  (let ((erased lbg)) (respects-length hd bd bG b rbd lbd))
  (let ((erased lbgr)) (revapp-length bG (Nil _) bGr b (Zero) b rv lbg (LengthNil _) (add-zero-right b)))
  (let ((erased rs) (erased qs) (erased sp)) (split-exists hd hr))
  (let ((erased a) (erased q) (erased la) (erased lq) (erased aq)) (split-length hd hr rs qs dr sp lhr))
  (let ((erased drs) (erased dqs)) (split-distinct hd hr rs qs sp dhr))
  (let ((erased srh) (erased sqh)) (split-sub hd hr rs qs sp))
  (let ((erased dbgr)) (respects-distinct hr br bGr dhr dbr rbr))
  (let-match erased (same-size rs bGr a b drs dbgr
      (ring-sub d hd hr bd bG bGr ids rs pp io uhr rbd rv srh (split-sub-t hd hr rs qs sp))
      (ring-sub-back hd hr bd br bG bGr rs qs bGr rbd rbr rv sp (sub-refl bGr)) la lbgr) (Refl _ _))
  (let ((erased us) (erased ap)) (app-exists hd qs))
  (let ((erased s0) (erased as0)) (add-ex dd q))
  (let ((erased lus)) (app-length hd qs us dd q s0 ap lhd lq as0))
  (let ((erased dus)) (app-distinct hd qs us ap dhd dqs (disj-sym qs hd (split-disj hd hr rs qs sp) hd (sub-refl hd))))
  (let-match erased (same-size us ids s0 d dus (iota-distinct d ids io)
      (app-sub hd qs us ids ap (under-sub d hd ids uhd io) (sub-trans qs hr ids sqh (under-sub d hr ids uhr io)))
      (parts-sub hd hr bd ids rs qs us pp sp ap) lus (iota-length d ids io)) (Refl _ _))
  (let ((erased s) (erased a1)) (add-ex dd dr))
  (let ((erased ab) (erased p1) (erased p2)) (add-assoc-inv dd b q dr s aq a1))
  (let ((erased bc) (erased p3) (erased p4)) (add-assoc b dd q ab s (add-comm dd b ab p1) p2))
  (let-match erased (add-fn dd q bc s0 p3 as0) (Refl _ _))
  (values b s lbd a1 p4))
