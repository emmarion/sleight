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

; Off a cycle b of p, p stays off b.
(def-fns _ $ (erased off-next : (erased (Nat) k x z) (erased (List (Nat)) p pi b) (erased (HPerm k p pi) pm) (erased (NCyc p b) nc) (erased (NotIn x b) out)
    (erased (Nth (Nat) p x z) px) -> (erased (NotIn z b) r))
  (match erased (in-dec z b) _
    (absurd (OrL _ _ iz) (apart-irrefl x (notin-in x x b out (ncyc-prev k p pi b x z pm nc iz px))))
    ((OrR _ _ oz) oz)))

; A walk along p off its cycle b, sent by h, a morphism to q off b, to a walk along q.
(def-fns _ $ (erased path-push : (erased (Nat) k x y x2) (erased (List (Nat)) h p pi q b ids s s2 xs) (erased (HPerm k p pi) pm) (erased (NCyc p b) nc)
    (erased (MorphOff h p q b ids) mo) (erased (Iota k ids) io) (erased (Distinct h) dh) (erased (Respects h s s2) rs)
    (subterm erased (Path p s x y xs) w) (erased (Lt x k) lx) (erased (NotIn x b) out) (erased (Nth (Nat) h x x2) hx)
    -> (erased (Nat) y2) (erased (List (Nat)) xs2) (erased (Nth (Nat) h y y2) hy) (erased (Path q s2 x2 y2 xs2) w2) (erased (Respects h xs xs2) rx))
  (let-match erased w (PathStep _ _ xs1 _ z _ pz ns w1) ((PathHere _ _ _) (values x2 (Nil _) hx (PathHere q s2 x2) (RespNil h))))
  (let ((erased z2) (erased hz) (erased qz)) (morph h p q b ids k x z x2 mo io lx out pz hx))
  (let ((erased y2) (erased xs2) (erased hy) (erased w2) (erased rx))
    (path-push k z y z2 h p pi q b ids s s2 xs1 pm nc mo io dh rs w1 (perm-val k x z p pi pm pz) (off-next k x z p pi b pm nc out pz) hz))
  (values y2 (Cons _ x2 xs2) hy (PathStep q s2 xs2 x2 z2 y2 qz (notin-respects h s s2 x x2 dh ns hx rs) w2) (RespCons h xs1 xs2 x x2 hx rx)))

; A walk along q from the image of a dart off b is the image of a walk along p.
(def-fns _ $ (erased path-pull : (erased (Nat) k x x2 y2) (erased (List (Nat)) h p pi q b ids s s2 xs2) (erased (HPerm k p pi) pm) (erased (NCyc p b) nc)
    (erased (MorphOff h p q b ids) mo) (erased (Iota k ids) io) (erased (Respects h s s2) rs)
    (subterm erased (Path q s2 x2 y2 xs2) w) (erased (Lt x k) lx) (erased (NotIn x b) out) (erased (Nth (Nat) h x x2) hx)
    -> (erased (Nat) y) (erased (List (Nat)) xs) (erased (Nth (Nat) h y y2) hy) (erased (Path p s x y xs) w1) (erased (Respects h xs xs2) rx))
  (let-match erased w (PathStep _ _ xs3 _ w2 _ qw ns w3) ((PathHere _ _ _) (values x (Nil _) hx (PathHere p s x) (RespNil h))))
  (let ((erased z) (erased pz) (erased lz)) (perm-nth k x p pi pm lx))
  (let ((erased z2) (erased hz) (erased qz)) (morph h p q b ids k x z x2 mo io lx out pz hx))
  (let-match erased (nth-fn _ q x2 z2 w2 qz qw) (Refl _ _))
  (let ((erased y) (erased xs) (erased hy) (erased w1) (erased rx))
    (path-pull k z z2 y2 h p pi q b ids s s2 xs3 pm nc mo io rs w3 lz (off-next k x z p pi b pm nc out pz) hz))
  (values y (Cons _ x xs) hy
    (PathStep p s xs x z y pz
      (match erased (in-dec x s) _
        (absurd (OrL _ _ ix) (apart-irrefl x2 (notin-in x2 x2 s2 ns (in-map h s s2 x x2 ix rs hx))))
        ((OrR _ _ o) o))
      w1)
    (RespCons h xs xs3 x x2 hx rx)))

(def-fns _ $ (erased order-push : (erased (Nat) k x x2 c) (erased (List (Nat)) h p pi q b ids) (erased (HPerm k p pi) pm) (erased (NCyc p b) nc)
    (erased (MorphOff h p q b ids) mo) (erased (Iota k ids) io) (erased (Distinct h) dh) (erased (Order p x c) o) (erased (Lt x k) lx) (erased (NotIn x b) out)
    (erased (Nth (Nat) h x x2) hx) -> (erased (Order q x2 c) r))
  (let-match erased o (MkOrder _ xs _ y c1 py w l))
  (let ((erased y2) (erased hy) (erased qy)) (morph h p q b ids k x y x2 mo io lx out py hx))
  (let ((erased x3) (erased xs2) (erased hx3) (erased w2) (erased rx))
    (path-push k y x y2 h p pi q b ids (Cons _ x (Nil _)) (Cons _ x2 (Nil _)) xs pm nc mo io dh (RespCons h (Nil _) (Nil _) x x2 hx (RespNil h)) w
      (perm-val k x y p pi pm py) (off-next k x y p pi b pm nc out py) hy))
  (let-match erased (nth-fn _ h x x3 x2 hx3 hx) (Refl _ _))
  (MkOrder q xs2 x2 y2 c1 qy w2 (respects-length h xs xs2 c1 rx l)))

(def-fns _ $ (erased order-pull : (erased (Nat) k x x2 c) (erased (List (Nat)) h p pi q b ids) (erased (HPerm k p pi) pm) (erased (NCyc p b) nc)
    (erased (MorphOff h p q b ids) mo) (erased (Iota k ids) io) (erased (Distinct h) dh) (erased (Order q x2 c) o) (erased (Lt x k) lx) (erased (NotIn x b) out)
    (erased (Nth (Nat) h x x2) hx) -> (erased (Order p x c) r))
  (let-match erased o (MkOrder _ xs2 _ y2 c1 qy w l))
  (let ((erased y) (erased py) (erased ly)) (perm-nth k x p pi pm lx))
  (let ((erased y3) (erased hy) (erased qy3)) (morph h p q b ids k x y x2 mo io lx out py hx))
  (let-match erased (nth-fn _ q x2 y3 y2 qy3 qy) (Refl _ _))
  (let ((erased x3) (erased xs) (erased hx3) (erased w1) (erased rx))
    (path-pull k y y2 x2 h p pi q b ids (Cons _ x (Nil _)) (Cons _ x2 (Nil _)) xs2 pm nc mo io (RespCons h (Nil _) (Nil _) x x2 hx (RespNil h)) w ly
      (off-next k x y p pi b pm nc out py) hy))
  (let-match erased (distinct-nth h x3 x x2 dh hx3 hx) (Refl _ _))
  (MkOrder p xs x y c1 py w1 (respects-length-inv h xs xs2 c1 rx l)))

; Every dart of xs not in b has order c under p.
(def-adts $ (OrdersOff : ((List (Nat)) p) ((Nat) c) ((List (Nat)) b xs) -> Type)
  enum
  (many OONil : (erased (List (Nat)) p b) (erased (Nat) c) -> (OrdersOff p c b (Nil (Nat))))
  (many OOSkip : (erased (List (Nat)) p b xs) (erased (Nat) c x) (erased (In x b) ib) (erased (OrdersOff p c b xs) rest)
      -> (OrdersOff p c b (Cons (Nat) x xs)))
  (many OOAt : (erased (List (Nat)) p b xs) (erased (Nat) c x) (erased (Order p x c) o) (erased (OrdersOff p c b xs) rest)
      -> (OrdersOff p c b (Cons (Nat) x xs))))

(def-fns _ $ (erased oo-at : (erased (List (Nat)) p b xs) (erased (Nat) c x) (subterm erased (OrdersOff p c b xs) oo) (erased (In x xs) ix) (erased (NotIn x b) out)
    -> (erased (Order p x c) r))
  (match erased oo _
    (absurd (OONil _ _ _) ix)
    ((OOSkip _ _ xs1 _ y ib oo1)
      (match erased ix _
        (absurd (InHere _ _) (apart-irrefl x (notin-in x x b out ib)))
        ((InThere _ _ _ ix1) (oo-at p b xs1 c x oo1 ix1 out))))
    ((OOAt _ _ xs1 _ y o oo1) (match erased ix _ ((InHere _ _) o) ((InThere _ _ _ ix1) (oo-at p b xs1 c x oo1 ix1 out))))))

(def-fns _ $ (erased oo-of-all : (erased (Nat) d c) (erased (List (Nat)) p m) (erased (AllOrder d p c) ao) (subterm erased (Under m d) u)
    -> (erased (OrdersOff p c (Nil (Nat)) m) r))
  (let-match erased u (UnderCons m1 x _ lx u1) ((UnderNil _) (OONil p (Nil _) c)))
  (OOAt p (Nil _) m1 c x (all-order d c x p ao lx) (oo-of-all d c p m1 ao u1)))

(def-fns _ $ (erased oo-orders : (erased (Nat) c n) (erased (List (Nat)) p xs) (subterm erased (OrdersOff p c (Nil (Nat)) xs) oo) (erased (Length (Nat) xs n) l)
    -> (erased (List (Nat)) ks) (erased (Orders p xs ks) os) (erased (Repeat (Nat) n c ks) rk))
  (match erased oo _
    ((OONil _ _ _) (let-match erased l (LengthNil _)) (values (Nil _) (OrdNil p) (RepeatNil _ c)))
    (absurd (OOSkip _ _ _ _ _ ib _) ib)
    ((OOAt _ _ xs1 _ x o oo1)
      (let-match erased l (LengthCons _ _ _ n1 l1))
      (let ((erased ks) (erased os) (erased rk)) (oo-orders c n1 p xs1 oo1 l1))
      (values (Cons _ c ks) (OrdCons p xs1 ks x c o os) (RepeatCons _ n1 c ks rk)))))

(def-fns _ $ (erased all-of-oo : (erased (Nat) d c) (erased (List (Nat)) p ids) (erased (Iota d ids) io) (erased (OrdersOff p c (Nil (Nat)) ids) oo)
    -> (erased (AllOrder d p c) r))
  (let ((erased ks) (erased os) (erased rk)) (oo-orders c d p ids oo (iota-length d ids io)))
  (MkAllOrder d c p ks (MkOrderList d p ids ks io os) rk))

; One side of a patch: the orders under q of the images of m, read back as orders under p off b.
(def-fns _ $ (erased oo-side : (erased (Nat) d k c) (erased (List (Nat)) h p pi q b ids idk m) (erased (HPerm k p pi) pm) (erased (NCyc p b) nc)
    (erased (MorphOff h p q b idk) mo) (erased (Iota k idk) io) (erased (Iota d ids) iod) (erased (Distinct h) dh) (erased (Length (Nat) h k) lh)
    (erased (Under h d) uh) (erased (OrdersOff q c (Nil (Nat)) ids) oo) (subterm erased (Under m k) u) -> (erased (OrdersOff p c b m) r))
  (let-match erased u (UnderCons m1 x _ lx u1) ((UnderNil _) (OONil p b c)))
  (let ((erased rest)) (oo-side d k c h p pi q b ids idk m1 pm nc mo io iod dh lh uh oo u1))
  (match erased (in-dec x b) _
    ((OrL _ _ ib) (OOSkip p b m1 c x ib rest))
    ((OrR _ _ out)
      (let ((erased x2) (erased hx)) (nth-exists _ h k x lh lx))
      (OOAt p b m1 c x
        (order-pull k x x2 c h p pi q b idk pm nc mo io dh (oo-at q (Nil _) ids c x2 oo (iota-in d x2 ids iod (under-nth h x x2 d uh hx)) (NotInNil x2)) lx out hx)
        rest))))

; Each dart of xs is an image under h1, or an image under h2 of a dart off b2.
(def-adts $ (Cover : ((List (Nat)) h1 h2 b2 xs) -> Type)
  enum
  (many CvNil : (erased (List (Nat)) h1 h2 b2) -> (Cover h1 h2 b2 (Nil (Nat))))
  (many CvL : (erased (List (Nat)) h1 h2 b2 xs) (erased (Nat) x x1) (erased (Nth (Nat) h1 x1 x) p) (erased (Cover h1 h2 b2 xs) rest)
      -> (Cover h1 h2 b2 (Cons (Nat) x xs)))
  (many CvR : (erased (List (Nat)) h1 h2 b2 xs) (erased (Nat) x x2) (erased (Nth (Nat) h2 x2 x) p) (erased (NotIn x2 b2) out) (erased (Cover h1 h2 b2 xs) rest)
      -> (Cover h1 h2 b2 (Cons (Nat) x xs))))

; The orders under q of the darts covered by two sides.
(def-fns _ $ (erased oo-glue : (erased (Nat) k1 k2 c) (erased (List (Nat)) h1 p1 pi1 h2 p2 pi2 q b2 id1 id2 xs)
    (erased (HPerm k1 p1 pi1) pm1) (erased (MorphOff h1 p1 q (Nil (Nat)) id1) mo1) (erased (Iota k1 id1) io1) (erased (Distinct h1) dh1) (erased (Length (Nat) h1 k1) lh1)
    (erased (OrdersOff p1 c (Nil (Nat)) id1) oo1)
    (erased (HPerm k2 p2 pi2) pm2) (erased (NCyc p2 b2) nc2) (erased (MorphOff h2 p2 q b2 id2) mo2) (erased (Iota k2 id2) io2) (erased (Distinct h2) dh2)
    (erased (Length (Nat) h2 k2) lh2) (erased (OrdersOff p2 c b2 id2) oo2) (subterm erased (Cover h1 h2 b2 xs) cv)
    -> (erased (OrdersOff q c (Nil (Nat)) xs) r))
  (match erased cv _
    ((CvNil _ _ _) (OONil q (Nil _) c))
    ((CvL _ _ _ xs1 x x1 px cv1)
      (let ((erased lx)) (nth-lt-length _ h1 x1 k1 x px lh1))
      (OOAt q (Nil _) xs1 c x
        (order-push k1 x1 x c h1 p1 pi1 q (Nil _) id1 pm1 (NCNil p1) mo1 io1 dh1 (oo-at p1 (Nil _) id1 c x1 oo1 (iota-in k1 x1 id1 io1 lx) (NotInNil x1)) lx (NotInNil x1) px)
        (oo-glue k1 k2 c h1 p1 pi1 h2 p2 pi2 q b2 id1 id2 xs1 pm1 mo1 io1 dh1 lh1 oo1 pm2 nc2 mo2 io2 dh2 lh2 oo2 cv1)))
    ((CvR _ _ _ xs1 x x2 px out cv1)
      (let ((erased lx)) (nth-lt-length _ h2 x2 k2 x px lh2))
      (OOAt q (Nil _) xs1 c x
        (order-push k2 x2 x c h2 p2 pi2 q b2 id2 pm2 nc2 mo2 io2 dh2 (oo-at p2 b2 id2 c x2 oo2 (iota-in k2 x2 id2 io2 lx) out) lx out px)
        (oo-glue k1 k2 c h1 p1 pi1 h2 p2 pi2 q b2 id1 id2 xs1 pm1 mo1 io1 dh1 lh1 oo1 pm2 nc2 mo2 io2 dh2 lh2 oo2 cv1)))))

; Every dart is an image under hr, or under hd of a dart off bd.
(def-fns _ $ (erased cover-e : (erased (List (Nat)) hd hr bd xs) (subterm erased (PatchParts hd hr bd xs) pp) -> (erased (Cover hr hd bd xs) r))
  (let-match erased pp (PPCons _ _ _ xs1 x p pp1) ((PPNil _ _ _) (CvNil hr hd bd)))
  (let ((erased rest)) (cover-e hd hr bd xs1 pp1))
  (match erased p _
    ((PtDisk _ _ _ _ xd px out outr) (CvR hr hd bd xs1 x xd px out rest))
    ((PtRing _ _ _ _ xd xr px pin pr) (CvL hr hd bd xs1 x xr pr rest))
    ((PtRest _ _ _ _ xr pr outd) (CvL hr hd bd xs1 x xr pr rest))))

; Every dart is an image under hd, or under hr of a dart off br.
(def-fns _ $ (erased cover-n : (erased (List (Nat)) hd hr bd br bG bGr xs) (erased (Respects hr br bGr) rbr) (erased (RevApp (Nat) bG (Nil (Nat)) bGr) rv)
    (erased (Respects hd bd bG) rbd) (subterm erased (PatchParts hd hr bd xs) pp) -> (erased (Cover hd hr br xs) r))
  (let-match erased pp (PPCons _ _ _ xs1 x p pp1) ((PPNil _ _ _) (CvNil hd hr br)))
  (let ((erased rest)) (cover-n hd hr bd br bG bGr xs1 rbr rv rbd pp1))
  (match erased p _
    ((PtDisk _ _ _ _ xd px out outr) (CvL hd hr br xs1 x xd px rest))
    ((PtRing _ _ _ _ xd xr px pin pr) (CvL hd hr br xs1 x xd px rest))
    ((PtRest _ _ _ _ xr pr outd)
      (CvR hd hr br xs1 x xr pr
        (match erased (in-dec xr br) _
          (absurd (OrL _ _ ib)
            (let-match erased (revapp-out bG (Nil _) bGr x rv (in-map hr br bGr xr x ib rbr pr)) (OrL _ _ ig) (absurd (OrR _ _ i) i))
            (let ((erased jd) (erased ijd) (erased pjd)) (respects-in hd bd bG x rbd ig))
            (apart-irrefl x (notin-in x x hd outd (nth-in hd jd x pjd))))
          ((OrR _ _ o) o))
        rest))))

; plain_patch and cubic_patch, for an order c of the edge and of the node permutation: every dart of the whole map has order c
; under e exactly when every dart of the disk map off bd and every dart of the remainder map does, and under n exactly when every
; dart of the disk map and every dart of the remainder map off br does.
(def-fns _ $ (erased edge-order-patch : (erased (Nat) d dd dr c) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (AllOrder d e c) ao) (erased (List (Nat)) idd)
    (erased (Iota dd idd) iod) -> (erased (OrdersOff ed c bd idd) od) (erased (AllOrder dr er c) ar))
  (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids idd2 idr bG bGr h hd2 hr2 io iod2 ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
  (let-match erased (iota-fn dd idd idd2 iod iod2) (Refl _ _))
  (let ((erased nfd) (erased ndi) (erased fdi) (erased rnf) (erased pmed) (erased pmnd) (erased pmfd)) (hyper-core dd ed nd fd hd2))
  (let ((erased nfr) (erased nri) (erased fri) (erased rnfr) (erased pmer) (erased pmnr) (erased pmfr)) (hyper-core dr er nr fr hr2))
  (let ((erased oo)) (oo-of-all d c e ids ao (perm-under d ids ids (perm-id d ids io))))
  (values (oo-side d dd c hd ed nfd e bd ids idd idd pmed cyd med iod io dhd lhd uhd oo (perm-under dd idd idd (perm-id dd idd iod)))
    (all-of-oo dr c er idr ior (oo-side d dr c hr er nfr e (Nil _) ids idr idr pmer (NCNil er) mer ior io dhr lhr uhr oo (perm-under dr idr idr (perm-id dr idr ior))))))

(def-fns _ $ (erased order-edge-patch : (erased (Nat) d dd dr c) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (List (Nat)) idd) (erased (Iota dd idd) iod) (erased (OrdersOff ed c bd idd) od)
    (erased (AllOrder dr er c) ar) -> (erased (AllOrder d e c) ao))
  (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids idd2 idr bG bGr h hd2 hr2 io iod2 ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
  (let-match erased (iota-fn dd idd idd2 iod iod2) (Refl _ _))
  (let ((erased nfd) (erased ndi) (erased fdi) (erased rnf) (erased pmed) (erased pmnd) (erased pmfd)) (hyper-core dd ed nd fd hd2))
  (let ((erased nfr) (erased nri) (erased fri) (erased rnfr) (erased pmer) (erased pmnr) (erased pmfr)) (hyper-core dr er nr fr hr2))
  (all-of-oo d c e ids io
    (oo-glue dr dd c hr er nfr hd ed nfd e bd idr idd ids pmer mer ior dhr lhr (oo-of-all dr c er idr ar (perm-under dr idr idr (perm-id dr idr ior)))
      pmed cyd med iod dhd lhd od (cover-e hd hr bd ids pp))))

(def-fns _ $ (erased node-order-patch : (erased (Nat) d dd dr c) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (AllOrder d n c) ao) (erased (List (Nat)) idr)
    (erased (Iota dr idr) ior) -> (erased (AllOrder dd nd c) ad) (erased (OrdersOff nr c br idr) orr))
  (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids idd idr2 bG bGr h hd2 hr2 io iod ior2 lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
  (let-match erased (iota-fn dr idr idr2 ior ior2) (Refl _ _))
  (let ((erased nfd) (erased ndi) (erased fdi) (erased rnf) (erased pmed) (erased pmnd) (erased pmfd)) (hyper-core dd ed nd fd hd2))
  (let ((erased nfr) (erased nri) (erased fri) (erased rnfr) (erased pmer) (erased pmnr) (erased pmfr)) (hyper-core dr er nr fr hr2))
  (let ((erased oo)) (oo-of-all d c n ids ao (perm-under d ids ids (perm-id d ids io))))
  (values (all-of-oo dd c nd idd iod (oo-side d dd c hd nd ndi n (Nil _) ids idd idd pmnd (NCNil nd) mnd iod io dhd lhd uhd oo (perm-under dd idd idd (perm-id dd idd iod))))
    (oo-side d dr c hr nr nri n br ids idr idr pmnr cyr mnr ior io dhr lhr uhr oo (perm-under dr idr idr (perm-id dr idr ior)))))

(def-fns _ $ (erased order-node-patch : (erased (Nat) d dd dr c) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (List (Nat)) idr) (erased (Iota dr idr) ior) (erased (AllOrder dd nd c) ad)
    (erased (OrdersOff nr c br idr) orr) -> (erased (AllOrder d n c) ao))
  (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids idd idr2 bG bGr h hd2 hr2 io iod ior2 lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
  (let-match erased (iota-fn dr idr idr2 ior ior2) (Refl _ _))
  (let ((erased nfd) (erased ndi) (erased fdi) (erased rnf) (erased pmed) (erased pmnd) (erased pmfd)) (hyper-core dd ed nd fd hd2))
  (let ((erased nfr) (erased nri) (erased fri) (erased rnfr) (erased pmer) (erased pmnr) (erased pmfr)) (hyper-core dr er nr fr hr2))
  (all-of-oo d c n ids io
    (oo-glue dd dr c hd nd ndi hr nr nri n br idd idr ids pmnd mnd iod dhd lhd (oo-of-all dd c nd idd ad (perm-under dd idd idd (perm-id dd idd iod)))
      pmnr cyr mnr ior dhr lhr orr (cover-n hd hr bd br bG bGr ids rbr rv rbd pp))))

; A side of a patch: sd lists the darts below k off c, h sends them to s, and l back. For a permutation p of the darts below k with
; c closed under p, h (p x) = q (h x) off b, a part of c.
(def-fns _ $ (erased side-in : (erased (Nat) k x) (erased (List (Nat)) c idk cs sd) (erased (Iota k idk) io) (erased (Split c idk cs sd) sp)
    (erased (Lt x k) lx) (erased (NotIn x c) out) -> (erased (In x sd) r))
  (match erased (split-cover c idk cs sd x sp (iota-in k x idk io lx)) _
    (absurd (OrL _ _ i) (apart-irrefl x (notin-in x x c out (split-in c idk cs sd x sp i))))
    ((OrR _ _ i) i)))

(def-fns _ $ (erased side-lift-d : (erased (Nat) k d) (erased (List (Nat)) h l ids sd s m) (erased (List (Bond)) gp) (erased (InvL h ids l) iv)
    (erased (Iota d ids) io) (erased (Distinct h) dh) (erased (Length (Nat) h k) lh) (erased (Under h d) uh) (erased (Respects h sd s) rp)
    (erased (Under sd k) us) (subterm erased (Sub m sd) sb) -> (erased (Lift gp h l s m) r))
  (let-match erased sb (HSubCons x m1 _ ix sb1) ((HSubNil _) (LiftNil gp h l s)))
  (let ((erased y) (erased hx)) (nth-exists _ h k x lh (under-in sd x k us ix)))
  (LiftCons gp h l s m1 x y x hx (in-map h sd s x y ix rp hx) (inv-nth h ids l y y x iv dh (iota-nth d y ids io (under-nth h x y d uh hx)) hx)
    (ConnHere gp x) (side-lift-d k d h l ids sd s m1 gp iv io dh lh uh rp us sb1)))

(def-fns _ $ (erased side-lift-g : (erased (Nat) d) (erased (List (Nat)) h l ids sd s m) (erased (List (Bond)) gq) (erased (InvL h ids l) iv)
    (erased (Iota d ids) io) (erased (Distinct h) dh) (erased (Under h d) uh) (erased (Respects h sd s) rp) (subterm erased (Sub m s) sb)
    -> (erased (Lift gq l h sd m) r))
  (let-match erased sb (HSubCons x m1 _ ix sb1) ((HSubNil _) (LiftNil gq l h sd)))
  (let ((erased xd) (erased ixd) (erased hx)) (respects-in h sd s x rp ix))
  (LiftCons gq l h sd m1 x xd x (inv-nth h ids l x x xd iv dh (iota-nth d x ids io (under-nth h xd x d uh hx)) hx) ixd hx (ConnHere gq x)
    (side-lift-g d h l ids sd s m1 gq iv io dh uh rp sb1)))

(def-fns _ $ (erased side-moves-d : (erased (Nat) k d) (erased (List (Nat)) h p pi q b c idk cs sd) (erased (List (Bond)) gp g gq g2) (erased (HPerm k p pi) pm)
    (erased (Graph k p gp) grp) (erased (Shut c gp) shc) (erased (Sub b c) sbc) (erased (MorphOff h p q b idk) mo) (erased (Iota k idk) io)
    (erased (Split c idk cs sd) sp) (erased (Length (Nat) h k) lh) (erased (Graph d q gq) grq) (erased (Spans g2 gq) s2) (subterm erased (Fun p g) fn)
    -> (erased (Moves g sd h g2) r))
  (let-match erased fn (FunCons _ g1 x y px fn1) ((FunNil _) (MvNil sd h g2)))
  (let ((erased rest)) (side-moves-d k d h p pi q b c idk cs sd gp g1 gq g2 pm grp shc sbc mo io sp lh grq s2 fn1))
  (let ((erased lx)) (pre-lt k x y p pi pm px))
  (let ((erased ly)) (perm-val k x y p pi pm px))
  (let ((erased a)) (graph-adj k x y p gp grp px))
  (match erased (in-dec x c) _
    ((OrL _ _ ic)
      (let ((erased dj)) (split-disj c idk cs sd sp))
      (MvOut g1 g2 sd h x y (notin-of-disj x sd c dj ic) (notin-of-disj y sd c dj (shut-adj-in c gp x y a shc ic)) rest))
    ((OrR _ _ oc)
      (let ((erased x2) (erased hx)) (nth-exists _ h k x lh lx))
      (let ((erased y2) (erased hy) (erased qx)) (morph h p q b idk k x y x2 mo io lx (notin-sub x b c sbc oc) px hx))
      (MvIn g1 g2 sd h x y x2 y2 (side-in k x c idk cs sd io sp lx oc) (side-in k y c idk cs sd io sp ly (shut-adj-out c gp x y a shc oc)) hx hy
        (spans-conn g2 gq x2 y2 (conn-adj gq x2 y2 (graph-adj d x2 y2 q gq grq qx)) s2) rest))))

(def-fns _ $ (erased side-moves-g : (erased (Nat) k d) (erased (List (Nat)) h l ids p pi q qi b c idk cs sd s) (erased (List (Bond)) gp g d2)
    (erased (HPerm k p pi) pm) (erased (HPerm d q qi) pq) (erased (Graph k p gp) grp) (erased (Shut c gp) shc) (erased (Sub b c) sbc)
    (erased (MorphOff h p q b idk) mo) (erased (Iota k idk) io) (erased (Iota d ids) iod) (erased (Split c idk cs sd) sp) (erased (InvL h ids l) iv)
    (erased (Distinct h) dh) (erased (Length (Nat) h k) lh) (erased (Under h d) uh) (erased (Under sd k) usd) (erased (Respects h sd s) rp)
    (erased (Spans d2 gp) s1) (subterm erased (Fun q g) fn) -> (erased (Moves g s l d2) r))
  (let-match erased fn (FunCons _ g1 x y qx fn1) ((FunNil _) (MvNil s l d2)))
  (let ((erased rest)) (side-moves-g k d h l ids p pi q qi b c idk cs sd s gp g1 d2 pm pq grp shc sbc mo io iod sp iv dh lh uh usd rp s1 fn1))
  (match erased (in-dec x s) _
    ((OrL _ _ ix)
      (let ((erased xd) (erased ixd) (erased hx)) (respects-in h sd s x rp ix))
      (let ((erased lxd)) (under-in sd xd k usd ixd))
      (let ((erased ocx)) (split-out c idk cs sd xd sp ixd))
      (let ((erased yd) (erased pyd) (erased lyd)) (perm-nth k xd p pi pm lxd))
      (let ((erased w) (erased hy) (erased qw)) (morph h p q b idk k xd yd x mo io lxd (notin-sub xd b c sbc ocx) pyd hx))
      (let-match erased (nth-fn _ q x w y qw qx) (Refl _ _))
      (let ((erased iyd)) (side-in k yd c idk cs sd io sp lyd (shut-adj-out c gp xd yd (graph-adj k xd yd p gp grp pyd) shc ocx)))
      (MvIn g1 d2 s l x y xd yd ix (in-map h sd s yd y iyd rp hy)
        (inv-nth h ids l x x xd iv dh (iota-nth d x ids iod (under-nth h xd x d uh hx)) hx)
        (inv-nth h ids l y y yd iv dh (iota-nth d y ids iod (under-nth h yd y d uh hy)) hy)
        (spans-conn d2 gp xd yd (conn-adj gp xd yd (graph-adj k xd yd p gp grp pyd)) s1) rest))
    ((OrR _ _ ox)
      (MvOut g1 d2 s l x y ox
        (match erased (in-dec y s) _
          (absurd (OrL _ _ iy)
            (let ((erased yd) (erased iyd) (erased hy)) (respects-in h sd s y rp iy))
            (let ((erased lyd)) (under-in sd yd k usd iyd))
            (let ((erased ocy)) (split-out c idk cs sd yd sp iyd))
            (let ((erased xd) (erased pxd) (erased lxd)) (perm-nth k yd pi p (perm-sym k p pi pm) lyd))
            (let ((erased pxy)) (perm-inv k yd xd pi p (perm-sym k p pi pm) pxd))
            (let ((erased ocx)) (match erased (in-dec xd c) (((NotIn xd c) r))
              (absurd (OrL _ _ ic) (apart-irrefl yd (notin-in yd yd c ocy (shut-adj-in c gp xd yd (graph-adj k xd yd p gp grp pxy) shc ic))))
              ((OrR _ _ o) o)))
            (let ((erased x2) (erased hx2)) (nth-exists _ h k xd lh lxd))
            (let ((erased w) (erased hw) (erased qw)) (morph h p q b idk k xd yd x2 mo io lxd (notin-sub xd b c sbc ocx) pxy hx2))
            (let-match erased (nth-fn _ h yd w y hw hy) (Refl _ _))
            (let-match erased (perm-inj d x2 x y q qi pq qw qx) (Refl _ _))
            (apart-irrefl x (notin-in x x s ox (in-map h sd s xd x (side-in k xd c idk cs sd io sp lxd ocx) rp hx2))))
          ((OrR _ _ oy) oy))
        rest))))

; The bonds of p and of q, moved along h and l, into graphs that join them.
(def-fns _ $ (erased perm-moves : (erased (Nat) k d) (erased (List (Nat)) h l ids p pi q qi b c idk cs sd s) (erased (List (Bond)) gp gq d2 g2)
    (erased (HPerm k p pi) pm) (erased (HPerm d q qi) pq) (erased (Graph k p gp) grp) (erased (Graph d q gq) grq) (erased (Shut c gp) shc) (erased (Sub b c) sbc)
    (erased (MorphOff h p q b idk) mo) (erased (Iota k idk) io) (erased (Iota d ids) iod) (erased (Split c idk cs sd) sp) (erased (InvL h ids l) iv)
    (erased (Distinct h) dh) (erased (Length (Nat) h k) lh) (erased (Under h d) uh) (erased (Under sd k) usd) (erased (Respects h sd s) rp)
    (erased (Spans g2 gq) s2) (erased (Spans d2 gp) s1) -> (erased (Moves gp sd h g2) mv1) (erased (Moves gq s l d2) mv2))
  (values (side-moves-d k d h p pi q b c idk cs sd gp gp gq g2 pm grp shc sbc mo io sp lh grq s2 (graph-fun k p gp grp))
    (side-moves-g k d h l ids p pi q qi b c idk cs sd s gp gq d2 pm pq grp shc sbc mo io iod sp iv dh lh uh usd rp s1 (graph-fun d q gq grq))))

; The classes of gD on sd and those of gG on s correspond.
(def-fns _ $ (erased side-co : (erased (Nat) k d c kq) (erased (List (Nat)) h l ids sd s) (erased (List (Bond)) gD gG) (erased (InvL h ids l) iv)
    (erased (Iota d ids) iod) (erased (Distinct h) dh) (erased (Length (Nat) h k) lh) (erased (Under h d) uh) (erased (Respects h sd s) rp)
    (erased (Under sd k) usd) (erased (Moves gD sd h gG) mv1) (erased (Moves gG s l gD) mv2) (erased (Classes gG d kq) cs) (erased (ClassesOn gD sd c) co)
    -> (erased (ClassesOn gG s c) r))
  (co-map gD gG sd s h l c d kq co (side-lift-d k d h l ids sd s sd gD iv iod dh lh uh rp usd (sub-refl sd))
    (side-lift-g d h l ids sd s s gG iv iod dh uh rp (sub-refl s)) mv1 mv2 cs (respects-under-vals h sd s d rp uh)))

(def-fns _ $ (erased side-co-back : (erased (Nat) k d c kp) (erased (List (Nat)) h l ids sd s) (erased (List (Bond)) gD gG) (erased (InvL h ids l) iv)
    (erased (Iota d ids) iod) (erased (Distinct h) dh) (erased (Length (Nat) h k) lh) (erased (Under h d) uh) (erased (Respects h sd s) rp)
    (erased (Under sd k) usd) (erased (Moves gD sd h gG) mv1) (erased (Moves gG s l gD) mv2) (erased (Classes gD k kp) cs) (erased (ClassesOn gG s c) co)
    -> (erased (ClassesOn gD sd c) r))
  (co-map gG gD s sd l h c k kp co (side-lift-g d h l ids sd s s gG iv iod dh uh rp (sub-refl s))
    (side-lift-d k d h l ids sd s sd gD iv iod dh lh uh rp usd (sub-refl sd)) mv2 mv1 cs usd))

; e is 0 for an empty list and 1 otherwise.
(def-adts $ (NonNil : ((List (Nat)) xs) ((Nat) e) -> Type)
  enum
  (many NNNil : -> (NonNil (Nil (Nat)) (Zero)))
  (many NNCons : (erased (Nat) x) (erased (List (Nat)) xs) -> (NonNil (Cons (Nat) x xs) (Succ (Zero)))))

(def-fns _ $ (erased split-nil : (subterm erased (List (Nat)) xs) -> (erased (Split (Nil (Nat)) xs (Nil (Nat)) xs) r))
  (let-match erased xs (Cons _ x xs1) ((Nil _) (SpNil (Nil _))))
  (SpOut (Nil _) xs1 (Nil _) xs1 x (NotInNil x) (split-nil xs1)))

(def-fns _ $ (erased ncyc-shut : (erased (Nat) k) (erased (List (Nat)) p pi b) (erased (List (Bond)) g) (erased (HPerm k p pi) pm) (erased (NCyc p b) nc)
    (subterm erased (Fun p g) fn) -> (erased (Shut b g) r))
  (let-match erased fn (FunCons _ g1 x y px fn1) ((FunNil _) (ShutNil b)))
  (let ((erased rest)) (ncyc-shut k p pi b g1 pm nc fn1))
  (match erased (in-dec x b) _
    ((OrL _ _ ib) (ShutIn b g1 x y ib (ncyc-next p b x y nc ib px) rest))
    ((OrR _ _ ob) (ShutOut b g1 x y ob (off-next k x y p pi b pm nc ob px) rest))))

(def-fns _ $ (erased shut-compl : (erased (Nat) k) (erased (List (Nat)) c idk cs sd) (erased (List (Bond)) g) (subterm erased (Shut c g) sh)
    (erased (Split c idk cs sd) sp) (erased (Iota k idk) io) (erased (Below g k) bg) -> (erased (Shut sd g) r))
  (match erased sh _
    ((ShutNil _) (ShutNil sd))
    ((ShutIn _ g1 x y px py sh1)
      (let-match erased bg (BelowCons _ _ _ _ lx ly bg1))
      (let ((erased dj)) (split-disj c idk cs sd sp))
      (ShutOut sd g1 x y (notin-of-disj x sd c dj px) (notin-of-disj y sd c dj py) (shut-compl k c idk cs sd g1 sh1 sp io bg1)))
    ((ShutOut _ g1 x y px py sh1)
      (let-match erased bg (BelowCons _ _ _ _ lx ly bg1))
      (ShutIn sd g1 x y (side-in k x c idk cs sd io sp lx px) (side-in k y c idk cs sd io sp ly py) (shut-compl k c idk cs sd g1 sh1 sp io bg1)))))

(def-fns _ $ (erased fpath-covers : (erased (List (Nat)) p xs) (erased (List (Bond)) g) (erased (Nat) k r x y) (erased (Graph k p g) gr) (erased (Conn g r x) c)
    (subterm erased (FPath p x xs y) fp) -> (erased (Covers g (Cons (Nat) r (Nil (Nat))) (Cons (Nat) x xs)) res))
  (let ((erased rs)) (Cons (Nat) r (Nil (Nat))))
  (match erased fp _
    ((FPNil _ _) (CovCons g rs (Nil _) x r (InHere r (Nil _)) c (CovNil g rs)))
    ((FPCons _ xs1 _ z _ px fp1)
      (CovCons g rs (Cons _ z xs1) x r (InHere r (Nil _)) c
        (fpath-covers p xs1 g k r z y gr (conn-cat g r x z c (conn-adj g x z (graph-adj k x z p g gr px))) fp1)))))

; A cycle of p lies in one orbit, if it is not empty.
(def-fns _ $ (erased co-cycle : (erased (Nat) k e) (erased (List (Nat)) p b) (erased (List (Bond)) g) (erased (Graph k p g) gr) (erased (NCyc p b) nc)
    (erased (NonNil b e) nn) -> (erased (ClassesOn g b e) r))
  (match erased nc _
    ((NCNil _) (let-match erased nn (NNNil)) (MkClassesOn g (Nil _) (Nil _) (Zero) (LengthNil _) (HSubNil _) (PrNil g) (CovNil g (Nil _))))
    ((NCCons _ xs x y fp back)
      (let-match erased nn (NNCons _ _))
      (let ((erased rs)) (Cons (Nat) x (Nil (Nat))))
      (MkClassesOn g (Cons _ x xs) rs (Succ (Zero)) (LengthCons _ x (Nil _) (Zero) (LengthNil _)) (HSubCons x (Nil _) _ (InHere x xs) (HSubNil _))
        (PrCons g x (Nil _) (SANil g x) (PrNil g)) (fpath-covers p xs g k x x y gr (ConnHere g x) fp)))))

(def-fns _ $ (erased cover-app-sub : (erased (Nat) k2) (erased (List (Nat)) h1 h2 b2 id2 cs2 sd2 s2 st xs) (subterm erased (Cover h1 h2 b2 xs) cv)
    (erased (AppN h1 s2 st) ap) (erased (Split b2 id2 cs2 sd2) sp) (erased (Respects h2 sd2 s2) rp) (erased (Iota k2 id2) io) (erased (Length (Nat) h2 k2) lh)
    -> (erased (Sub xs st) r))
  (match erased cv _
    ((CvNil _ _ _) (HSubNil st))
    ((CvL _ _ _ xs1 x x1 px cv1) (HSubCons x xs1 st (app-in-l h1 s2 st x ap (nth-in h1 x1 x px)) (cover-app-sub k2 h1 h2 b2 id2 cs2 sd2 s2 st xs1 cv1 ap sp rp io lh)))
    ((CvR _ _ _ xs1 x x2 px out cv1)
      (HSubCons x xs1 st
        (app-in-r h1 s2 st x ap (in-map h2 sd2 s2 x2 x (side-in k2 x2 b2 id2 cs2 sd2 io sp (nth-lt-length _ h2 x2 k2 x px lh) out) rp px))
        (cover-app-sub k2 h1 h2 b2 id2 cs2 sd2 s2 st xs1 cv1 ap sp rp io lh)))))

; The orbits of q on the whole map, of p1 on one side that h1 sends exactly, and of p2 on the other side, where h2 is exact off
; the cycle b2 of p2: kq + eb = k1 + k2.
(def-fns _ $ (erased patch-count : (erased (Nat) k1 k2 d kq ko1 ko2 eb) (erased (List (Nat)) h1 p1 pi1 h2 p2 pi2 q qi b2 id1 id2 ids cs2 sd2 s2)
    (erased (HPerm k1 p1 pi1) pm1) (erased (HPerm k2 p2 pi2) pm2) (erased (HPerm d q qi) pq)
    (erased (MorphOff h1 p1 q (Nil (Nat)) id1) mo1) (erased (MorphOff h2 p2 q b2 id2) mo2) (erased (Iota k1 id1) io1) (erased (Iota k2 id2) io2) (erased (Iota d ids) io)
    (erased (Distinct h1) dh1) (erased (Length (Nat) h1 k1) lh1) (erased (Under h1 d) uh1) (erased (Distinct h2) dh2) (erased (Length (Nat) h2 k2) lh2)
    (erased (Under h2 d) uh2) (erased (NCyc p2 b2) nc2) (erased (Under b2 k2) ub2) (erased (NonNil b2 eb) nn) (erased (Cover h1 h2 b2 ids) cv)
    (erased (Split b2 id2 cs2 sd2) sp2) (erased (Respects h2 sd2 s2) rp2) (erased (Disj s2 h1) dj)
    (erased (Orbits d q kq) oq) (erased (Orbits k1 p1 ko1) o1) (erased (Orbits k2 p2 ko2) o2) -> (erased (Nat) s) (erased (Add kq eb s) a1) (erased (Add ko1 ko2 s) a2))
  (let-match erased oq (MkOrbits _ _ _ gq grq csq))
  (let-match erased o1 (MkOrbits _ _ _ gp1 grp1 cs1))
  (let-match erased o2 (MkOrbits _ _ _ gp2 grp2 cs2c))
  (let ((erased bq)) (classes-below gq d kq csq))
  (let ((erased bp2)) (classes-below gp2 k2 ko2 cs2c))
  (let ((erased uid1)) (perm-under k1 id1 id1 (perm-id k1 id1 io1)))
  (let ((erased uid2)) (perm-under k2 id2 id2 (perm-id k2 id2 io2)))
  (let ((erased l1) (erased iv1)) (inv-exists h1 ids))
  (let ((erased sp1)) (split-nil id1))
  (let ((erased rp1)) (respects-id-right k1 id1 h1 io1 lh1))
  (let ((erased mv1a) (erased mv1b))
    (perm-moves k1 d h1 l1 ids p1 pi1 q qi (Nil _) (Nil _) id1 (Nil _) id1 h1 gp1 gq gp1 gq pm1 pq grp1 grq
      (ncyc-shut k1 p1 pi1 (Nil _) gp1 pm1 (NCNil p1) (graph-fun k1 p1 gp1 grp1)) (HSubNil _) mo1 io1 io sp1 iv1 dh1 lh1 uh1 uid1 rp1
      (spans-self gq) (spans-self gp1)))
  (let ((erased c1)) (side-co k1 d ko1 kq h1 l1 ids id1 h1 gp1 gq iv1 io dh1 lh1 uh1 rp1 uid1 mv1a mv1b csq (co-of-classes gp1 k1 ko1 id1 cs1 io1)))
  (let ((erased shb)) (ncyc-shut k2 p2 pi2 b2 gp2 pm2 nc2 (graph-fun k2 p2 gp2 grp2)))
  (let ((erased shs)) (shut-compl k2 b2 id2 cs2 sd2 gp2 shb sp2 io2 bp2))
  (let ((erased sb2) (erased ssd2)) (split-sub b2 id2 cs2 sd2 sp2))
  (let ((erased usd2)) (sub-under sd2 id2 k2 ssd2 uid2))
  (let ((erased ks) (erased cos)) (co-exists gp2 k2 ko2 sd2 cs2c shs usd2))
  (let ((erased l2) (erased iv2)) (inv-exists h2 ids))
  (let ((erased mv2a) (erased mv2b))
    (perm-moves k2 d h2 l2 ids p2 pi2 q qi b2 b2 id2 cs2 sd2 s2 gp2 gq gp2 gq pm2 pq grp2 grq shb (sub-refl b2) mo2 io2 io sp2 iv2 dh2 lh2 uh2 usd2 rp2
      (spans-self gq) (spans-self gp2)))
  (let ((erased c2)) (side-co k2 d ks kq h2 l2 ids sd2 s2 gp2 gq iv2 io dh2 lh2 uh2 rp2 usd2 mv2a mv2b csq cos))
  (let ((erased st2) (erased ap2)) (app-exists b2 sd2))
  (let ((erased t2) (erased at2)) (add-ex eb ks))
  (let ((erased all2)) (co-union gp2 k2 eb ks t2 b2 sd2 st2 id2 (co-cycle k2 eb p2 b2 gp2 grp2 nc2 nn) cos ap2
    (split-app-sub b2 id2 cs2 sd2 st2 id2 sp2 ap2 (sub-refl id2)) (app-sub b2 sd2 st2 id2 ap2 (under-sub k2 b2 id2 ub2 io2) ssd2) shb bp2 (split-disj b2 id2 cs2 sd2 sp2) ub2 usd2 at2))
  (let-match erased (co-unique gp2 id2 t2 ko2 all2 (co-of-classes gp2 k2 ko2 id2 cs2c io2)) (Refl _ _))
  (let ((erased st) (erased ap)) (app-exists h1 s2))
  (let ((erased t1) (erased at1)) (add-ex ko1 ks))
  (let ((erased us2)) (respects-under-vals h2 sd2 s2 d rp2 uh2))
  (let ((erased all)) (co-union gq d ko1 ks t1 h1 s2 st ids c1 c2 ap
    (cover-app-sub k2 h1 h2 b2 id2 cs2 sd2 s2 st ids cv ap sp2 rp2 io2 lh2) (app-sub h1 s2 st ids ap (under-sub d h1 ids uh1 io) (under-sub d s2 ids us2 io))
    (moves-shut gq gp1 h1 l1 mv1b) bq dj uh1 us2 at1))
  (let-match erased (co-unique gq ids t1 kq all (co-of-classes gq d kq ids csq io)) (Refl _ _))
  (let ((erased s) (erased a1)) (add-ex kq eb))
  (let ((erased x) (erased q1) (erased q2)) (add-assoc ko1 ks eb kq s at1 a1))
  (let-match erased (add-fn eb ks x t2 (add-comm ks eb x q1) at2) (Refl _ _))
  (values s a1 q2))

; The image of a dart of the disk map off its ring is not an image of the remainder map.
(def-fns _ $ (erased disk-notin-r : (erased (Nat) d xd x) (erased (List (Nat)) hd hr bd ids) (erased (PatchParts hd hr bd ids) pp) (erased (Iota d ids) io)
    (erased (Distinct hd) dh) (erased (Under hd d) uh) (erased (Nth (Nat) hd xd x) px) (erased (NotIn xd bd) out) -> (erased (NotIn x hr) r))
  (match erased (parts-at hd hr bd ids x pp (iota-in d x ids io (under-nth hd xd x d uh px))) _
    ((PtDisk _ _ _ _ xd2 px2 out2 outr) outr)
    (absurd (PtRing _ _ _ _ xd2 xr px2 pin pr)
      (let-match erased (distinct-nth hd xd2 xd x dh px2 px) (Refl _ _))
      (apart-irrefl xd (notin-in xd xd bd out pin)))
    (absurd (PtRest _ _ _ _ xr pr outd) (apart-irrefl x (notin-in x x hd outd (nth-in hd xd x px))))))

; The image of a dart of the remainder map off its ring is not an image of the disk map.
(def-fns _ $ (erased rest-notin-d : (erased (Nat) d xr x) (erased (List (Nat)) hd hr bd br bG bGr ids) (erased (PatchParts hd hr bd ids) pp) (erased (Iota d ids) io)
    (erased (Distinct hr) dh) (erased (Under hr d) uh) (erased (Respects hd bd bG) rbd) (erased (Respects hr br bGr) rbr) (erased (RevApp (Nat) bG (Nil (Nat)) bGr) rv)
    (erased (Nth (Nat) hr xr x) px) (erased (NotIn xr br) out) -> (erased (NotIn x hd) r))
  (match erased (parts-at hd hr bd ids x pp (iota-in d x ids io (under-nth hr xr x d uh px))) _
    (absurd (PtDisk _ _ _ _ xd px2 out2 outr) (apart-irrefl x (notin-in x x hr outr (nth-in hr xr x px))))
    (absurd (PtRing _ _ _ _ xd xr2 px2 pin pr)
      (let ((erased xr3) (erased ixr) (erased p3)) (respects-in hr br bGr x rbr (revapp-in bG (Nil _) bGr x rv (OrL _ _ (in-map hd bd bG xd x pin rbd px2)))))
      (let-match erased (distinct-nth hr xr3 xr x dh p3 px) (Refl _ _))
      (apart-irrefl xr (notin-in xr xr br out ixr)))
    ((PtRest _ _ _ _ xr2 pr outd) outd)))

(def-fns _ $ (erased disk-disj : (erased (Nat) d) (erased (List (Nat)) hd hr bd ids idd cs sd m ys) (erased (PatchParts hd hr bd ids) pp) (erased (Iota d ids) io)
    (erased (Distinct hd) dh) (erased (Under hd d) uh) (erased (Split bd idd cs sd) sp) (erased (Sub m sd) sb) (subterm erased (Respects hd m ys) rp)
    -> (erased (Disj ys hr) r))
  (let-match erased rp (RespCons _ m1 ys1 xd x px rp1) ((RespNil _) (DisjNil hr)))
  (let-match erased sb (HSubCons _ _ _ ixd sb1))
  (DisjCons x ys1 hr (disk-notin-r d xd x hd hr bd ids pp io dh uh px (split-out bd idd cs sd xd sp ixd)) (disk-disj d hd hr bd ids idd cs sd m1 ys1 pp io dh uh sp sb1 rp1)))

(def-fns _ $ (erased rest-disj : (erased (Nat) d) (erased (List (Nat)) hd hr bd br bG bGr ids idr cs sd m ys) (erased (PatchParts hd hr bd ids) pp) (erased (Iota d ids) io)
    (erased (Distinct hr) dh) (erased (Under hr d) uh) (erased (Respects hd bd bG) rbd) (erased (Respects hr br bGr) rbr) (erased (RevApp (Nat) bG (Nil (Nat)) bGr) rv)
    (erased (Split br idr cs sd) sp) (erased (Sub m sd) sb) (subterm erased (Respects hr m ys) rp) -> (erased (Disj ys hd) r))
  (let-match erased rp (RespCons _ m1 ys1 xr x px rp1) ((RespNil _) (DisjNil hd)))
  (let-match erased sb (HSubCons _ _ _ ixr sb1))
  (DisjCons x ys1 hd (rest-notin-d d xr x hd hr bd br bG bGr ids pp io dh uh rbd rbr rv px (split-out br idr cs sd xr sp ixr))
    (rest-disj d hd hr bd br bG bGr ids idr cs sd m1 ys1 pp io dh uh rbd rbr rv sp sb1 rp1)))

; The edge orbits of the whole map, and one more if the ring is not empty, are those of the disk map and of the remainder map.
(def-fns _ $ (erased edge-patch : (erased (Nat) d dd dr ke ked ker eb) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (Orbits d e ke) oe) (erased (Orbits dd ed ked) od) (erased (Orbits dr er ker) orr)
    (erased (NonNil bd eb) nn) -> (erased (Nat) s) (erased (Add ke eb s) a1) (erased (Add ker ked s) a2))
  (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids idd idr bG bGr h hd2 hr2 io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pme) (erased pmn) (erased pmf)) (hyper-core d e n f h))
  (let ((erased nfd) (erased ndi) (erased fdi) (erased rnfd) (erased pmed) (erased pmnd) (erased pmfd)) (hyper-core dd ed nd fd hd2))
  (let ((erased nfr) (erased nri) (erased fri) (erased rnfr) (erased pmer) (erased pmnr) (erased pmfr)) (hyper-core dr er nr fr hr2))
  (let ((erased cs) (erased sdd) (erased sp)) (split-exists bd idd))
  (let ((erased sb) (erased ssd)) (split-sub bd idd cs sdd sp))
  (let ((erased s2) (erased rp)) (respects-exists hd sdd dd (sub-under sdd idd dd ssd (perm-under dd idd idd (perm-id dd idd iod))) lhd))
  (patch-count dr dd d ke ker ked eb hr er nfr hd ed nfd e nf bd idr idd ids cs sdd s2 pmer pmed pme mer med ior iod io dhr lhr uhr dhd lhd uhd cyd
    (respects-under hd bd bG dd rbd lhd) nn (cover-e hd hr bd ids pp) sp rp (disk-disj d hd hr bd ids idd cs sdd sdd s2 pp io dhd uhd sp (sub-refl sdd) rp)
    oe orr od))

; The node orbits of the whole map, and one more if the ring is not empty, are those of the disk map and of the remainder map.
(def-fns _ $ (erased node-patch : (erased (Nat) d dd dr kn knd knr eb) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (Orbits d n kn) on) (erased (Orbits dd nd knd) od) (erased (Orbits dr nr knr) orr)
    (erased (NonNil br eb) nn) -> (erased (Nat) s) (erased (Add kn eb s) a1) (erased (Add knd knr s) a2))
  (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids idd idr bG bGr h hd2 hr2 io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pme) (erased pmn) (erased pmf)) (hyper-core d e n f h))
  (let ((erased nfd) (erased ndi) (erased fdi) (erased rnfd) (erased pmed) (erased pmnd) (erased pmfd)) (hyper-core dd ed nd fd hd2))
  (let ((erased nfr) (erased nri) (erased fri) (erased rnfr) (erased pmer) (erased pmnr) (erased pmfr)) (hyper-core dr er nr fr hr2))
  (let ((erased cs) (erased sdr) (erased sp)) (split-exists br idr))
  (let ((erased sb) (erased ssd)) (split-sub br idr cs sdr sp))
  (let ((erased s2) (erased rp)) (respects-exists hr sdr dr (sub-under sdr idr dr ssd (perm-under dr idr idr (perm-id dr idr ior))) lhr))
  (patch-count dd dr d kn knd knr eb hd nd ndi hr nr nri n ni br idd idr ids cs sdr s2 pmnd pmnr pmn mnd mnr iod ior io dhd lhd uhd dhr lhr uhr cyr
    (respects-under hr br bGr dr rbr lhr) nn (cover-n hd hr bd br bG bGr ids rbr rv rbd pp) sp rp
    (rest-disj d hd hr bd br bG bGr ids idr cs sdr sdr s2 pp io dhr uhr rbd rbr rv sp (sub-refl sdr) rp)
    on od orr))

; b follows a in R.
(def-adts $ (Adj2 : ((List (Nat)) R) ((Nat) a b) -> Type)
  enum
  (many A2Here : (erased (Nat) a b) (erased (List (Nat)) R) -> (Adj2 (Cons (Nat) a (Cons (Nat) b R)) a b))
  (many A2There : (erased (Nat) c a b) (erased (List (Nat)) R) (erased (Adj2 R a b) p) -> (Adj2 (Cons (Nat) c R) a b)))

; R starts with x.
(def-adts $ (HeadIs : ((List (Nat)) R) ((Nat) x) -> Type)
  enum
  (many HI : (erased (Nat) x) (erased (List (Nat)) R) -> (HeadIs (Cons (Nat) x R) x)))

; R ends with x.
(def-adts $ (LastIs : ((List (Nat)) R) ((Nat) x) -> Type)
  enum
  (many LIOne : (erased (Nat) x) -> (LastIs (Cons (Nat) x (Nil (Nat))) x))
  (many LIMore : (erased (Nat) c x) (erased (List (Nat)) R) (erased (LastIs R x) p) -> (LastIs (Cons (Nat) c R) x)))

; u heads pre and v heads w.
(def-adts $ (HeadPair : ((List (Nat)) pre w) ((Nat) u v) -> Type)
  enum
  (many HP : (erased (Nat) u v) (erased (List (Nat)) pre w) -> (HeadPair (Cons (Nat) u pre) (Cons (Nat) v w) u v)))

(def-fns _ $ (erased lastis-fn : (erased (List (Nat)) R) (erased (Nat) x y) (subterm erased (LastIs R x) p) (erased (LastIs R y) q) -> (erased (Eq (Nat) x y) e))
  (match erased p _
    ((LIOne _) (match erased q _ ((LIOne _) (Refl _ x)) (absurd (LIMore _ _ _ q1) q1)))
    ((LIMore c _ R1 p1) (match erased q _ (absurd (LIOne _) p1) ((LIMore _ _ _ q1) (lastis-fn R1 x y p1 q1))))))

(def-fns _ $ (erased lastis-map : (erased (List (Nat)) h R S) (erased (Nat) x x2) (subterm erased (LastIs R x) p) (erased (Respects h R S) rp) (erased (Nth (Nat) h x x2) px)
    -> (erased (LastIs S x2) r))
  (let-match erased rp (RespCons _ R1 S1 j l pj rp1) (absurd (RespNil _) p))
  (match erased p _
    ((LIOne _) (let-match erased rp1 (RespNil _)) (let-match erased (nth-fn _ h x l x2 pj px) (Refl _ _)) (LIOne l))
    ((LIMore _ _ _ p1) (LIMore l x2 S1 (lastis-map h R1 S1 x x2 p1 rp1 px)))))

(def-fns _ $ (erased fpath-lastis : (erased (List (Nat)) n xs) (erased (Nat) x y) (subterm erased (FPath n x xs y) fp) -> (erased (LastIs (Cons (Nat) x xs) y) r))
  (match erased fp _
    ((FPNil _ _) (LIOne x))
    ((FPCons _ xs1 _ z _ px fp1) (LIMore x y (Cons _ z xs1) (fpath-lastis n xs1 z y fp1)))))

(def-fns _ $ (erased revapp-last : (erased (List (Nat)) pre w r) (erased (Nat) z) (subterm erased (RevApp (Nat) pre w r) ra) (erased (LastIs w z) lw)
    -> (erased (LastIs r z) res))
  (let-match erased ra (RACons _ s pre1 _ _ ra1) ((RANil _ _) lw))
  (revapp-last pre1 (Cons _ s w) r z ra1 (LIMore s z w lw)))

(def-fns _ $ (erased revapp-head : (erased (List (Nat)) pre w r) (erased (Nat) z) (subterm erased (RevApp (Nat) pre w r) ra) (erased (LastIs pre z) lp)
    -> (erased (HeadIs r z) res))
  (let-match erased ra (RACons _ s pre1 _ _ ra1) (absurd (RANil _ _) lp))
  (match erased lp _
    ((LIOne _) (let-match erased ra1 (RANil _ _)) (HI z w))
    ((LIMore _ _ _ lp1) (revapp-head pre1 (Cons _ s w) r z ra1 lp1))))

(def-fns _ $ (erased revapp-adj-back : (erased (List (Nat)) pre w r) (erased (Nat) u v) (subterm erased (RevApp (Nat) pre w r) ra) (erased (Adj2 r u v) a)
    -> (erased (HOr (Adj2 pre v u) (HOr (Adj2 w u v) (HeadPair pre w u v))) res))
  (let-match erased ra (RACons _ s pre1 _ _ ra1) ((RANil _ _) (OrR _ _ (OrL _ _ a))))
  (match erased (revapp-adj-back pre1 (Cons _ s w) r u v ra1 a) _
    ((OrL _ _ a1) (OrL _ _ (A2There s v u pre1 a1)))
    ((OrR _ _ o)
      (match erased o _
        ((OrL _ _ a2)
          (match erased a2 _
            ((A2Here _ _ w1) (OrR _ _ (OrR _ _ (HP u v pre1 w1))))
            ((A2There _ _ _ _ a3) (OrR _ _ (OrL _ _ a3)))))
        ((OrR _ _ hp) (let-match erased hp (HP _ _ p2 _)) (OrL _ _ (A2Here v u p2)))))))

(def-fns _ $ (erased fpath-adj : (erased (List (Nat)) n xs) (erased (Nat) x y a b) (subterm erased (FPath n x xs y) fp) (erased (In a (Cons (Nat) x xs)) ia)
    (erased (Nth (Nat) n a b) pa) -> (erased (HOr (Adj2 (Cons (Nat) x xs) a b) (Eq (Nat) a y)) r))
  (match erased fp _
    ((FPNil _ _) (let-match erased ia (InHere _ _) (absurd (InThere _ _ _ i) i)) (OrR _ _ (Refl _ a)))
    ((FPCons _ xs1 _ z _ px fp1)
      (match erased ia _
        ((InHere _ _) (let-match erased (nth-fn _ n a z b px pa) (Refl _ _)) (OrL _ _ (A2Here a b xs1)))
        ((InThere _ _ _ ia1)
          (match erased (fpath-adj n xs1 z y a b fp1 ia1 pa) _
            ((OrL _ _ a1) (OrL _ _ (A2There x a b (Cons _ z xs1) a1)))
            ((OrR _ _ e) (OrR _ _ e))))))))

(def-fns _ $ (erased fpath-adj-nth : (erased (List (Nat)) n xs) (erased (Nat) x y a b) (subterm erased (FPath n x xs y) fp) (erased (Adj2 (Cons (Nat) x xs) a b) ad)
    -> (erased (Nth (Nat) n a b) r))
  (let-match erased fp (FPCons _ xs1 _ z _ px fp1) (absurd (FPNil _ _) (let-match erased ad (A2There _ _ _ _ a1)) a1))
  (match erased ad _
    ((A2Here _ _ _) px)
    ((A2There _ _ _ _ a1) (fpath-adj-nth n xs1 z y a b fp1 a1))))

(def-fns _ $ (erased adj2-map : (erased (List (Nat)) h R S) (erased (Nat) a b a2 b2) (subterm erased (Adj2 R a b) ad) (erased (Respects h R S) rp)
    (erased (Nth (Nat) h a a2) pa) (erased (Nth (Nat) h b b2) pb) -> (erased (Adj2 S a2 b2) r))
  (match erased ad _
    ((A2Here _ _ R1)
      (let-match erased rp (RespCons _ _ S1 _ a3 pa3 rp1))
      (let-match erased rp1 (RespCons _ _ S2 _ b3 pb3 rp2))
      (let-match erased (nth-fn _ h a a3 a2 pa3 pa) (Refl _ _))
      (let-match erased (nth-fn _ h b b3 b2 pb3 pb) (Refl _ _))
      (A2Here a2 b2 S2))
    ((A2There c _ _ R1 ad1)
      (let-match erased rp (RespCons _ _ S1 _ c2 pc rp1))
      (A2There c2 a2 b2 S1 (adj2-map h R1 S1 a b a2 b2 ad1 rp1 pa pb)))))

(def-fns _ $ (erased adj2-unmap : (erased (List (Nat)) h R S) (erased (Nat) u v) (erased (Respects h R S) rp) (subterm erased (Adj2 S u v) ad)
    -> (erased (Nat) a b) (erased (Adj2 R a b) r) (erased (Nth (Nat) h a u) pa) (erased (Nth (Nat) h b v) pb))
  (let-match erased rp (RespCons _ R1 S1 a l pa rp1) (absurd (RespNil _) ad))
  (match erased ad _
    ((A2Here _ _ S2)
      (let-match erased rp1 (RespCons _ R2 _ b _ pb _))
      (values a b (A2Here a b R2) pa pb))
    ((A2There _ _ _ _ ad1)
      (let ((erased a1) (erased b1) (erased r1) (erased q1) (erased q2)) (adj2-unmap h R1 S1 u v rp1 ad1))
      (values a1 b1 (A2There a a1 b1 R1 r1) q1 q2))))

(def-fns _ $ (erased headis-map : (erased (List (Nat)) h R S) (erased (Nat) x) (erased (Respects h R S) rp) (erased (HeadIs R x) hi)
    -> (erased (Nat) x2) (erased (Nth (Nat) h x x2) px) (erased (HeadIs S x2) r))
  (let-match erased hi (HI _ R1))
  (let-match erased rp (RespCons _ _ S1 _ l pl _))
  (values l pl (HI l S1)))

(def-fns _ $ (erased headis-fn : (erased (List (Nat)) R) (erased (Nat) x y) (erased (HeadIs R x) p) (erased (HeadIs R y) q) -> (erased (Eq (Nat) x y) e))
  (let-match erased p (HI _ R1))
  (let-match erased q (HI _ _))
  (Refl _ x))

(def-fns _ $ (erased lastis-in : (erased (List (Nat)) R) (erased (Nat) x) (subterm erased (LastIs R x) p) -> (erased (In x R) r))
  (match erased p _
    ((LIOne _) (InHere x (Nil _)))
    ((LIMore c _ R1 p1) (InThere x c R1 (lastis-in R1 x p1)))))

(def-fns _ $ (erased respects-val : (erased (List (Nat)) h R S) (erased (Nat) x) (subterm erased (Respects h R S) rp) (erased (In x R) ix)
    -> (erased (Nat) x2) (erased (Nth (Nat) h x x2) px) (erased (In x2 S) ix2))
  (let-match erased rp (RespCons _ R1 S1 j l pj rp1) (absurd (RespNil _) ix))
  (match erased ix _
    ((InHere _ _) (values l pj (InHere l S1)))
    ((InThere _ _ _ ix1)
      (let ((erased x2) (erased px) (erased ix2)) (respects-val h R1 S1 x rp1 ix1))
      (values x2 px (InThere x2 l S1 ix2)))))

(def-fns _ $ (erased revapp-last-head : (erased (List (Nat)) pre r) (erased (Nat) z) (erased (RevApp (Nat) pre (Nil (Nat)) r) ra) (erased (HeadIs pre z) hp)
    -> (erased (LastIs r z) res))
  (let-match erased hp (HI _ pre1))
  (let-match erased ra (RACons _ _ _ _ _ ra1))
  (revapp-last pre1 (Cons _ z (Nil _)) r z ra1 (LIOne z)))

; The ring darts of the two maps go round in opposite directions (bGrP): for yr on br with the node step yr2, there are yd and its
; edge image zd on bd with hd zd = hr yr and hd yd = hr yr2.
(def-fns _ $ (erased ring-pair : (erased (Nat) yr yr2 u v) (erased (List (Nat)) hd hr ed nr bd br bG bGr) (erased (NCyc ed bd) cyd) (erased (NCyc nr br) cyr)
    (erased (Respects hd bd bG) rbd) (erased (Respects hr br bGr) rbr) (erased (RevApp (Nat) bG (Nil (Nat)) bGr) rv)
    (erased (In yr br) iy) (erased (Nth (Nat) nr yr yr2) py) (erased (Nth (Nat) hr yr u) pu) (erased (Nth (Nat) hr yr2 v) pv)
    -> (erased (Nat) yd zd) (erased (Nth (Nat) ed yd zd) pe) (erased (Nth (Nat) hd zd u) pz) (erased (Nth (Nat) hd yd v) pyd))
  (let-match erased cyr (NCCons _ rs r0 rl fpr backr) (absurd (NCNil _) iy))
  (let-match erased cyd (NCCons _ bs b0 bl fpd backd) (absurd (NCNil _) (let-match erased rbd (RespNil _)) (let-match erased rv (RANil _ _)) rbr))
  (match erased (fpath-adj nr rs r0 rl yr yr2 fpr iy py) _
    ((OrL _ _ ad)
      (match erased (revapp-adj-back bG (Nil _) bGr u v rv (adj2-map hr br bGr yr yr2 u v ad rbr pu pv)) _
        ((OrL _ _ ab)
          (let ((erased yd) (erased zd) (erased adb) (erased qy) (erased qz)) (adj2-unmap hd bd bG v u rbd ab))
          (values yd zd (fpath-adj-nth ed bs b0 bl yd zd fpd adb) qz qy))
        (absurd (OrR _ _ o) (match erased o _ (absurd (OrL _ _ a2) a2) (absurd (OrR _ _ hp) hp)))))
    ((OrR _ _ e)
      (let-match erased e (Refl _ _))
      (let-match erased (nth-fn _ nr yr yr2 r0 py backr) (Refl _ _))
      (let ((erased u2) (erased pu2) (erased hu)) (headis-map hd bd bG b0 rbd (HI b0 bs)))
      (let-match erased (lastis-fn bGr u2 u (revapp-last-head bG bGr u2 rv hu)
        (lastis-map hr br bGr yr u (fpath-lastis nr rs r0 yr fpr) rbr pu)) (Refl _ _))
      (let ((erased v2) (erased pv2) (erased hv)) (headis-map hr br bGr r0 rbr (HI r0 rs)))
      (let-match erased (nth-fn _ hr r0 v2 v pv2 pv) (Refl _ _))
      (let ((erased ll)) (fpath-lastis ed bs b0 bl fpd))
      (let ((erased l) (erased pl) (erased il)) (respects-val hd bd bG bl rbd (lastis-in bd bl ll)))
      (let-match erased (headis-fn bGr l v2 (revapp-head bG (Nil _) bGr l rv (lastis-map hd bd bG bl l ll rbd pl)) hv) (Refl _ _))
      (values bl b0 backd pu2 pl))))

(def-fns _ $ (erased path-label : (erased (List (Nat)) p lab s xs) (erased (Nat) x y l) (subterm erased (Path p s x y xs) w) (erased (Respects lab p lab) rf)
    (erased (Nth (Nat) lab x l) px) -> (erased (Nth (Nat) lab y l) r))
  (let-match erased w (PathStep _ _ xs1 _ z _ pz ns w1) ((PathHere _ _ _) px))
  (path-label p lab s xs1 z y l w1 rf (respects-nth lab p lab x z l rf pz px)))

; hdF as a morphism off bd.
(def-fns _ $ (erased morph-face-d : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br fdi m)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (HPerm dd fd fdi) pm) (erased (Length (Nat) hd dd) lh) (subterm erased (Under m dd) u)
    -> (erased (MorphOff hd fd f bd m) r))
  (let-match erased u (UnderCons m1 x _ lx u1) ((UnderNil _) (MONil hd fd f bd)))
  (let ((erased rest)) (morph-face-d d dd dr e n f ed nd fd er nr fr hd hr bd br fdi m1 pt pm lh u1))
  (match erased (in-dec x bd) _
    ((OrL _ _ ib) (MOSkip hd fd f bd m1 x ib rest))
    ((OrR _ _ ob)
      (let ((erased y) (erased py) (erased ly)) (perm-nth dd x fd fdi pm lx))
      (let ((erased z) (erased hz)) (nth-exists _ hd dd x lh lx))
      (let ((erased w) (erased hw)) (nth-exists _ hd dd y lh ly))
      (MOAt hd fd f bd m1 x y z w py hz hw (patch-face-d d dd dr e n f ed nd fd er nr fr hd hr bd br pt x y z w ob py hz hw) rest))))

(def-fns _ $ (erased path-reavoid : (erased (List (Nat)) p s s2 xs) (erased (Nat) x y) (subterm erased (Path p s x y xs) w) (erased (Off s2 xs) off)
    -> (erased (Path p s2 x y xs) r))
  (let-match erased w (PathStep _ _ xs1 _ z _ pz ns w1) ((PathHere _ _ _) (PathHere p s2 x)))
  (let-match erased off (OffCons _ _ _ ox off1))
  (PathStep p s2 xs1 x z y pz ox (path-reavoid p s s2 xs1 z y w1 off1)))

; A walk along p never leaving s, part of which is b, sent by h, a morphism to q off b, to a walk along q.
(def-fns _ $ (erased path-push2 : (erased (Nat) k x y x2) (erased (List (Nat)) h p pi q b ids s s2 xs) (erased (HPerm k p pi) pm)
    (erased (MorphOff h p q b ids) mo) (erased (Iota k ids) io) (erased (Distinct h) dh) (erased (Respects h s s2) rs) (erased (Sub b s) sbs)
    (subterm erased (Path p s x y xs) w) (erased (Nth (Nat) h x x2) hx)
    -> (erased (Nat) y2) (erased (List (Nat)) xs2) (erased (Nth (Nat) h y y2) hy) (erased (Path q s2 x2 y2 xs2) w2) (erased (Respects h xs xs2) rx))
  (let-match erased w (PathStep _ _ xs1 _ z _ pz ns w1) ((PathHere _ _ _) (values x2 (Nil _) hx (PathHere q s2 x2) (RespNil h))))
  (let ((erased z2) (erased hz) (erased qz)) (morph h p q b ids k x z x2 mo io (pre-lt k x z p pi pm pz) (notin-sub x b s sbs ns) pz hx))
  (let ((erased y2) (erased xs2) (erased hy) (erased w2) (erased rx)) (path-push2 k z y z2 h p pi q b ids s s2 xs1 pm mo io dh rs sbs w1 hz))
  (values y2 (Cons _ x2 xs2) hy (PathStep q s2 xs2 x2 z2 y2 qz (notin-respects h s s2 x x2 dh ns hx rs) w2) (RespCons h xs1 xs2 x x2 hx rx)))

; Two darts of p with one label under a labelling giving the darts of p distinct labels are one dart.
(def-fns _ $ (erased simple-inj : (erased (List (Nat)) lab p ls) (erased (Nat) a b l) (erased (Respects lab p ls) rp) (erased (Distinct ls) dl)
    (erased (In a p) ia) (erased (In b p) ib) (erased (Nth (Nat) lab a l) pa) (erased (Nth (Nat) lab b l) pb) -> (erased (Eq (Nat) a b) e))
  (let ((erased i) (erased qi)) (in-nth a p ia))
  (let ((erased j) (erased qj)) (in-nth b p ib))
  (let-match erased (distinct-nth ls i j l dl (respects-at lab p ls i a l rp qi pa) (respects-at lab p ls j b l rp qj pb)) (Refl _ _))
  (nth-fn _ p i a b qi qj))

; A walk along a face to a dart y of a simple list p leaves from no dart of p.
(def-fns _ $ (erased path-off-simple : (erased (List (Nat)) f lab p ls xs) (erased (Nat) x y l) (subterm erased (Path f (Cons (Nat) y (Nil (Nat))) x y xs) w)
    (erased (Respects lab f lab) rf) (erased (Respects lab p ls) rp) (erased (Distinct ls) dl) (erased (In y p) iy) (erased (Nth (Nat) lab x l) px)
    (erased (Nth (Nat) lab y l) py) -> (erased (Off p xs) r))
  (let-match erased w (PathStep _ _ xs1 _ z _ pz ns w1) ((PathHere _ _ _) (OffNil p)))
  (OffCons p xs1 x
    (match erased (in-dec x p) _
      (absurd (OrL _ _ ix)
        (let-match erased (simple-inj lab p ls x y l rp dl ix iy px py) (Refl _ _))
        (let-match erased ns (NotInCons _ _ _ ne _))
        (apart-irrefl x ne))
      ((OrR _ _ o) o))
    (path-off-simple f lab p ls xs1 z y l w1 rf rp dl iy (respects-nth lab f lab x z l rf pz px) py)))

; Darts of the disk map off its ring have images off the image of the remainder map.
(def-fns _ $ (erased off-image : (erased (Nat) d) (erased (List (Nat)) hd hr bd ids xs ys) (erased (PatchParts hd hr bd ids) pp) (erased (Iota d ids) io)
    (erased (Distinct hd) dh) (erased (Under hd d) uh) (subterm erased (Respects hd xs ys) rp) (erased (Off bd xs) off) -> (erased (Off hr ys) r))
  (let-match erased rp (RespCons _ xs1 ys1 xd x px rp1) ((RespNil _) (OffNil hr)))
  (let-match erased off (OffCons _ _ _ oxd off1))
  (OffCons hr ys1 x (disk-notin-r d xd x hd hr bd ids pp io dh uh px oxd) (off-image d hd hr bd ids xs1 ys1 pp io dh uh rp1 off1)))

; The face step of an image of the remainder map reaches the image of the face step in the remainder map before any other dart of
; that image.
(def-fns _ $ (erased face-next-r : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (Nat) xr yr x x1 y) (erased (Nth (Nat) fr xr yr) pf) (erased (Nth (Nat) hr xr x) hx)
    (erased (Nth (Nat) f x x1) px1) (erased (Nth (Nat) hr yr y) hy) -> (erased (FirstHit f hr x1 y) r))
  (match erased (in-dec yr br) _
    ((OrR _ _ out)
      (let-match erased (nth-fn _ f x x1 y px1 (patch-face-r d dd dr e n f ed nd fd er nr fr hd hr bd br pt xr yr x y out pf hx hy)) (Refl _ _))
      (MkFirstHit f hr (Nil _) x1 x1 (PathHere f hr x1) (nth-in hr yr x1 hy)))
    ((OrL _ _ iyr)
      (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids idd idr bG bGr h hd2 hr2 io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
      (let ((erased nfd) (erased ndi) (erased fdi) (erased rnfd) (erased pmed) (erased pmnd) (erased pmfd)) (hyper-core dd ed nd fd hd2))
      (let ((erased nfr) (erased nri) (erased fri) (erased rnfr) (erased pmer) (erased pmnr) (erased pmfr)) (hyper-core dr er nr fr hr2))
      (let ((erased lxr)) (pre-lt dr xr yr fr fri pmfr pf))
      (let ((erased c) (erased pc) (erased lc)) (perm-nth dr xr nfr er (perm-sym dr er nfr pmer) lxr))
      (let ((erased pec)) (perm-inv dr xr c nfr er (perm-sym dr er nfr pmer) pc))
      (let ((erased pnc)) (hyper-node dr yr xr c er nr fr hr2 pf pec))
      (let ((erased v) (erased hv)) (nth-exists _ hr dr c lhr lc))
      (let ((erased yd) (erased zd) (erased pez) (erased hz) (erased hyd)) (ring-pair yr c y v hd hr ed nr bd br bG bGr cyd cyr rbd rbr rv iyr pnc hy hv))
      (let ((erased w) (erased hw) (erased qw)) (morph hr er e (Nil _) idr dr c xr v mer ior lc (NotInNil c) pec hv))
      (let-match erased (nth-fn _ hr xr w x hw hx) (Refl _ _))
      (let ((erased lyd)) (nth-lt-length _ hd yd dd v hyd lhd))
      (let ((erased ud) (erased pud) (erased lud)) (perm-nth dd yd ndi nd (perm-sym dd nd ndi pmnd) lyd))
      (let ((erased pnu)) (perm-inv dd yd ud ndi nd (perm-sym dd nd ndi pmnd) pud))
      (let ((erased u2) (erased hu)) (nth-exists _ hd dd ud lhd lud))
      (let ((erased w2) (erased hw2) (erased qw2)) (morph hd nd n (Nil _) idd dd ud yd u2 mnd iod lud (NotInNil ud) pnu hu))
      (let-match erased (nth-fn _ hd yd w2 v hw2 hyd) (Refl _ _))
      (let-match erased (nth-fn _ f x x1 u2 px1 (hyper-third d x v u2 e n f h qw qw2)) (Refl _ _))
      (let ((erased pfz)) (hyper-third dd zd yd ud ed nd fd hd2 pez pnu))
      (let ((erased lzd)) (pre-lt dd zd ud fd fdi pmfd pfz))
      (let ((erased ws) (erased cw)) (cycle dd zd ud fd fdi pmfd pfz lzd))
      (let ((erased ws1) (erased cw1)) (cut-first fd (Nil _) ws ud zd cw))
      (let-match erased sd (MkSimple _ _ lab ls rf rp dl))
      (let-match erased (revapp-out bG (Nil _) bGr y rv (in-map hr br bGr yr y iyr rbr hy)) (OrL _ _ iyg) (absurd (OrR _ _ i) i))
      (let ((erased j) (erased ij) (erased pj)) (respects-in hd bd bG y rbd iyg))
      (let-match erased (distinct-nth hd j zd y dhd pj hz) (Refl _ _))
      (let ((erased le) (erased ln) (erased lf)) (hyper-lengths dd ed nd fd hd2))
      (let ((erased l) (erased pl)) (nth-exists _ lab dd ud (respects-length lab fd lab dd rf lf) lud))
      (let ((erased off)) (path-off-simple fd lab bd ls ws1 ud j l cw1 rf rp dl ij pl (path-label fd lab (Cons _ j (Nil _)) ws1 ud j l cw1 rf pl)))
      (let ((erased z2) (erased ws2) (erased hz2) (erased cw2) (erased rx))
        (path-push2 dd ud zd x1 hd fd fdi f bd idd bd bG ws1 pmfd (morph-face-d d dd dr e n f ed nd fd er nr fr hd hr bd br fdi idd pt pmfd lhd (perm-under dd idd idd (perm-id dd idd iod))) iod dhd rbd (sub-refl bd) (path-reavoid fd (Cons _ zd (Nil _)) bd ws1 ud zd cw1 off) hu))
      (let-match erased (nth-fn _ hd zd z2 y hz2 hz) (Refl _ _))
      (MkFirstHit f hr ws2 x1 y (path-reavoid f bG hr ws2 x1 y cw2 (off-image d hd hr bd ids ws1 ws2 pp io dhd uhd rx off)) (nth-in hr yr y hy)))))

; A walk along q from the image of a dart off c, a set closed under p, ends at the image of a dart off c.
(def-fns _ $ (erased path-pull-c : (erased (Nat) k x x2 y2) (erased (List (Nat)) h p pi q b c ids xs2) (erased (List (Bond)) gp) (erased (HPerm k p pi) pm)
    (erased (Graph k p gp) grp) (erased (Shut c gp) sh) (erased (Sub b c) sbc) (erased (MorphOff h p q b ids) mo) (erased (Iota k ids) io)
    (subterm erased (Path q (Nil (Nat)) x2 y2 xs2) w) (erased (Lt x k) lx) (erased (NotIn x c) out) (erased (Nth (Nat) h x x2) hx)
    -> (erased (Nat) y) (erased (Nth (Nat) h y y2) hy) (erased (NotIn y c) oy))
  (let-match erased w (PathStep _ _ xs3 _ w2 _ qw ns w3) ((PathHere _ _ _) (values x hx out)))
  (let ((erased z) (erased pz) (erased lz)) (perm-nth k x p pi pm lx))
  (let ((erased z2) (erased hz) (erased qz)) (morph h p q b ids k x z x2 mo io lx (notin-sub x b c sbc out) pz hx))
  (let-match erased (nth-fn _ q x2 z2 w2 qz qw) (Refl _ _))
  (path-pull-c k z z2 y2 h p pi q b c ids xs3 gp pm grp sh sbc mo io w3 lz (shut-adj-out c gp x z (graph-adj k x z p gp grp pz) sh out) hz))

(def-fns _ $ (erased sub-label : (erased (List (Nat)) lab R LR xs ys zs m) (erased (Respects lab R LR) rp) (erased (SplitBy lab LR xs ys zs) sp)
    (erased (Sub m xs) sx) (subterm erased (Sub m R) sb) -> (erased (Sub m ys) r))
  (let-match erased sb (HSubCons x m1 _ ix sb1) ((HSubNil _) (HSubNil ys)))
  (let-match erased sx (HSubCons _ _ _ jx sx1))
  (let ((erased l) (erased px) (erased il)) (respects-val lab R LR x rp ix))
  (HSubCons x m1 ys (sb-member lab LR xs ys zs x l sp jx px il) (sub-label lab R LR xs ys zs m1 rp sp sx1 sb1)))

; outer: the darts of the whole map whose face meets the image of hr, with the face labelling labf.
(def-fns _ $ (erased outer-hit : (erased (Nat) d x) (erased (List (Nat)) f fi hr labf rsf ids LH outer inner) (erased (List (Bond)) gf) (erased (HPerm d f fi) pmf)
    (erased (Graph d f gf) grf) (erased (Iota d ids) io) (erased (Rooted gf rsf ids labf) ro) (erased (Under hr d) uhr) (erased (Respects labf hr LH) rlh)
    (erased (SplitBy labf LH ids outer inner) sp) (erased (In x outer) ix) (erased (Lt x d) lx) -> (erased (Nat) z) (erased (FirstHit f hr x z) r))
  (let ((erased l) (erased px) (erased il)) (sb-in-key labf LH ids outer inner x sp ix))
  (let ((erased j) (erased ij) (erased pj)) (respects-in labf hr LH l rlh il))
  (let ((erased ws) (erased w)) (conn-path d x j f fi gf pmf grf (same-root gf d x j l ids labf rsf io ro px pj lx (under-in hr j d uhr ij))))
  (first-hit f (Nil _) hr ws x j w ij))

(def-fns _ $ (erased outer-hitinv : (erased (Nat) d) (erased (List (Nat)) f fi hr labf rsf ids LH outer inner xs) (erased (List (Bond)) gf) (erased (HPerm d f fi) pmf)
    (erased (Graph d f gf) grf) (erased (Iota d ids) io) (erased (Rooted gf rsf ids labf) ro) (erased (Under hr d) uhr) (erased (Respects labf hr LH) rlh)
    (erased (SplitBy labf LH ids outer inner) sp) (subterm erased (Under xs d) u) -> (erased (List (Nat)) ls) (erased (HitInv f hr hr outer xs ls) r))
  (let-match erased u (UnderCons xs1 x _ lx u1) ((UnderNil _) (values (Nil _) (HvNil f hr hr outer))))
  (let ((erased ls1) (erased r1)) (outer-hitinv d f fi hr labf rsf ids LH outer inner xs1 gf pmf grf io ro uhr rlh sp u1))
  (match erased (in-dec x outer) _
    ((OrL _ _ ix)
      (let ((erased z) (erased fh)) (outer-hit d x f fi hr labf rsf ids LH outer inner gf pmf grf io ro uhr rlh sp ix lx))
      (let-match erased fh (MkFirstHit _ _ ws _ _ w iz))
      (let ((erased j) (erased pj)) (in-nth z hr iz))
      (values (Cons _ j ls1) (HvIn f hr hr outer xs1 ls1 x z j fh pj r1)))
    ((OrR _ _ o) (values (Cons _ (Zero) ls1) (HvOut f hr hr outer xs1 ls1 x o r1)))))

(def-fns _ $ (erased outer-mem : (erased (Nat) d x xr) (erased (List (Nat)) hr labf ids LH outer inner) (erased (Iota d ids) io) (erased (Length (Nat) labf d) ll)
    (erased (Under hr d) uhr) (erased (Respects labf hr LH) rlh) (erased (SplitBy labf LH ids outer inner) sp) (erased (Nth (Nat) hr xr x) hx) -> (erased (In x outer) r))
  (let ((erased lx)) (under-nth hr xr x d uhr hx))
  (let ((erased l) (erased px)) (nth-exists _ labf d x ll lx))
  (sb-member labf LH ids outer inner x l sp (iota-in d x ids io lx) px (in-map labf hr LH x l (nth-in hr xr x hx) rlh px)))

(def-fns _ $ (erased outer-lift-r : (erased (Nat) d dr) (erased (List (Nat)) f hr L labf ids idr LH outer inner m) (erased (List (Bond)) gfr) (erased (HitInv f hr hr outer ids L) hv)
    (erased (Iota d ids) io) (erased (Length (Nat) labf d) ll) (erased (Distinct hr) dh) (erased (Length (Nat) hr dr) lh) (erased (Under hr d) uhr)
    (erased (Respects labf hr LH) rlh) (erased (SplitBy labf LH ids outer inner) sp) (erased (Under idr dr) ui) (subterm erased (Sub m idr) sb)
    -> (erased (Lift gfr hr L outer m) r))
  (let-match erased sb (HSubCons xr m1 _ ixr sb1) ((HSubNil _) (LiftNil gfr hr L outer)))
  (let ((erased x) (erased hx)) (nth-exists _ hr dr xr lh (under-in idr xr dr ui ixr)))
  (let ((erased ix)) (outer-mem d x xr hr labf ids LH outer inner io ll uhr rlh sp hx))
  (LiftCons gfr hr L outer m1 xr x xr hx ix
    (hitinv-at f hr hr outer ids L x x x xr hv dh (iota-nth d x ids io (under-nth hr xr x d uhr hx)) ix (MkFirstHit f hr (Nil _) x x (PathHere f hr x) (nth-in hr xr x hx)) hx)
    (ConnHere gfr xr) (outer-lift-r d dr f hr L labf ids idr LH outer inner m1 gfr hv io ll dh lh uhr rlh sp ui sb1)))

(def-fns _ $ (erased outer-lift-g : (erased (Nat) d dr) (erased (List (Nat)) f fi hr L labf rsf ids idr LH outer inner m) (erased (List (Bond)) gf) (erased (HitInv f hr hr outer ids L) hv)
    (erased (HPerm d f fi) pmf) (erased (Graph d f gf) grf) (erased (Iota d ids) io) (erased (Iota dr idr) ior) (erased (Rooted gf rsf ids labf) ro)
    (erased (Distinct hr) dh) (erased (Length (Nat) hr dr) lh) (erased (Under hr d) uhr) (erased (Respects labf hr LH) rlh) (erased (SplitBy labf LH ids outer inner) sp)
    (erased (Under outer d) uo) (subterm erased (Sub m outer) sb) -> (erased (Lift gf L hr idr m) r))
  (let-match erased sb (HSubCons x m1 _ ix sb1) ((HSubNil _) (LiftNil gf L hr idr)))
  (let ((erased lx)) (under-in outer x d uo ix))
  (let ((erased z) (erased fh)) (outer-hit d x f fi hr labf rsf ids LH outer inner gf pmf grf io ro uhr rlh sp ix lx))
  (let-match erased fh (MkFirstHit _ _ ws _ _ w iz))
  (let ((erased j) (erased pj)) (in-nth z hr iz))
  (LiftCons gf L hr idr m1 x j z (hitinv-at f hr hr outer ids L x x z j hv dh (iota-nth d x ids io lx) ix fh pj)
    (iota-in dr j idr ior (nth-lt-length _ hr j dr z pj lh)) pj (path-graph-conn d x z f hr ws gf w grf)
    (outer-lift-g d dr f fi hr L labf rsf ids idr LH outer inner m1 gf hv pmf grf io ior ro dh lh uhr rlh sp uo sb1)))

(def-fns _ $ (erased outer-moves-r : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br fi fri idr) (erased (List (Bond)) g gf)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (HPerm d f fi) pmf) (erased (HPerm dr fr fri) pmfr) (erased (Graph d f gf) grf)
    (erased (Iota dr idr) ior) (erased (Length (Nat) hr dr) lh) (erased (Under hr d) uhr) (subterm erased (Fun fr g) fn) -> (erased (Moves g idr hr gf) r))
  (let-match erased fn (FunCons _ g1 xr yr pf fn1) ((FunNil _) (MvNil idr hr gf)))
  (let ((erased lxr)) (pre-lt dr xr yr fr fri pmfr pf))
  (let ((erased lyr)) (perm-val dr xr yr fr fri pmfr pf))
  (let ((erased x) (erased hx)) (nth-exists _ hr dr xr lh lxr))
  (let ((erased y) (erased hy)) (nth-exists _ hr dr yr lh lyr))
  (let ((erased x1) (erased px1) (erased lx1)) (perm-nth d x f fi pmf (under-nth hr xr x d uhr hx)))
  (let-match erased (face-next-r d dd dr e n f ed nd fd er nr fr hd hr bd br pt xr yr x x1 y pf hx px1 hy) (MkFirstHit _ _ ws _ _ w iy))
  (MvIn g1 gf idr hr xr yr x y (iota-in dr xr idr ior lxr) (iota-in dr yr idr ior lyr) hx hy
    (ConnStep gf x x1 y (graph-adj d x x1 f gf grf px1) (path-graph-conn d x1 y f hr ws gf w grf))
    (outer-moves-r d dd dr e n f ed nd fd er nr fr hd hr bd br fi fri idr g1 gf pt pmf pmfr grf ior lh uhr fn1)))

(def-fns _ $ (erased outer-moves-g : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br fi fri L labf rsf ids LH outer inner)
    (erased (List (Bond)) g gf gfr) (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (HitInv f hr hr outer ids L) hv) (erased (HPerm d f fi) pmf)
    (erased (HPerm dr fr fri) pmfr) (erased (Graph d f gf) grf) (erased (Graph dr fr gfr) grfr) (erased (Iota d ids) io) (erased (Rooted gf rsf ids labf) ro)
    (erased (Const labf gf) cl) (erased (Length (Nat) labf d) ll) (erased (Distinct hr) dh) (erased (Length (Nat) hr dr) lh) (erased (Under hr d) uhr)
    (erased (Respects labf hr LH) rlh) (erased (SplitBy labf LH ids outer inner) sp) (subterm erased (Fun f g) fn) -> (erased (Moves g outer L gfr) r))
  (let-match erased fn (FunCons _ g1 x x1 px fn1) ((FunNil _) (MvNil outer L gfr)))
  (let ((erased rest)) (outer-moves-g d dd dr e n f ed nd fd er nr fr hd hr bd br fi fri L labf rsf ids LH outer inner g1 gf gfr pt hv pmf pmfr grf grfr io ro cl ll dh lh uhr rlh sp fn1))
  (let ((erased lx)) (pre-lt d x x1 f fi pmf px))
  (let ((erased lx1)) (perm-val d x x1 f fi pmf px))
  (let ((erased l) (erased pl)) (nth-exists _ labf d x ll lx))
  (let ((erased pl1)) (adj-const labf gf x x1 l (graph-adj d x x1 f gf grf px) cl pl))
  (match erased (in-dec x outer) _
    ((OrL _ _ ix)
      (let ((erased ix1)) (sb-member labf LH ids outer inner x1 l sp (iota-in d x1 ids io lx1) pl1 (sb-in-key-at labf LH ids outer inner x l sp ix pl)))
      (let ((erased z) (erased fh)) (outer-hit d x f fi hr labf rsf ids LH outer inner gf pmf grf io ro uhr rlh sp ix lx))
      (let-match erased fh (MkFirstHit _ _ ws _ _ w iz))
      (let ((erased j) (erased pj)) (in-nth z hr iz))
      (let ((erased lj)) (hitinv-at f hr hr outer ids L x x z j hv dh (iota-nth d x ids io lx) ix fh pj))
      (match erased (in-dec x hr) _
        ((OrL _ _ ixh)
          (let-match erased (hit-fn f hr x z x fh (MkFirstHit f hr (Nil _) x x (PathHere f hr x) ixh)) (Refl _ _))
          (let ((erased lj2)) (nth-lt-length _ hr j dr z pj lh))
          (let ((erased yr) (erased pyr) (erased lyr)) (perm-nth dr j fr fri pmfr lj2))
          (let ((erased y) (erased hy)) (nth-exists _ hr dr yr lh lyr))
          (let ((erased fh1)) (face-next-r d dd dr e n f ed nd fd er nr fr hd hr bd br pt j yr z x1 y pyr pj px hy))
          (MvIn g1 gfr outer L x x1 j yr ix ix1 lj (hitinv-at f hr hr outer ids L x1 x1 y yr hv dh (iota-nth d x1 ids io lx1) ix1 fh1 hy)
            (conn-adj gfr j yr (graph-adj dr j yr fr gfr grfr pyr)) rest))
        ((OrR _ _ oxh)
          (MvIn g1 gfr outer L x x1 j j ix ix1 lj (hitinv-at f hr hr outer ids L x1 x1 z j hv dh (iota-nth d x1 ids io lx1) ix1 (hit-next f hr x x1 z fh oxh px) pj)
            (ConnHere gfr j) rest))))
    ((OrR _ _ ox)
      (let ((erased ol)) (match erased (in-dec l LH) (((NotIn l LH) r))
        (absurd (OrL _ _ il) (apart-irrefl x (notin-in x x outer ox (sb-member labf LH ids outer inner x l sp (iota-in d x ids io lx) pl il))))
        ((OrR _ _ o) o)))
      (MvOut g1 gfr outer L x x1 ox (sb-notmember labf LH ids outer inner x1 l sp pl1 ol) rest))))

; A dart whose face misses the image of hr is the image of a disk dart whose face misses bd.
(def-fns _ $ (erased inner-sub : (erased (Nat) d dd) (erased (List (Nat)) f fd fdi hd hr bd bG bGr br labf labd rsd ids idd LH LB outer inner FL sdf tf st m)
    (erased (List (Bond)) gf gfd) (erased (HPerm dd fd fdi) pmfd) (erased (Graph d f gf) grf) (erased (Graph dd fd gfd) grfd) (erased (MorphOff hd fd f bd idd) mo)
    (erased (PatchParts hd hr bd ids) pp) (erased (Iota d ids) io) (erased (Iota dd idd) iod) (erased (Rooted gfd rsd idd labd) rod) (erased (Const labf gf) cl)
    (erased (Length (Nat) labf d) ll) (erased (Distinct hd) dhd) (erased (Length (Nat) hd dd) lhd) (erased (Respects hd bd bG) rbd) (erased (Respects hr br bGr) rbr)
    (erased (RevApp (Nat) bG (Nil (Nat)) bGr) rv) (erased (Under bd dd) ubd) (erased (Respects labf hr LH) rlh) (erased (Respects labd bd LB) rlb)
    (erased (SplitBy labf LH ids outer inner) sp) (erased (SplitBy labd LB idd FL sdf) spd) (erased (Split FL idd FL sdf) sf) (erased (Respects hd sdf tf) rtf)
    (erased (AppN tf outer st) ap) (subterm erased (Sub m ids) sb) -> (erased (Sub m st) r))
  (let-match erased sb (HSubCons x m1 _ ix sb1) ((HSubNil _) (HSubNil st)))
  (let ((erased rest)) (inner-sub d dd f fd fdi hd hr bd bG bGr br labf labd rsd ids idd LH LB outer inner FL sdf tf st m1 gf gfd pmfd grf grfd mo pp io iod rod cl ll dhd lhd
    rbd rbr rv ubd rlh rlb sp spd sf rtf ap sb1))
  (let ((erased lx)) (under-in ids x d (perm-under d ids ids (perm-id d ids io)) ix))
  (let ((erased l) (erased pl)) (nth-exists _ labf d x ll lx))
  (HSubCons x m1 st
    (match erased (in-dec x outer) _
      ((OrL _ _ io2) (app-in-r tf outer st x ap io2))
      ((OrR _ _ ox)
        (let ((erased ol)) (match erased (in-dec l LH) (((NotIn l LH) r))
          (absurd (OrL _ _ il) (apart-irrefl x (notin-in x x outer ox (sb-member labf LH ids outer inner x l sp ix pl il))))
          ((OrR _ _ o) o)))
        (match erased (parts-at hd hr bd ids x pp ix) _
          (absurd (PtRing _ _ _ _ xd xr px pin pr) (apart-irrefl l (notin-in l l LH ol (in-map labf hr LH x l (nth-in hr xr x pr) rlh pl))))
          (absurd (PtRest _ _ _ _ xr pr outd) (apart-irrefl l (notin-in l l LH ol (in-map labf hr LH x l (nth-in hr xr x pr) rlh pl))))
          ((PtDisk _ _ _ _ xd px out outr)
            (let ((erased lxd)) (nth-lt-length _ hd xd dd x px lhd))
            (match erased (in-dec xd FL) _
              ((OrR _ _ oxf) (app-in-l tf outer st x ap (in-map hd sdf tf xd x (side-in dd xd FL idd FL sdf iod sf lxd oxf) rtf px)))
              (absurd (OrL _ _ ixf)
                (let ((erased l2) (erased p2) (erased i2)) (sb-in-key labd LB idd FL sdf xd spd ixf))
                (let ((erased b0) (erased ib0) (erased pb0)) (respects-in labd bd LB l2 rlb i2))
                (let ((erased ws) (erased w)) (conn-path dd xd b0 fd fdi gfd pmfd grfd (same-root gfd dd xd b0 l2 idd labd rsd iod rod p2 pb0 lxd (under-in bd b0 dd ubd ib0))))
                (let ((erased zd) (erased fh)) (first-hit fd (Nil _) bd ws xd b0 w ib0))
                (let-match erased fh (MkFirstHit _ _ ws2 _ _ w2 izd))
                (let ((erased z2) (erased ws3) (erased hz) (erased w3) (erased rx)) (path-push2 dd xd zd x hd fd fdi f bd idd bd bG ws2 pmfd mo iod dhd rbd (sub-refl bd) w2 px))
                (let ((erased jr) (erased ijr) (erased pjr)) (respects-in hr br bGr z2 rbr (revapp-in bG (Nil _) bGr z2 rv (OrL _ _ (in-map hd bd bG zd z2 izd rbd hz)))))
                (apart-irrefl l (notin-in l l LH ol (in-map labf hr LH z2 l (nth-in hr jr z2 pjr) rlh
                  (conn-const labf gf x z2 l (path-graph-conn d x z2 f bG ws3 gf w3 grf) cl pl))))))))))
    rest))

; No dart whose face meets the image of hr is the image of a disk dart whose face misses bd.
(def-fns _ $ (erased outer-disj : (erased (Nat) d dd) (erased (List (Nat)) f fi fd fdi hd hr bd labf rsf ids idd LH outer inner FL sdf tf m)
    (erased (List (Bond)) gf gfd) (erased (HPerm d f fi) pmf) (erased (HPerm dd fd fdi) pmfd) (erased (Graph d f gf) grf) (erased (Graph dd fd gfd) grfd)
    (erased (Shut FL gfd) sh) (erased (Sub bd FL) sbf) (erased (MorphOff hd fd f bd idd) mo) (erased (PatchParts hd hr bd ids) pp) (erased (Iota d ids) io)
    (erased (Iota dd idd) iod) (erased (Rooted gf rsf ids labf) ro) (erased (Distinct hd) dhd) (erased (Under hd d) uhd) (erased (Under hr d) uhr)
    (erased (Respects labf hr LH) rlh) (erased (SplitBy labf LH ids outer inner) sp) (erased (Split FL idd FL sdf) sf) (erased (Respects hd sdf tf) rtf)
    (erased (Under sdf dd) usd) (erased (Under outer d) uo) (subterm erased (Sub m outer) sb) -> (erased (Disj m tf) r))
  (let-match erased sb (HSubCons x m1 _ ix sb1) ((HSubNil _) (DisjNil tf)))
  (DisjCons x m1 tf
    (match erased (in-dec x tf) _
      (absurd (OrL _ _ it)
        (let ((erased xd) (erased ixd) (erased px)) (respects-in hd sdf tf x rtf it))
        (let ((erased z) (erased fh)) (outer-hit d x f fi hr labf rsf ids LH outer inner gf pmf grf io ro uhr rlh sp ix (under-in outer x d uo ix)))
        (let-match erased fh (MkFirstHit _ _ ws _ _ w iz))
        (let ((erased y) (erased hy) (erased oy))
          (path-pull-c dd xd x z hd fd fdi f bd FL idd ws gfd pmfd grfd sh sbf mo iod (path-forget f hr ws x z w) (under-in sdf xd dd usd ixd)
            (split-out FL idd FL sdf xd sf ixd) px))
        (apart-irrefl z (notin-in z z hr (disk-notin-r d y z hd hr bd ids pp io dhd uhd hy (notin-sub y bd FL sbf oy)) iz)))
      ((OrR _ _ o) o))
    (outer-disj d dd f fi fd fdi hd hr bd labf rsf ids idd LH outer inner FL sdf tf m1 gf gfd pmf pmfd grf grfd sh sbf mo pp io iod ro dhd uhd uhr rlh sp sf rtf usd uo sb1)))

; The faces of the whole map, and as many more as the ring has darts, are those of the disk map and of the remainder map
; (patch_fcard_face_d, patch_fcard_face_r and the face step of genus_patch).
(def-fns _ $ (erased face-patch : (erased (Nat) d dd dr kf kfd kfr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (Orbits d f kf) of) (erased (Orbits dd fd kfd) od) (erased (Orbits dr fr kfr) orr)
    -> (erased (Nat) b s) (erased (Length (Nat) bd b) lb) (erased (Add kf b s) a1) (erased (Add kfd kfr s) a2))
  (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids idd idr bG bGr h hd2 hr2 io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pme) (erased pmn) (erased pmf)) (hyper-core d e n f h))
  (let ((erased nfd) (erased ndi) (erased fdi) (erased rnfd) (erased pmed) (erased pmnd) (erased pmfd)) (hyper-core dd ed nd fd hd2))
  (let ((erased nfr) (erased nri) (erased fri) (erased rnfr) (erased pmer) (erased pmnr) (erased pmfr)) (hyper-core dr er nr fr hr2))
  (let-match erased of (MkOrbits _ _ _ gf grf csf))
  (let-match erased od (MkOrbits _ _ _ gfd grfd csfd))
  (let-match erased orr (MkOrbits _ _ _ gfr grfr csfr))
  (let ((erased bgf)) (classes-below gf d kf csf))
  (let ((erased bgfd)) (classes-below gfd dd kfd csfd))
  (let-match erased csf (MkClasses _ _ _ ids2 labf rsf io2 llf lrf drf fixf clf rof))
  (let-match erased (iota-fn d ids ids2 io io2) (Refl _ _))
  (let-match erased csfd (MkClasses _ _ _ idd2 labd rsd iod2 lld lrd drd fixd cld rod))
  (let-match erased (iota-fn dd idd idd2 iod iod2) (Refl _ _))
  (let ((erased uids)) (perm-under d ids ids (perm-id d ids io)))
  (let ((erased uidd)) (perm-under dd idd idd (perm-id dd idd iod)))
  (let ((erased uidr)) (perm-under dr idr idr (perm-id dr idr ior)))
  (let ((erased ubd)) (respects-under hd bd bG dd rbd lhd))
  (let ((erased b) (erased lbd)) (length-exists _ bd))
  (let ((erased LB) (erased rlb)) (respects-exists labd bd dd ubd lld))
  (let ((erased FL) (erased sdf) (erased spd)) (sb-exists labd LB dd lld idd uidd))
  (let ((erased sf)) (sb-split labd LB idd FL sdf idd FL sdf spd spd (sub-refl FL)))
  (let ((erased sFL) (erased ssdf)) (split-sub FL idd FL sdf sf))
  (let ((erased uFL)) (sub-under FL idd dd sFL uidd))
  (let ((erased usdf)) (sub-under sdf idd dd ssdf uidd))
  (let ((erased shFL)) (sb-shut labd LB idd FL sdf gfd dd spd cld bgfd iod))
  (let ((erased sbf)) (sub-label labd bd LB idd FL sdf bd rlb spd (under-sub dd bd idd ubd iod) (sub-refl bd)))
  (let-match erased sd (MkSimple _ _ labs lss rfs rps dls))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths dd ed nd fd hd2))
  (let ((erased cls)) (resp-const dd labs fd gfd (graph-fun dd fd gfd grfd) rfs (respects-length labs fd labs dd rfs lf)))
  (let ((erased coFL)) (MkClassesOn gfd FL bd b lbd sbf (labels-pairsep gfd labs bd lss cls rps dls)
    (label-covers gfd dd idd labd rsd bd LB FL sdf FL iod rod ubd rlb spd uFL (sub-refl FL))))
  (let ((erased shs)) (shut-compl dd FL idd FL sdf gfd shFL sf iod bgfd))
  (let ((erased ks) (erased coS)) (co-exists gfd dd kfd sdf (MkClasses gfd dd kfd idd labd rsd iod lld lrd drd fixd cld rod) shs usdf))
  (let ((erased std) (erased apd)) (app-exists FL sdf))
  (let ((erased t) (erased at)) (add-ex b ks))
  (let ((erased coD)) (co-union gfd dd b ks t FL sdf std idd coFL coS apd (split-app-sub FL idd FL sdf std idd sf apd (sub-refl idd))
    (app-sub FL sdf std idd apd (under-sub dd FL idd uFL iod) ssdf) shFL bgfd (split-disj FL idd FL sdf sf) uFL usdf at))
  (let-match erased (co-unique gfd idd t kfd coD (co-of-classes gfd dd kfd idd (MkClasses gfd dd kfd idd labd rsd iod lld lrd drd fixd cld rod) iod)) (Refl _ _))
  (let ((erased tf) (erased rtf)) (respects-exists hd sdf dd usdf lhd))
  (let ((erased ld) (erased ivd)) (inv-exists hd ids))
  (let ((erased mo)) (morph-face-d d dd dr e n f ed nd fd er nr fr hd hr bd br fdi idd pt pmfd lhd uidd))
  (let ((erased mvA) (erased mvB)) (perm-moves dd d hd ld ids fd fdi f fi bd FL idd FL sdf tf gfd gf gfd gf pmfd pmf grfd grf shFL sbf mo iod io sf ivd dhd lhd uhd usdf rtf
    (spans-self gf) (spans-self gfd)))
  (let ((erased csf2)) (MkClasses gf d kf ids labf rsf io llf lrf drf fixf clf rof))
  (let ((erased coT)) (side-co dd d ks kf hd ld ids sdf tf gfd gf ivd io dhd lhd uhd rtf usdf mvA mvB csf2 coS))
  (let ((erased LH) (erased rlh)) (respects-exists labf hr d uhr llf))
  (let ((erased outer) (erased inner) (erased spo)) (sb-exists labf LH d llf ids uids))
  (let ((erased so)) (sb-split labf LH ids outer inner ids outer inner spo spo (sub-refl outer)))
  (let ((erased souter) (erased sinner)) (split-sub outer ids outer inner so))
  (let ((erased uo)) (sub-under outer ids d souter uids))
  (let ((erased L) (erased hv)) (outer-hitinv d f fi hr labf rsf ids LH outer inner ids gf pmf grf io rof uhr rlh spo uids))
  (let ((erased coO)) (co-map gfr gf idr outer hr L kfr d kf (co-of-classes gfr dr kfr idr csfr ior)
    (outer-lift-r d dr f hr L labf ids idr LH outer inner idr gfr hv io llf dhr lhr uhr rlh spo uidr (sub-refl idr))
    (outer-lift-g d dr f fi hr L labf rsf ids idr LH outer inner outer gf hv pmf grf io ior rof dhr lhr uhr rlh spo uo (sub-refl outer))
    (outer-moves-r d dd dr e n f ed nd fd er nr fr hd hr bd br fi fri idr gfr gf pt pmf pmfr grf ior lhr uhr (graph-fun dr fr gfr grfr))
    (outer-moves-g d dd dr e n f ed nd fd er nr fr hd hr bd br fi fri L labf rsf ids LH outer inner gf gf gfr pt hv pmf pmfr grf grfr io rof clf llf dhr lhr uhr rlh spo
      (graph-fun d f gf grf))
    csf2 uo))
  (let ((erased st) (erased ap)) (app-exists tf outer))
  (let ((erased utf)) (respects-under-vals hd sdf tf d rtf uhd))
  (let ((erased kt) (erased akt)) (add-ex ks kfr))
  (let ((erased coG)) (co-union gf d ks kfr kt tf outer st ids coT coO ap
    (inner-sub d dd f fd fdi hd hr bd bG bGr br labf labd rsd ids idd LH LB outer inner FL sdf tf st ids gf gfd pmfd grf grfd mo pp io iod rod clf llf dhd lhd
      rbd rbr rv ubd rlh rlb spo spd sf rtf ap (sub-refl ids))
    (app-sub tf outer st ids ap (under-sub d tf ids utf io) souter) (moves-shut gf gfd tf ld mvB) bgf
    (outer-disj d dd f fi fd fdi hd hr bd labf rsf ids idd LH outer inner FL sdf tf outer gf gfd pmf pmfd grf grfd shFL sbf mo pp io iod rof dhd uhd uhr rlh spo sf rtf
      usdf uo (sub-refl outer))
    utf uo akt))
  (let-match erased (co-unique gf ids kt kf coG (co-of-classes gf d kf ids csf2 io)) (Refl _ _))
  (let ((erased s) (erased a2)) (add-ex kfd kfr))
  (let ((erased bc) (erased q1) (erased q2)) (add-assoc b ks kfr kfd s at a2))
  (let-match erased (add-fn ks kfr bc kt q1 akt) (Refl _ _))
  (values b s lbd (add-comm b bc s q2) a2))

; The images of a disk dart and of its face step are on one face (cFhd).
(def-fns _ $ (erased face-hd : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br) (erased (List (Bond)) gf)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (Graph d f gf) grf) (erased (Nat) xd yd x y) (erased (Nth (Nat) fd xd yd) pf)
    (erased (Nth (Nat) hd xd x) hx) (erased (Nth (Nat) hd yd y) hy) -> (erased (Conn gf x y) r))
  (match erased (in-dec xd bd) _
    ((OrR _ _ out) (conn-adj gf x y (graph-adj d x y f gf grf (patch-face-d d dd dr e n f ed nd fd er nr fr hd hr bd br pt xd yd x y out pf hx hy))))
    ((OrL _ _ ib)
      (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids idd idr bG bGr h hd2 hr2 io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
      (let ((erased nfd) (erased ndi) (erased fdi) (erased rnfd) (erased pmed) (erased pmnd) (erased pmfd)) (hyper-core dd ed nd fd hd2))
      (let ((erased le) (erased ln) (erased lf)) (hyper-lengths dd ed nd fd hd2))
      (let ((erased lxd)) (pre-lt dd xd yd fd fdi pmfd pf))
      (let ((erased ws) (erased cw)) (cycle dd xd yd fd fdi pmfd pf lxd))
      (let ((erased ws1) (erased cw1)) (cut-first fd (Nil _) ws yd xd cw))
      (let-match erased sd (MkSimple _ _ lab ls rf rp dl))
      (let ((erased l) (erased pl)) (nth-exists _ lab dd yd (respects-length lab fd lab dd rf lf) (perm-val dd xd yd fd fdi pmfd pf)))
      (let ((erased off)) (path-off-simple fd lab bd ls ws1 yd xd l cw1 rf rp dl ib pl (path-label fd lab (Cons _ xd (Nil _)) ws1 yd xd l cw1 rf pl)))
      (let ((erased mo)) (morph-face-d d dd dr e n f ed nd fd er nr fr hd hr bd br fdi idd pt pmfd lhd (perm-under dd idd idd (perm-id dd idd iod))))
      (let ((erased z2) (erased ws2) (erased hz) (erased cw2) (erased rx))
        (path-push2 dd yd xd y hd fd fdi f bd idd bd bG ws1 pmfd mo iod dhd rbd (sub-refl bd) (path-reavoid fd (Cons _ xd (Nil _)) bd ws1 yd xd cw1 off) hy))
      (let-match erased (nth-fn _ hd xd z2 x hz hx) (Refl _ _))
      (conn-sym gf y x (path-graph-conn d y x f bG ws2 gf cw2 grf)))))

; v2 = hd v is a glink neighbour of u2.
(def-adts $ (DiskNext : ((List (Nat)) hd) ((List (Bond)) g) ((Nat) u2 v) -> Type)
  enum
  (many MkDiskNext : (erased (List (Nat)) hd) (erased (List (Bond)) g) (erased (Nat) u2 v v2) (erased (Nth (Nat) hd v v2) hv) (erased (Adj g u2 v2) a)
      -> (DiskNext hd g u2 v)))

; u2 is joined in g to the image of a dart of bd.
(def-adts $ (RingAt : ((List (Nat)) hd bd) ((List (Bond)) g) ((Nat) u2) -> Type)
  enum
  (many MkRingAt : (erased (List (Nat)) hd bd) (erased (List (Bond)) g) (erased (Nat) u2 wd w) (erased (In wd bd) iw) (erased (Nth (Nat) hd wd w) hw)
      (erased (Conn g u2 w) c) -> (RingAt hd bd g u2)))

; A glink step of the disk map off bd is sent to a glink step, or the image of its start is joined to the ring.
(def-fns _ $ (erased disk-adj : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br)
    (erased (List (Bond)) ge gn gf gnf g ged gnd gfd gnfd gd) (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt)
    (erased (Graph d e ge) pe) (erased (Graph d n gn) pn) (erased (Graph d f gf) pf) (erased (Cat gn gf gnf) c1) (erased (Cat ge gnf g) c2)
    (erased (Graph dd ed ged) pde) (erased (Graph dd nd gnd) pdn) (erased (Graph dd fd gfd) pdf) (erased (Cat gnd gfd gnfd) cd1) (erased (Cat ged gnfd gd) cd2)
    (erased (Nat) u v u2) (erased (Adj gd u v) a) (erased (NotIn u bd) ou) (erased (Nth (Nat) hd u u2) hu)
    -> (erased (HOr (DiskNext hd g u2 v) (RingAt hd bd g u2)) r))
  (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids idd idr bG bGr h hd2 hr2 io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
  (let ((erased nfd) (erased ndi) (erased fdi) (erased rnfd) (erased pmed) (erased pmnd) (erased pmfd)) (hyper-core dd ed nd fd hd2))
  (let ((erased mfd)) (morph-face-d d dd dr e n f ed nd fd er nr fr hd hr bd br fdi idd pt pmfd lhd (perm-under dd idd idd (perm-id dd idd iod))))
  (let ((erased sgf)) (spans-lift-r ge gnf g gf (spans-lift-r gn gf gnf gf (spans-self gf) c1) c2))
  (match erased (adj-cat-inv ged gnfd gd u v cd2 a) _
    ((OrL _ _ ae)
      (match erased (graph-adj-inv dd u v ed ged pde ae) _
        ((OrL _ _ puv)
          (let ((erased v2) (erased hv) (erased qv)) (morph hd ed e bd idd dd u v u2 med iod (pre-lt dd u v ed nfd pmed puv) ou puv hu))
          (OrL _ _ (MkDiskNext hd g u2 v v2 hv (gl-e ge gn gf gnf g u2 v2 c1 c2 (graph-adj d u2 v2 e ge pe qv)))))
        ((OrR _ _ pvu)
          (let ((erased ov)) (match erased (in-dec v bd) (((NotIn v bd) r))
            (absurd (OrL _ _ iv) (apart-irrefl u (notin-in u u bd ou (ncyc-next ed bd v u cyd iv pvu))))
            ((OrR _ _ o) o)))
          (let ((erased lv)) (pre-lt dd v u ed nfd pmed pvu))
          (let ((erased v2) (erased hv)) (nth-exists _ hd dd v lhd lv))
          (let ((erased u3) (erased hu3) (erased qu)) (morph hd ed e bd idd dd v u v2 med iod lv ov pvu hv))
          (let-match erased (nth-fn _ hd u u3 u2 hu3 hu) (Refl _ _))
          (OrL _ _ (MkDiskNext hd g u2 v v2 hv (gl-e ge gn gf gnf g u2 v2 c1 c2 (adj-sym ge v2 u2 (graph-adj d v2 u2 e ge pe qu))))))))
    ((OrR _ _ anf)
      (match erased (adj-cat-inv gnd gfd gnfd u v cd1 anf) _
        ((OrL _ _ an)
          (match erased (graph-adj-inv dd u v nd gnd pdn an) _
            ((OrL _ _ puv)
              (let ((erased v2) (erased hv) (erased qv)) (morph hd nd n (Nil _) idd dd u v u2 mnd iod (pre-lt dd u v nd ndi pmnd puv) (NotInNil u) puv hu))
              (OrL _ _ (MkDiskNext hd g u2 v v2 hv (gl-n ge gn gf gnf g u2 v2 c1 c2 (graph-adj d u2 v2 n gn pn qv)))))
            ((OrR _ _ pvu)
              (let ((erased lv)) (pre-lt dd v u nd ndi pmnd pvu))
              (let ((erased v2) (erased hv)) (nth-exists _ hd dd v lhd lv))
              (let ((erased u3) (erased hu3) (erased qu)) (morph hd nd n (Nil _) idd dd v u v2 mnd iod lv (NotInNil v) pvu hv))
              (let-match erased (nth-fn _ hd u u3 u2 hu3 hu) (Refl _ _))
              (OrL _ _ (MkDiskNext hd g u2 v v2 hv (gl-n ge gn gf gnf g u2 v2 c1 c2 (adj-sym gn v2 u2 (graph-adj d v2 u2 n gn pn qu))))))))
        ((OrR _ _ af)
          (match erased (graph-adj-inv dd u v fd gfd pdf af) _
            ((OrL _ _ puv)
              (let ((erased v2) (erased hv) (erased qv)) (morph hd fd f bd idd dd u v u2 mfd iod (pre-lt dd u v fd fdi pmfd puv) ou puv hu))
              (OrL _ _ (MkDiskNext hd g u2 v v2 hv (gl-f ge gn gf gnf g u2 v2 c1 c2 (graph-adj d u2 v2 f gf pf qv)))))
            ((OrR _ _ pvu)
              (let ((erased lv)) (pre-lt dd v u fd fdi pmfd pvu))
              (let ((erased v2) (erased hv)) (nth-exists _ hd dd v lhd lv))
              (match erased (in-dec v bd) _
                ((OrL _ _ iv)
                  (OrR _ _ (MkRingAt hd bd g u2 v v2 iv hv
                    (spans-conn g gf u2 v2 (conn-sym gf v2 u2 (face-hd d dd dr e n f ed nd fd er nr fr hd hr bd br gf pt pf v u v2 u2 pvu hv hu)) sgf))))
                ((OrR _ _ ov)
                  (let ((erased u3) (erased hu3) (erased qu)) (morph hd fd f bd idd dd v u v2 mfd iod lv ov pvu hv))
                  (let-match erased (nth-fn _ hd u u3 u2 hu3 hu) (Refl _ _))
                  (OrL _ _ (MkDiskNext hd g u2 v v2 hv (gl-f ge gn gf gnf g u2 v2 c1 c2 (adj-sym gf v2 u2 (graph-adj d v2 u2 f gf pf qu))))))))))))))

; A disk dart glink-joined to bd has its image glink-joined to the image of a dart of bd.
(def-fns _ $ (erased disk-to-ring : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br)
    (erased (List (Bond)) ge gn gf gnf g ged gnd gfd gnfd gd) (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt)
    (erased (Graph d e ge) pe) (erased (Graph d n gn) pn) (erased (Graph d f gf) pf) (erased (Cat gn gf gnf) c1) (erased (Cat ge gnf g) c2)
    (erased (Graph dd ed ged) pde) (erased (Graph dd nd gnd) pdn) (erased (Graph dd fd gfd) pdf) (erased (Cat gnd gfd gnfd) cd1) (erased (Cat ged gnfd gd) cd2)
    (erased (Nat) u b u2) (subterm erased (Conn gd u b) cn) (erased (In b bd) ib) (erased (Nth (Nat) hd u u2) hu) -> (erased (RingAt hd bd g u2) r))
  (match erased (in-dec u bd) _
    ((OrL _ _ iu) (MkRingAt hd bd g u2 u u2 iu hu (ConnHere g u2)))
    ((OrR _ _ ou)
      (let-match erased cn (ConnStep _ _ v _ a cn1) (absurd (ConnHere _ _) (apart-irrefl u (notin-in u u bd ou ib))))
      (match erased (disk-adj d dd dr e n f ed nd fd er nr fr hd hr bd br ge gn gf gnf g ged gnd gfd gnfd gd pt pe pn pf c1 c2 pde pdn pdf cd1 cd2 u v u2 a ou hu) _
        ((OrL _ _ dn)
          (let-match erased dn (MkDiskNext _ _ _ _ v2 hv av))
          (let-match erased (disk-to-ring d dd dr e n f ed nd fd er nr fr hd hr bd br ge gn gf gnf g ged gnd gfd gnfd gd pt pe pn pf c1 c2 pde pdn pdf cd1 cd2 v b v2 cn1 ib hv)
            (MkRingAt _ _ _ _ wd w iw hw cw))
          (MkRingAt hd bd g u2 wd w iw hw (ConnStep g u2 v2 w av cw)))
        ((OrR _ _ ra) ra)))))

; A dart of both images is the image of a dart of br.
(def-fns _ $ (erased hd-hr-ring : (erased (Nat) d xd xr x) (erased (List (Nat)) hd hr bd br bG bGr ids) (erased (PatchParts hd hr bd ids) pp) (erased (Iota d ids) io)
    (erased (Under hr d) uhr) (erased (Distinct hr) dhr) (erased (Respects hd bd bG) rbd) (erased (Respects hr br bGr) rbr) (erased (RevApp (Nat) bG (Nil (Nat)) bGr) rv)
    (erased (Nth (Nat) hd xd x) hx) (erased (Nth (Nat) hr xr x) rx) -> (erased (In xr br) r))
  (match erased (parts-at hd hr bd ids x pp (iota-in d x ids io (under-nth hr xr x d uhr rx))) _
    (absurd (PtDisk _ _ _ _ xd2 px out outr) (apart-irrefl x (notin-in x x hr outr (nth-in hr xr x rx))))
    ((PtRing _ _ _ _ xd2 xr2 px pin pr)
      (let ((erased r2) (erased ir2) (erased p2)) (respects-in hr br bGr x rbr (revapp-in bG (Nil _) bGr x rv (OrL _ _ (in-map hd bd bG xd2 x pin rbd px)))))
      (let-match erased (distinct-nth hr r2 xr x dhr p2 rx) (Refl _ _))
      ir2)
    (absurd (PtRest _ _ _ _ xr2 pr outd) (apart-irrefl x (notin-in x x hd outd (nth-in hd xd x hx))))))

; Any two darts of a node cycle are joined.
(def-fns _ $ (erased ring-conn : (erased (Nat) k r1 r2) (erased (List (Nat)) n R) (erased (List (Bond)) gn g) (erased (NCyc n R) nc) (erased (Graph k n gn) gr)
    (erased (Spans g gn) sp) (erased (In r1 R) i1) (erased (In r2 R) i2) -> (erased (Conn g r1 r2) r))
  (let-match erased nc (NCCons _ xs r0 yl fp back) (absurd (NCNil _) i1))
  (let ((erased cv)) (fpath-covers n xs gn k r0 r0 yl gr (ConnHere gn r0) fp))
  (let ((erased s1) (erased j1) (erased c1)) (covers-at gn (Cons _ r0 (Nil _)) (Cons _ r0 xs) r1 cv i1))
  (let ((erased s2) (erased j2) (erased c2)) (covers-at gn (Cons _ r0 (Nil _)) (Cons _ r0 xs) r2 cv i2))
  (let-match erased j1 (InHere _ _) (absurd (InThere _ _ _ i) i))
  (let-match erased j2 (InHere _ _) (absurd (InThere _ _ _ i) i))
  (spans-conn g gn r1 r2 (conn-cat gn r1 r0 r2 (conn-sym gn r0 r1 c1) c2) sp))

; The face step in the remainder map is a face walk in the whole map.
(def-fns _ $ (erased r-face-conn : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br fi) (erased (List (Bond)) gf)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (HPerm d f fi) pmf) (erased (Graph d f gf) grf) (erased (Under hr d) uhr)
    (erased (Nat) xr yr x y) (erased (Nth (Nat) fr xr yr) pfr) (erased (Nth (Nat) hr xr x) hx) (erased (Nth (Nat) hr yr y) hy) -> (erased (Conn gf x y) r))
  (let ((erased x1) (erased px1) (erased lx1)) (perm-nth d x f fi pmf (under-nth hr xr x d uhr hx)))
  (let-match erased (face-next-r d dd dr e n f ed nd fd er nr fr hd hr bd br pt xr yr x x1 y pfr hx px1 hy) (MkFirstHit _ _ ws _ _ w iy))
  (ConnStep gf x x1 y (graph-adj d x x1 f gf grf px1) (path-graph-conn d x1 y f hr ws gf w grf)))

; ls sends each dart x of xs to its position in hr, to a dart of br whose image is joined to x in g if x is in a and not in hr, and to 0
; if x is not in a.
(def-adts $ (RingInv : ((List (Nat)) hr br a) ((List (Bond)) g) ((List (Nat)) xs ls) -> Type)
  enum
  (many RvNil : (erased (List (Nat)) hr br a) (erased (List (Bond)) g) -> (RingInv hr br a g (Nil (Nat)) (Nil (Nat))))
  (many RvHit : (erased (List (Nat)) hr br a xs ls) (erased (List (Bond)) g) (erased (Nat) x j) (erased (Nth (Nat) hr j x) pj) (erased (RingInv hr br a g xs ls) rest)
      -> (RingInv hr br a g (Cons (Nat) x xs) (Cons (Nat) j ls)))
  (many RvRing : (erased (List (Nat)) hr br a xs ls) (erased (List (Bond)) g) (erased (Nat) x r w) (erased (NotIn x hr) ox) (erased (In r br) ir) (erased (Nth (Nat) hr r w) pw)
      (erased (Conn g x w) c) (erased (RingInv hr br a g xs ls) rest) -> (RingInv hr br a g (Cons (Nat) x xs) (Cons (Nat) r ls)))
  (many RvOut : (erased (List (Nat)) hr br a xs ls) (erased (List (Bond)) g) (erased (Nat) x) (erased (NotIn x a) oa) (erased (RingInv hr br a g xs ls) rest)
      -> (RingInv hr br a g (Cons (Nat) x xs) (Cons (Nat) (Zero) ls))))

; What the entry of a dart of a is.
(def-adts $ (RingAt2 : ((List (Nat)) hr br) ((List (Bond)) g) ((Nat) x r) -> Type)
  enum
  (many RAHit : (erased (List (Nat)) hr br) (erased (List (Bond)) g) (erased (Nat) x r) (erased (Nth (Nat) hr r x) pr) -> (RingAt2 hr br g x r))
  (many RARing : (erased (List (Nat)) hr br) (erased (List (Bond)) g) (erased (Nat) x r w) (erased (NotIn x hr) ox) (erased (In r br) ir) (erased (Nth (Nat) hr r w) pw)
      (erased (Conn g x w) c) -> (RingAt2 hr br g x r)))

(def-fns _ $ (erased ringinv-at : (erased (List (Nat)) hr br a xs ls) (erased (List (Bond)) g) (erased (Nat) i x) (subterm erased (RingInv hr br a g xs ls) rv)
    (erased (Nth (Nat) xs i x) px) (erased (In x a) ia) -> (erased (Nat) r) (erased (Nth (Nat) ls i r) pr) (erased (RingAt2 hr br g x r) ra))
  (match erased rv _
    (absurd (RvNil _ _ _ _) px)
    ((RvHit _ _ _ xs1 ls1 _ y j pj rv1)
      (match erased px _
        ((NthHere _ _ _) (values j (NthHere _ j ls1) (RAHit hr br g x j pj)))
        ((NthThere _ _ _ i1 _ px1)
          (let ((erased r) (erased pr) (erased ra)) (ringinv-at hr br a xs1 ls1 g i1 x rv1 px1 ia))
          (values r (NthThere _ j ls1 i1 r pr) ra))))
    ((RvRing _ _ _ xs1 ls1 _ y r0 w ox ir pw c rv1)
      (match erased px _
        ((NthHere _ _ _) (values r0 (NthHere _ r0 ls1) (RARing hr br g x r0 w ox ir pw c)))
        ((NthThere _ _ _ i1 _ px1)
          (let ((erased r) (erased pr) (erased ra)) (ringinv-at hr br a xs1 ls1 g i1 x rv1 px1 ia))
          (values r (NthThere _ r0 ls1 i1 r pr) ra))))
    ((RvOut _ _ _ xs1 ls1 _ y oa rv1)
      (match erased px _
        (absurd (NthHere _ _ _) (apart-irrefl x (notin-in x x a oa ia)))
        ((NthThere _ _ _ i1 _ px1)
          (let ((erased r) (erased pr) (erased ra)) (ringinv-at hr br a xs1 ls1 g i1 x rv1 px1 ia))
          (values r (NthThere _ (Zero) ls1 i1 r pr) ra))))))

; The entry of an image of hr is its position.
(def-fns _ $ (erased ring-at-hit : (erased (List (Nat)) hr br) (erased (List (Bond)) g) (erased (Nat) x r j) (erased (RingAt2 hr br g x r) ra) (erased (Distinct hr) dh)
    (erased (Nth (Nat) hr j x) pj) -> (erased (Eq (Nat) r j) e))
  (match erased ra _
    ((RAHit _ _ _ _ _ pr) (distinct-nth hr r j x dh pr pj))
    (absurd (RARing _ _ _ _ _ w ox ir pw c) (apart-irrefl x (notin-in x x hr ox (nth-in hr j x pj))))))

; A dart off the image of hr is the image of a disk dart off bd.
(def-fns _ $ (erased disk-of : (erased (Nat) d u) (erased (List (Nat)) hd hr bd ids) (erased (PatchParts hd hr bd ids) pp) (erased (Iota d ids) io) (erased (Lt u d) lu)
    (erased (NotIn u hr) ou) -> (erased (Nat) ud) (erased (Nth (Nat) hd ud u) hu) (erased (NotIn ud bd) out))
  (match erased (parts-at hd hr bd ids u pp (iota-in d u ids io lu)) _
    ((PtDisk _ _ _ _ ud px out outr) (values ud px out))
    (absurd (PtRing _ _ _ _ ud ur px pin pr) (apart-irrefl u (notin-in u u hr ou (nth-in hr ur u pr))))
    (absurd (PtRest _ _ _ _ ur pr outd) (apart-irrefl u (notin-in u u hr ou (nth-in hr ur u pr))))))

; The entries of the ends of an edge step of the whole map in a are joined in the remainder map.
(def-fns _ $ (erased conn-e : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br ids a L) (erased (List (Bond)) g gr ger gnr gfr gnfr)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (RingInv hr br a g ids L) ri) (erased (Iota d ids) io0) (erased (Graph dr er ger) pger)
    (erased (Graph dr nr gnr) pgnr) (erased (Cat gnr gfr gnfr) cr1) (erased (Cat ger gnfr gr) cr2) (erased (Nat) u v) (erased (Nth (Nat) e u v) puv)
    (erased (In u a) ia) (erased (In v a) iv) -> (erased (Nat) ru rv) (erased (Nth (Nat) L u ru) pu) (erased (Nth (Nat) L v rv) pv) (erased (Conn gr ru rv) cn))
  (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids2 idd idr bG bGr h hd2 hr2 io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
  (let-match erased (iota-fn d ids ids2 io0 io) (Refl _ _))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pme) (erased pmn) (erased pmf)) (hyper-core d e n f h))
  (let ((erased nfd) (erased ndi) (erased fdi) (erased rnfd) (erased pmed) (erased pmnd) (erased pmfd)) (hyper-core dd ed nd fd hd2))
  (let ((erased nfr) (erased nri) (erased fri) (erased rnfr) (erased pmer) (erased pmnr) (erased pmfr)) (hyper-core dr er nr fr hr2))
  (let ((erased sgn)) (spans-lift-r ger gnfr gr gnr (spans-lift-l gnr gfr gnfr gnr (spans-self gnr) cr1) cr2))
  (let ((erased lu)) (pre-lt d u v e nf pme puv))
  (let ((erased ru) (erased pu) (erased rau)) (ringinv-at hr br a ids L g u u ri (iota-nth d u ids io lu) ia))
  (let ((erased rv0) (erased pv) (erased rav)) (ringinv-at hr br a ids L g v v ri (iota-nth d v ids io (perm-val d u v e nf pme puv)) iv))
  (match erased rau _
    ((RAHit _ _ _ _ _ hru)
      (let ((erased lru)) (nth-lt-length _ hr ru dr u hru lhr))
      (let ((erased ru2) (erased pr) (erased lr2)) (perm-nth dr ru er nfr pmer lru))
      (let ((erased w) (erased hw) (erased qw)) (morph hr er e (Nil _) idr dr ru ru2 u mer ior lru (NotInNil ru) pr hru))
      (let-match erased (nth-fn _ e u w v qw puv) (Refl _ _))
      (match erased rav _
        ((RAHit _ _ _ _ _ hrv)
          (let-match erased (distinct-nth hr ru2 rv0 v dhr hw hrv) (Refl _ _))
          (values ru rv0 pu pv (conn-adj gr ru rv0 (gl-e ger gnr gfr gnfr gr ru rv0 cr1 cr2 (graph-adj dr ru rv0 er ger pger pr)))))
        (absurd (RARing _ _ _ _ _ w2 ov _ _ _) (apart-irrefl v (notin-in v v hr ov (nth-in hr ru2 v hw))))))
    ((RARing _ _ _ _ _ wu ou iru _ _)
      (match erased rav _
        ((RAHit _ _ _ _ _ hrv)
          (let ((erased ud) (erased hud) (erased oud)) (disk-of d u hd hr bd ids pp io lu ou))
          (let ((erased lud)) (nth-lt-length _ hd ud dd u hud lhd))
          (let ((erased vd) (erased pvd) (erased lvd)) (perm-nth dd ud ed nfd pmed lud))
          (let ((erased w) (erased hw) (erased qw)) (morph hd ed e bd idd dd ud vd u med iod lud oud pvd hud))
          (let-match erased (nth-fn _ e u w v qw puv) (Refl _ _))
          (values ru rv0 pu pv (ring-conn dr ru rv0 nr br gnr gr cyr pgnr sgn iru (hd-hr-ring d vd rv0 v hd hr bd br bG bGr ids pp io uhr dhr rbd rbr rv hw hrv))))
        ((RARing _ _ _ _ _ wv ov irv _ _) (values ru rv0 pu pv (ring-conn dr ru rv0 nr br gnr gr cyr pgnr sgn iru irv)))))))

(def-fns _ $ (erased conn-n : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br ids a L) (erased (List (Bond)) g gr ger gnr gfr gnfr)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (RingInv hr br a g ids L) ri) (erased (Iota d ids) io0)
    (erased (Graph dr nr gnr) pgnr) (erased (Cat gnr gfr gnfr) cr1) (erased (Cat ger gnfr gr) cr2) (erased (Nat) u v) (erased (Nth (Nat) n u v) puv)
    (erased (In u a) ia) (erased (In v a) iv) -> (erased (Nat) ru rv) (erased (Nth (Nat) L u ru) pu) (erased (Nth (Nat) L v rv) pv) (erased (Conn gr ru rv) cn))
  (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids2 idd idr bG bGr h hd2 hr2 io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
  (let-match erased (iota-fn d ids ids2 io0 io) (Refl _ _))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pme) (erased pmn) (erased pmf)) (hyper-core d e n f h))
  (let ((erased nfd) (erased ndi) (erased fdi) (erased rnfd) (erased pmed) (erased pmnd) (erased pmfd)) (hyper-core dd ed nd fd hd2))
  (let ((erased nfr) (erased nri) (erased fri) (erased rnfr) (erased pmer) (erased pmnr) (erased pmfr)) (hyper-core dr er nr fr hr2))
  (let ((erased sgn)) (spans-lift-r ger gnfr gr gnr (spans-lift-l gnr gfr gnfr gnr (spans-self gnr) cr1) cr2))
  (let ((erased lu)) (pre-lt d u v n ni pmn puv))
  (let ((erased ru) (erased pu) (erased rau)) (ringinv-at hr br a ids L g u u ri (iota-nth d u ids io lu) ia))
  (let ((erased rv0) (erased pv) (erased rav)) (ringinv-at hr br a ids L g v v ri (iota-nth d v ids io (perm-val d u v n ni pmn puv)) iv))
  (let ((erased lv)) (perm-val d u v n ni pmn puv))
  (match erased rau _
    ((RAHit _ _ _ _ _ hru)
      (let ((erased lru)) (nth-lt-length _ hr ru dr u hru lhr))
      (match erased (in-dec ru br) _
        ((OrR _ _ obr)
          (let ((erased ru2) (erased pr) (erased lr2)) (perm-nth dr ru nr nri pmnr lru))
          (let ((erased w) (erased hw) (erased qw)) (morph hr nr n br idr dr ru ru2 u mnr ior lru obr pr hru))
          (let-match erased (nth-fn _ n u w v qw puv) (Refl _ _))
          (match erased rav _
            ((RAHit _ _ _ _ _ hrv)
              (let-match erased (distinct-nth hr ru2 rv0 v dhr hw hrv) (Refl _ _))
              (values ru rv0 pu pv (conn-adj gr ru rv0 (gl-n ger gnr gfr gnfr gr ru rv0 cr1 cr2 (graph-adj dr ru rv0 nr gnr pgnr pr)))))
            (absurd (RARing _ _ _ _ _ w2 ov _ _ _) (apart-irrefl v (notin-in v v hr ov (nth-in hr ru2 v hw))))))
        ((OrL _ _ ibr)
          (match erased rav _
            ((RAHit _ _ _ _ _ hrv)
              (let-match erased (revapp-out bG (Nil _) bGr u rv (in-map hr br bGr ru u ibr rbr hru)) (OrL _ _ iug) (absurd (OrR _ _ i) i))
              (let ((erased ud) (erased iud) (erased hud)) (respects-in hd bd bG u rbd iug))
              (let ((erased lud)) (nth-lt-length _ hd ud dd u hud lhd))
              (let ((erased vd) (erased pvd) (erased lvd)) (perm-nth dd ud nd ndi pmnd lud))
              (let ((erased w) (erased hw) (erased qw)) (morph hd nd n (Nil _) idd dd ud vd u mnd iod lud (NotInNil ud) pvd hud))
              (let-match erased (nth-fn _ n u w v qw puv) (Refl _ _))
              (values ru rv0 pu pv (ring-conn dr ru rv0 nr br gnr gr cyr pgnr sgn ibr (hd-hr-ring d vd rv0 v hd hr bd br bG bGr ids pp io uhr dhr rbd rbr rv hw hrv))))
            ((RARing _ _ _ _ _ wv ov irv _ _) (values ru rv0 pu pv (ring-conn dr ru rv0 nr br gnr gr cyr pgnr sgn ibr irv)))))))
    ((RARing _ _ _ _ _ wu ou iru _ _)
      (match erased rav _
        ((RAHit _ _ _ _ _ hrv)
          (let ((erased ud) (erased hud) (erased oud)) (disk-of d u hd hr bd ids pp io lu ou))
          (let ((erased lud)) (nth-lt-length _ hd ud dd u hud lhd))
          (let ((erased vd) (erased pvd) (erased lvd)) (perm-nth dd ud nd ndi pmnd lud))
          (let ((erased w) (erased hw) (erased qw)) (morph hd nd n (Nil _) idd dd ud vd u mnd iod lud (NotInNil ud) pvd hud))
          (let-match erased (nth-fn _ n u w v qw puv) (Refl _ _))
          (values ru rv0 pu pv (ring-conn dr ru rv0 nr br gnr gr cyr pgnr sgn iru (hd-hr-ring d vd rv0 v hd hr bd br bG bGr ids pp io uhr dhr rbd rbr rv hw hrv))))
        ((RARing _ _ _ _ _ wv ov irv _ _) (values ru rv0 pu pv (ring-conn dr ru rv0 nr br gnr gr cyr pgnr sgn iru irv)))))))

(def-fns _ $ (erased conn-f : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br ids a L) (erased (List (Bond)) g gr ger gnr gfr gnfr)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (RingInv hr br a g ids L) ri) (erased (Iota d ids) io0)
    (erased (Graph dr nr gnr) pgnr) (erased (Graph dr fr gfr) pgfr) (erased (Cat gnr gfr gnfr) cr1) (erased (Cat ger gnfr gr) cr2) (erased (Nat) u v) (erased (Nth (Nat) f u v) puv)
    (erased (In u a) ia) (erased (In v a) iv) -> (erased (Nat) ru rv) (erased (Nth (Nat) L u ru) pu) (erased (Nth (Nat) L v rv) pv) (erased (Conn gr ru rv) cn))
  (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids2 idd idr bG bGr h hd2 hr2 io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
  (let-match erased (iota-fn d ids ids2 io0 io) (Refl _ _))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pme) (erased pmn) (erased pmf)) (hyper-core d e n f h))
  (let ((erased nfd) (erased ndi) (erased fdi) (erased rnfd) (erased pmed) (erased pmnd) (erased pmfd)) (hyper-core dd ed nd fd hd2))
  (let ((erased nfr) (erased nri) (erased fri) (erased rnfr) (erased pmer) (erased pmnr) (erased pmfr)) (hyper-core dr er nr fr hr2))
  (let ((erased sgn)) (spans-lift-r ger gnfr gr gnr (spans-lift-l gnr gfr gnfr gnr (spans-self gnr) cr1) cr2))
  (let ((erased lu)) (pre-lt d u v f fi pmf puv))
  (let ((erased ru) (erased pu) (erased rau)) (ringinv-at hr br a ids L g u u ri (iota-nth d u ids io lu) ia))
  (let ((erased rv0) (erased pv) (erased rav)) (ringinv-at hr br a ids L g v v ri (iota-nth d v ids io (perm-val d u v f fi pmf puv)) iv))
  (match erased rau _
    ((RAHit _ _ _ _ _ hru)
      (let ((erased lru)) (nth-lt-length _ hr ru dr u hru lhr))
      (let ((erased yr) (erased pyr) (erased lyr)) (perm-nth dr ru fr fri pmfr lru))
      (let ((erased y) (erased hy)) (nth-exists _ hr dr yr lhr lyr))
      (let ((erased fh)) (face-next-r d dd dr e n f ed nd fd er nr fr hd hr bd br pt ru yr u v y pyr hru puv hy))
      (let ((erased ad)) (conn-adj gr ru yr (gl-f ger gnr gfr gnfr gr ru yr cr1 cr2 (graph-adj dr ru yr fr gfr pgfr pyr))))
      (match erased rav _
        ((RAHit _ _ _ _ _ hrv)
          (let-match erased (hit-fn f hr v y v fh (MkFirstHit f hr (Nil _) v v (PathHere f hr v) (nth-in hr rv0 v hrv))) (Refl _ _))
          (let-match erased (distinct-nth hr yr rv0 y dhr hy hrv) (Refl _ _))
          (values ru rv0 pu pv ad))
        ((RARing _ _ _ _ _ wv ov irv _ _)
          (match erased (in-dec yr br) _
            (absurd (OrR _ _ oyr)
              (let-match erased (nth-fn _ f u v y puv (patch-face-r d dd dr e n f ed nd fd er nr fr hd hr bd br pt ru yr u y oyr pyr hru hy)) (Refl _ _))
              (apart-irrefl v (notin-in v v hr ov (nth-in hr yr v hy))))
            ((OrL _ _ iyr) (values ru rv0 pu pv (conn-cat gr ru yr rv0 ad (ring-conn dr yr rv0 nr br gnr gr cyr pgnr sgn iyr irv))))))))
    ((RARing _ _ _ _ _ wu ou iru _ _)
      (match erased rav _
        ((RAHit _ _ _ _ _ hrv)
          (let ((erased ud) (erased hud) (erased oud)) (disk-of d u hd hr bd ids pp io lu ou))
          (let ((erased lud)) (nth-lt-length _ hd ud dd u hud lhd))
          (let ((erased vd) (erased pvd) (erased lvd)) (perm-nth dd ud fd fdi pmfd lud))
          (let ((erased w) (erased hw)) (nth-exists _ hd dd vd lhd lvd))
          (let-match erased (nth-fn _ f u w v (patch-face-d d dd dr e n f ed nd fd er nr fr hd hr bd br pt ud vd u w oud pvd hud hw) puv) (Refl _ _))
          (values ru rv0 pu pv (ring-conn dr ru rv0 nr br gnr gr cyr pgnr sgn iru (hd-hr-ring d vd rv0 v hd hr bd br bG bGr ids pp io uhr dhr rbd rbr rv hw hrv))))
        ((RARing _ _ _ _ _ wv ov irv _ _) (values ru rv0 pu pv (ring-conn dr ru rv0 nr br gnr gr cyr pgnr sgn iru irv)))))))

; The entries of the ends of a glink step of the whole map in a are joined in the remainder map.
(def-fns _ $ (erased g-step-conn : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br ids a L) (erased (List (Bond)) ge gn gf gnf g gr ger gnr gfr gnfr)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (RingInv hr br a g ids L) ri) (erased (Iota d ids) io)
    (erased (Graph d e ge) pe) (erased (Graph d n gn) pn) (erased (Graph d f gf) pf) (erased (Cat gn gf gnf) c1) (erased (Cat ge gnf g) c2)
    (erased (Graph dr er ger) pger) (erased (Graph dr nr gnr) pgnr) (erased (Graph dr fr gfr) pgfr) (erased (Cat gnr gfr gnfr) cr1) (erased (Cat ger gnfr gr) cr2)
    (erased (Nat) u v) (erased (Adj g u v) a0) (erased (In u a) ia) (erased (In v a) iv)
    -> (erased (Nat) ru rv) (erased (Nth (Nat) L u ru) pu) (erased (Nth (Nat) L v rv) pv) (erased (Conn gr ru rv) cn))
  (match erased (adj-cat-inv ge gnf g u v c2 a0) _
    ((OrL _ _ ae)
      (match erased (graph-adj-inv d u v e ge pe ae) _
        ((OrL _ _ q) (conn-e d dd dr e n f ed nd fd er nr fr hd hr bd br ids a L g gr ger gnr gfr gnfr pt ri io pger pgnr cr1 cr2 u v q ia iv))
        ((OrR _ _ q)
          (let ((erased rv) (erased ru) (erased pv) (erased pu) (erased cn)) (conn-e d dd dr e n f ed nd fd er nr fr hd hr bd br ids a L g gr ger gnr gfr gnfr pt ri io pger pgnr cr1 cr2 v u q iv ia))
          (values ru rv pu pv (conn-sym gr rv ru cn)))))
    ((OrR _ _ anf)
      (match erased (adj-cat-inv gn gf gnf u v c1 anf) _
        ((OrL _ _ an)
          (match erased (graph-adj-inv d u v n gn pn an) _
            ((OrL _ _ q) (conn-n d dd dr e n f ed nd fd er nr fr hd hr bd br ids a L g gr ger gnr gfr gnfr pt ri io pgnr cr1 cr2 u v q ia iv))
            ((OrR _ _ q)
              (let ((erased rv) (erased ru) (erased pv) (erased pu) (erased cn)) (conn-n d dd dr e n f ed nd fd er nr fr hd hr bd br ids a L g gr ger gnr gfr gnfr pt ri io pgnr cr1 cr2 v u q iv ia))
              (values ru rv pu pv (conn-sym gr rv ru cn)))))
        ((OrR _ _ af)
          (match erased (graph-adj-inv d u v f gf pf af) _
            ((OrL _ _ q) (conn-f d dd dr e n f ed nd fd er nr fr hd hr bd br ids a L g gr ger gnr gfr gnfr pt ri io pgnr pgfr cr1 cr2 u v q ia iv))
            ((OrR _ _ q)
              (let ((erased rv) (erased ru) (erased pv) (erased pu) (erased cn)) (conn-f d dd dr e n f ed nd fd er nr fr hd hr bd br ids a L g gr ger gnr gfr gnfr pt ri io pgnr pgfr cr1 cr2 v u q iv ia))
              (values ru rv pu pv (conn-sym gr rv ru cn)))))))))

(def-fns _ $ (erased g-moves : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br ids a ra L labg LHg)
    (erased (List (Bond)) g0 ge gn gf gnf g gr ger gnr gfr gnfr) (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (RingInv hr br a g ids L) ri)
    (erased (Iota d ids) io) (erased (Graph d e ge) pe) (erased (Graph d n gn) pn) (erased (Graph d f gf) pf) (erased (Cat gn gf gnf) c1) (erased (Cat ge gnf g) c2)
    (erased (Graph dr er ger) pger) (erased (Graph dr nr gnr) pgnr) (erased (Graph dr fr gfr) pgfr) (erased (Cat gnr gfr gnfr) cr1) (erased (Cat ger gnfr gr) cr2)
    (erased (Const labg g) cl) (erased (Length (Nat) labg d) ll) (erased (SplitBy labg LHg ids a ra) sp) (erased (Below g d) bg) (subterm erased (Within g0 g) wt)
    -> (erased (Moves g0 a L gr) r))
  (let-match erased wt (WithinCons g1 _ b j pj wt1) ((WithinNil _) (MvNil a L gr)))
  (let-match erased b (MkBond u v))
  (let ((erased rest)) (g-moves d dd dr e n f ed nd fd er nr fr hd hr bd br ids a ra L labg LHg g1 ge gn gf gnf g gr ger gnr gfr gnfr pt ri io pe pn pf c1 c2
    pger pgnr pgfr cr1 cr2 cl ll sp bg wt1))
  (let ((erased a0)) (nth-adj g j u v pj))
  (let ((erased lu)) (below-adj g d v u (adj-sym g u v a0) bg))
  (let ((erased lv)) (below-adj g d u v a0 bg))
  (let ((erased l) (erased pl)) (nth-exists _ labg d u ll lu))
  (let ((erased pl2)) (adj-const labg g u v l a0 cl pl))
  (match erased (in-dec u a) _
    ((OrL _ _ ia)
      (let ((erased iv)) (sb-member labg LHg ids a ra v l sp (iota-in d v ids io lv) pl2 (sb-in-key-at labg LHg ids a ra u l sp ia pl)))
      (let ((erased ru) (erased rv) (erased pu) (erased pv) (erased cn))
        (g-step-conn d dd dr e n f ed nd fd er nr fr hd hr bd br ids a L ge gn gf gnf g gr ger gnr gfr gnfr pt ri io pe pn pf c1 c2 pger pgnr pgfr cr1 cr2 u v a0 ia iv))
      (MvIn g1 gr a L u v ru rv ia iv pu pv cn rest))
    ((OrR _ _ oa)
      (let ((erased ol)) (match erased (in-dec l LHg) (((NotIn l LHg) r))
        (absurd (OrL _ _ il) (apart-irrefl u (notin-in u u a oa (sb-member labg LHg ids a ra u l sp (iota-in d u ids io lu) pl il))))
        ((OrR _ _ o) o)))
      (MvOut g1 gr a L u v oa (sb-notmember labg LHg ids a ra v l sp pl2 ol) rest))))

; A node step of the remainder map is joined in the whole map: x = fr (er y).
(def-fns _ $ (erased nr-conn : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br fi) (erased (List (Bond)) ge gn gf gnf g)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (HPerm d f fi) pmf) (erased (Graph d e ge) pe) (erased (Graph d f gf) pf)
    (erased (Cat gn gf gnf) c1) (erased (Cat ge gnf g) c2) (erased (Nat) xr yr x y) (erased (Nth (Nat) nr xr yr) pn) (erased (Nth (Nat) hr xr x) hx) (erased (Nth (Nat) hr yr y) hy)
    -> (erased (Conn g x y) r))
  (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids idd idr bG bGr h hd2 hr2 io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
  (let ((erased nfr) (erased nri) (erased fri) (erased rnfr) (erased pmer) (erased pmnr) (erased pmfr)) (hyper-core dr er nr fr hr2))
  (let ((erased lyr)) (perm-val dr xr yr nr nri pmnr pn))
  (let ((erased ar) (erased pa) (erased la)) (perm-nth dr yr er nfr pmer lyr))
  (let ((erased paf)) (hyper-third dr ar yr xr er nr fr hr2 pa pn))
  (let ((erased z) (erased hz) (erased qz)) (morph hr er e (Nil _) idr dr yr ar y mer ior lyr (NotInNil yr) pa hy))
  (conn-sym g y x (ConnStep g y z x (gl-e ge gn gf gnf g y z c1 c2 (graph-adj d y z e ge pe qz))
    (spans-conn g gf z x (r-face-conn d dd dr e n f ed nd fd er nr fr hd hr bd br fi gf pt pmf pf uhr ar xr z x paf hz hx)
      (spans-lift-r ge gnf g gf (spans-lift-r gn gf gnf gf (spans-self gf) c1) c2)))))

; The images of the ends of a glink step of the remainder map are joined in the whole map.
(def-fns _ $ (erased r-step-conn : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br fi) (erased (List (Bond)) ge gn gf gnf g gr ger gnr gfr gnfr)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (HPerm d f fi) pmf) (erased (Graph d e ge) pe) (erased (Graph d f gf) pf)
    (erased (Cat gn gf gnf) c1) (erased (Cat ge gnf g) c2) (erased (Graph dr er ger) pger) (erased (Graph dr nr gnr) pgnr) (erased (Graph dr fr gfr) pgfr)
    (erased (Cat gnr gfr gnfr) cr1) (erased (Cat ger gnfr gr) cr2) (erased (Nat) xr yr x y) (erased (Adj gr xr yr) a0) (erased (Nth (Nat) hr xr x) hx) (erased (Nth (Nat) hr yr y) hy)
    -> (erased (Conn g x y) r))
  (let ((erased sgf)) (spans-lift-r ge gnf g gf (spans-lift-r gn gf gnf gf (spans-self gf) c1) c2))
  (match erased (adj-cat-inv ger gnfr gr xr yr cr2 a0) _
    ((OrL _ _ ae)
      (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids idd idr bG bGr h hd2 hr2 io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
      (let ((erased nfr) (erased nri) (erased fri) (erased rnfr) (erased pmer) (erased pmnr) (erased pmfr)) (hyper-core dr er nr fr hr2))
      (match erased (graph-adj-inv dr xr yr er ger pger ae) _
        ((OrL _ _ q)
          (let ((erased w) (erased hw) (erased qw)) (morph hr er e (Nil _) idr dr xr yr x mer ior (pre-lt dr xr yr er nfr pmer q) (NotInNil xr) q hx))
          (let-match erased (nth-fn _ hr yr w y hw hy) (Refl _ _))
          (conn-adj g x y (gl-e ge gn gf gnf g x y c1 c2 (graph-adj d x y e ge pe qw))))
        ((OrR _ _ q)
          (let ((erased w) (erased hw) (erased qw)) (morph hr er e (Nil _) idr dr yr xr y mer ior (pre-lt dr yr xr er nfr pmer q) (NotInNil yr) q hy))
          (let-match erased (nth-fn _ hr xr w x hw hx) (Refl _ _))
          (conn-adj g x y (adj-sym g y x (gl-e ge gn gf gnf g y x c1 c2 (graph-adj d y x e ge pe qw)))))))
    ((OrR _ _ anf)
      (match erased (adj-cat-inv gnr gfr gnfr xr yr cr1 anf) _
        ((OrL _ _ an)
          (match erased (graph-adj-inv dr xr yr nr gnr pgnr an) _
            ((OrL _ _ q) (nr-conn d dd dr e n f ed nd fd er nr fr hd hr bd br fi ge gn gf gnf g pt pmf pe pf c1 c2 xr yr x y q hx hy))
            ((OrR _ _ q) (conn-sym g y x (nr-conn d dd dr e n f ed nd fd er nr fr hd hr bd br fi ge gn gf gnf g pt pmf pe pf c1 c2 yr xr y x q hy hx)))))
        ((OrR _ _ af)
          (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids idd idr bG bGr h hd2 hr2 io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
          (match erased (graph-adj-inv dr xr yr fr gfr pgfr af) _
            ((OrL _ _ q) (spans-conn g gf x y (r-face-conn d dd dr e n f ed nd fd er nr fr hd hr bd br fi gf pt pmf pf uhr xr yr x y q hx hy) sgf))
            ((OrR _ _ q) (conn-sym g y x (spans-conn g gf y x (r-face-conn d dd dr e n f ed nd fd er nr fr hd hr bd br fi gf pt pmf pf uhr yr xr y x q hy hx) sgf)))))))))

(def-fns _ $ (erased r-moves : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br fi idr) (erased (List (Bond)) gr0 ge gn gf gnf g gr ger gnr gfr gnfr)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (HPerm d f fi) pmf) (erased (Graph d e ge) pe) (erased (Graph d f gf) pf)
    (erased (Cat gn gf gnf) c1) (erased (Cat ge gnf g) c2) (erased (Graph dr er ger) pger) (erased (Graph dr nr gnr) pgnr) (erased (Graph dr fr gfr) pgfr)
    (erased (Cat gnr gfr gnfr) cr1) (erased (Cat ger gnfr gr) cr2) (erased (Iota dr idr) ior) (erased (Length (Nat) hr dr) lhr) (erased (Below gr dr) bg)
    (subterm erased (Within gr0 gr) wt) -> (erased (Moves gr0 idr hr g) r))
  (let-match erased wt (WithinCons g1 _ b j pj wt1) ((WithinNil _) (MvNil idr hr g)))
  (let-match erased b (MkBond xr yr))
  (let ((erased a0)) (nth-adj gr j xr yr pj))
  (let ((erased lx)) (below-adj gr dr yr xr (adj-sym gr xr yr a0) bg))
  (let ((erased ly)) (below-adj gr dr xr yr a0 bg))
  (let ((erased x) (erased hx)) (nth-exists _ hr dr xr lhr lx))
  (let ((erased y) (erased hy)) (nth-exists _ hr dr yr lhr ly))
  (MvIn g1 g idr hr xr yr x y (iota-in dr xr idr ior lx) (iota-in dr yr idr ior ly) hx hy
    (r-step-conn d dd dr e n f ed nd fd er nr fr hd hr bd br fi ge gn gf gnf g gr ger gnr gfr gnfr pt pmf pe pf c1 c2 pger pgnr pgfr cr1 cr2 xr yr x y a0 hx hy)
    (r-moves d dd dr e n f ed nd fd er nr fr hd hr bd br fi idr g1 ge gn gf gnf g gr ger gnr gfr gnfr pt pmf pe pf c1 c2 pger pgnr pgfr cr1 cr2 ior lhr bg wt1)))

; No dart of a, the closure of the image of hr, is an image of a disk dart off C, the darts glink-joined to bd.
(def-fns _ $ (erased gl-disj : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br ids labg rsg LHg a ra ld C sdg tg m) (erased (List (Bond)) g gd)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (Iota d ids) io0) (erased (Rooted g rsg ids labg) rog) (erased (Respects labg hr LHg) rlh)
    (erased (SplitBy labg LHg ids a ra) spa) (erased (List (Nat)) idd) (erased (Split C idd C sdg) sfc) (erased (Respects hd sdg tg) rtg) (erased (Sub bd C) sbdc)
    (erased (InvL hd ids ld) ivd) (erased (Moves g tg ld gd) mvb) (erased (Under a d) ua) (subterm erased (Sub m a) sb) -> (erased (Disj m tg) r))
  (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids2 idd2 idr bG bGr h hd2 hr2 io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
  (let-match erased (iota-fn d ids ids2 io0 io) (Refl _ _))
  (let-match erased sb (HSubCons x m1 _ ix sb1) ((HSubNil _) (DisjNil tg)))
  (DisjCons x m1 tg
    (match erased (in-dec x tg) _
      (absurd (OrL _ _ it)
        (let ((erased l) (erased pl) (erased il)) (sb-in-key labg LHg ids a ra x spa ix))
        (let ((erased j) (erased ij) (erased pj)) (respects-in labg hr LHg l rlh il))
        (let ((erased lx)) (under-in a x d ua ix))
        (let ((erased c)) (same-root g d x j l ids labg rsg io rog pl pj lx (under-in hr j d uhr ij)))
        (let ((erased xd) (erased ixd) (erased hxd)) (respects-in hd sdg tg x rtg it))
        (let ((erased j2) (erased pj2) (erased cj) (erased ijt))
          (conn-move g gd tg ld x j xd c mvb it (inv-nth hd ids ld x x xd ivd dhd (iota-nth d x ids io lx) hxd)))
        (let ((erased jd) (erased ijd) (erased hjd)) (respects-in hd sdg tg j rtg ijt))
        (apart-irrefl j (notin-in j j hr (disk-notin-r d jd j hd hr bd ids pp io dhd uhd hjd (notin-sub jd bd C sbdc (split-out C idd C sdg jd sfc ijd))) ij)))
      ((OrR _ _ o) o))
    (gl-disj d dd dr e n f ed nd fd er nr fr hd hr bd br ids labg rsg LHg a ra ld C sdg tg m1 g gd pt io0 rog rlh spa idd sfc rtg sbdc ivd mvb ua sb1)))

; A dart of a off the image of hr is glink-joined to the image of a dart of br.
(def-fns _ $ (erased ring-witness : (erased (Nat) d dd dr x) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br ids idd labgd rsgd LBg a C sdg tg)
    (erased (List (Bond)) ge gn gf gnf g ged gnd gfd gnfd gd) (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (Iota d ids) io0) (erased (Iota dd idd) iod0)
    (erased (Graph d e ge) pe) (erased (Graph d n gn) pn) (erased (Graph d f gf) pf) (erased (Cat gn gf gnf) c1) (erased (Cat ge gnf g) c2)
    (erased (Graph dd ed ged) pde) (erased (Graph dd nd gnd) pdn) (erased (Graph dd fd gfd) pdf) (erased (Cat gnd gfd gnfd) cd1) (erased (Cat ged gnfd gd) cd2)
    (erased (Rooted gd rsgd idd labgd) rogd) (erased (Respects labgd bd LBg) rlbg) (erased (SplitBy labgd LBg idd C sdg) spc) (erased (Split C idd C sdg) sfc)
    (erased (Respects hd sdg tg) rtg) (erased (Disj a tg) dj) (erased (In x a) ia) (erased (NotIn x hr) ox) (erased (Lt x d) lx)
    -> (erased (Nat) r w) (erased (In r br) ir) (erased (Nth (Nat) hr r w) pw) (erased (Conn g x w) c))
  (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids2 idd2 idr bG bGr h hd2 hr2 io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
  (let-match erased (iota-fn d ids ids2 io0 io) (Refl _ _))
  (let-match erased (iota-fn dd idd idd2 iod0 iod) (Refl _ _))
  (let ((erased xd) (erased hxd) (erased oxd)) (disk-of d x hd hr bd ids pp io lx ox))
  (let ((erased lxd)) (nth-lt-length _ hd xd dd x hxd lhd))
  (match erased (in-dec xd C) _
    (absurd (OrR _ _ oxc)
      (apart-irrefl x (notin-in x x tg (disj-notin x a tg dj ia) (in-map hd sdg tg xd x (side-in dd xd C idd C sdg iod sfc lxd oxc) rtg hxd))))
    ((OrL _ _ ixc)
      (let ((erased l2) (erased p2) (erased i2)) (sb-in-key labgd LBg idd C sdg xd spc ixc))
      (let ((erased b) (erased ib) (erased pb)) (respects-in labgd bd LBg l2 rlbg i2))
      (let ((erased cgd)) (same-root gd dd xd b l2 idd labgd rsgd iod rogd p2 pb lxd (under-in bd b dd (respects-under hd bd bG dd rbd lhd) ib)))
      (let-match erased (disk-to-ring d dd dr e n f ed nd fd er nr fr hd hr bd br ge gn gf gnf g ged gnd gfd gnfd gd pt pe pn pf c1 c2 pde pdn pdf cd1 cd2 xd b x cgd ib hxd)
        (MkRingAt _ _ _ _ wd w iw hw cw))
      (let ((erased r) (erased ir) (erased pr)) (respects-in hr br bGr w rbr (revapp-in bG (Nil _) bGr w rv (OrL _ _ (in-map hd bd bG wd w iw rbd hw)))))
      (values r w ir pr cw))))

(def-fns _ $ (erased ring-inv : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br ids idd labgd rsgd LBg a C sdg tg xs)
    (erased (List (Bond)) ge gn gf gnf g ged gnd gfd gnfd gd) (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (Iota d ids) io0) (erased (Iota dd idd) iod0)
    (erased (Graph d e ge) pe) (erased (Graph d n gn) pn) (erased (Graph d f gf) pf) (erased (Cat gn gf gnf) c1) (erased (Cat ge gnf g) c2)
    (erased (Graph dd ed ged) pde) (erased (Graph dd nd gnd) pdn) (erased (Graph dd fd gfd) pdf) (erased (Cat gnd gfd gnfd) cd1) (erased (Cat ged gnfd gd) cd2)
    (erased (Rooted gd rsgd idd labgd) rogd) (erased (Respects labgd bd LBg) rlbg) (erased (SplitBy labgd LBg idd C sdg) spc) (erased (Split C idd C sdg) sfc)
    (erased (Respects hd sdg tg) rtg) (erased (Disj a tg) dj) (subterm erased (Under xs d) u) -> (erased (List (Nat)) ls) (erased (RingInv hr br a g xs ls) r))
  (let-match erased u (UnderCons xs1 x _ lx u1) ((UnderNil _) (values (Nil _) (RvNil hr br a g))))
  (let ((erased ls1) (erased r1)) (ring-inv d dd dr e n f ed nd fd er nr fr hd hr bd br ids idd labgd rsgd LBg a C sdg tg xs1 ge gn gf gnf g ged gnd gfd gnfd gd pt io0 iod0
    pe pn pf c1 c2 pde pdn pdf cd1 cd2 rogd rlbg spc sfc rtg dj u1))
  (match erased (in-dec x hr) _
    ((OrL _ _ ixh) (let ((erased j) (erased pj)) (in-nth x hr ixh)) (values (Cons _ j ls1) (RvHit hr br a xs1 ls1 g x j pj r1)))
    ((OrR _ _ oxh)
      (match erased (in-dec x a) _
        ((OrR _ _ oa) (values (Cons _ (Zero) ls1) (RvOut hr br a xs1 ls1 g x oa r1)))
        ((OrL _ _ ia)
          (let ((erased rr) (erased w) (erased ir) (erased pw) (erased c))
            (ring-witness d dd dr x e n f ed nd fd er nr fr hd hr bd br ids idd labgd rsgd LBg a C sdg tg ge gn gf gnf g ged gnd gfd gnfd gd pt io0 iod0
              pe pn pf c1 c2 pde pdn pdf cd1 cd2 rogd rlbg spc sfc rtg dj ia oxh lx))
          (values (Cons _ rr ls1) (RvRing hr br a xs1 ls1 g x rr w oxh ir pw c r1)))))))

(def-fns _ $ (erased glift-r : (erased (Nat) d dr) (erased (List (Nat)) hr br ids idr labg LHg a ra L m) (erased (List (Bond)) g gr) (erased (RingInv hr br a g ids L) ri)
    (erased (Iota d ids) io) (erased (Length (Nat) labg d) ll) (erased (Distinct hr) dh) (erased (Length (Nat) hr dr) lh) (erased (Under hr d) uhr)
    (erased (Respects labg hr LHg) rlh) (erased (SplitBy labg LHg ids a ra) spa) (erased (Under idr dr) ui) (subterm erased (Sub m idr) sb) -> (erased (Lift gr hr L a m) r))
  (let-match erased sb (HSubCons xr m1 _ ixr sb1) ((HSubNil _) (LiftNil gr hr L a)))
  (let ((erased x) (erased hx)) (nth-exists _ hr dr xr lh (under-in idr xr dr ui ixr)))
  (let ((erased ia)) (outer-mem d x xr hr labg ids LHg a ra io ll uhr rlh spa hx))
  (let ((erased r) (erased pr) (erased ra2)) (ringinv-at hr br a ids L g x x ri (iota-nth d x ids io (under-nth hr xr x d uhr hx)) ia))
  (let-match erased (ring-at-hit hr br g x r xr ra2 dh hx) (Refl _ _))
  (LiftCons gr hr L a m1 xr x xr hx ia pr (ConnHere gr xr) (glift-r d dr hr br ids idr labg LHg a ra L m1 g gr ri io ll dh lh uhr rlh spa ui sb1)))

(def-fns _ $ (erased glift-g : (erased (Nat) d dr) (erased (List (Nat)) hr br ids idr a L m) (erased (List (Bond)) g) (erased (RingInv hr br a g ids L) ri)
    (erased (Iota d ids) io) (erased (Iota dr idr) ior) (erased (Length (Nat) hr dr) lh) (erased (Under br dr) ubr) (erased (Under a d) ua) (subterm erased (Sub m a) sb)
    -> (erased (Lift g L hr idr m) r))
  (let-match erased sb (HSubCons x m1 _ ix sb1) ((HSubNil _) (LiftNil g L hr idr)))
  (let ((erased rest)) (glift-g d dr hr br ids idr a L m1 g ri io ior lh ubr ua sb1))
  (let ((erased r) (erased pr) (erased ra2)) (ringinv-at hr br a ids L g x x ri (iota-nth d x ids io (under-in a x d ua ix)) ix))
  (match erased ra2 _
    ((RAHit _ _ _ _ _ ph) (LiftCons g L hr idr m1 x r x pr (iota-in dr r idr ior (nth-lt-length _ hr r dr x ph lh)) ph (ConnHere g x) rest))
    ((RARing _ _ _ _ _ w ox ir pw c) (LiftCons g L hr idr m1 x r w pr (iota-in dr r idr ior (under-in br r dr ubr ir)) pw c rest))))

; Every dart off a is an image of a disk dart off C.
(def-fns _ $ (erased gl-sub : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br ids idd labg labgd rsgd LBg LHg a ra C sdg tg st m)
    (erased (List (Bond)) ge gn gf gnf g ged gnd gfd gnfd gd) (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (Iota d ids) io0) (erased (Iota dd idd) iod0)
    (erased (Graph d e ge) pe) (erased (Graph d n gn) pn) (erased (Graph d f gf) pf) (erased (Cat gn gf gnf) c1) (erased (Cat ge gnf g) c2)
    (erased (Graph dd ed ged) pde) (erased (Graph dd nd gnd) pdn) (erased (Graph dd fd gfd) pdf) (erased (Cat gnd gfd gnfd) cd1) (erased (Cat ged gnfd gd) cd2)
    (erased (Rooted gd rsgd idd labgd) rogd) (erased (Respects labgd bd LBg) rlbg) (erased (SplitBy labgd LBg idd C sdg) spc) (erased (Split C idd C sdg) sfc)
    (erased (Respects hd sdg tg) rtg) (erased (Const labg g) clg) (erased (Length (Nat) labg d) llg) (erased (Respects labg hr LHg) rlh) (erased (SplitBy labg LHg ids a ra) spa)
    (erased (AppN tg a st) ap) (subterm erased (Sub m ids) sb) -> (erased (Sub m st) r))
  (let-match erased sb (HSubCons x m1 _ ix sb1) ((HSubNil _) (HSubNil st)))
  (let ((erased rest)) (gl-sub d dd dr e n f ed nd fd er nr fr hd hr bd br ids idd labg labgd rsgd LBg LHg a ra C sdg tg st m1 ge gn gf gnf g ged gnd gfd gnfd gd pt io0 iod0
    pe pn pf c1 c2 pde pdn pdf cd1 cd2 rogd rlbg spc sfc rtg clg llg rlh spa ap sb1))
  (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids2 idd2 idr bG bGr h hd2 hr2 io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
  (let-match erased (iota-fn d ids ids2 io0 io) (Refl _ _))
  (let-match erased (iota-fn dd idd idd2 iod0 iod) (Refl _ _))
  (let ((erased lx)) (under-in ids x d (perm-under d ids ids (perm-id d ids io)) ix))
  (let ((erased l) (erased pl)) (nth-exists _ labg d x llg lx))
  (HSubCons x m1 st
    (match erased (in-dec x a) _
      ((OrL _ _ ia) (app-in-r tg a st x ap ia))
      ((OrR _ _ oa)
        (let ((erased ol)) (match erased (in-dec l LHg) (((NotIn l LHg) r))
          (absurd (OrL _ _ il) (apart-irrefl x (notin-in x x a oa (sb-member labg LHg ids a ra x l spa ix pl il))))
          ((OrR _ _ o) o)))
        (match erased (in-dec x hr) _
          (absurd (OrL _ _ ixh)
            (let ((erased j) (erased pj)) (in-nth x hr ixh))
            (apart-irrefl l (notin-in l l LHg ol (in-map labg hr LHg x l ixh rlh pl))))
          ((OrR _ _ oxh)
            (let ((erased xd) (erased hxd) (erased oxd)) (disk-of d x hd hr bd ids pp io lx oxh))
            (let ((erased lxd)) (nth-lt-length _ hd xd dd x hxd lhd))
            (match erased (in-dec xd C) _
              ((OrR _ _ oxc) (app-in-l tg a st x ap (in-map hd sdg tg xd x (side-in dd xd C idd C sdg iod sfc lxd oxc) rtg hxd)))
              (absurd (OrL _ _ ixc)
                (let ((erased l2) (erased p2) (erased i2)) (sb-in-key labgd LBg idd C sdg xd spc ixc))
                (let ((erased b) (erased ib) (erased pb)) (respects-in labgd bd LBg l2 rlbg i2))
                (let ((erased cgd)) (same-root gd dd xd b l2 idd labgd rsgd iod rogd p2 pb lxd (under-in bd b dd (respects-under hd bd bG dd rbd lhd) ib)))
                (let-match erased (disk-to-ring d dd dr e n f ed nd fd er nr fr hd hr bd br ge gn gf gnf g ged gnd gfd gnfd gd pt pe pn pf c1 c2 pde pdn pdf cd1 cd2 xd b x cgd ib hxd)
                  (MkRingAt _ _ _ _ wd w iw hw cw))
                (let ((erased r) (erased ir) (erased pr)) (respects-in hr br bGr w rbr (revapp-in bG (Nil _) bGr w rv (OrL _ _ (in-map hd bd bG wd w iw rbd hw)))))
                (apart-irrefl l (notin-in l l LHg ol (in-map labg hr LHg w l (nth-in hr r w pr) rlh (conn-const labg g x w l cw clg pl))))))))))
    rest))

; C, the disk darts glink-joined to bd, lies in one class if bd is not empty.
(def-fns _ $ (erased co-ring-comp : (erased (Nat) dd eb) (erased (List (Nat)) ed bd idd labgd rsgd LBg C sdg) (erased (List (Bond)) ged gnd gfd gnfd gd)
    (erased (NCyc ed bd) cyd) (erased (Graph dd ed ged) pde) (erased (Cat gnd gfd gnfd) cd1) (erased (Cat ged gnfd gd) cd2) (erased (Iota dd idd) iod)
    (erased (Rooted gd rsgd idd labgd) rogd) (erased (Under bd dd) ubd) (erased (Respects labgd bd LBg) rlbg) (erased (SplitBy labgd LBg idd C sdg) spc)
    (erased (Under C dd) uc) (erased (Sub bd C) sbdc) (erased (NonNil bd eb) nn) -> (erased (ClassesOn gd C eb) r))
  (match erased nn _
    ((NNNil)
      (let-match erased rlbg (RespNil _))
      (MkClassesOn gd C (Nil _) (Zero) (LengthNil _) (HSubNil C) (PrNil gd) (covers-none gd labgd idd C sdg C spc (sub-refl C))))
    ((NNCons b0 bs)
      (let-match erased cyd (NCCons _ _ _ bl fp back))
      (MkClassesOn gd C (Cons _ b0 (Nil _)) (Succ (Zero)) (LengthCons _ b0 (Nil _) (Zero) (LengthNil _))
        (HSubCons b0 (Nil _) C (sub-in bd C b0 sbdc (InHere b0 bs)) (HSubNil C)) (PrCons gd b0 (Nil _) (SANil gd b0) (PrNil gd))
        (covers-trans gd bd (Cons _ b0 (Nil _)) C (label-covers gd dd idd labgd rsgd bd LBg C sdg C iod rogd ubd rlbg spc uc (sub-refl C))
          (covers-spans gd ged (Cons _ b0 (Nil _)) bd (fpath-covers ed bs ged dd b0 b0 bl pde (ConnHere ged b0) fp) (spans-lift-l ged gnfd gd ged (spans-self ged) cd2)))))))

; The glink classes of the whole map, and one more if the ring is not empty, are those of the disk map and of the remainder map (the
; oGdG and oaGr steps of genus_patch).
(def-fns _ $ (erased glink-patch : (erased (Nat) d dd dr kc kcd kcr eb) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br) (erased (List (Bond)) g gd gr)
    (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (Glink d e n f g) gl) (erased (Classes g d kc) cs) (erased (Glink dd ed nd fd gd) gld)
    (erased (Classes gd dd kcd) csd) (erased (Glink dr er nr fr gr) glr) (erased (Classes gr dr kcr) csr) (erased (NonNil bd eb) nn)
    -> (erased (Nat) s) (erased (Add kc eb s) a1) (erased (Add kcd kcr s) a2))
  (let-match erased pt (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids idd idr bG bGr h hd2 hr2 io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pme) (erased pmn) (erased pmf)) (hyper-core d e n f h))
  (let ((erased nfd) (erased ndi) (erased fdi) (erased rnfd) (erased pmed) (erased pmnd) (erased pmfd)) (hyper-core dd ed nd fd hd2))
  (let-match erased gl (MkGlink _ _ _ _ ge gn gf gnf _ pe pn pf c1 c2))
  (let-match erased gld (MkGlink _ _ _ _ ged gnd gfd gnfd _ pde pdn pdf cd1 cd2))
  (let-match erased glr (MkGlink _ _ _ _ ger gnr gfr gnfr _ pger pgnr pgfr cr1 cr2))
  (let ((erased bg)) (classes-below g d kc cs))
  (let ((erased bgd)) (classes-below gd dd kcd csd))
  (let ((erased bgr)) (classes-below gr dr kcr csr))
  (let ((erased cs1)) cs)
  (let ((erased csd1)) csd)
  (let-match erased cs1 (MkClasses _ _ _ ids2 labg rsg io2 llg lrg drg fixg clg rog))
  (let-match erased (iota-fn d ids ids2 io io2) (Refl _ _))
  (let-match erased csd1 (MkClasses _ _ _ idd2 labgd rsgd iod2 lld lrd drd fixd cld rogd))
  (let-match erased (iota-fn dd idd idd2 iod iod2) (Refl _ _))
  (let ((erased uids)) (perm-under d ids ids (perm-id d ids io)))
  (let ((erased uidd)) (perm-under dd idd idd (perm-id dd idd iod)))
  (let ((erased uidr)) (perm-under dr idr idr (perm-id dr idr ior)))
  (let ((erased ubd)) (respects-under hd bd bG dd rbd lhd))
  (let ((erased LBg) (erased rlbg)) (respects-exists labgd bd dd ubd lld))
  (let ((erased C) (erased sdg) (erased spc)) (sb-exists labgd LBg dd lld idd uidd))
  (let ((erased sfc)) (sb-split labgd LBg idd C sdg idd C sdg spc spc (sub-refl C)))
  (let ((erased sC) (erased ssdg)) (split-sub C idd C sdg sfc))
  (let ((erased uC)) (sub-under C idd dd sC uidd))
  (let ((erased usdg)) (sub-under sdg idd dd ssdg uidd))
  (let ((erased shC)) (sb-shut labgd LBg idd C sdg gd dd spc cld bgd iod))
  (let ((erased sbdc)) (sub-label labgd bd LBg idd C sdg bd rlbg spc (under-sub dd bd idd ubd iod) (sub-refl bd)))
  (let ((erased coC)) (co-ring-comp dd eb ed bd idd labgd rsgd LBg C sdg ged gnd gfd gnfd gd cyd pde cd1 cd2 iod rogd ubd rlbg spc uC sbdc nn))
  (let ((erased shs)) (shut-compl dd C idd C sdg gd shC sfc iod bgd))
  (let ((erased ks) (erased coS)) (co-exists gd dd kcd sdg csd shs usdg))
  (let ((erased std) (erased apd)) (app-exists C sdg))
  (let ((erased t) (erased at)) (add-ex eb ks))
  (let ((erased coD)) (co-union gd dd eb ks t C sdg std idd coC coS apd (split-app-sub C idd C sdg std idd sfc apd (sub-refl idd))
    (app-sub C sdg std idd apd (under-sub dd C idd uC iod) ssdg) shC bgd (split-disj C idd C sdg sfc) uC usdg at))
  (let-match erased (co-unique gd idd t kcd coD (co-of-classes gd dd kcd idd csd iod)) (Refl _ _))
  (let ((erased tg) (erased rtg)) (respects-exists hd sdg dd usdg lhd))
  (let ((erased ld) (erased ivd)) (inv-exists hd ids))
  (let ((erased mfd)) (morph-face-d d dd dr e n f ed nd fd er nr fr hd hr bd br fdi idd pt pmfd lhd uidd))
  (let ((erased shcr)) (shut-cat-r C ged gnfd gd cd2 shC))
  (let ((erased mvE1) (erased mvE2)) (perm-moves dd d hd ld ids ed nfd e nf bd C idd C sdg tg ged ge gd g pmed pme pde pe (shut-cat-l C ged gnfd gd cd2 shC) sbdc
    med iod io sfc ivd dhd lhd uhd usdg rtg (spans-lift-l ge gnf g ge (spans-self ge) c2) (spans-lift-l ged gnfd gd ged (spans-self ged) cd2)))
  (let ((erased mvN1) (erased mvN2)) (perm-moves dd d hd ld ids nd ndi n ni (Nil _) C idd C sdg tg gnd gn gd g pmnd pmn pdn pn (shut-cat-l C gnd gfd gnfd cd1 shcr) (HSubNil C)
    mnd iod io sfc ivd dhd lhd uhd usdg rtg (spans-lift-r ge gnf g gn (spans-lift-l gn gf gnf gn (spans-self gn) c1) c2)
    (spans-lift-r ged gnfd gd gnd (spans-lift-l gnd gfd gnfd gnd (spans-self gnd) cd1) cd2)))
  (let ((erased mvF1) (erased mvF2)) (perm-moves dd d hd ld ids fd fdi f fi bd C idd C sdg tg gfd gf gd g pmfd pmf pdf pf (shut-cat-r C gnd gfd gnfd cd1 shcr) sbdc
    mfd iod io sfc ivd dhd lhd uhd usdg rtg (spans-lift-r ge gnf g gf (spans-lift-r gn gf gnf gf (spans-self gf) c1) c2)
    (spans-lift-r ged gnfd gd gfd (spans-lift-r gnd gfd gnfd gfd (spans-self gfd) cd1) cd2)))
  (let ((erased mvA)) (moves-cat ged gnfd gd g sdg hd cd2 mvE1 (moves-cat gnd gfd gnfd g sdg hd cd1 mvN1 mvF1)))
  (let ((erased mvB)) (moves-cat ge gnf g gd tg ld c2 mvE2 (moves-cat gn gf gnf gd tg ld c1 mvN2 mvF2)))
  (let ((erased coT)) (side-co dd d ks kc hd ld ids sdg tg gd g ivd io dhd lhd uhd rtg usdg mvA mvB cs coS))
  (let ((erased LHg) (erased rlh)) (respects-exists labg hr d uhr llg))
  (let ((erased a) (erased ra) (erased spa)) (sb-exists labg LHg d llg ids uids))
  (let ((erased sa)) (sb-split labg LHg ids a ra ids a ra spa spa (sub-refl a)))
  (let ((erased sa1) (erased sra)) (split-sub a ids a ra sa))
  (let ((erased ua)) (sub-under a ids d sa1 uids))
  (let ((erased dj)) (gl-disj d dd dr e n f ed nd fd er nr fr hd hr bd br ids labg rsg LHg a ra ld C sdg tg a g gd pt io rog rlh spa idd sfc rtg sbdc ivd mvB ua (sub-refl a)))
  (let ((erased L) (erased ri)) (ring-inv d dd dr e n f ed nd fd er nr fr hd hr bd br ids idd labgd rsgd LBg a C sdg tg ids ge gn gf gnf g ged gnd gfd gnfd gd pt io iod
    pe pn pf c1 c2 pde pdn pdf cd1 cd2 rogd rlbg spc sfc rtg dj uids))
  (let ((erased coA)) (co-map gr g idr a hr L kcr d kc (co-of-classes gr dr kcr idr csr ior)
    (glift-r d dr hr br ids idr labg LHg a ra L idr g gr ri io llg dhr lhr uhr rlh spa uidr (sub-refl idr))
    (glift-g d dr hr br ids idr a L a g ri io ior lhr (respects-under hr br bGr dr rbr lhr) ua (sub-refl a))
    (r-moves d dd dr e n f ed nd fd er nr fr hd hr bd br fi idr gr ge gn gf gnf g gr ger gnr gfr gnfr pt pmf pe pf c1 c2 pger pgnr pgfr cr1 cr2 ior lhr bgr (within-self gr))
    (g-moves d dd dr e n f ed nd fd er nr fr hd hr bd br ids a ra L labg LHg g ge gn gf gnf g gr ger gnr gfr gnfr pt ri io pe pn pf c1 c2 pger pgnr pgfr cr1 cr2 clg llg spa bg
      (within-self g))
    cs ua))
  (let ((erased st) (erased ap)) (app-exists tg a))
  (let ((erased utg)) (respects-under-vals hd sdg tg d rtg uhd))
  (let ((erased kt) (erased akt)) (add-ex ks kcr))
  (let ((erased coG)) (co-union g d ks kcr kt tg a st ids coT coA ap
    (gl-sub d dd dr e n f ed nd fd er nr fr hd hr bd br ids idd labg labgd rsgd LBg LHg a ra C sdg tg st ids ge gn gf gnf g ged gnd gfd gnfd gd pt io iod
      pe pn pf c1 c2 pde pdn pdf cd1 cd2 rogd rlbg spc sfc rtg clg llg rlh spa ap (sub-refl ids))
    (app-sub tg a st ids ap (under-sub d tg ids utg io) sa1) (moves-shut g gd tg ld mvB) bg dj utg ua akt))
  (let-match erased (co-unique g ids kt kc coG (co-of-classes g d kc ids cs io)) (Refl _ _))
  (let ((erased s) (erased a2)) (add-ex kcd kcr))
  (let ((erased bc) (erased q1) (erased q2)) (add-assoc eb ks kcr kcd s at a2))
  (let-match erased (add-fn ks kcr bc kt q1 akt) (Refl _ _))
  (values s (add-comm eb bc s q2) a2))
