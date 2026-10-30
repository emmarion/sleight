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
