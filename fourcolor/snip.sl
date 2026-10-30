; Cutting a planar map along a ring into a disk map and a remainder map, after snip.v. Load after sew.sl.

; x then the darts p, each on the face of the edge image of the one before, ending at y (Gonthier's path rlink).
(def-adts $ (RPath : ((List (Nat)) e f) ((Nat) x) ((List (Nat)) p) ((Nat) y) -> Type)
  enum
  (many RPNil : (erased (List (Nat)) e f) (erased (Nat) x) -> (RPath e f x (Nil (Nat)) x))
  (many RPCons : (erased (List (Nat)) e f p) (erased (Nat) x ex z y) (erased (Nth (Nat) e x ex) pe) (erased (SomePath f (Nil (Nat)) ex z) w)
      (erased (RPath e f z p y) rest) -> (RPath e f x (Cons (Nat) z p) y)))

; x :: p is a ring: a cycle of rlink on distinct faces (Gonthier's scycle rlink, for a ring that is not empty).
(def-adts $ (Ring : ((List (Nat)) e f) ((Nat) x) ((List (Nat)) p) -> Type)
  enum
  (many MkRing : (erased (List (Nat)) e f p) (erased (Nat) x y ey) (erased (RPath e f x p y) rp) (erased (Nth (Nat) e y ey) pe)
      (erased (SomePath f (Nil (Nat)) ey x) w) (erased (Simple f (Cons (Nat) x p)) s) -> (Ring e f x p)))

; A clink path from x to y leaving from no dart of r (Gonthier's path dlink).
(def-adts $ (DPath : ((List (Nat)) n f r) ((Nat) x y) -> Type)
  enum
  (many DPNil : (erased (List (Nat)) n f r) (erased (Nat) x) -> (DPath n f r x x))
  (many DPNode : (erased (List (Nat)) n f r) (erased (Nat) x y z) (erased (NotIn x r) out) (erased (Nth (Nat) n y x) pn)
      (erased (DPath n f r y z) rest) -> (DPath n f r x z))
  (many DPFace : (erased (List (Nat)) n f r) (erased (Nat) x y z) (erased (NotIn x r) out) (erased (Nth (Nat) f x y) pf)
      (erased (DPath n f r y z) rest) -> (DPath n f r x z)))

; x is in diskN r: a dlink path reaches it from the node preimage of a dart of r.
(def-adts $ (DiskN : ((List (Nat)) n f r) ((Nat) x) -> Type)
  enum
  (many MkDiskN : (erased (List (Nat)) n f r) (erased (Nat) x y y2) (erased (In y r) iy) (erased (Nth (Nat) n y2 y) pn)
      (erased (DPath n f r y2 x) dp) -> (DiskN n f r x)))

(def-fns _ $ (erased dpath-cat : (erased (List (Nat)) n f r) (erased (Nat) x y z) (subterm erased (DPath n f r x y) p) (erased (DPath n f r y z) q)
    -> (erased (DPath n f r x z) res))
  (match erased p _
    ((DPNil _ _ _ _) q)
    ((DPNode _ _ _ _ x1 _ out pn p1) (DPNode n f r x x1 z out pn (dpath-cat n f r x1 y z p1 q)))
    ((DPFace _ _ _ _ x1 _ out pf p1) (DPFace n f r x x1 z out pf (dpath-cat n f r x1 y z p1 q)))))

(def-fns _ $ (erased disk-step : (erased (List (Nat)) n f r) (erased (Nat) x y) (erased (DiskN n f r x) dn) (erased (DPath n f r x y) p)
    -> (erased (DiskN n f r y) res))
  (let-match erased dn (MkDiskN _ _ _ _ z z2 iz pn dp))
  (MkDiskN n f r y z z2 iz pn (dpath-cat n f r z2 x y dp p)))

; diskN is closed under the node preimage.
(def-fns _ $ (erased disk-pre : (erased (List (Nat)) n f r) (erased (Nat) x x2) (erased (DiskN n f r x) dn) (erased (Nth (Nat) n x2 x) pn)
    -> (erased (DiskN n f r x2) res))
  (match erased (in-dec x r) _
    ((OrL _ _ ix) (MkDiskN n f r x2 x x2 ix pn (DPNil n f r x2)))
    ((OrR _ _ ox) (disk-step n f r x x2 dn (DPNode n f r x x2 x2 ox pn (DPNil n f r x2))))))

(def-fns _ $ (erased disk-walk-pre : (erased (Nat) d a b) (erased (List (Nat)) n ni f r s xs) (erased (HPerm d n ni) pn) (subterm erased (Path ni s a b xs) w)
    (erased (DiskN n f r a) dn) -> (erased (DiskN n f r b) res))
  (let-match erased w (PathStep _ _ xs1 _ a1 _ pa _ w1) ((PathHere _ _ _) dn))
  (disk-walk-pre d a1 b n ni f r s xs1 pn w1 (disk-pre n f r a a1 dn (perm-inv d a a1 ni n (perm-sym d n ni pn) pa))))

; diskN is closed under node (diskN_node).
(def-fns _ $ (erased disk-node : (erased (Nat) d x x2) (erased (List (Nat)) n ni f r) (erased (HPerm d n ni) pn) (erased (DiskN n f r x) dn)
    (erased (Nth (Nat) n x x2) px) -> (erased (DiskN n f r x2) res))
  (let ((erased pni)) (perm-sym d n ni pn))
  (let ((erased xs) (erased w)) (cycle d x2 x ni n pni (perm-inv d x x2 n ni pn px) (perm-val d x x2 n ni pn px)))
  (disk-walk-pre d x x2 n ni f r (Nil _) xs pn w dn))

; r lies in diskN.
(def-fns _ $ (erased disk-ring : (erased (Nat) d y) (erased (List (Nat)) n ni f r) (erased (HPerm d n ni) pn) (erased (In y r) iy) (erased (Lt y d) ly)
    -> (erased (DiskN n f r y) res))
  (let ((erased y2) (erased py) (erased l2)) (perm-nth d y ni n (perm-sym d n ni pn) ly))
  (let ((erased pn2)) (perm-inv d y y2 ni n (perm-sym d n ni pn) py))
  (disk-node d y2 y n ni f r pn (MkDiskN n f r y2 y y2 iy pn2 (DPNil n f r y2)) pn2))

; c sends x as a does if x is in t, and as b does otherwise.
(def-adts $ (ChooseAt : ((List (Nat)) t a b) ((Nat) x y) -> Type)
  enum
  (many CAIn : (erased (List (Nat)) t a b) (erased (Nat) x y) (erased (In x t) ix) (erased (Nth (Nat) a x y) pa) -> (ChooseAt t a b x y))
  (many CAOut : (erased (List (Nat)) t a b) (erased (Nat) x y) (erased (NotIn x t) ox) (erased (Nth (Nat) b x y) pb) -> (ChooseAt t a b x y)))

; cs lists, for each dart x of xs, the image of x under a if x is in t, and under b otherwise.
(def-adts $ (Choose : ((List (Nat)) t a b xs cs) -> Type)
  enum
  (many ChNil : (erased (List (Nat)) t a b) -> (Choose t a b (Nil (Nat)) (Nil (Nat))))
  (many ChCons : (erased (List (Nat)) t a b xs cs) (erased (Nat) x y) (erased (ChooseAt t a b x y) ca) (erased (Choose t a b xs cs) rest)
      -> (Choose t a b (Cons (Nat) x xs) (Cons (Nat) y cs))))

(def-fns _ $ (erased choose-exists : (erased (List (Nat)) t a b) (erased (Nat) d) (erased (Length (Nat) a d) la) (erased (Length (Nat) b d) lb)
    (erased (List (Nat)) xs) (subterm erased (Under xs d) u) -> (erased (List (Nat)) cs) (erased (Choose t a b xs cs) r))
  (let-match erased u (UnderCons xs1 x _ lx u1) ((UnderNil _) (values (Nil _) (ChNil t a b))))
  (let ((erased cs1) (erased r1)) (choose-exists t a b d la lb xs1 u1))
  (match erased (in-dec x t) _
    ((OrL _ _ ix)
      (let ((erased y) (erased py)) (nth-exists _ a d x la lx))
      (values (Cons _ y cs1) (ChCons t a b xs1 cs1 x y (CAIn t a b x y ix py) r1)))
    ((OrR _ _ ox)
      (let ((erased y) (erased py)) (nth-exists _ b d x lb lx))
      (values (Cons _ y cs1) (ChCons t a b xs1 cs1 x y (CAOut t a b x y ox py) r1)))))

(def-fns _ $ (erased choose-nth : (erased (List (Nat)) t a b xs cs) (erased (Nat) i x) (subterm erased (Choose t a b xs cs) ch) (erased (Nth (Nat) xs i x) p)
    -> (erased (Nat) y) (erased (Nth (Nat) cs i y) q) (erased (ChooseAt t a b x y) ca))
  (let-match erased ch (ChCons _ _ _ xs1 cs1 x1 y1 ca1 ch1) (absurd (ChNil _ _ _) p))
  (let-match erased p (NthThere _ _ _ i1 _ p1) ((NthHere _ _ _) (values y1 (NthHere _ y1 cs1) ca1)))
  (let ((erased y) (erased q) (erased ca)) (choose-nth t a b xs1 cs1 i1 x ch1 p1))
  (values y (NthThere _ y1 cs1 i1 y q) ca))

; The image of x under cs, for cs chosen over the darts 0..d-1.
(def-fns _ $ (erased choose-get : (erased (List (Nat)) t a b ids cs) (erased (Nat) d x) (erased (Choose t a b ids cs) ch) (erased (Iota d ids) io)
    (erased (Lt x d) lx) -> (erased (Nat) y) (erased (Nth (Nat) cs x y) q) (erased (ChooseAt t a b x y) ca))
  (choose-nth t a b ids cs x x ch (iota-nth d x ids io lx)))

(def-fns _ $ (erased choose-at : (erased (List (Nat)) t a b ids cs) (erased (Nat) d x y) (erased (Choose t a b ids cs) ch) (erased (Iota d ids) io)
    (erased (Lt x d) lx) (erased (Nth (Nat) cs x y) px) -> (erased (ChooseAt t a b x y) r))
  (let ((erased y2) (erased q) (erased ca)) (choose-get t a b ids cs d x ch io lx))
  (let-match erased (nth-fn _ cs x y y2 px q) (Refl _ _))
  ca)

(def-fns _ $ (erased choose-in : (erased (List (Nat)) t a b ids cs) (erased (Nat) d x u) (erased (Choose t a b ids cs) ch) (erased (Iota d ids) io)
    (erased (Length (Nat) a d) la) (erased (In x t) ix) (erased (Nth (Nat) a x u) pa) -> (erased (Nth (Nat) cs x u) r))
  (let ((erased y) (erased q) (erased ca)) (choose-get t a b ids cs d x ch io (nth-lt-length _ a x d u pa la)))
  (let-match erased ca (CAIn _ _ _ _ _ _ pa2) (absurd (CAOut _ _ _ _ _ ox _) (apart-irrefl x (notin-in x x t ox ix))))
  (let-match erased (nth-fn _ a x u y pa pa2) (Refl _ _))
  q)

(def-fns _ $ (erased choose-out : (erased (List (Nat)) t a b ids cs) (erased (Nat) d x u) (erased (Choose t a b ids cs) ch) (erased (Iota d ids) io)
    (erased (Length (Nat) b d) lb) (erased (NotIn x t) ox) (erased (Nth (Nat) b x u) pb) -> (erased (Nth (Nat) cs x u) r))
  (let ((erased y) (erased q) (erased ca)) (choose-get t a b ids cs d x ch io (nth-lt-length _ b x d u pb lb)))
  (let-match erased ca (CAOut _ _ _ _ _ _ pb2) (absurd (CAIn _ _ _ _ _ ix _) (apart-irrefl x (notin-in x x t ox ix))))
  (let-match erased (nth-fn _ b x u y pb pb2) (Refl _ _))
  q)

(def-fns _ $ (erased notin-off1 : (erased (Nat) b) (subterm erased (List (Nat)) xs) (erased (NotIn b xs) o) -> (erased (Off (Cons (Nat) b (Nil (Nat))) xs) r))
  (let-match erased o (NotInCons _ x xs1 ne o1) ((NotInNil _) (OffNil _)))
  (OffCons _ xs1 x (NotInCons x b (Nil _) (apart-sym b x ne) (NotInNil x)) (notin-off1 b xs1 o1)))

; A walk to b, cut where it first reaches b.
(def-fns _ $ (erased walk-to : (erased (List (Nat)) p xs) (erased (Nat) a b) (erased (Path p (Nil (Nat)) a b xs) w)
    -> (erased (List (Nat)) ys) (erased (Path p (Cons (Nat) b (Nil (Nat))) a b ys) r))
  (match erased (in-dec b xs) _
    ((OrL _ _ ib)
      (let ((erased j) (erased l)) (length-exists _ xs))
      (let ((erased ys) (erased j2) (erased r) (erased l2) (erased lt)) (path-upto p (Nil _) xs a b b j w ib l))
      (values ys r))
    ((OrR _ _ ob) (values xs (path-reavoid p (Nil _) (Cons _ b (Nil _)) xs a b w (notin-off1 b xs ob))))))

; A walk through u splits at u.
(def-fns _ $ (erased path-split : (erased (List (Nat)) p s xs) (erased (Nat) x y u) (subterm erased (Path p s x y xs) w) (erased (In u xs) iu)
    -> (erased (List (Nat)) P Q) (erased (Path p s x u P) w1) (erased (Path p s u y (Cons (Nat) u Q)) w2) (erased (AppN P (Cons (Nat) u Q) xs) ap))
  (let-match erased w (PathStep _ _ xs1 _ x1 _ px out w1) (absurd (PathHere _ _ _) iu))
  (let-match erased (nat-eq x u) (Unequal _ _ _ _ nxu) ((Equal _ _ _) (values (Nil _) xs1 (PathHere p s x) w (AppNil _))))
  (let ((erased P1) (erased Q) (erased v1) (erased v2) (erased ap)) (path-split p s xs1 x1 y u w1 (in-tail u x xs1 iu (apart-sym x u nxu))))
  (values (Cons _ x P1) Q (PathStep p s P1 x x1 u px out v1) v2 (AppCons P1 _ xs1 x ap)))

; Every dart a walk leaves has the label of its start, for a labelling constant along p.
(def-fns _ $ (erased path-lab-in : (erased (List (Nat)) p lab s xs) (erased (Nat) x y t l) (subterm erased (Path p s x y xs) w) (erased (Respects lab p lab) rf)
    (erased (Nth (Nat) lab x l) px) (erased (In t xs) it) -> (erased (Nth (Nat) lab t l) r))
  (let-match erased w (PathStep _ _ xs1 _ x1 _ pp _ w1) (absurd (PathHere _ _ _) it))
  (match erased it _
    ((InHere _ _) px)
    ((InThere _ _ _ it1) (path-lab-in p lab s xs1 x1 y t l w1 rf (respects-nth lab p lab x x1 l rf pp px) it1))))

; A face walk leaving from no dart of r is a dlink path.
(def-fns _ $ (erased walk-dpath : (erased (List (Nat)) n f r s xs) (erased (Nat) a b) (subterm erased (Path f s a b xs) w) (erased (Off r xs) o)
    -> (erased (DPath n f r a b) res))
  (let-match erased w (PathStep _ _ xs1 _ a1 _ pf _ w1) ((PathHere _ _ _) (DPNil n f r a)))
  (let-match erased o (OffCons _ _ _ oa o1))
  (DPFace n f r a a1 b oa pf (walk-dpath n f r s xs1 a1 b w1 o1)))

; A walk along b leaving from no dart of t is one along the list chosen from a on t and b off t.
(def-fns _ $ (erased path-choose : (erased (List (Nat)) t a b ids cs s xs) (erased (Nat) d x y) (subterm erased (Path b s x y xs) w) (erased (Off t xs) o)
    (erased (Choose t a b ids cs) ch) (erased (Iota d ids) io) (erased (Length (Nat) b d) lb) -> (erased (Path cs s x y xs) res))
  (let-match erased w (PathStep _ _ xs1 _ x1 _ pb out w1) ((PathHere _ _ _) (PathHere cs s x)))
  (let-match erased o (OffCons _ _ _ ox o1))
  (PathStep cs s xs1 x x1 y (choose-out t a b ids cs d x x1 ch io lb ox pb) out (path-choose t a b ids cs s xs1 d x1 y w1 o1 ch io lb)))

; Walking along a permutation from a to b, one can walk on from b back to a.
(def-fns _ $ (erased walk-back : (erased (Nat) d a b) (erased (List (Nat)) p q s xs) (erased (HPerm d p q) pm) (erased (Path p s a b xs) w) (erased (Lt a d) la)
    -> (erased (SomePath p (Nil (Nat)) b a) r))
  (let ((erased a1) (erased pa) (erased l1)) (perm-nth d a p q pm la))
  (let ((erased cs) (erased cy)) (cycle d a a1 p q pm pa la))
  (match erased (orbit-walk-in d a a1 a b p q cs s xs pm pa cy (InHere a cs) w) _
    ((InHere _ _) (MkSomePath p (Nil _) (Nil _) a a (PathHere p (Nil _) a)))
    ((InThere _ _ _ ic) (path-from p (Nil _) cs a1 a b cy ic))))

(def-fns _ $ (erased cpath-tail : (erased (List (Nat)) n f M) (erased (Nat) y y1 z) (erased (CPath n f y (Cons (Nat) y1 M) z) p) -> (erased (CPath n f y1 M z) r))
  (match erased p _ ((CPNode _ _ _ _ _ _ _ p1) p1) ((CPFace _ _ _ _ _ _ _ p1) p1)))

(def-fns _ $ (erased cpath-restep : (erased (List (Nat)) n f M M2) (erased (Nat) x y a z) (erased (CPath n f x (Cons (Nat) y M) a) p) (erased (CPath n f y M2 z) q)
    -> (erased (CPath n f x (Cons (Nat) y M2) z) r))
  (match erased p _ ((CPNode _ _ _ _ _ _ pn _) (CPNode n f M2 x y z pn q)) ((CPFace _ _ _ _ _ _ pf _) (CPFace n f M2 x y z pf q))))

; A clink path to a, a face step from a to b, and a clink path from b.
(def-fns _ $ (erased cpath-join : (erased (List (Nat)) n f C) (subterm erased (List (Nat)) M) (erased (Nat) x a b z) (erased (CPath n f x M a) p)
    (erased (Nth (Nat) f a b) pf) (erased (CPath n f b C z) q) -> (erased (List (Nat)) M2) (erased (CPath n f x M2 z) res) (erased (AppN M (Cons (Nat) b C) M2) ap))
  (let-match erased M (Cons _ x1 M1) ((Nil _) (let-match erased p (CPNil _ _ _)) (values (Cons _ b C) (CPFace n f C x b z pf q) (AppNil _))))
  (let ((erased M3) (erased r1) (erased ap1)) (cpath-join n f C M1 x1 a b z (cpath-tail n f M1 x x1 a p) pf q))
  (values (Cons _ x1 M3) (cpath-restep n f M1 M3 x x1 a z p r1) (AppCons M1 _ M3 x1 ap1)))

; The part of a duplicate-free clink path after a dart u on it.
(def-fns _ $ (erased cpath-suffix : (erased (List (Nat)) n f) (subterm erased (List (Nat)) M) (erased (Nat) y z u) (erased (CPath n f y M z) p) (erased (In u M) iu)
    (erased (Distinct M) dm) -> (erased (List (Nat)) B) (erased (CPath n f u B z) res) (erased (Sub B M) sb) (erased (Distinct (Cons (Nat) u B)) db))
  (let-match erased M (Cons _ y1 M1) (absurd (Nil _) iu))
  (let ((erased p1)) (cpath-tail n f M1 y y1 z p))
  (let-match erased (nat-eq u y1) (Unequal _ _ _ _ ne) ((Equal _ _ _) (values M1 p1 (sub-cons y1 M1 M1 (sub-refl M1)) dm)))
  (let-match erased dm (DistCons _ _ _ dm1))
  (let ((erased B) (erased r) (erased sb) (erased db)) (cpath-suffix n f M1 y1 z u p1 (in-tail u y1 M1 iu ne) dm1))
  (values B r (sub-trans B M1 (Cons _ y1 M1) sb (sub-cons y1 M1 M1 (sub-refl M1))) db))

; A clink path shortened to one with no dart twice.
(def-fns _ $ (erased cpath-short : (erased (List (Nat)) n f) (subterm erased (List (Nat)) M) (erased (Nat) x z) (erased (CPath n f x M z) p)
    -> (erased (List (Nat)) M2) (erased (CPath n f x M2 z) res) (erased (Distinct (Cons (Nat) x M2)) dm) (erased (Sub M2 M) sb))
  (let-match erased M (Cons _ y M1)
    ((Nil _) (let-match erased p (CPNil _ _ _)) (values (Nil _) p (DistCons x _ (NotInNil x) (DistNil)) (HSubNil _))))
  (let ((erased M3) (erased r1) (erased d1) (erased s1)) (cpath-short n f M1 y z (cpath-tail n f M1 x y z p)))
  (let ((erased s2)) (sub-cons y M3 M1 s1))
  (match erased (in-dec x (Cons _ y M3)) (((List (Nat)) M2) ((CPath n f x M2 z) res) ((Distinct (Cons (Nat) x M2)) dm) ((Sub M2 M) sb))
    ((OrL _ _ ix)
      (match erased ix (((List (Nat)) M2) ((CPath n f x M2 z) res) ((Distinct (Cons (Nat) x M2)) dm) ((Sub M2 M) sb))
        ((InHere _ _) (values M3 r1 d1 s2))
        ((InThere _ _ _ ix1)
          (let-match erased d1 (DistCons _ _ _ d2))
          (let ((erased B) (erased r2) (erased s3) (erased d3)) (cpath-suffix n f M3 y z x r1 ix1 d2))
          (values B r2 d3 (sub-trans B M3 M s3 s2)))))
    ((OrR _ _ ox) (values (Cons _ y M3) (cpath-restep n f M1 M3 x y z z p r1) (DistCons x _ ox d1) (HSubCons y M3 _ (InHere y M1) s2)))))

(def-fns _ $ (erased mem2-app : (erased (List (Nat)) A B AB) (erased (Nat) a b) (subterm erased (AppN A B AB) ap) (erased (Mem2 B a b) m)
    -> (erased (Mem2 AB a b) r))
  (match erased ap _
    ((AppNil _) m)
    ((AppCons A1 _ AB1 c ap1) (M2There AB1 a b c (mem2-app A1 B AB1 a b ap1 m)))))

; A walk along cs, chosen from ni on t and f off t, is a clink path; x :: L is xs followed by y.
(def-fns _ $ (erased path-cpath : (erased (List (Nat)) n ni f fi t ids cs s xs) (erased (Nat) d x y) (erased (HPerm d n ni) pn) (erased (HPerm d f fi) pf)
    (erased (Choose t ni f ids cs) ch) (erased (Iota d ids) io) (erased (Lt x d) lx) (subterm erased (Path cs s x y xs) w)
    -> (erased (List (Nat)) L) (erased (CPath n f x L y) cp) (erased (HSnoc (Nat) xs y (Cons (Nat) x L)) sn))
  (let-match erased w (PathStep _ _ xs1 _ x1 _ pc _ w1) ((PathHere _ _ _) (values (Nil _) (CPNil n f x) (SnocNil _ x))))
  (let ((erased pni)) (perm-sym d n ni pn))
  (match erased (choose-at t ni f ids cs d x x1 ch io lx pc) _
    ((CAIn _ _ _ _ _ _ pa)
      (let ((erased L1) (erased cp1) (erased sn1)) (path-cpath n ni f fi t ids cs s xs1 d x1 y pn pf ch io (perm-val d x x1 ni n pni pa) w1))
      (values (Cons _ x1 L1) (CPNode n f L1 x x1 y (perm-inv d x x1 ni n pni pa) cp1) (SnocCons _ x y xs1 (Cons _ x1 L1) sn1)))
    ((CAOut _ _ _ _ _ _ pb)
      (let ((erased L1) (erased cp1) (erased sn1)) (path-cpath n ni f fi t ids cs s xs1 d x1 y pn pf ch io (perm-val d x x1 f fi pf pb) w1))
      (values (Cons _ x1 L1) (CPFace n f L1 x x1 y pb cp1) (SnocCons _ x y xs1 (Cons _ x1 L1) sn1)))))

(def-fns _ $ (erased snoc-sub : (erased (List (Nat)) R0 R2) (erased (Nat) y) (subterm erased (HSnoc (Nat) R0 y R2) sn) -> (erased (Sub R2 (Cons (Nat) y R0)) r))
  (match erased sn _
    ((SnocNil _ _) (HSubCons y (Nil _) _ (InHere y R0) (HSubNil _)))
    ((SnocCons _ x _ R1 R3 sn1) (HSubCons x R3 _ (InThere x y _ (InHere x R1)) (sub-trans R3 (Cons _ y R1) (Cons _ y R0) (snoc-sub R1 R3 y sn1)
      (HSubCons y R1 _ (InHere y R0) (sub-cons y R1 R0 (sub-cons x R1 R1 (sub-refl R1)))))))))

(def-fns _ $ (erased disj-sub : (erased (List (Nat)) m t) (subterm erased (List (Nat)) s) (erased (Disj s m) dj) (erased (Sub t m) sb) -> (erased (Disj s t) r))
  (let-match erased dj (DisjCons x s1 _ ox dj1) ((DisjNil _) (DisjNil t)))
  (DisjCons x s1 t (notin-sub x t m sb ox) (disj-sub m t s1 dj1 sb)))

; path-cat, with the departing darts appended.
(def-fns _ $ (erased path-app : (erased (List (Nat)) p s ys) (subterm erased (List (Nat)) xs) (erased (Nat) x y z) (erased (Path p s x y xs) w)
    (erased (Path p s y z ys) v) -> (erased (List (Nat)) zs) (erased (Path p s x z zs) r) (erased (AppN xs ys zs) ap))
  (let-match erased w (PathStep _ _ xs1 _ u _ px out w1) ((PathHere _ _ _) (values ys v (AppNil ys))))
  (let ((erased zs1) (erased r1) (erased ap1)) (path-app p s ys xs1 u y z w1 v))
  (values (Cons _ x zs1) (PathStep p s zs1 x u z px out r1) (AppCons xs1 ys zs1 x ap1)))

; ys and z, with c z the start of a walk along c to z, are closed under c.
(def-fns _ $ (erased cyc-step : (erased (List (Nat)) c s ys) (erased (Nat) z z2 t u) (erased (Path c s z2 z ys) cy) (erased (Nth (Nat) c z z2) pz)
    (erased (In t (Cons (Nat) z ys)) it) (erased (Nth (Nat) c t u) pt) -> (erased (In u (Cons (Nat) z ys)) r))
  (match erased it _
    ((InHere _ _) (let-match erased (nth-fn _ c z z2 u pz pt) (Refl _ _)) (path-start-in c s ys z2 z cy))
    ((InThere _ _ _ it1) (path-next c s ys z2 z t u cy it1 pt))))

(def-fns _ $ (erased walk-in-cyc : (erased (List (Nat)) c s s2 ys xs) (erased (Nat) z z2 a b) (erased (Path c s z2 z ys) cy) (erased (Nth (Nat) c z z2) pz)
    (subterm erased (Path c s2 a b xs) w) (erased (In a (Cons (Nat) z ys)) ia) -> (erased (Sub xs (Cons (Nat) z ys)) sb) (erased (In b (Cons (Nat) z ys)) ib))
  (let-match erased w (PathStep _ _ xs1 _ a1 _ pa _ w1) ((PathHere _ _ _) (values (HSubNil _) ia)))
  (let ((erased sb1) (erased ib1)) (walk-in-cyc c s s2 ys xs1 z z2 a1 b cy pz w1 (cyc-step c s ys z z2 a a1 cy pz ia pa)))
  (values (HSubCons a xs1 _ ia sb1) ib1))

(def-fns _ $ (erased rpath-split : (erased (List (Nat)) e f) (subterm erased (List (Nat)) p) (erased (Nat) x w y) (erased (RPath e f x p w) rp) (erased (In y p) iy)
    -> (erased (List (Nat)) A B) (erased (Nat) c ec) (erased (RPath e f x A c) r1) (erased (Nth (Nat) e c ec) pe) (erased (SomePath f (Nil (Nat)) ec y) sp)
       (erased (RPath e f y B w) r2) (erased (AppN A (Cons (Nat) y B) p) ap))
  (let-match erased rp (RPCons _ _ p1 _ ex z _ pe w1 rp1) (absurd (RPNil _ _ _) iy))
  (let-match erased (nat-eq y z) (Unequal _ _ _ _ ne) ((Equal _ _ _) (values (Nil _) p1 x ex (RPNil e f x) pe w1 rp1 (AppNil _))))
  (let ((erased A1) (erased B) (erased c) (erased ec) (erased r1) (erased pe1) (erased sp) (erased r2) (erased ap))
    (rpath-split e f p1 z w y rp1 (in-tail y z p1 iy ne)))
  (values (Cons _ z A1) B c ec (RPCons e f A1 x ex z c pe w1 r1) pe1 sp r2 (AppCons A1 _ p1 z ap)))

(def-fns _ $ (erased rpath-join : (erased (List (Nat)) e f Q) (subterm erased (List (Nat)) P) (erased (Nat) a b eb c d) (erased (RPath e f a P b) r1)
    (erased (Nth (Nat) e b eb) pe) (erased (SomePath f (Nil (Nat)) eb c) sp) (erased (RPath e f c Q d) r2)
    -> (erased (List (Nat)) PQ) (erased (RPath e f a PQ d) r) (erased (AppN P (Cons (Nat) c Q) PQ) ap))
  (let-match erased r1 (RPCons _ _ P1 _ ea z _ pa wa r11) ((RPNil _ _ _) (values (Cons _ c Q) (RPCons e f Q a eb c d pe sp r2) (AppNil _))))
  (let ((erased PQ1) (erased r3) (erased ap1)) (rpath-join e f Q P1 z b eb c d r11 pe sp r2))
  (values (Cons _ z PQ1) (RPCons e f PQ1 a ea z d pa wa r3) (AppCons P1 _ PQ1 z ap1)))

(def-fns _ $ (erased app-mid-notin : (erased (List (Nat)) B p) (subterm erased (List (Nat)) A) (erased (Nat) y) (erased (AppN A (Cons (Nat) y B) p) ap)
    (erased (Distinct p) dp) -> (erased (NotIn y A) oa) (erased (NotIn y B) ob))
  (let-match erased ap (AppCons A1 _ p1 a ap1) ((AppNil _) (let-match erased dp (DistCons _ _ o _)) (values (NotInNil y) o)))
  (let-match erased dp (DistCons _ _ oa1 dp1))
  (let ((erased o1) (erased o2)) (app-mid-notin B p1 A1 y ap1 dp1))
  (values (NotInCons y a A1 (apart-sym a y (notin-in a y p1 oa1 (app-in-r A1 (Cons _ y B) p1 y ap1 (InHere y B)))) o1) o2))

; The ring read from any of its darts y, ending at z, the dart before y.
(def-fns _ $ (erased ring-rot : (erased (List (Nat)) e f p) (erased (Nat) x y) (erased (Ring e f x p) rg) (erased (In y (Cons (Nat) x p)) iy)
    -> (erased (List (Nat)) q) (erased (Nat) z ez) (erased (RPath e f y q z) rq) (erased (Nth (Nat) e z ez) pe) (erased (SomePath f (Nil (Nat)) ez y) sp)
       (erased (NotIn y q) oy) (erased (Sub (Cons (Nat) x p) (Cons (Nat) y q)) s1) (erased (Sub (Cons (Nat) y q) (Cons (Nat) x p)) s2))
  (let-match erased rg (MkRing _ _ _ _ w ew rp pw sw sm))
  (let-match erased sm (MkSimple _ _ lab ls rf rpl dl))
  (let ((erased dr)) (distinct-back lab (Cons _ x p) ls dl rpl))
  (let-match erased dr (DistCons _ _ ox dp))
  (let ((erased sr)) (sub-refl (Cons _ x p)))
  (let-match erased iy (InThere _ _ _ iy1) ((InHere _ _) (values p w ew rp pw sw ox sr sr)))
  (let ((erased A) (erased B) (erased c) (erased ec) (erased r1) (erased pc) (erased spc) (erased r2) (erased ap)) (rpath-split e f p x w y rp iy1))
  (let ((erased q) (erased rq) (erased aq)) (rpath-join e f A B y w ew x c r2 pw sw r1))
  (let ((erased oa) (erased ob)) (app-mid-notin B p A y ap dp))
  (let ((erased oyx)) (NotInCons y x A (apart-sym x y (notin-in x y p ox (app-in-r A (Cons _ y B) p y ap (InHere y B)))) oa))
  (let ((erased sA)) (sub-cons x A A (sub-refl A)))
  (let ((erased sB)) (sub-cons y B B (sub-refl B)))
  (values q c ec rq pc spc (notin-app B (Cons _ x A) q y aq ob oyx)
    (HSubCons x p (Cons _ y q) (InThere x y q (app-in-r B (Cons _ x A) q x aq (InHere x A)))
      (app-sub A (Cons _ y B) p (Cons _ y q) ap (sub-cons y A q (app-sub-r B (Cons _ x A) q A aq sA))
        (HSubCons y B (Cons _ y q) (InHere y q) (sub-cons y B q (app-sub-l B (Cons _ x A) q B aq (sub-refl B))))))
    (HSubCons y q (Cons _ x p) (InThere y x p iy1)
      (app-sub B (Cons _ x A) q (Cons _ x p) aq (sub-cons x B p (app-sub-r A (Cons _ y B) p B ap sB))
        (HSubCons x A (Cons _ x p) (InHere x p) (sub-cons x A p (app-sub-l A (Cons _ y B) p A ap (sub-refl A))))))))

; Every dart of xs is a or has the label of a dart of q.
(def-adts $ (OnRing : ((List (Nat)) lab q) ((Nat) a) ((List (Nat)) xs) -> Type)
  enum
  (many ORNil : (erased (List (Nat)) lab q) (erased (Nat) a) -> (OnRing lab q a (Nil (Nat))))
  (many ORHead : (erased (List (Nat)) lab q xs) (erased (Nat) a) (erased (OnRing lab q a xs) rest) -> (OnRing lab q a (Cons (Nat) a xs)))
  (many ORLab : (erased (List (Nat)) lab q xs) (erased (Nat) a x k l) (erased (In k q) ik) (erased (Nth (Nat) lab k l) pk) (erased (Nth (Nat) lab x l) px)
      (erased (OnRing lab q a xs) rest) -> (OnRing lab q a (Cons (Nat) x xs))))

(def-fns _ $ (erased onring-app : (erased (List (Nat)) lab q Y Z) (subterm erased (List (Nat)) X) (erased (Nat) a) (erased (AppN X Y Z) ap)
    (erased (OnRing lab q a X) ox) (erased (OnRing lab q a Y) oy) -> (erased (OnRing lab q a Z) r))
  (let-match erased ap (AppCons X1 _ Z1 x ap1) ((AppNil _) oy))
  (match erased ox _
    ((ORHead _ _ _ _ ox1) (ORHead lab q Z1 a (onring-app lab q Y Z1 X1 a ap1 ox1 oy)))
    ((ORLab _ _ _ _ _ k l ik pk px ox1) (ORLab lab q Z1 a x k l ik pk px (onring-app lab q Y Z1 X1 a ap1 ox1 oy)))))

(def-fns _ $ (erased onring-lift : (erased (List (Nat)) lab q) (subterm erased (List (Nat)) xs) (erased (Nat) a b la) (erased (OnRing lab q a xs) o)
    (erased (Nth (Nat) lab a la) pa) -> (erased (OnRing lab (Cons (Nat) a q) b xs) r))
  (match erased o _
    ((ORNil _ _ _) (ORNil lab _ b))
    ((ORHead _ _ xs1 _ o1) (ORLab lab _ xs1 b a a la (InHere a q) pa pa (onring-lift lab q xs1 a b la o1 pa)))
    ((ORLab _ _ xs1 _ x k l ik pk px o1) (ORLab lab _ xs1 b x k l (InThere k a q ik) pk px (onring-lift lab q xs1 a b la o1 pa)))))

(def-fns _ $ (erased onring-walk : (erased (List (Nat)) p lab s q xs) (erased (Nat) x y a k l) (subterm erased (Path p s x y xs) w) (erased (Respects lab p lab) rf)
    (erased (Nth (Nat) lab x l) px) (erased (In k q) ik) (erased (Nth (Nat) lab k l) pk) -> (erased (OnRing lab q a xs) r))
  (let-match erased w (PathStep _ _ xs1 _ x1 _ pp _ w1) ((PathHere _ _ _) (ORNil lab q a)))
  (ORLab lab q xs1 a x k l ik pk px (onring-walk p lab s q xs1 x1 y a k l w1 rf (respects-nth lab p lab x x1 l rf pp px) ik pk)))

; From a walk along a permutation f from b to z, one from f b to z.
(def-fns _ $ (erased walk-next : (erased (Nat) d b b2 z) (erased (List (Nat)) f fi s xs) (erased (HPerm d f fi) pf) (erased (Path f s b z xs) w)
    (erased (Nth (Nat) f b b2) pb) (erased (Lt b d) lb) -> (erased (SomePath f (Nil (Nat)) b2 z) r))
  (let-match erased w (PathStep _ _ xs1 _ b3 _ pb3 _ w1)
    ((PathHere _ _ _) (let ((erased cs) (erased cy)) (cycle d b b2 f fi pf pb lb)) (MkSomePath f (Nil _) cs b2 b cy)))
  (let-match erased (nth-fn _ f b b2 b3 pb pb3) (Refl _ _))
  (MkSomePath f (Nil _) xs1 b2 z (path-forget f s xs1 b2 z w1)))

; The darts of a ring path from a to b, each followed by the face walk to the next one, as a walk along cs from a to b; it
; leaves from a and from darts on the faces of the darts of q, and it reaches every dart of q.
(def-fns _ $ (erased ring-walk : (erased (Nat) d a b) (erased (List (Nat)) e n ni f fi r ids cs lab ls) (subterm erased (List (Nat)) q)
    (erased (Hypermap d e n f) h) (erased (HPerm d n ni) pn) (erased (HPerm d f fi) pf) (erased (Choose r ni f ids cs) ch) (erased (Iota d ids) io)
    (erased (Respects lab f lab) rf) (erased (Respects lab r ls) rl) (erased (Distinct ls) dl) (erased (RPath e f a q b) rp)
    (erased (In a r) ia) (erased (Sub q r) sq)
    -> (erased (List (Nat)) xs) (erased (Path cs (Nil (Nat)) a b xs) w) (erased (OnRing lab q a xs) orr) (erased (Sub q (Cons (Nat) b xs)) cov))
  (let-match erased rp (RPCons _ _ q1 _ ea z _ pe sp rp1) ((RPNil _ _ _) (values (Nil _) (PathHere cs (Nil _) a) (ORNil lab q a) (HSubNil _))))
  (let-match erased sq (HSubCons _ _ _ iz sq1))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased nf) (erased pme)) (hyper-perm d e n f h))
  (let ((erased lea)) (perm-val d a ea e nf pme pe))
  (let ((erased a2) (erased pa2) (erased la2)) (perm-nth d ea f fi pf lea))
  (let ((erased pn2)) (hyper-node d a2 ea a e n f h pa2 pe))
  (let ((erased pc)) (choose-in r ni f ids cs d a a2 ch io (perm-length d ni n (perm-sym d n ni pn)) ia (perm-inv d a2 a n ni pn pn2)))
  (let-match erased sp (MkSomePath _ _ ws _ _ w0))
  (let-match erased (walk-next d ea a2 z f fi (Nil _) ws pf w0 pa2 lea) (MkSomePath _ _ ws2 _ _ w2))
  (let ((erased W) (erased w3)) (walk-to f ws2 a2 z w2))
  (let ((erased ll)) (respects-length lab f lab d rf lf))
  (let ((erased l) (erased pl)) (nth-exists _ lab d a2 ll la2))
  (let ((erased plz)) (path-label f lab (Cons _ z (Nil _)) W a2 z l w3 rf pl))
  (let ((erased w4)) (path-choose r ni f ids cs (Cons _ z (Nil _)) W d a2 z w3 (path-off-simple f lab r ls W a2 z l w3 rf rl dl iz pl plz) ch io lf))
  (let ((erased xs1) (erased w5) (erased or1) (erased cov1)) (ring-walk d z b e n ni f fi r ids cs lab ls q1 h pn pf ch io rf rl dl rp1 iz sq1))
  (let ((erased zs) (erased w6) (erased ap))
    (path-app cs (Nil _) xs1 (Cons _ a W) a z b (PathStep cs (Nil _) W a a2 z pc (NotInNil a) (path-forget cs _ W a2 z w4)) w5))
  (let ((erased sb)) (HSubCons b xs1 (Cons _ b zs) (InHere b zs) (sub-cons b xs1 zs (app-sub-r (Cons _ a W) xs1 zs xs1 ap (sub-refl xs1)))))
  (values zs w6
    (onring-app lab (Cons _ z q1) xs1 zs (Cons _ a W) a ap
      (ORHead lab _ W a (onring-walk f lab (Cons _ z (Nil _)) (Cons _ z q1) W a2 z a z l w3 rf pl (InHere z q1) plz))
      (onring-lift lab q1 xs1 z a l or1 plz))
    (HSubCons z q1 (Cons _ b zs) (sub-in (Cons _ b xs1) (Cons _ b zs) z sb (path-start-in cs (Nil _) xs1 z b w5)) (sub-trans q1 (Cons _ b xs1) (Cons _ b zs) cov1 sb))))

(def-fns _ $ (erased resp-lt : (erased (List (Nat)) lab xs ls) (erased (Nat) y d) (subterm erased (Respects lab xs ls) rp) (erased (In y xs) iy)
    (erased (Length (Nat) lab d) ll) -> (erased (Lt y d) r))
  (let-match erased rp (RespCons _ xs1 ls1 j l pj rp1) (absurd (RespNil _) iy))
  (match erased iy _ ((InHere _ _) (nth-lt-length _ lab j d l pj ll)) ((InThere _ _ _ iy1) (resp-lt lab xs1 ls1 y d rp1 iy1 ll))))

(def-fns _ $ (erased rpath-last : (erased (List (Nat)) e f) (subterm erased (List (Nat)) q) (erased (Nat) a b) (erased (RPath e f a q b) rp)
    -> (erased (In b (Cons (Nat) a q)) r))
  (let-match erased rp (RPCons _ _ q1 _ ea z _ pe sp rp1) ((RPNil _ _ _) (InHere a (Nil _))))
  (InThere b a q (rpath-last e f q1 z b rp1)))

(def-fns _ $ (erased walk-lab : (erased (List (Nat)) p lab s xs) (erased (Nat) x y t l) (erased (Path p s x y xs) w) (erased (Respects lab p lab) rf)
    (erased (Nth (Nat) lab x l) px) (erased (In t (Cons (Nat) y xs)) it) -> (erased (Nth (Nat) lab t l) r))
  (match erased it _
    ((InHere _ _) (path-label p lab s xs x y l w rf px))
    ((InThere _ _ _ it1) (path-lab-in p lab s xs x y t l w rf px it1))))

(def-fns _ $ (erased disj-nil : (subterm erased (List (Nat)) s) -> (erased (Disj s (Nil (Nat))) r))
  (let-match erased s (Cons _ x s1) ((Nil _) (DisjNil _)))
  (DisjCons x s1 _ (NotInNil x) (disj-nil s1)))

(def-fns _ $ (erased disj-cons-r : (erased (List (Nat)) m) (erased (Nat) y) (subterm erased (List (Nat)) s) (erased (Disj s m) dj) (erased (NotIn y s) oy)
    -> (erased (Disj s (Cons (Nat) y m)) r))
  (let-match erased dj (DisjCons x s1 _ ox dj1) ((DisjNil _) (DisjNil _)))
  (let-match erased oy (NotInCons _ _ _ ne oy1))
  (DisjCons x s1 _ (NotInCons x y m (apart-sym y x ne) ox) (disj-cons-r m y s1 dj1 oy1)))

(def-fns _ $ (erased disj-at : (erased (List (Nat)) m) (erased (Nat) x) (subterm erased (List (Nat)) s) (erased (Disj s m) dj) (erased (In x s) ix)
    -> (erased (NotIn x m) r))
  (let-match erased dj (DisjCons y s1 _ oy dj1) (absurd (DisjNil _) ix))
  (match erased ix _ ((InHere _ _) oy) ((InThere _ _ _ ix1) (disj-at m x s1 dj1 ix1))))

(def-fns _ $ (erased app-disj : (erased (List (Nat)) B C) (subterm erased (List (Nat)) A) (erased (AppN A B C) ap) (erased (Distinct C) dc) -> (erased (Disj A B) r))
  (let-match erased ap (AppCons A1 _ C1 a ap1) ((AppNil _) (DisjNil B)))
  (let-match erased dc (DistCons _ _ oa dc1))
  (DisjCons a A1 B (notin-sub a B C1 (app-sub-r A1 B C1 B ap1 (sub-refl B)) oa) (app-disj B C1 A1 ap1 dc1)))

; A walk to y that never leaves y, split at a dart u on it or at y.
(def-fns _ $ (erased wsplit : (erased (List (Nat)) p xs) (erased (Nat) x y u) (erased (Path p (Cons (Nat) y (Nil (Nat))) x y xs) w)
    (erased (In u (Cons (Nat) y xs)) iu)
    -> (erased (List (Nat)) P Q) (erased (Path p (Cons (Nat) y (Nil (Nat))) x u P) w1) (erased (Path p (Cons (Nat) y (Nil (Nat))) u y Q) w2)
       (erased (Disj P (Cons (Nat) y Q)) dj) (erased (In u (Cons (Nat) y Q)) iq) (erased (Sub P xs) sp) (erased (Sub Q xs) sq))
  (let ((erased oy)) (path-avoid p _ xs x y y w (InHere y (Nil _))))
  (let-match erased iu (InThere _ _ _ iu1)
    ((InHere _ _) (values xs (Nil _) w (PathHere p _ y) (disj-cons-r (Nil _) y xs (disj-nil xs) oy) (InHere y (Nil _)) (sub-refl xs) (HSubNil xs))))
  (let ((erased P) (erased Q1) (erased w1) (erased w2) (erased ap)) (path-split p _ xs x y u w iu1))
  (let ((erased sP)) (app-sub-l P (Cons _ u Q1) xs P ap (sub-refl P)))
  (values P (Cons _ u Q1) w1 w2
    (disj-cons-r (Cons _ u Q1) y P (app-disj (Cons _ u Q1) xs P ap (walk-distinct p (Nil _) xs x y w)) (notin-sub y P xs sP oy))
    (InThere u y _ (InHere u Q1)) sP (app-sub-r P (Cons _ u Q1) xs (Cons _ u Q1) ap (sub-refl (Cons _ u Q1)))))

; A face walk on the face of the dart y of a simple list r, never leaving from y, leaves from no dart of r.
(def-fns _ $ (erased walk-off : (erased (List (Nat)) f lab r ls s Q) (erased (Nat) a b y l) (subterm erased (Path f s a b Q) w) (erased (Respects lab f lab) rf)
    (erased (Nth (Nat) lab a l) pa) (erased (Respects lab r ls) rl) (erased (Distinct ls) dl) (erased (In y r) iy) (erased (Nth (Nat) lab y l) py)
    (erased (NotIn y Q) oy) -> (erased (Off r Q) res))
  (let-match erased w (PathStep _ _ Q1 _ a1 _ pp _ w1) ((PathHere _ _ _) (OffNil r)))
  (let-match erased oy (NotInCons _ _ _ ne oy1))
  (OffCons r Q1 a
    (match erased (in-dec a r) _
      (absurd (OrL _ _ ia) (let-match erased (simple-inj lab r ls a y l rl dl ia iy pa py) (Refl _ _)) (apart-irrefl a ne))
      ((OrR _ _ oa) oa))
    (walk-off f lab r ls s Q1 a1 b y l w1 rf (respects-nth lab f lab a a1 l rf pp pa) rl dl iy py oy1)))

(def-fns _ $ (erased absurd onring-off : (erased (List (Nat)) lab r ls q) (subterm erased (List (Nat)) X) (erased (Nat) t y l) (erased (In t X) it)
    (erased (OnRing lab q y X) orr) (erased (Nth (Nat) lab t l) pt) (erased (Nth (Nat) lab y l) py) (erased (Apart (Nat) Lt t y) ne)
    (erased (Respects lab r ls) rl) (erased (Distinct ls) dl) (erased (In y r) iy) (erased (Sub q r) sq) (erased (NotIn y q) oyq) -> (erased (False) fl))
  (match erased orr _
    (absurd (ORNil _ _ _) it)
    (absurd (ORHead _ _ X1 _ or1)
      (match erased it _
        (absurd (InHere _ _) (apart-irrefl t ne))
        (absurd (InThere _ _ _ it1) (onring-off lab r ls q X1 t y l it1 or1 pt py ne rl dl iy sq oyq))))
    (absurd (ORLab _ _ X1 _ x k lk ik pk px or1)
      (match erased it _
        (absurd (InHere _ _)
          (let-match erased (nth-fn _ lab t l lk pt px) (Refl _ _))
          (let-match erased (simple-inj lab r ls k y l rl dl (sub-in q r k sq ik) iy pk py) (Refl _ _))
          (apart-irrefl k (notin-in k k q oyq ik)))
        (absurd (InThere _ _ _ it1) (onring-off lab r ls q X1 t y l it1 or1 pt py ne rl dl iy sq oyq))))))

; A dart t on the face of y, off Q and other than y, is not on z :: D, D the arc A, part of Q, followed by the walk X around the
; ring from y to z.
(def-fns _ $ (erased absurd off-contour : (erased (List (Nat)) lab r ls q A X D Q) (erased (Nat) t y z l) (erased (In t (Cons (Nat) z D)) it)
    (erased (AppN A X D) ap) (erased (Sub A Q) sa) (erased (NotIn t Q) oq) (erased (Nth (Nat) lab t l) pt) (erased (Nth (Nat) lab y l) py)
    (erased (Apart (Nat) Lt t y) ne) (erased (OnRing lab q y X) orr) (erased (Respects lab r ls) rl) (erased (Distinct ls) dl) (erased (In y r) iy)
    (erased (In z r) iz) (erased (Sub q r) sq) (erased (NotIn y q) oyq) -> (erased (False) fl))
  (match erased it _
    (absurd (InHere _ _) (let-match erased (simple-inj lab r ls t y l rl dl iz iy pt py) (Refl _ _)) (apart-irrefl t ne))
    (absurd (InThere _ _ _ it1)
      (match erased (app-in-inv A X D t ap it1) _
        (absurd (OrL _ _ ia) (apart-irrefl t (notin-in t t Q oq (sub-in A Q t sa ia))))
        (absurd (OrR _ _ ix) (onring-off lab r ls q X t y l ix orr pt py ne rl dl iy sq oyq))))))

; xs avoids r, or meets it at y.
(def-adts $ (Meet : ((List (Nat)) r xs) -> Type)
  enum
  (many MeetNone : (erased (List (Nat)) r xs) (erased (Off r xs) o) -> (Meet r xs))
  (many MeetAt : (erased (List (Nat)) r xs) (erased (Nat) y) (erased (In y xs) iy) (erased (In y r) ir) -> (Meet r xs)))

(def-fns _ $ (erased meet-dec : (erased (List (Nat)) r) (subterm erased (List (Nat)) xs) -> (erased (Meet r xs) m))
  (let-match erased xs (Cons _ x xs1) ((Nil _) (MeetNone r (Nil _) (OffNil r))))
  (match erased (in-dec x r) _
    ((OrL _ _ ix) (MeetAt r xs x (InHere x xs1) ix))
    ((OrR _ _ ox)
      (match erased (meet-dec r xs1) _
        ((MeetNone _ _ o) (MeetNone r xs (OffCons r xs1 x ox o)))
        ((MeetAt _ _ y iy ir) (MeetAt r xs y (InThere y x xs1 iy) ir))))))

; The end of a dlink path from u to b, off S: the whole path avoids S, or a node step from x1 to v in S is followed by a clink path
; from x1 to b that avoids S.
(def-adts $ (Exit : ((List (Nat)) n f S) ((Nat) u b) -> Type)
  enum
  (many ExAvoid : (erased (List (Nat)) n f S M) (erased (Nat) u b) (erased (CPath n f u M b) cp) (erased (Disj (Cons (Nat) u M) S) dj)
      -> (Exit n f S u b))
  (many ExOut : (erased (List (Nat)) n f S M) (erased (Nat) u b x1 v) (erased (Nth (Nat) n x1 v) pv) (erased (In v S) iv) (erased (CPath n f x1 M b) cp)
      (erased (Disj (Cons (Nat) x1 M) S) dj) -> (Exit n f S u b)))

; S = z :: ys, the darts of a walk along cs from cs z to z, with cs chosen from ni on r and f off r.
(def-fns _ $ (erased exit-go : (erased (Nat) d z z2 u b) (erased (List (Nat)) n ni f r ids cs s ys) (erased (Choose r ni f ids cs) ch) (erased (Iota d ids) io)
    (erased (Length (Nat) f d) lf) (erased (Path cs s z2 z ys) cy) (erased (Nth (Nat) cs z z2) pz) (subterm erased (DPath n f r u b) dp)
    (erased (NotIn b (Cons (Nat) z ys)) ob) -> (erased (Exit n f (Cons (Nat) z ys) u b) res))
  (match erased dp _
    ((DPNil _ _ _ _) (ExAvoid n f _ (Nil _) u u (CPNil n f u) (DisjCons u (Nil _) _ ob (DisjNil _))))
    ((DPNode _ _ _ _ u2 _ out pn dp1)
      (match erased (exit-go d z z2 u2 b n ni f r ids cs s ys ch io lf cy pz dp1 ob) _
        ((ExAvoid _ _ _ M _ _ cp dj)
          (match erased (in-dec u (Cons _ z ys)) _
            ((OrL _ _ iu) (ExOut n f _ M u b u2 u pn iu cp dj))
            ((OrR _ _ ou) (ExAvoid n f _ (Cons _ u2 M) u b (CPNode n f M u u2 b pn cp) (DisjCons u _ _ ou dj)))))
        ((ExOut _ _ _ M _ _ x1 v pv iv cp dj) (ExOut n f _ M u b x1 v pv iv cp dj))))
    ((DPFace _ _ _ _ u2 _ out pf dp1)
      (match erased (exit-go d z z2 u2 b n ni f r ids cs s ys ch io lf cy pz dp1 ob) _
        ((ExAvoid _ _ _ M _ _ cp dj)
          (match erased (in-dec u (Cons _ z ys)) _
            (absurd (OrL _ _ iu)
              (let-match erased dj (DisjCons _ _ _ o2 _))
              (apart-irrefl u2 (notin-in u2 u2 _ o2 (cyc-step cs s ys z z2 u u2 cy pz iu (choose-out r ni f ids cs d u u2 ch io lf out pf)))))
            ((OrR _ _ ou) (ExAvoid n f _ (Cons _ u2 M) u b (CPFace n f M u u2 b pf cp) (DisjCons u _ _ ou dj)))))
        ((ExOut _ _ _ M _ _ x1 v pv iv cp dj) (ExOut n f _ M u b x1 v pv iv cp dj))))))

(def-fns _ $ (erased exit : (erased (Nat) d z z2 a b) (erased (List (Nat)) n ni f r ids cs s ys) (erased (Choose r ni f ids cs) ch) (erased (Iota d ids) io)
    (erased (Length (Nat) f d) lf) (erased (Path cs s z2 z ys) cy) (erased (Nth (Nat) cs z z2) pz) (erased (DPath n f r a b) dp)
    (erased (In a (Cons (Nat) z ys)) ia) (erased (NotIn b (Cons (Nat) z ys)) ob)
    -> (erased (Nat) x1 v) (erased (List (Nat)) M) (erased (Nth (Nat) n x1 v) pv) (erased (In v (Cons (Nat) z ys)) iv) (erased (CPath n f x1 M b) cp)
       (erased (Disj (Cons (Nat) x1 M) (Cons (Nat) z ys)) dj))
  (match erased (exit-go d z z2 a b n ni f r ids cs s ys ch io lf cy pz dp ob) _
    (absurd (ExAvoid _ _ _ M _ _ cp dj) (let-match erased dj (DisjCons _ _ _ oa _)) (apart-irrefl a (notin-in a a _ oa ia)))
    ((ExOut _ _ _ M _ _ x1 v pv iv cp dj) (values x1 v M pv iv cp dj))))
