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

; diskE_edge: in a planar map, the edge image of a dart of diskN off r is in diskN off r. Off the trivial case, a dart y of r on
; the face of e x would make a Moebius path: x is reached from the ring, and its face walk to e x crosses the contour of the
; disk, which runs from z2, after the dart z before y, along the face to y and around the ring to z.
(def-fns _ $ (erased disk-edge : (erased (Nat) d x ex x0) (erased (List (Nat)) e n f p) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) g)
    (erased (Ring e f x0 p) rg) (erased (DiskN n f (Cons (Nat) x0 p) x) dn) (erased (NotIn x (Cons (Nat) x0 p)) ox) (erased (Nth (Nat) e x ex) pex)
    -> (erased (DiskN n f (Cons (Nat) x0 p) ex) dex) (erased (NotIn ex (Cons (Nat) x0 p)) oex))
  (let ((erased r)) (Cons _ x0 p))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased pni)) (perm-sym d n ni pn))
  (let ((erased lni)) (perm-length d ni n pni))
  (let ((erased rg2)) rg)
  (let-match erased rg2 (MkRing _ _ _ _ w ew rp pw sw sm))
  (let-match erased sm (MkSimple _ _ lab ls rf rl dl))
  (let ((erased ll)) (respects-length lab f lab d rf lf))
  (let ((erased ids) (erased io)) (iota-exists d))
  (let ((erased cs) (erased ch)) (choose-exists r ni f d lni lf ids (perm-under d ids ids (perm-id d ids io))))
  (let ((erased lx)) (nth-lt-length _ e x d ex pex le))
  (let ((erased lex)) (perm-val d x ex e nf pe pex))
  (let ((erased x2) (erased px2) (erased lx2)) (perm-nth d x ni n pni lx))
  (let ((erased pnx)) (perm-inv d x x2 ni n pni px2))
  (let ((erased pfx)) (hyper-third d ex x x2 e n f h pex pnx))
  (let ((erased ws) (erased w0)) (cycle d ex x2 f fi pf pfx lex))
  (let ((erased xs) (erased wx)) (walk-to f ws x2 ex w0))
  (let ((erased lF) (erased plx2)) (nth-exists _ lab d x2 ll lx2))
  (let-match erased dn (MkDiskN _ _ _ _ y0 y1 iy0 pny0 dp0))
  (let-match erased (meet-dec r (Cons _ ex xs)) (MeetAt _ _ y iy iry)
    ((MeetNone _ _ o)
      (let-match erased o (OffCons _ _ _ oex o1))
      (values (disk-step n f r x ex dn (DPNode n f r x x2 ex ox pnx (walk-dpath n f r _ xs x2 ex wx o1))) oex)))
  (let ((erased ply)) (walk-lab f lab _ xs x2 ex y lF wx rf plx2 iy))
  (let ((erased q) (erased z) (erased ez) (erased rq) (erased pez) (erased spz) (erased oyq) (erased s1) (erased s2)) (ring-rot e f p x0 y rg iry))
  (let-match erased s2 (HSubCons _ _ _ iyr sq))
  (let ((erased iz)) (sub-in (Cons _ y q) r z s2 (rpath-last e f q y z rq)))
  (let ((erased lz)) (resp-lt lab r ls z d rl iz ll))
  (let ((erased z2) (erased pz2) (erased lz2)) (perm-nth d z ni n pni lz))
  (let ((erased pnz)) (perm-inv d z z2 ni n pni pz2))
  (let ((erased pfz)) (hyper-third d ez z z2 e n f h pez pnz))
  (let ((erased lez)) (perm-val d z ez e nf pe pez))
  (let-match erased spz (MkSomePath _ _ wsz _ _ wz))
  (let-match erased (walk-back d ez y f fi (Nil _) wsz pf wz lez) (MkSomePath _ _ wyz _ _ wy))
  (let ((erased ys2) (erased sn2) (erased wy2)) (path-snoc f (Nil _) wyz y ez z2 wy pfz (NotInNil ez)))
  (let ((erased sb0) (erased iz2)) (walk-in-cyc f (Cons _ ex (Nil _)) (Nil _) xs ys2 ex x2 y z2 wx pfx wy2 iy))
  (let-match erased (nat-eq z2 x2) (Unequal _ _ _ _ nzx)
    (absurd (Equal _ _ _) (let-match erased (nth-fn _ n x2 z x pnz pnx) (Refl _ _)) (apart-irrefl x (notin-in x x r ox iz))))
  (let ((erased plz2)) (walk-lab f lab _ xs x2 ex z2 lF wx rf plx2 iz2))
  (let ((erased P) (erased Q) (erased wP) (erased wQ) (erased djP) (erased iqz) (erased sP) (erased sQ)) (wsplit f xs x2 ex z2 wx iz2))
  (match erased (in-dec y (Cons _ ex Q)) _
    ((OrR _ _ oyQ)
      (let-match erased oyQ (NotInCons _ _ _ ney oyQ1))
      (values (MkDiskN n f r ex z z2 iz pnz (walk-dpath n f r _ Q z2 ex wQ (walk-off f lab r ls _ Q z2 ex y lF wQ rf plz2 rl dl iry ply oyQ1)))
        (match erased (in-dec ex r) _
          (absurd (OrL _ _ iex)
            (let-match erased (simple-inj lab r ls ex y lF rl dl iex iry (walk-lab f lab _ xs x2 ex ex lF wx rf plx2 (InHere ex xs)) ply) (Refl _ _))
            (apart-irrefl y ney))
          ((OrR _ _ o) o))))
    (absurd (OrL _ _ iyQ)
      (let ((erased yP)) (notin-of-disj y P (Cons _ ex Q) djP iyQ))
      (let ((erased A) (erased Q2) (erased wA) (erased wQ2) (erased djA) (erased iyA) (erased sA) (erased sQ2)) (wsplit f Q z2 ex y wQ iyQ))
      (let ((erased wAc)) (path-forget cs _ A z2 y (path-choose r ni f ids cs _ A d z2 y wA
        (walk-off f lab r ls _ A z2 y y lF wA rf plz2 rl dl iry ply (notin-of-disj y A (Cons _ ex Q2) djA iyA)) ch io lf)))
      (let ((erased X) (erased wX) (erased orX) (erased covX)) (ring-walk d y z e n ni f fi r ids cs lab ls q h pn pf ch io rf rl dl rq iry sq))
      (let ((erased D) (erased wD) (erased apD)) (path-app cs (Nil _) X A z2 y z wAc wX))
      (let ((erased pz)) (choose-in r ni f ids cs d z z2 ch io lni iz pz2))
      (let ((erased SC) (erased wSC)) (walk-to cs D z2 z wD))
      (let ((erased S)) (Cons _ z SC))
      (let ((erased sbD) (erased _)) (walk-in-cyc cs (Cons _ z (Nil _)) (Nil _) SC D z z2 z2 z wSC pz wD (path-start-in cs _ SC z2 z wSC)))
      (let ((erased sbS) (erased _)) (walk-in-cyc cs (Nil _) (Cons _ z (Nil _)) D SC z z2 z2 z wD pz wSC (path-start-in cs _ D z2 z wD)))
      (let ((erased sXD)) (HSubCons z X _ (InHere z D) (sub-cons z X D (app-sub-r A X D X apD (sub-refl X)))))
      (let ((erased sDS)) (HSubCons z D S (InHere z SC) sbD))
      (let ((erased srX)) (sub-trans r (Cons _ y q) (Cons _ z X) s1 (HSubCons y q _ (path-start-in cs (Nil _) X y z wX) covX)))
      (let ((erased iy0S)) (sub-in (Cons _ z D) S y0 sDS (sub-in (Cons _ z X) (Cons _ z D) y0 sXD (sub-in r (Cons _ z X) y0 srX iy0))))
      (let ((erased iy1S)) (cyc-step cs _ SC z z2 y0 y1 wSC pz iy0S (choose-in r ni f ids cs d y0 y1 ch io lni iy0 (perm-inv d y1 y0 n ni pn pny0))))
      (let ((erased v0) (erased iv0) (erased pv0)) (path-prev f _ P x2 z2 z2 wP (InHere z2 P) nzx))
      (let-match erased (perm-inj d v0 ez z2 f fi pf pv0 pfz) (Refl _ _))
      (let ((erased P0) (erased P1) (erased wP0) (erased wP1) (erased apP)) (path-split f _ P x2 z2 ez wP iv0))
      (let ((erased offP0)) (walk-off f lab r ls _ P0 x2 ez y lF wP0 rf plx2 rl dl iry ply
        (notin-sub y P0 P (app-sub-l P0 (Cons _ ez P1) P P0 apP (sub-refl P0)) yP)))
      (let ((erased dpE)) (dpath-cat n f r y1 x ez dp0 (DPNode n f r x x2 ez ox pnx (walk-dpath n f r _ P0 x2 ez wP0 offP0))))
      (let ((erased pez2)) (walk-lab f lab _ xs x2 ex ez lF wx rf plx2 (InThere ez ex xs (sub-in P xs ez sP iv0))))
      (let-match erased (disj-at (Cons _ ex Q) ez P djP iv0) (NotInCons _ _ _ _ oezQ))
      (let ((erased oezS)) (match erased (in-dec ez S) (((NotIn ez S) res))
        (absurd (OrL _ _ ieS)
          (off-contour lab r ls q A X D Q ez y z lF (sub-in S (Cons _ z D) ez (HSubCons z SC _ (InHere z D) sbS) ieS) apD sA oezQ pez2 ply
            (apart-sym y ez (notin-in y ez P yP iv0)) orX rl dl iry iz sq oyq))
        ((OrR _ _ o) o)))
      (let ((erased x1) (erased v) (erased M) (erased pv) (erased iv) (erased cpM) (erased djM))
        (exit d z z2 y1 ez n ni f r ids cs _ SC ch io lf wSC pz dpE iy1S oezS))
      (let ((erased M3) (erased cp3) (erased d3) (erased s3)) (cpath-short n f M x1 ez cpM))
      (let ((erased dj3)) (disj-sym S (Cons _ x1 M) (disj-sym (Cons _ x1 M) S djM S (sub-refl S)) (Cons _ x1 M3)
        (HSubCons x1 M3 (Cons _ x1 M) (InHere x1 M) (sub-cons x1 M3 M s3))))
      (let ((erased L) (erased cpL) (erased snL)) (path-cpath n ni f fi r ids cs _ SC d z2 z pn pf ch io lz2 wSC))
      (let ((erased dL)) (distinct-snoc-cons z SC (Cons _ z2 L) snL
        (DistCons z SC (path-avoid cs _ SC z2 z z wSC (InHere z (Nil _))) (walk-distinct cs (Nil _) SC z2 z wSC))))
      (let ((erased M2) (erased cp2) (erased ap2)) (cpath-join n f L M3 x1 ez z2 z cp3 pfz cpL))
      (planar-moebius d x1 e n f M2 h g
        (MkMoebius n f M2 x1 z z2 v
          (app-distinct (Cons _ x1 M3) (Cons _ z2 L) (Cons _ x1 M2) (AppCons M3 _ M2 x1 ap2) d3 dL (disj-sub S (Cons _ z2 L) (Cons _ x1 M3) dj3 (snoc-sub SC (Cons _ z2 L) z snL)))
          cp2 pnz pv (mem2-app M3 (Cons _ z2 L) M2 z2 v ap2 (M2Here L z2 v (in-snoc v z SC (Cons _ z2 L) snL iv))))))))

(def-fns _ $ (erased disk-walk-e : (erased (Nat) d a b x0) (erased (List (Nat)) e n f p s xs) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) g)
    (erased (Ring e f x0 p) rg) (subterm erased (Path e s a b xs) w) (erased (DiskN n f (Cons (Nat) x0 p) a) da) (erased (NotIn a (Cons (Nat) x0 p)) oa)
    -> (erased (DiskN n f (Cons (Nat) x0 p) b) db) (erased (NotIn b (Cons (Nat) x0 p)) ob))
  (let-match erased w (PathStep _ _ xs1 _ a1 _ pa _ w1) ((PathHere _ _ _) (values da oa)))
  (let ((erased da1) (erased oa1)) (disk-edge d a a1 x0 e n f p h g rg da oa pa))
  (disk-walk-e d a1 b x0 e n f p s xs1 h g rg w1 da1 oa1))

; The converse of diskE_edge.
(def-fns _ $ (erased disk-edge-inv : (erased (Nat) d x ex x0) (erased (List (Nat)) e n f p) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) g)
    (erased (Ring e f x0 p) rg) (erased (DiskN n f (Cons (Nat) x0 p) ex) dn) (erased (NotIn ex (Cons (Nat) x0 p)) oex) (erased (Nth (Nat) e x ex) pex)
    -> (erased (DiskN n f (Cons (Nat) x0 p) x) dx) (erased (NotIn x (Cons (Nat) x0 p)) ox))
  (let ((erased nf) (erased pe)) (hyper-perm d e n f h))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased xs) (erased w)) (cycle d x ex e nf pe pex (nth-lt-length _ e x d ex pex le)))
  (disk-walk-e d ex x x0 e n f p (Nil _) xs h g rg w dn oex))

(def-fns _ $ (erased choose-under : (erased (List (Nat)) t a b xs) (erased (Nat) d) (erased (Under a d) ua) (erased (Under b d) ub) (subterm erased (List (Nat)) cs)
    (erased (Choose t a b xs cs) ch) -> (erased (Under cs d) r))
  (let-match erased ch (ChCons _ _ _ xs1 cs1 x y ca ch1) ((ChNil _ _ _) (UnderNil d)))
  (UnderCons cs1 y d
    (match erased ca _ ((CAIn _ _ _ _ _ _ pa) (under-nth a x y d ua pa)) ((CAOut _ _ _ _ _ _ pb) (under-nth b x y d ub pb)))
    (choose-under t a b xs1 d ua ub cs1 ch1)))

(def-fns _ $ (erased choose-length : (erased (List (Nat)) t a b xs cs) (erased (Nat) k) (subterm erased (Choose t a b xs cs) ch) (erased (Length (Nat) xs k) l)
    -> (erased (Length (Nat) cs k) r))
  (let-match erased ch (ChCons _ _ _ xs1 cs1 x y ca ch1) ((ChNil _ _ _) (let-match erased l (LengthNil _)) (LengthNil _)))
  (let-match erased l (LengthCons _ _ _ k1 l1))
  (LengthCons _ y cs1 k1 (choose-length t a b xs1 cs1 k1 ch1 l1)))

(def-fns _ $ (erased zip-below : (erased (List (Nat)) xs ys) (erased (Nat) d) (subterm erased (List (Bond)) g) (erased (Zip xs ys g) z) (erased (Under xs d) ux)
    (erased (Under ys d) uy) -> (erased (Below g d) r))
  (let-match erased z (ZipCons xs1 ys1 g1 x y z1) ((ZipNil) (BelowNil d)))
  (let-match erased ux (UnderCons _ _ _ lx ux1))
  (let-match erased uy (UnderCons _ _ _ ly uy1))
  (BelowCons g1 x y d lx ly (zip-below xs1 ys1 d g1 z1 ux1 uy1)))

(def-fns _ $ (erased resp-under : (erased (List (Nat)) lab ls) (erased (Nat) d) (subterm erased (List (Nat)) xs) (erased (Respects lab xs ls) rp)
    (erased (Length (Nat) lab d) ll) -> (erased (Under xs d) r))
  (let-match erased rp (RespCons _ xs1 ls1 j l pj rp1) ((RespNil _) (UnderNil d)))
  (UnderCons xs1 j d (nth-lt-length _ lab j d l pj ll) (resp-under lab ls1 d xs1 rp1 ll)))

; The bonds x - n x for every dart, and x - e x for x and e x off r: e2 fixes the darts of t, r followed by their edge preimages er.
(def-adts $ (DiskGraph : ((Nat) d) ((List (Nat)) e n r) ((List (Bond)) g) -> Type)
  enum
  (many MkDiskGraph : (erased (Nat) d) (erased (List (Nat)) e n r nf er t ids e2) (erased (List (Bond)) gn ge g)
      (erased (HPerm d e nf) pe) (erased (Respects nf r er) re) (erased (AppN r er t) ap) (erased (Iota d ids) io)
      (erased (Choose t ids e ids e2) ch) (erased (Graph d n gn) grn) (erased (Graph d e2 ge) gre) (erased (Cat gn ge g) c) -> (DiskGraph d e n r g)))

(def-fns _ $ (erased dg-exists : (erased (Nat) d) (erased (List (Nat)) e n f r) (erased (Hypermap d e n f) h) (erased (Under r d) ur)
    -> (erased (List (Bond)) g) (erased (DiskGraph d e n r g) dg) (erased (Below g d) bg))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased ids) (erased io)) (iota-exists d))
  (let ((erased uids)) (perm-under d ids ids (perm-id d ids io)))
  (let ((erased er) (erased re)) (respects-exists nf r d ur (perm-length d nf e (perm-sym d e nf pe))))
  (let ((erased t) (erased ap)) (app-exists r er))
  (let ((erased e2) (erased ch)) (choose-exists t ids e d (iota-length d ids io) le ids uids))
  (let ((erased le2)) (choose-length t ids e ids e2 d ch (iota-length d ids io)))
  (let ((erased gn) (erased grn)) (perm-graph d n ni pn))
  (let ((erased ge) (erased gre)) (graph-exists d e2 le2))
  (let ((erased g) (erased c)) (cat-exists gn ge))
  (let-match erased gre (MkGraph _ _ ids2 _ io2 _ z))
  (let-match erased (iota-fn d ids ids2 io io2) (Refl _ _))
  (values g (MkDiskGraph d e n r nf er t ids e2 gn ge g pe re ap io ch grn gre c)
    (below-cat gn ge g d c (graph-below d n ni gn (graph-fun d n gn grn) pn)
      (zip-below ids e2 d ge z uids (choose-under t ids e ids d uids (perm-under d e nf pe) e2 ch)))))

; A bond of the disk graph.
(def-adts $ (DGStep : ((List (Nat)) e n r) ((Nat) u v) -> Type)
  enum
  (many DGNode : (erased (List (Nat)) e n r) (erased (Nat) u v) (erased (Nth (Nat) n u v) pn) -> (DGStep e n r u v))
  (many DGNodeBack : (erased (List (Nat)) e n r) (erased (Nat) u v) (erased (Nth (Nat) n v u) pn) -> (DGStep e n r u v))
  (many DGEdge : (erased (List (Nat)) e n r) (erased (Nat) u v) (erased (NotIn u r) ou) (erased (Nth (Nat) e u v) pe) -> (DGStep e n r u v))
  (many DGEdgeBack : (erased (List (Nat)) e n r) (erased (Nat) u v) (erased (NotIn v r) ov) (erased (NotIn u r) ou) (erased (Nth (Nat) e v u) pe)
      -> (DGStep e n r u v))
  (many DGSame : (erased (List (Nat)) e n r) (erased (Nat) u) -> (DGStep e n r u u)))

; x - e x with x off t: neither end is on r.
(def-fns _ $ (erased dg-edge : (erased (Nat) d u v) (erased (List (Nat)) e r nf er t) (erased (HPerm d e nf) pe) (erased (Respects nf r er) re)
    (erased (AppN r er t) ap) (erased (NotIn u t) ou) (erased (Nth (Nat) e u v) pv) -> (erased (NotIn u r) ou2) (erased (NotIn v r) ov))
  (values (notin-sub u r t (app-sub-l r er t r ap (sub-refl r)) ou)
    (match erased (in-dec v r) _
      (absurd (OrL _ _ iv) (apart-irrefl u (notin-in u u t ou (app-in-r r er t u ap (in-map nf r er v u iv re (perm-inv d u v e nf pe pv))))))
      ((OrR _ _ o) o))))

(def-fns _ $ (erased dg-adj : (erased (Nat) d u v) (erased (List (Nat)) e n r) (erased (List (Bond)) g) (erased (DiskGraph d e n r g) dg) (erased (Adj g u v) a)
    -> (erased (DGStep e n r u v) s))
  (let-match erased dg (MkDiskGraph _ _ _ _ nf er t ids e2 gn ge _ pe re ap io ch grn gre c))
  (let-match erased gre (MkGraph _ _ ids2 _ io2 le2 z))
  (match erased (adj-cat-inv gn ge g u v c a) _
    ((OrL _ _ an) (match erased (graph-adj-inv d u v n gn grn an) _ ((OrL _ _ p) (DGNode e n r u v p)) ((OrR _ _ p) (DGNodeBack e n r u v p))))
    ((OrR _ _ ae)
      (match erased (graph-adj-inv d u v e2 ge gre ae) _
        ((OrL _ _ p)
          (match erased (choose-at t ids e ids e2 d u v ch io (nth-lt-length _ e2 u d v p le2) p) _
            ((CAIn _ _ _ _ _ _ pi) (let-match erased (nth-fn _ ids u v u pi (iota-nth d u ids io (nth-lt-length _ e2 u d v p le2))) (Refl _ _)) (DGSame e n r u))
            ((CAOut _ _ _ _ _ ou pb) (let ((erased o1) (erased o2)) (dg-edge d u v e r nf er t pe re ap ou pb)) (DGEdge e n r u v o1 pb))))
        ((OrR _ _ p)
          (match erased (choose-at t ids e ids e2 d v u ch io (nth-lt-length _ e2 v d u p le2) p) _
            ((CAIn _ _ _ _ _ _ pi) (let-match erased (nth-fn _ ids v u v pi (iota-nth d v ids io (nth-lt-length _ e2 v d u p le2))) (Refl _ _)) (DGSame e n r u))
            ((CAOut _ _ _ _ _ ov pb) (let ((erased o1) (erased o2)) (dg-edge d v u e r nf er t pe re ap ov pb)) (DGEdgeBack e n r u v o1 o2 pb))))))))

; diskN is a union of classes of the disk graph ...
(def-fns _ $ (erased conn-disk : (erased (Nat) d a b x0) (erased (List (Nat)) e n f p) (erased (List (Bond)) g) (erased (Hypermap d e n f) h)
    (erased (Genus d e n f (Zero)) gen) (erased (Ring e f x0 p) rg) (erased (DiskGraph d e n (Cons (Nat) x0 p) g) dg) (subterm erased (Conn g a b) c)
    (erased (DiskN n f (Cons (Nat) x0 p) a) da) -> (erased (DiskN n f (Cons (Nat) x0 p) b) db))
  (let-match erased c (ConnStep _ _ a1 _ ad c1) ((ConnHere _ _) da))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (conn-disk d a1 b x0 e n f p g h gen rg dg c1
    (match erased (dg-adj d a a1 e n (Cons _ x0 p) g dg ad) _
      ((DGNode _ _ _ _ _ pn1) (disk-node d a a1 n ni f _ pn da pn1))
      ((DGNodeBack _ _ _ _ _ pn1) (disk-pre n f _ a a1 da pn1))
      ((DGEdge _ _ _ _ _ ou pe1) (let ((erased d1) (erased o1)) (disk-edge d a a1 x0 e n f p h gen rg da ou pe1)) d1)
      ((DGEdgeBack _ _ _ _ _ ov ou pe1) (let ((erased d1) (erased o1)) (disk-edge-inv d a1 a x0 e n f p h gen rg da ou pe1)) d1)
      ((DGSame _ _ _ _) da))))

; ... and its darts are joined to r.
(def-fns _ $ (erased disk-conn : (erased (Nat) d u x y x0) (erased (List (Nat)) e n f p) (erased (List (Bond)) g) (erased (Hypermap d e n f) h)
    (erased (Genus d e n f (Zero)) gen) (erased (Ring e f x0 p) rg) (erased (DiskGraph d e n (Cons (Nat) x0 p) g) dg)
    (subterm erased (DPath n f (Cons (Nat) x0 p) u x) dp) (erased (DiskN n f (Cons (Nat) x0 p) u) du) (erased (Conn g u y) c) -> (erased (Conn g x y) res))
  (let ((erased r)) (Cons _ x0 p))
  (let-match erased dg (MkDiskGraph _ _ _ _ nf er t ids e2 gn ge _ pe re ap io ch grn gre c0))
  (let ((erased nf2) (erased ni) (erased fi) (erased rnf) (erased pe2) (erased pn) (erased pf)) (hyper-core d e n f h))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (match erased dp _
    ((DPNil _ _ _ _) c)
    ((DPNode _ _ _ _ u2 _ out pn1 dp1)
      (disk-conn d u2 x y x0 e n f p g h gen rg dg dp1 (disk-pre n f r u u2 du pn1)
        (ConnStep g u2 u y (adj-cat-l gn ge g u2 u (graph-adj d u2 u n gn grn pn1) c0) c)))
    ((DPFace _ _ _ _ u2 _ out pf1 dp1)
      (let ((erased du2)) (disk-step n f r u u2 du (DPFace n f r u u2 u2 out pf1 (DPNil n f r u2))))
      (let ((erased w) (erased pw) (erased lw)) (perm-nth d u2 n ni pn (perm-val d u u2 f fi pf pf1)))
      (let ((erased pew)) (hyper-edge d w u2 u e n f h pw pf1))
      (let ((erased dw) (erased ow)) (disk-edge-inv d w u x0 e n f p h gen rg du out pew))
      (let ((erased owe)) (match erased (in-dec w er) (((NotIn w er) res))
        (absurd (OrL _ _ iw)
          (let ((erased y2) (erased iy2) (erased py2)) (respects-in nf r er w re iw))
          (let-match erased (nth-fn _ e w u y2 pew (perm-inv d y2 w nf e (perm-sym d e nf pe) py2)) (Refl _ _))
          (apart-irrefl u (notin-in u u r out iy2)))
        ((OrR _ _ o) o)))
      (let ((erased pe3)) (choose-out t ids e ids e2 d w u ch io le (notin-app r er t w ap ow owe) pew))
      (disk-conn d u2 x y x0 e n f p g h gen rg dg dp1 du2
        (ConnStep g u2 w y (adj-cat-l gn ge g u2 w (graph-adj d u2 w n gn grn pw) c0)
          (ConnStep g w u y (adj-cat-r gn ge g w u (graph-adj d w u e2 ge gre pe3) c0) c))))))

; hd lists the darts of diskN r in order and zs the other darts, split by the root labels lab of the classes of the disk graph.
(def-adts $ (DiskSplit : ((Nat) d) ((List (Nat)) e n r hd zs) -> Type)
  enum
  (many MkDiskSplit : (erased (Nat) d) (erased (List (Nat)) e n r ids lab rs lr hd zs) (erased (List (Bond)) g) (erased (DiskGraph d e n r g) dg)
      (erased (Iota d ids) io) (erased (Length (Nat) lab d) ll) (erased (Const lab g) cl) (erased (Rooted g rs ids lab) ro) (erased (Respects lab r lr) rl)
      (erased (SplitBy lab lr ids hd zs) sp) -> (DiskSplit d e n r hd zs)))

(def-fns _ $ (erased ds-exists : (erased (Nat) d) (erased (List (Nat)) e n f r) (erased (Hypermap d e n f) h) (erased (Under r d) ur)
    -> (erased (List (Nat)) hd zs) (erased (DiskSplit d e n r hd zs) ds))
  (let ((erased g) (erased dg) (erased bg)) (dg-exists d e n f r h ur))
  (let ((erased k) (erased cs)) (classes-exists g d bg))
  (let-match erased cs (MkClasses _ _ _ ids lab rs io ll lr dr fix cl ro))
  (let ((erased lrr) (erased rl)) (respects-exists lab r d ur ll))
  (let ((erased hd) (erased zs) (erased sp)) (sb-exists lab lrr d ll ids (perm-under d ids ids (perm-id d ids io))))
  (values hd zs (MkDiskSplit d e n r ids lab rs lrr hd zs g dg io ll cl ro rl sp)))

; The darts 0..d-1 split into hd and zs.
(def-fns _ $ (erased ds-split : (erased (Nat) d) (erased (List (Nat)) e n r hd zs) (erased (DiskSplit d e n r hd zs) ds)
    -> (erased (List (Nat)) ids) (erased (Iota d ids) io) (erased (Split hd ids hd zs) sp))
  (let-match erased ds (MkDiskSplit _ _ _ _ ids lab rs lr _ _ g dg io ll cl ro rl sp))
  (values ids io (sb-split lab lr ids hd zs ids hd zs sp sp (sub-refl hd))))

(def-fns _ $ (erased ds-in : (erased (Nat) d x x0) (erased (List (Nat)) e n f p hd zs) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) gen)
    (erased (Ring e f x0 p) rg) (erased (Under (Cons (Nat) x0 p) d) ur) (erased (DiskSplit d e n (Cons (Nat) x0 p) hd zs) ds) (erased (In x hd) ix)
    -> (erased (DiskN n f (Cons (Nat) x0 p) x) dx))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (let-match erased ds (MkDiskSplit _ _ _ _ ids lab rs lr _ _ g dg io ll cl ro rl sp))
  (let ((erased l) (erased pl) (erased il)) (sb-in-key lab lr ids hd zs x sp ix))
  (let ((erased y) (erased iy) (erased py)) (respects-in lab _ lr l rl il))
  (let ((erased sa) (erased sb)) (split-sub hd ids hd zs (sb-split lab lr ids hd zs ids hd zs sp sp (sub-refl hd))))
  (let ((erased ly)) (under-in _ y d ur iy))
  (conn-disk d y x x0 e n f p g h gen rg dg
    (conn-sym g x y (same-root g d x y l ids lab rs io ro pl py
      (under-in ids x d (perm-under d ids ids (perm-id d ids io)) (sub-in hd ids x sa ix)) ly))
    (disk-ring d y n ni f _ pn iy ly)))

(def-fns _ $ (erased ds-mem : (erased (Nat) d x x0) (erased (List (Nat)) e n f p hd zs) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) gen)
    (erased (Ring e f x0 p) rg) (erased (Under (Cons (Nat) x0 p) d) ur) (erased (DiskSplit d e n (Cons (Nat) x0 p) hd zs) ds)
    (erased (DiskN n f (Cons (Nat) x0 p) x) dx) (erased (Lt x d) lx) -> (erased (In x hd) ix))
  (let-match erased ds (MkDiskSplit _ _ _ _ ids lab rs lr _ _ g dg io ll cl ro rl sp))
  (let ((erased dg2)) dg)
  (let-match erased dg2 (MkDiskGraph _ _ _ _ nf er t ids2 e2 gn ge _ pe re ap io2 ch grn gre c0))
  (let-match erased dx (MkDiskN _ _ _ _ y y1 iy pn1 dp))
  (let ((erased c)) (disk-conn d y1 x y x0 e n f p g h gen rg dg dp (MkDiskN n f _ y1 y y1 iy pn1 (DPNil n f _ y1))
    (ConnStep g y1 y y (adj-cat-l gn ge g y1 y (graph-adj d y1 y n gn grn pn1) c0) (ConnHere g y))))
  (let ((erased l) (erased py)) (nth-exists _ lab d y ll (under-in _ y d ur iy)))
  (sb-member lab lr ids hd zs x l sp (iota-in d x ids io lx) (conn-const lab g y x l (conn-sym g x y c) cl py) (in-map lab _ lr y l iy rl py)))

(def-fns _ $ (erased absurd ds-out : (erased (Nat) d x x0) (erased (List (Nat)) e n f p hd zs) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) gen)
    (erased (Ring e f x0 p) rg) (erased (Under (Cons (Nat) x0 p) d) ur) (erased (DiskSplit d e n (Cons (Nat) x0 p) hd zs) ds) (erased (In x zs) iz)
    (erased (DiskN n f (Cons (Nat) x0 p) x) dx) -> (erased (False) fl))
  (let ((erased ids) (erased io) (erased sp)) (ds-split d e n _ hd zs ds))
  (let ((erased sa) (erased sb)) (split-sub hd ids hd zs sp))
  (apart-irrefl x (notin-in x x hd (disj-at hd x zs (split-disj hd ids hd zs sp) iz)
    (ds-mem d x x0 e n f p hd zs h gen rg ur ds dx (under-in ids x d (perm-under d ids ids (perm-id d ids io)) (sub-in zs ids x sb iz))))))

; p2 is p with each dart of As sent to the dart at the same position of Bs.
(def-adts $ (SetAll : ((List (Nat)) p As Bs p2) -> Type)
  enum
  (many SANil : (erased (List (Nat)) p) -> (SetAll p (Nil (Nat)) (Nil (Nat)) p))
  (many SACons : (erased (List (Nat)) p p1 As Bs p2) (erased (Nat) a b) (erased (SetNth (Nat) p a b p1) sn) (erased (SetAll p1 As Bs p2) rest)
      -> (SetAll p (Cons (Nat) a As) (Cons (Nat) b Bs) p2)))

; q sends each dart of As to the dart at the same position of Bs.
(def-adts $ (Hits : ((List (Nat)) q As Bs) -> Type)
  enum
  (many HitsNil : (erased (List (Nat)) q) -> (Hits q (Nil (Nat)) (Nil (Nat))))
  (many HitsCons : (erased (List (Nat)) q As Bs) (erased (Nat) a b) (erased (Nth (Nat) q a b) p) (erased (Hits q As Bs) rest)
      -> (Hits q (Cons (Nat) a As) (Cons (Nat) b Bs))))

(def-fns _ $ (erased setall-exists : (erased (List (Nat)) p Bs) (erased (Nat) d k) (erased (Length (Nat) p d) lp) (subterm erased (List (Nat)) As)
    (erased (Under As d) ua) (erased (Length (Nat) As k) la) (erased (Length (Nat) Bs k) lb) -> (erased (List (Nat)) p2) (erased (SetAll p As Bs p2) r))
  (let-match erased ua (UnderCons As1 a _ lt ua1) ((UnderNil _) (let-match erased la (LengthNil _)) (let-match erased lb (LengthNil _)) (values p (SANil p))))
  (let-match erased la (LengthCons _ _ _ k1 la1))
  (let-match erased lb (LengthCons _ b Bs1 _ lb1))
  (let ((erased p1) (erased sn)) (setnth-exists _ p d a b lp lt))
  (let ((erased p2) (erased r)) (setall-exists p1 Bs1 d k1 (setnth-length _ p a d b p1 sn lp) As1 ua1 la1 lb1))
  (values p2 (SACons p p1 As1 Bs1 p2 a b sn r)))

(def-fns _ $ (erased setall-length : (erased (List (Nat)) p As Bs p2) (erased (Nat) d) (subterm erased (SetAll p As Bs p2) sa) (erased (Length (Nat) p d) lp)
    -> (erased (Length (Nat) p2 d) r))
  (match erased sa _
    ((SANil _) lp)
    ((SACons _ p1 As1 Bs1 _ a b sn sa1) (setall-length p1 As1 Bs1 p2 d sa1 (setnth-length _ p a d b p1 sn lp)))))

(def-fns _ $ (erased setall-miss : (erased (List (Nat)) p As Bs p2) (erased (Nat) t v) (subterm erased (SetAll p As Bs p2) sa) (erased (NotIn t As) ot)
    (erased (Nth (Nat) p t v) pt) -> (erased (Nth (Nat) p2 t v) r))
  (match erased sa _
    ((SANil _) pt)
    ((SACons _ p1 As1 Bs1 _ a b sn sa1)
      (let-match erased ot (NotInCons _ _ _ ne ot1))
      (setall-miss p1 As1 Bs1 p2 t v sa1 ot1 (setnth-keep p p1 a t b v sn pt ne)))))

(def-fns _ $ (erased setall-hits : (erased (List (Nat)) p As Bs p2) (subterm erased (SetAll p As Bs p2) sa) (erased (Distinct As) da) -> (erased (Hits p2 As Bs) r))
  (match erased sa _
    ((SANil _) (HitsNil p))
    ((SACons _ p1 As1 Bs1 _ a b sn sa1)
      (let-match erased da (DistCons _ _ oa da1))
      (HitsCons p2 As1 Bs1 a b (setall-miss p1 As1 Bs1 p2 a b sa1 oa (setnth-nth _ p a b p1 sn)) (setall-hits p1 As1 Bs1 p2 sa1 da1)))))

(def-fns _ $ (erased hits-in2 : (erased (List (Nat)) q As Bs) (erased (Nat) a b) (subterm erased (Hits q As Bs) hs) (erased (In2 As Bs a b) i)
    -> (erased (Nth (Nat) q a b) r))
  (let-match erased hs (HitsCons _ As1 Bs1 a1 b1 p hs1) (absurd (HitsNil _) i))
  (match erased i _ ((I2Here _ _ _ _) p) ((I2There _ _ _ _ _ _ i1) (hits-in2 q As1 Bs1 a b hs1 i1))))

; q sends a :: P one step along, and the last dart y of a :: P to c: P followed by c is PP.
(def-fns _ $ (erased hits-fpath : (erased (List (Nat)) q PP) (subterm erased (List (Nat)) P) (erased (Nat) a c) (erased (Hits q (Cons (Nat) a P) PP) hs)
    (erased (HSnoc (Nat) P c PP) sn) -> (erased (Nat) y) (erased (FPath q a P y) fp) (erased (Nth (Nat) q y c) py))
  (let-match erased P (Cons _ z P1)
    ((Nil _) (let-match erased sn (SnocNil _ _)) (let-match erased hs (HitsCons _ _ _ _ _ p _)) (values a (FPNil q a) p)))
  (let-match erased sn (SnocCons _ _ _ _ PP1 sn1))
  (let-match erased hs (HitsCons _ _ _ _ _ p hs1))
  (let ((erased y) (erased fp) (erased py)) (hits-fpath q PP1 P1 z c hs1 sn1))
  (values y (FPCons q P1 a z y p fp) py))

; p and q are inverse on s, which each sends into itself, at x.
(def-adts $ (BijAt : ((List (Nat)) p q s) ((Nat) x) -> Type)
  enum
  (many MkBijAt : (erased (List (Nat)) p q s) (erased (Nat) x y z) (erased (Nth (Nat) p x y) py) (erased (In y s) iy) (erased (Nth (Nat) q y x) qy)
      (erased (Nth (Nat) q x z) qz) (erased (In z s) iz) (erased (Nth (Nat) p z x) pz) -> (BijAt p q s x)))

(def-adts $ (Bij : ((List (Nat)) p q s xs) -> Type)
  enum
  (many BijNil : (erased (List (Nat)) p q s) -> (Bij p q s (Nil (Nat))))
  (many BijCons : (erased (List (Nat)) p q s xs) (erased (Nat) x) (erased (BijAt p q s x) b) (erased (Bij p q s xs) rest) -> (Bij p q s (Cons (Nat) x xs))))

(def-fns _ $ (erased bij-get : (erased (List (Nat)) p q s xs) (erased (Nat) x) (subterm erased (Bij p q s xs) bj) (erased (In x xs) ix) -> (erased (BijAt p q s x) r))
  (let-match erased bj (BijCons _ _ _ xs1 y b bj1) (absurd (BijNil _ _ _) ix))
  (match erased ix _ ((InHere _ _) b) ((InThere _ _ _ ix1) (bij-get p q s xs1 x bj1 ix1))))

(def-fns _ $ (erased bij-swap : (erased (List (Nat)) p q s xs) (subterm erased (Bij p q s xs) bj) -> (erased (Bij q p s xs) r))
  (let-match erased bj (BijCons _ _ _ xs1 x b bj1) ((BijNil _ _ _) (BijNil q p s)))
  (let-match erased b (MkBijAt _ _ _ _ y z py iy qy qz iz pz))
  (BijCons q p s xs1 x (MkBijAt q p s x z y qz iz pz py iy qy) (bij-swap p q s xs1 bj1)))

; How p, p0 with As sent along Bs, and q, q0 with Bs sent back along As, act at x: on As, or off the ring As = Bs with images under
; p0 and q0 in s and off the ring.
(def-adts $ (Side : ((List (Nat)) p0 q0 As Bs s) ((Nat) x) -> Type)
  enum
  (many SideRing : (erased (List (Nat)) p0 q0 As Bs s) (erased (Nat) x) (erased (In x As) ix) -> (Side p0 q0 As Bs s x))
  (many SideOff : (erased (List (Nat)) p0 q0 As Bs s) (erased (Nat) x y z) (erased (NotIn x As) oa) (erased (NotIn x Bs) ob) (erased (Nth (Nat) p0 x y) py)
      (erased (In y s) iy) (erased (NotIn y Bs) oy) (erased (Nth (Nat) q0 x z) qz) (erased (In z s) iz) (erased (NotIn z As) oz) -> (Side p0 q0 As Bs s x)))

(def-fns _ $ (erased bij-at : (erased (Nat) d k x) (erased (List (Nat)) p0 q0 As Bs s p q) (erased (HPerm d p0 q0) pm) (erased (SetAll p0 As Bs p) sp)
    (erased (SetAll q0 Bs As q) sq) (erased (Hits p As Bs) hp) (erased (Hits q Bs As) hq) (erased (Length (Nat) As k) la) (erased (Length (Nat) Bs k) lb)
    (erased (Sub As s) sas) (erased (Sub As Bs) sab) (erased (Sub Bs As) sba) (erased (Side p0 q0 As Bs s x) sd) -> (erased (BijAt p q s x) r))
  (match erased sd _
    ((SideRing _ _ _ _ _ _ ix)
      (let ((erased y) (erased i2)) (in2-exists As Bs x k ix la lb))
      (let ((erased z) (erased j2)) (in2-exists Bs As x k (sub-in As Bs x sab ix) lb la))
      (let ((erased j3)) (in2-sym Bs As x z j2))
      (MkBijAt p q s x y z (hits-in2 p As Bs x y hp i2) (sub-in As s y sas (sub-in Bs As y sba (in2-in-left Bs As y x (in2-sym As Bs x y i2))))
        (hits-in2 q Bs As y x hq (in2-sym As Bs x y i2)) (hits-in2 q Bs As x z hq j2) (sub-in As s z sas (in2-in-left As Bs z x j3)) (hits-in2 p As Bs z x hp j3)))
    ((SideOff _ _ _ _ _ _ y z oa ob py iy oy qz iz oz)
      (MkBijAt p q s x y z (setall-miss p0 As Bs p x y sp oa py) iy (setall-miss q0 Bs As q y x sq oy (perm-inv d x y p0 q0 pm py))
        (setall-miss q0 Bs As q x z sq ob qz) iz (setall-miss p0 As Bs p z x sp oz (perm-inv d x z q0 p0 (perm-sym d p0 q0 pm) qz))))))

; ys sends each position i of xs to the position j in hd of p (hd i).
(def-adts $ (Rel : ((List (Nat)) hd p xs ys) -> Type)
  enum
  (many RelNil : (erased (List (Nat)) hd p) -> (Rel hd p (Nil (Nat)) (Nil (Nat))))
  (many RelCons : (erased (List (Nat)) hd p xs ys) (erased (Nat) i a b j) (erased (Nth (Nat) hd i a) pa) (erased (Nth (Nat) p a b) pb) (erased (Nth (Nat) hd j b) pj)
      (erased (Rel hd p xs ys) rest) -> (Rel hd p (Cons (Nat) i xs) (Cons (Nat) j ys))))

(def-fns _ $ (erased rel-exists : (erased (List (Nat)) hd p q) (erased (Nat) k) (erased (Length (Nat) hd k) lh) (erased (Bij p q hd hd) bj) (subterm erased (List (Nat)) xs)
    (erased (Under xs k) u) -> (erased (List (Nat)) ys) (erased (Rel hd p xs ys) r))
  (let-match erased u (UnderCons xs1 i _ li u1) ((UnderNil _) (values (Nil _) (RelNil hd p))))
  (let ((erased a) (erased pa)) (nth-exists _ hd k i lh li))
  (let-match erased (bij-get p q hd hd a bj (nth-in hd i a pa)) (MkBijAt _ _ _ _ b z pb ib qb qz iz pz))
  (let ((erased j) (erased pj)) (in-nth b hd ib))
  (let ((erased ys) (erased r)) (rel-exists hd p q k lh bj xs1 u1))
  (values (Cons _ j ys) (RelCons hd p xs1 ys i a b j pa pb pj r)))

(def-fns _ $ (erased rel-nth : (erased (List (Nat)) hd p xs ys) (erased (Nat) i x) (subterm erased (Rel hd p xs ys) rl) (erased (Nth (Nat) xs i x) px)
    -> (erased (Nat) y a b) (erased (Nth (Nat) ys i y) py) (erased (Nth (Nat) hd x a) pa) (erased (Nth (Nat) p a b) pb) (erased (Nth (Nat) hd y b) pj))
  (let-match erased rl (RelCons _ _ xs1 ys1 x1 a1 b1 j1 pa1 pb1 pj1 rl1) (absurd (RelNil _ _) px))
  (let-match erased px (NthThere _ _ _ i1 _ px1) ((NthHere _ _ _) (values j1 a1 b1 (NthHere _ j1 ys1) pa1 pb1 pj1)))
  (let ((erased y) (erased a) (erased b) (erased py) (erased pa) (erased pb) (erased pj)) (rel-nth hd p xs1 ys1 i1 x rl1 px1))
  (values y a b (NthThere _ j1 ys1 i1 y py) pa pb pj))

(def-fns _ $ (erased rel-length : (erased (List (Nat)) hd p xs ys) (erased (Nat) k) (subterm erased (Rel hd p xs ys) rl) (erased (Length (Nat) xs k) l)
    -> (erased (Length (Nat) ys k) r))
  (let-match erased rl (RelCons _ _ xs1 ys1 i a b j pa pb pj rl1) ((RelNil _ _) (let-match erased l (LengthNil _)) (LengthNil _)))
  (let-match erased l (LengthCons _ _ _ k1 l1))
  (LengthCons _ j ys1 k1 (rel-length hd p xs1 ys1 k1 rl1 l1)))

(def-fns _ $ (erased rel-morph : (erased (List (Nat)) hd p idk ys) (erased (Nat) k) (erased (Rel hd p idk ys) rl) (erased (Iota k idk) io) (subterm erased (List (Nat)) m)
    (erased (Under m k) u) -> (erased (MorphOff hd ys p (Nil (Nat)) m) r))
  (let-match erased u (UnderCons m1 x _ lx u1) ((UnderNil _) (MONil hd ys p (Nil _))))
  (let ((erased y) (erased a) (erased b) (erased py) (erased pa) (erased pb) (erased pj)) (rel-nth hd p idk ys x x rl (iota-nth k x idk io lx)))
  (MOAt hd ys p (Nil _) m1 x y a b py pa pj pb (rel-morph hd p idk ys k rl io m1 u1)))

(def-fns _ $ (erased rel-inv : (erased (List (Nat)) hd p q idk Q) (erased (Nat) k) (erased (Rel hd q idk Q) rq) (erased (Iota k idk) io) (erased (Distinct hd) dh)
    (erased (Length (Nat) hd k) lh) (erased (Bij p q hd hd) bj) (erased (List (Nat)) xs) (subterm erased (List (Nat)) P) (erased (Rel hd p xs P) rp)
    -> (erased (Respects Q P xs) r))
  (let-match erased rp (RelCons _ _ xs1 P1 i a b j pa pb pj rp1) ((RelNil _ _) (RespNil Q)))
  (let ((erased y) (erased b2) (erased c) (erased py) (erased pb2) (erased qb) (erased pc)) (rel-nth hd q idk Q j j rq (iota-nth k j idk io (nth-lt-length _ hd j k b pj lh))))
  (let-match erased (nth-fn _ hd j b b2 pj pb2) (Refl _ _))
  (let-match erased (bij-get p q hd hd a bj (nth-in hd i a pa)) (MkBijAt _ _ _ _ b3 z pb3 ib3 qb3 qz iz pz))
  (let-match erased (nth-fn _ p a b b3 pb pb3) (Refl _ _))
  (let-match erased (nth-fn _ q b a c qb3 qb) (Refl _ _))
  (let-match erased (distinct-nth hd y i a dh pc pa) (Refl _ _))
  (RespCons Q P1 xs1 j y py (rel-inv hd p q idk Q k rq io dh lh bj xs1 P1 rp1)))

; A permutation of the darts listed by hd, read on their positions.
(def-fns _ $ (erased restrict : (erased (Nat) k) (erased (List (Nat)) p q hd) (erased (Bij p q hd hd) bj) (erased (Distinct hd) dh) (erased (Length (Nat) hd k) lh)
    -> (erased (List (Nat)) idk P Q) (erased (Iota k idk) io) (erased (HPerm k P Q) pm) (erased (MorphOff hd P p (Nil (Nat)) idk) mp)
       (erased (MorphOff hd Q q (Nil (Nat)) idk) mq))
  (let ((erased idk) (erased io)) (iota-exists k))
  (let ((erased uk)) (perm-under k idk idk (perm-id k idk io)))
  (let ((erased bj2)) (bij-swap p q hd hd bj))
  (let ((erased P) (erased rp)) (rel-exists hd p q k lh bj idk uk))
  (let ((erased Q) (erased rq)) (rel-exists hd q p k lh bj2 idk uk))
  (values idk P Q io
    (HMkPerm k P Q idk io (rel-length hd p idk P k rp (iota-length k idk io)) (rel-inv hd p q idk Q k rq io dh lh bj idk P rp)
      (rel-inv hd q p idk P k rp io dh lh bj2 idk Q rq))
    (rel-morph hd p idk P k rp io idk uk) (rel-morph hd q idk Q k rq io idk uk)))

; The positions B in h of the darts R.
(def-fns _ $ (erased pos-exists : (erased (List (Nat)) h) (subterm erased (List (Nat)) R) (erased (Sub R h) sb) -> (erased (List (Nat)) B) (erased (Respects h B R) r))
  (let-match erased sb (HSubCons x R1 _ ix sb1) ((HSubNil _) (values (Nil _) (RespNil h))))
  (let ((erased j) (erased pj)) (in-nth x h ix))
  (let ((erased B1) (erased r1)) (pos-exists h R1 sb1))
  (values (Cons _ j B1) (RespCons h B1 R1 j x pj r1)))

(def-fns _ $ (erased pos-in : (erased (List (Nat)) h R) (erased (Nat) i x) (subterm erased (List (Nat)) B) (erased (Respects h B R) rp) (erased (Distinct h) dh)
    (erased (Nth (Nat) h i x) px) (erased (In x R) ix) -> (erased (In i B) r))
  (let-match erased rp (RespCons _ B1 R1 j y pj rp1) (absurd (RespNil _) ix))
  (match erased ix _
    ((InHere _ _) (let-match erased (distinct-nth h j i x dh pj px) (Refl _ _)) (InHere j B1))
    ((InThere _ _ _ ix1) (InThere i j B1 (pos-in h R1 i x B1 rp1 dh px ix1)))))

(def-fns _ $ (erased pos-out : (erased (List (Nat)) h R) (erased (Nat) i x) (subterm erased (List (Nat)) B) (erased (Respects h B R) rp)
    (erased (In i B) ib) (erased (Nth (Nat) h i x) px) -> (erased (In x R) r))
  (let-match erased rp (RespCons _ B1 R1 j y pj rp1) (absurd (RespNil _) ib))
  (match erased ib _
    ((InHere _ _) (let-match erased (nth-fn _ h i x y px pj) (Refl _ _)) (InHere x R1))
    ((InThere _ _ _ ib1) (InThere x y R1 (pos-out h R1 i x B1 rp1 ib1 px)))))

; Off the positions B of As, the morphism to q, q0 with As sent elsewhere, is one to q0.
(def-fns _ $ (erased morph-relax : (erased (List (Nat)) h P q q0 As Bs B) (erased (Nat) d) (erased (SetAll q0 As Bs q) sa) (erased (Respects h B As) rb)
    (erased (Distinct h) dh) (erased (Length (Nat) q0 d) lq) (erased (Under h d) uh) (subterm erased (List (Nat)) xs) (erased (MorphOff h P q (Nil (Nat)) xs) mo)
    -> (erased (MorphOff h P q0 B xs) r))
  (match erased mo _
    ((MONil _ _ _ _) (MONil h P q0 B))
    (absurd (MOSkip _ _ _ _ xs1 x ib mo1) (match erased ib _))
    ((MOAt _ _ _ _ xs1 x y z w px hx hy qz mo1)
      (let ((erased rest)) (morph-relax h P q q0 As Bs B d sa rb dh lq uh xs1 mo1))
      (match erased (in-dec x B) _
        ((OrL _ _ ib) (MOSkip h P q0 B xs1 x ib rest))
        ((OrR _ _ ob)
          (let ((erased oz)) (match erased (in-dec z As) (((NotIn z As) o))
            (absurd (OrL _ _ iz) (apart-irrefl x (notin-in x x B ob (pos-in h As x z B rb dh hx iz))))
            ((OrR _ _ o) o)))
          (let ((erased w0) (erased pw0)) (nth-exists _ q0 d z lq (under-nth h x z d uh hx)))
          (let-match erased (nth-fn _ q z w w0 qz (setall-miss q0 As Bs q z w0 sa oz pw0)) (Refl _ _))
          (MOAt h P q0 B xs1 x y z w px hx hy pw0 rest))))))

; Along a morphism h from P to q: P b is the position c of q (h b).
(def-fns _ $ (erased pull-step : (erased (List (Nat)) h P q ids) (erased (Nat) k b a z c) (erased (MorphOff h P q (Nil (Nat)) ids) mo) (erased (Iota k ids) io)
    (erased (Distinct h) dh) (erased (Length (Nat) h k) lh) (erased (Length (Nat) P k) lp) (erased (Nth (Nat) h b a) hb) (erased (Nth (Nat) q a z) pz)
    (erased (Nth (Nat) h c z) hc) -> (erased (Nth (Nat) P b c) r))
  (let ((erased lb)) (nth-lt-length _ h b k a hb lh))
  (let ((erased j) (erased pj)) (nth-exists _ P k b lp lb))
  (let ((erased w) (erased hj) (erased qw)) (morph h P q (Nil _) ids k b j a mo io lb (NotInNil b) pj hb))
  (let-match erased (nth-fn _ q a z w pz qw) (Refl _ _))
  (let-match erased (distinct-nth h j c z dh hj hc) (Refl _ _))
  pj)

; A walk along q through the darts R, all in the image of h, pulled back along a morphism from P to q.
(def-fns _ $ (erased fpath-pull : (erased (List (Nat)) h P q ids R) (erased (Nat) k a b y) (erased (MorphOff h P q (Nil (Nat)) ids) mo) (erased (Iota k ids) io)
    (erased (Distinct h) dh) (erased (Length (Nat) h k) lh) (erased (Length (Nat) P k) lp) (subterm erased (List (Nat)) B) (erased (Respects h B R) rb)
    (erased (Nth (Nat) h b a) hb) (erased (FPath q a R y) fp) -> (erased (Nat) y2) (erased (FPath P b B y2) fp2) (erased (Nth (Nat) h y2 y) hy))
  (let-match erased rb (RespCons _ B1 R1 c z hc rb1) ((RespNil _) (let-match erased fp (FPNil _ _)) (values b (FPNil P b) hb)))
  (let-match erased fp (FPCons _ _ _ _ _ pz fp1))
  (let ((erased y2) (erased fp2) (erased hy)) (fpath-pull h P q ids R1 k z c y mo io dh lh lp B1 rb1 hc fp1))
  (values y2 (FPCons P B1 b c y2 (pull-step h P q ids k b a z c mo io dh lh lp hb pz hc) fp2) hy))

(def-fns _ $ (erased ncyc-pull : (erased (List (Nat)) h P q ids R B) (erased (Nat) k) (erased (MorphOff h P q (Nil (Nat)) ids) mo) (erased (Iota k ids) io)
    (erased (Distinct h) dh) (erased (Length (Nat) h k) lh) (erased (Length (Nat) P k) lp) (erased (Respects h B R) rb) (erased (NCyc q R) nc)
    -> (erased (NCyc P B) r))
  (let-match erased nc (NCCons _ Rs r0 y fp back) ((NCNil _) (let-match erased rb (RespNil _)) (NCNil P)))
  (let-match erased rb (RespCons _ Bs _ b0 _ hb0 rb1))
  (let ((erased y2) (erased fp2) (erased hy)) (fpath-pull h P q ids Rs k r0 b0 y mo io dh lh lp Bs rb1 hb0 fp))
  (NCCons P Bs b0 y2 fp2 (pull-step h P q ids k y2 y r0 b0 mo io dh lh lp hy back hb0)))

; The ring links its darts in order: b follows a on r = a0 :: P, PP being P followed by a0, and e a is on the face of b.
(def-fns _ $ (erased rpath-in2 : (erased (List (Nat)) e f PP) (subterm erased (List (Nat)) P) (erased (Nat) a0 w ew c u v) (erased (RPath e f a0 P w) rp)
    (erased (Nth (Nat) e w ew) pw) (erased (SomePath f (Nil (Nat)) ew c) sw) (erased (HSnoc (Nat) P c PP) sn) (erased (In2 (Cons (Nat) a0 P) PP u v) i)
    -> (erased (Nat) eu) (erased (Nth (Nat) e u eu) pe) (erased (SomePath f (Nil (Nat)) eu v) sp))
  (let-match erased rp (RPCons _ _ P1 _ ea z _ pa wa rp1)
    ((RPNil _ _ _) (let-match erased sn (SnocNil _ _)) (let-match erased i (I2Here _ _ _ _) (absurd (I2There _ _ _ _ _ _ i1) (match erased i1 _))) (values ew pw sw)))
  (let-match erased sn (SnocCons _ _ _ _ PP1 sn1))
  (match erased i _
    ((I2Here _ _ _ _) (values ea pa wa))
    ((I2There _ _ _ _ _ _ i1) (rpath-in2 e f PP1 P1 z w ew c u v rp1 pw sw sn1 i1))))

(def-fns _ $ (erased ring-link : (erased (List (Nat)) e f p rr) (erased (Nat) x0 u v) (erased (Ring e f x0 p) rg) (erased (HSnoc (Nat) p x0 rr) sn)
    (erased (In2 (Cons (Nat) x0 p) rr u v) i) -> (erased (Nat) eu) (erased (Nth (Nat) e u eu) pe) (erased (SomePath f (Nil (Nat)) eu v) sp))
  (let-match erased rg (MkRing _ _ _ _ w ew rp pw sw sm))
  (rpath-in2 e f rr p x0 w ew x0 u v rp pw sw sn i))

(def-fns _ $ (erased sub-of-snoc : (erased (List (Nat)) R0 R2) (erased (Nat) y) (erased (HSnoc (Nat) R0 y R2) sn) (subterm erased (List (Nat)) m)
    (erased (Sub m (Cons (Nat) y R0)) sb) -> (erased (Sub m R2) r))
  (let-match erased sb (HSubCons x m1 _ ix sb1) ((HSubNil _) (HSubNil R2)))
  (HSubCons x m1 R2 (in-snoc x y R0 R2 sn ix) (sub-of-snoc R0 R2 y sn m1 sb1)))

(def-fns _ $ (erased revapp-sub : (erased (List (Nat)) r RV) (erased (RevApp (Nat) r (Nil (Nat)) RV) rv) (subterm erased (List (Nat)) m) (erased (Sub m RV) sb)
    -> (erased (Sub m r) res))
  (let-match erased sb (HSubCons x m1 _ ix sb1) ((HSubNil _) (HSubNil r)))
  (HSubCons x m1 r (match erased (revapp-out r (Nil _) RV x rv ix) _ ((OrL _ _ i) i) (absurd (OrR _ _ i) (match erased i _))) (revapp-sub r RV rv m1 sb1)))

(def-fns _ $ (erased revapp-sup : (erased (List (Nat)) r RV) (erased (RevApp (Nat) r (Nil (Nat)) RV) rv) (subterm erased (List (Nat)) m) (erased (Sub m r) sb)
    -> (erased (Sub m RV) res))
  (let-match erased sb (HSubCons x m1 _ ix sb1) ((HSubNil _) (HSubNil RV)))
  (HSubCons x m1 RV (revapp-in r (Nil _) RV x rv (OrL _ _ ix)) (revapp-sup r RV rv m1 sb1)))

(def-fns _ $ (erased ring-hd : (erased (Nat) d y x0) (erased (List (Nat)) e n f p hd zs) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) gen)
    (erased (Ring e f x0 p) rg) (erased (Under (Cons (Nat) x0 p) d) ur) (erased (DiskSplit d e n (Cons (Nat) x0 p) hd zs) ds) (erased (In y (Cons (Nat) x0 p)) iy)
    -> (erased (In y hd) r))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (let ((erased ly)) (under-in _ y d ur iy))
  (ds-mem d y x0 e n f p hd zs h gen rg ur ds (disk-ring d y n ni f _ pn iy ly) ly))

(def-fns _ $ (erased ring-sub-hd : (erased (Nat) d x0) (erased (List (Nat)) e n f p hd zs) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) gen)
    (erased (Ring e f x0 p) rg) (erased (Under (Cons (Nat) x0 p) d) ur) (erased (DiskSplit d e n (Cons (Nat) x0 p) hd zs) ds) (subterm erased (List (Nat)) m)
    (erased (Sub m (Cons (Nat) x0 p)) sb) -> (erased (Sub m hd) r))
  (let-match erased sb (HSubCons x m1 _ ix sb1) ((HSubNil _) (HSubNil hd)))
  (HSubCons x m1 hd (ring-hd d x x0 e n f p hd zs h gen rg ur ds ix) (ring-sub-hd d x0 e n f p hd zs h gen rg ur ds m1 sb1)))

(def-fns _ $ (erased off-hd : (erased (Nat) d y x0) (erased (List (Nat)) e n f p hd zs) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) gen)
    (erased (Ring e f x0 p) rg) (erased (Under (Cons (Nat) x0 p) d) ur) (erased (DiskSplit d e n (Cons (Nat) x0 p) hd zs) ds) (erased (NotIn y hd) oy)
    -> (erased (NotIn y (Cons (Nat) x0 p)) r))
  (match erased (in-dec y (Cons _ x0 p)) _
    (absurd (OrL _ _ iy) (apart-irrefl y (notin-in y y hd oy (ring-hd d y x0 e n f p hd zs h gen rg ur ds iy))))
    ((OrR _ _ o) o)))

(def-fns _ $ (erased disk-side-e : (erased (Nat) d x x0) (erased (List (Nat)) e n f p hd zs nf rr) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) gen)
    (erased (Ring e f x0 p) rg) (erased (Under (Cons (Nat) x0 p) d) ur) (erased (DiskSplit d e n (Cons (Nat) x0 p) hd zs) ds) (erased (HPerm d e nf) pe)
    (erased (Sub rr (Cons (Nat) x0 p)) srr) (erased (In x hd) ix) (erased (Lt x d) lx) -> (erased (Side e nf (Cons (Nat) x0 p) rr hd x) res))
  (let ((erased r)) (Cons _ x0 p))
  (let ((erased pei)) (perm-sym d e nf pe))
  (match erased (in-dec x r) _
    ((OrL _ _ ixr) (SideRing e nf r rr hd x ixr))
    ((OrR _ _ oxr)
      (let ((erased dx)) (ds-in d x x0 e n f p hd zs h gen rg ur ds ix))
      (let ((erased y) (erased py) (erased ly)) (perm-nth d x e nf pe lx))
      (let ((erased dy) (erased oy)) (disk-edge d x y x0 e n f p h gen rg dx oxr py))
      (let ((erased z) (erased pz) (erased lz)) (perm-nth d x nf e pei lx))
      (let ((erased dz) (erased oz)) (disk-edge-inv d z x x0 e n f p h gen rg dx oxr (perm-inv d x z nf e pei pz)))
      (SideOff e nf r rr hd x y z oxr (notin-sub x rr r srr oxr) py (ds-mem d y x0 e n f p hd zs h gen rg ur ds dy ly) (notin-sub y rr r srr oy)
        pz (ds-mem d z x0 e n f p hd zs h gen rg ur ds dz lz) oz))))

(def-fns _ $ (erased disk-side-n : (erased (Nat) d x x0) (erased (List (Nat)) e n f p hd zs ni) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) gen)
    (erased (Ring e f x0 p) rg) (erased (Under (Cons (Nat) x0 p) d) ur) (erased (DiskSplit d e n (Cons (Nat) x0 p) hd zs) ds) (erased (HPerm d n ni) pn)
    (erased (In x hd) ix) (erased (Lt x d) lx) -> (erased (Side n ni (Nil (Nat)) (Nil (Nat)) hd x) res))
  (let ((erased pni)) (perm-sym d n ni pn))
  (let ((erased dx)) (ds-in d x x0 e n f p hd zs h gen rg ur ds ix))
  (let ((erased y) (erased py) (erased ly)) (perm-nth d x n ni pn lx))
  (let ((erased z) (erased pz) (erased lz)) (perm-nth d x ni n pni lx))
  (SideOff n ni (Nil _) (Nil _) hd x y z (NotInNil x) (NotInNil x) py (ds-mem d y x0 e n f p hd zs h gen rg ur ds (disk-node d x y n ni f _ pn dx py) ly)
    (NotInNil y) pz (ds-mem d z x0 e n f p hd zs h gen rg ur ds (disk-pre n f _ x z dx (perm-inv d x z ni n pni pz)) lz) (NotInNil z)))

; The remainder darts hr: the reverse RV of r, then the darts off diskN.
(def-fns _ $ (erased absurd rem-out : (erased (Nat) d x x0) (erased (List (Nat)) e n f p hd zs RV hr) (erased (Hypermap d e n f) h)
    (erased (Genus d e n f (Zero)) gen) (erased (Ring e f x0 p) rg) (erased (Under (Cons (Nat) x0 p) d) ur) (erased (DiskSplit d e n (Cons (Nat) x0 p) hd zs) ds)
    (erased (RevApp (Nat) (Cons (Nat) x0 p) (Nil (Nat)) RV) rv) (erased (AppN RV zs hr) ap) (erased (In x hr) ix)
    (erased (DiskN n f (Cons (Nat) x0 p) x) dx) (erased (NotIn x (Cons (Nat) x0 p)) ox) -> (erased (False) fl))
  (match erased (app-in-inv RV zs hr x ap ix) _
    (absurd (OrL _ _ iv)
      (match erased (revapp-out _ (Nil _) RV x rv iv) _
        (absurd (OrL _ _ ir) (apart-irrefl x (notin-in x x _ ox ir)))
        (absurd (OrR _ _ i0) (match erased i0 _))))
    (absurd (OrR _ _ iz) (ds-out d x x0 e n f p hd zs h gen rg ur ds iz dx))))

(def-fns _ $ (erased rem-ring : (erased (List (Nat)) r RV zs hr) (erased (Nat) y) (erased (RevApp (Nat) r (Nil (Nat)) RV) rv) (erased (AppN RV zs hr) ap)
    (erased (In y r) iy) -> (erased (In y hr) res))
  (app-in-l RV zs hr y ap (revapp-in r (Nil _) RV y rv (OrL _ _ iy))))

(def-fns _ $ (erased rem-off : (erased (Nat) d y) (erased (List (Nat)) e n r hd zs RV hr) (erased (DiskSplit d e n r hd zs) ds) (erased (AppN RV zs hr) ap)
    (erased (Lt y d) ly) (erased (NotIn y hd) oy) -> (erased (In y hr) res))
  (let ((erased ids) (erased io) (erased sp)) (ds-split d e n r hd zs ds))
  (match erased (split-cover hd ids hd zs y sp (iota-in d y ids io ly)) _
    (absurd (OrL _ _ ih) (apart-irrefl y (notin-in y y hd oy ih)))
    ((OrR _ _ iz) (app-in-r RV zs hr y ap iz))))

(def-fns _ $ (erased rem-side-e : (erased (Nat) d x x0) (erased (List (Nat)) e n f p hd zs nf RV hr) (erased (Hypermap d e n f) h)
    (erased (Genus d e n f (Zero)) gen) (erased (Ring e f x0 p) rg) (erased (Under (Cons (Nat) x0 p) d) ur) (erased (DiskSplit d e n (Cons (Nat) x0 p) hd zs) ds)
    (erased (HPerm d e nf) pe) (erased (RevApp (Nat) (Cons (Nat) x0 p) (Nil (Nat)) RV) rv) (erased (AppN RV zs hr) ap) (erased (In x hr) ix) (erased (Lt x d) lx)
    -> (erased (Side e nf (Nil (Nat)) (Nil (Nat)) hr x) res))
  (let ((erased r)) (Cons _ x0 p))
  (let ((erased pei)) (perm-sym d e nf pe))
  (let ((erased y) (erased py) (erased ly)) (perm-nth d x e nf pe lx))
  (let ((erased z) (erased pz) (erased lz)) (perm-nth d x nf e pei lx))
  (let ((erased pez)) (perm-inv d x z nf e pei pz))
  (SideOff e nf (Nil _) (Nil _) hr x y z (NotInNil x) (NotInNil x) py
    (match erased (in-dec y r) (((In y hr) res))
      ((OrL _ _ iy) (rem-ring r RV zs hr y rv ap iy))
      ((OrR _ _ oy)
        (rem-off d y e n r hd zs RV hr ds ap ly
          (match erased (in-dec y hd) (((NotIn y hd) res))
            (absurd (OrL _ _ iyh)
              (let ((erased dx) (erased ox)) (disk-edge-inv d x y x0 e n f p h gen rg (ds-in d y x0 e n f p hd zs h gen rg ur ds iyh) oy py))
              (rem-out d x x0 e n f p hd zs RV hr h gen rg ur ds rv ap ix dx ox))
            ((OrR _ _ o) o)))))
    (NotInNil y) pz
    (match erased (in-dec z r) (((In z hr) res))
      ((OrL _ _ iz) (rem-ring r RV zs hr z rv ap iz))
      ((OrR _ _ oz)
        (rem-off d z e n r hd zs RV hr ds ap lz
          (match erased (in-dec z hd) (((NotIn z hd) res))
            (absurd (OrL _ _ izh)
              (let ((erased dx) (erased ox)) (disk-edge d z x x0 e n f p h gen rg (ds-in d z x0 e n f p hd zs h gen rg ur ds izh) oz pez))
              (rem-out d x x0 e n f p hd zs RV hr h gen rg ur ds rv ap ix dx ox))
            ((OrR _ _ o) o)))))
    (NotInNil z)))

(def-fns _ $ (erased rem-side-n : (erased (Nat) d x x0 v0) (erased (List (Nat)) e n f p hd zs ni V RVR hr) (erased (Hypermap d e n f) h)
    (erased (Genus d e n f (Zero)) gen) (erased (Ring e f x0 p) rg) (erased (Under (Cons (Nat) x0 p) d) ur) (erased (DiskSplit d e n (Cons (Nat) x0 p) hd zs) ds)
    (erased (HPerm d n ni) pn) (erased (RevApp (Nat) (Cons (Nat) x0 p) (Nil (Nat)) (Cons (Nat) v0 V)) rv) (erased (AppN (Cons (Nat) v0 V) zs hr) ap)
    (erased (HSnoc (Nat) V v0 RVR) sn) (erased (In x hr) ix) (erased (Lt x d) lx) -> (erased (Side n ni (Cons (Nat) v0 V) RVR hr x) res))
  (let ((erased r)) (Cons _ x0 p))
  (let ((erased RV)) (Cons _ v0 V))
  (let ((erased pni)) (perm-sym d n ni pn))
  (let ((erased svr)) (revapp-sub r RV rv RV (sub-refl RV)))
  (let ((erased srv)) (snoc-sub V RVR v0 sn))
  (match erased (in-dec x RV) _
    ((OrL _ _ ixv) (SideRing n ni RV RVR hr x ixv))
    ((OrR _ _ oxv)
      (let ((erased oxr)) (match erased (in-dec x r) (((NotIn x r) res))
        (absurd (OrL _ _ ixr) (apart-irrefl x (notin-in x x RV oxv (revapp-in r (Nil _) RV x rv (OrL _ _ ixr)))))
        ((OrR _ _ o) o)))
      (let ((erased y) (erased py) (erased ly)) (perm-nth d x n ni pn lx))
      (let ((erased z) (erased pz) (erased lz)) (perm-nth d x ni n pni lx))
      (let ((erased pnz)) (perm-inv d x z ni n pni pz))
      (let ((erased oyh)) (match erased (in-dec y hd) (((NotIn y hd) res))
        (absurd (OrL _ _ iyh)
          (rem-out d x x0 e n f p hd zs RV hr h gen rg ur ds rv ap ix (disk-pre n f r y x (ds-in d y x0 e n f p hd zs h gen rg ur ds iyh) py) oxr))
        ((OrR _ _ o) o)))
      (let ((erased ozh)) (match erased (in-dec z hd) (((NotIn z hd) res))
        (absurd (OrL _ _ izh)
          (rem-out d x x0 e n f p hd zs RV hr h gen rg ur ds rv ap ix (disk-node d z x n ni f r pn (ds-in d z x0 e n f p hd zs h gen rg ur ds izh) pnz) oxr))
        ((OrR _ _ o) o)))
      (SideOff n ni RV RVR hr x y z oxv (notin-sub x RVR RV srv oxv) py (rem-off d y e n r hd zs RV hr ds ap ly oyh)
        (notin-sub y RVR r (sub-trans RVR RV r srv svr) (off-hd d y x0 e n f p hd zs h gen rg ur ds oyh)) pz (rem-off d z e n r hd zs RV hr ds ap lz ozh)
        (notin-sub z RV r svr (off-hd d z x0 e n f p hd zs h gen rg ur ds ozh))))))
