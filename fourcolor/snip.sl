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
