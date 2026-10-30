; More of revsnip.v, for plain maps: the faces and disks of the reverse ring, nontrivial rings and the chord rings. Load after
; revsnip.sl.

(def-fns _ $ (erased some-cat : (erased (List (Nat)) f) (erased (Nat) x y z) (erased (SomePath f (Nil (Nat)) x y) p) (erased (SomePath f (Nil (Nat)) y z) q)
    -> (erased (SomePath f (Nil (Nat)) x z) r))
  (let-match erased p (MkSomePath _ _ xs _ _ w))
  (let-match erased q (MkSomePath _ _ ys _ _ v))
  (let ((erased zs) (erased u)) (path-cat f (Nil _) xs ys x y z w v))
  (MkSomePath f (Nil _) zs x z u))

; Every dart of B is on the face of a dart of A.
(def-adts $ (FaceSub : ((List (Nat)) f B A) -> Type)
  enum
  (many FSNil : (erased (List (Nat)) f A) -> (FaceSub f (Nil (Nat)) A))
  (many FSCons : (erased (List (Nat)) f B A) (erased (Nat) b a) (erased (In a A) ia) (erased (SomePath f (Nil (Nat)) b a) sp) (erased (FaceSub f B A) rest)
      -> (FaceSub f (Cons (Nat) b B) A)))

(def-fns _ $ (erased facesub-at : (erased (List (Nat)) f B A) (erased (Nat) b) (subterm erased (FaceSub f B A) fs) (erased (In b B) ib)
    -> (erased (Nat) a) (erased (In a A) ia) (erased (SomePath f (Nil (Nat)) b a) sp))
  (let-match erased fs (FSCons _ Bt _ b1 a ia sp fs1) (absurd (FSNil _ _) ib))
  (match erased ib _ ((InHere _ _) (values a ia sp)) ((InThere _ _ _ ib1) (facesub-at f Bt A b fs1 ib1))))

; fband B is part of fband A.
(def-fns _ $ (erased fband-sub : (erased (List (Nat)) f B A) (erased (Nat) x) (erased (FaceSub f B A) fs) (erased (Fband f B x) fb) -> (erased (Fband f A x) r))
  (let-match erased fb (MkFband _ _ _ y iy w))
  (let ((erased a) (erased ia) (erased sp)) (facesub-at f B A y fs iy))
  (MkFband f A x a ia (some-cat f x y a w sp)))

(def-fns _ $ (erased labs-sub : (erased (List (Nat)) f A lab lsA) (erased (Nat) d) (subterm erased (List (Nat)) B) (erased (FaceSub f B A) fs)
    (erased (Respects lab f lab) rf) (erased (Respects lab A lsA) ra) (erased (Under B d) ub) (erased (Length (Nat) lab d) ll)
    -> (erased (List (Nat)) lsB) (erased (Respects lab B lsB) rb) (erased (Sub lsB lsA) sb))
  (let-match erased fs (FSCons _ Bt _ b a ia sp fs1) ((FSNil _ _) (values (Nil _) (RespNil lab) (HSubNil lsA))))
  (let-match erased ub (UnderCons _ _ _ lb ub1))
  (let ((erased l) (erased pl)) (nth-exists _ lab d b ll lb))
  (let-match erased sp (MkSomePath _ _ xs _ _ w))
  (let ((erased lsB1) (erased rb1) (erased sb1)) (labs-sub f A lab lsA d Bt fs1 rf ra ub1 ll))
  (values (Cons _ l lsB1) (RespCons lab Bt lsB1 b l pl rb1)
    (HSubCons l lsB1 lsA (in-map lab A lsA a l ia ra (path-label f lab (Nil _) xs b a l w rf pl)) sb1)))

; kernel A is part of kernel B.
(def-fns _ $ (erased kernel-sub : (erased (List (Nat)) f B A) (erased (Nat) d x) (erased (FaceSub f B A) fs) (erased (Under B d) ub) (erased (Length (Nat) f d) lf)
    (erased (Kernel f A x) k) -> (erased (Kernel f B x) r))
  (let-match erased k (MkKernel _ _ lab lsA _ l rf ra px ol))
  (let ((erased lsB) (erased rb) (erased sb)) (labs-sub f A lab lsA d B fs rf ra ub (respects-length lab f lab d rf lf)))
  (MkKernel f B lab lsB x l rf rb px (notin-sub l lsB lsA sb ol)))

; A dart u of RR = rev (map e r) is on the face of the dart after e u on r, and a dart a of r on the face of the edge image of the
; dart before it, which is on RR.
(def-fns _ $ (erased rev-face : (erased (Nat) d x0 u) (erased (List (Nat)) e n f p er RR) (erased (Hypermap d e n f) h) (erased (AllOrder d e (Succ (Succ (Zero)))) pl)
    (erased (Ring e f x0 p) rg) (erased (Respects e (Cons (Nat) x0 p) er) rm) (erased (RevApp (Nat) er (Nil (Nat)) RR) ra) (erased (In u RR) iu)
    -> (erased (Nat) a2) (erased (In a2 (Cons (Nat) x0 p)) ia) (erased (SomePath f (Nil (Nat)) u a2) sp))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased a) (erased pa) (erased ia)) (rev-ring-in d u e _ er RR pl le rm ra iu))
  (let ((erased m) (erased lr)) (length-exists _ (Cons _ x0 p)))
  (let ((erased rr) (erased sn)) (snoc-exists _ p x0))
  (let ((erased lr2)) lr)
  (let-match erased lr2 (LengthCons _ _ _ m1 lp))
  (let ((erased a2) (erased ia2)) (in2-exists _ rr a m ia lr (snoc-length _ p rr x0 m1 sn lp)))
  (let ((erased ea) (erased pea) (erased spa)) (ring-link e f p rr x0 a a2 rg sn ia2))
  (let ((erased pa2) (erased na)) (plain-eq d u a e pl (nth-lt-length _ e u d a pa le) pa))
  (let-match erased (nth-fn _ e a u ea pa2 pea) (Refl _ _))
  (values a2 (sub-in rr _ a2 (snoc-sub p rr x0 sn) (in2-in-left rr _ a2 a (in2-sym _ rr a a2 ia2))) spa))

(def-fns _ $ (erased ring-face : (erased (Nat) d x0 a) (erased (List (Nat)) e n f p er RR) (erased (Hypermap d e n f) h) (erased (AllOrder d e (Succ (Succ (Zero)))) pl)
    (erased (Ring e f x0 p) rg) (erased (Respects e (Cons (Nat) x0 p) er) rm) (erased (RevApp (Nat) er (Nil (Nat)) RR) ra) (erased (In a (Cons (Nat) x0 p)) ia)
    -> (erased (Nat) u) (erased (In u RR) iu) (erased (SomePath f (Nil (Nat)) a u) sp))
  (let ((erased r)) (Cons _ x0 p))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased m) (erased lr)) (length-exists _ r))
  (let ((erased rr) (erased sn)) (snoc-exists _ p x0))
  (let ((erased lr2)) lr)
  (let-match erased lr2 (LengthCons _ _ _ m1 lp))
  (let ((erased a1) (erased j2)) (in2-exists rr _ a m (sub-in r rr a (sub-of-snoc p rr x0 sn r (sub-refl r)) ia) (snoc-length _ p rr x0 m1 sn lp) lr))
  (let ((erased j3)) (in2-sym rr r a a1 j2))
  (let ((erased u) (erased pu) (erased sp)) (ring-link e f p rr x0 a1 a rg sn j3))
  (let ((erased ia1)) (in2-in-left r rr a1 a j3))
  (let ((erased pu2) (erased nu)) (plain-eq d a1 u e pl (nth-lt-length _ e a1 d u pu le) pu))
  (values u (ring-rev-in d u a1 e r er RR pl le rm ra pu2 ia1) (some-sym d u a f fi pf sp (nth-lt-length _ e u d a1 pu2 le))))

(def-fns _ $ (erased facesub-rev : (erased (Nat) d x0) (erased (List (Nat)) e n f p er RR) (erased (Hypermap d e n f) h) (erased (AllOrder d e (Succ (Succ (Zero)))) pl)
    (erased (Ring e f x0 p) rg) (erased (Respects e (Cons (Nat) x0 p) er) rm) (erased (RevApp (Nat) er (Nil (Nat)) RR) ra) (subterm erased (List (Nat)) B)
    (erased (Sub B RR) sb) -> (erased (FaceSub f B (Cons (Nat) x0 p)) r))
  (let-match erased sb (HSubCons b Bt _ ib sb1) ((HSubNil _) (FSNil f _)))
  (let ((erased a) (erased ia) (erased sp)) (rev-face d x0 b e n f p er RR h pl rg rm ra ib))
  (FSCons f Bt _ b a ia sp (facesub-rev d x0 e n f p er RR h pl rg rm ra Bt sb1)))

(def-fns _ $ (erased facesub-ring : (erased (Nat) d x0) (erased (List (Nat)) e n f p er RR) (erased (Hypermap d e n f) h) (erased (AllOrder d e (Succ (Succ (Zero)))) pl)
    (erased (Ring e f x0 p) rg) (erased (Respects e (Cons (Nat) x0 p) er) rm) (erased (RevApp (Nat) er (Nil (Nat)) RR) ra) (subterm erased (List (Nat)) B)
    (erased (Sub B (Cons (Nat) x0 p)) sb) -> (erased (FaceSub f B RR) r))
  (let-match erased sb (HSubCons b Bt _ ib sb1) ((HSubNil _) (FSNil f _)))
  (let ((erased u) (erased iu) (erased sp)) (ring-face d x0 b e n f p er RR h pl rg rm ra ib))
  (FSCons f Bt _ b u iu sp (facesub-ring d x0 e n f p er RR h pl rg rm ra Bt sb1)))

(def-fns _ $ (erased ring-under : (erased (Nat) d x0) (erased (List (Nat)) e n f p) (erased (Hypermap d e n f) h) (erased (Ring e f x0 p) rg)
    -> (erased (Under (Cons (Nat) x0 p) d) ur))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let-match erased rg (MkRing _ _ _ _ w ew rp pw sw sm))
  (let-match erased sm (MkSimple _ _ lab ls rf rl dl))
  (resp-under lab ls d (Cons _ x0 p) rl (respects-length lab f lab d rf lf)))

; fband_rev_ring and its kernel form: RR and r are each on the faces of the other.
(def-fns _ $ (erased rev-subs : (erased (Nat) d x0) (erased (List (Nat)) e n f p er RR) (erased (Hypermap d e n f) h) (erased (AllOrder d e (Succ (Succ (Zero)))) pl)
    (erased (Ring e f x0 p) rg) (erased (Respects e (Cons (Nat) x0 p) er) rm) (erased (RevApp (Nat) er (Nil (Nat)) RR) ra)
    -> (erased (FaceSub f RR (Cons (Nat) x0 p)) a) (erased (FaceSub f (Cons (Nat) x0 p) RR) b) (erased (Under (Cons (Nat) x0 p) d) ur) (erased (Under RR d) uR))
  (let ((erased r)) (Cons _ x0 p))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (values (facesub-rev d x0 e n f p er RR h pl rg rm ra RR (sub-refl RR)) (facesub-ring d x0 e n f p er RR h pl rg rm ra r (sub-refl r))
    (ring-under d x0 e n f p h rg) (revapp-under er (Nil _) RR d ra (respects-under-vals e r er d rm (perm-under d e nf pe)) (UnderNil d))))

; The darts of xs lie on distinct faces, none of them the face of a dart of r: a labelling constant along f gives them distinct
; labels, none of them that of a dart of r.
(def-adts $ (Scattered : ((List (Nat)) f r xs) -> Type)
  enum
  (many MkScattered : (erased (List (Nat)) f r xs lab lr lx) (erased (Respects lab f lab) rf) (erased (Respects lab r lr) rr) (erased (Respects lab xs lx) rx)
      (erased (Distinct lx) dx) (erased (Disj lx lr) dj) -> (Scattered f r xs)))

(def-fns _ $ (erased scattered-sub : (erased (List (Nat)) f B A xs) (erased (Nat) d) (erased (FaceSub f B A) fs) (erased (Under B d) ub) (erased (Length (Nat) f d) lf)
    (erased (Scattered f A xs) sp) -> (erased (Scattered f B xs) r))
  (let-match erased sp (MkScattered _ _ _ lab lA lx rf ra rx dx dj))
  (let ((erased lB) (erased rb) (erased sb)) (labs-sub f A lab lA d B fs rf ra ub (respects-length lab f lab d rf lf)))
  (MkScattered f B xs lab lB lx rf rb rx dx (disj-sub lA lB lx dj sb)))

; nontrivial_ring m r: m < fcard face (diskF r) and m < fcard face (diskFC r), read as m + 1 darts of each on distinct faces, the
; darts of diskN r and those off it given by a DiskSplit. That this matches Coq's fcard has been checked only by reading.
(def-adts $ (NonTrivial : ((Nat) d) ((List (Nat)) e n f r) ((Nat) m) -> Type)
  enum
  (many MkNonTrivial : (erased (Nat) d m) (erased (List (Nat)) e n f r hd zs xs ys) (erased (DiskSplit d e n r hd zs) ds)
      (erased (Length (Nat) xs (Succ m)) lx) (erased (Length (Nat) ys (Succ m)) ly) (erased (Sub xs hd) sx) (erased (Sub ys zs) sy)
      (erased (Scattered f r xs) px) (erased (Scattered f r ys) py) -> (NonTrivial d e n f r m)))

(def-fns _ $ (erased ds-lt : (erased (Nat) d x) (erased (List (Nat)) e n r hd zs) (erased (DiskSplit d e n r hd zs) ds) (erased (HOr (In x hd) (In x zs)) ix)
    -> (erased (Lt x d) lx))
  (let ((erased ids) (erased io) (erased sp)) (ds-split d e n r hd zs ds))
  (let ((erased sa) (erased sb)) (split-sub hd ids hd zs sp))
  (under-in ids x d (perm-under d ids ids (perm-id d ids io))
    (match erased ix (((In x ids) res)) ((OrL _ _ i) (sub-in hd ids x sa i)) ((OrR _ _ i) (sub-in zs ids x sb i)))))

; With e x0 = y on r = x0 :: y, every dart a clink path reaches from diskN r is in diskN r.
(def-fns _ $ (erased pair-disk : (erased (Nat) d x0 y a b) (erased (List (Nat)) e n f L) (erased (Hypermap d e n f) h) (erased (AllOrder d e (Succ (Succ (Zero)))) pl)
    (erased (Nth (Nat) e x0 y) pxy) (subterm erased (CPath n f a L b) cp) (erased (DiskN n f (Cons (Nat) x0 (Cons (Nat) y (Nil (Nat)))) a) da)
    -> (erased (DiskN n f (Cons (Nat) x0 (Cons (Nat) y (Nil (Nat)))) b) db))
  (let ((erased r)) (Cons _ x0 (Cons _ y (Nil _))))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pe) (erased pn) (erased pf2)) (hyper-core d e n f h))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (match erased cp _
    ((CPNil _ _ _) da)
    ((CPNode _ _ L1 _ c _ pnc cp1) (pair-disk d x0 y c b e n f L1 h pl pxy cp1 (disk-pre n f r a c da pnc)))
    ((CPFace _ _ L1 _ c _ pf cp1)
      (pair-disk d x0 y c b e n f L1 h pl pxy cp1
        (match erased (in-dec a r) (((DiskN n f r c) res))
          ((OrR _ _ o) (disk-step n f r a c da (DPFace n f r a c c o pf (DPNil n f r c))))
          ((OrL _ _ ia)
            (let ((erased la)) (nth-lt-length _ f a d c pf lf))
            (let ((erased ea) (erased pea) (erased lea)) (perm-nth d a e nf pe la))
            (let ((erased pea2) (erased nea)) (plain-eq d a ea e pl la pea))
            (let ((erased iea)) (match erased ia (((In ea r) res))
              ((InHere _ _) (let-match erased (nth-fn _ e x0 y ea pxy pea) (Refl _ _)) (InThere ea x0 _ (InHere ea (Nil _))))
              ((InThere _ _ _ ia1)
                (let-match erased ia1 (InHere _ _) (absurd (InThere _ _ _ i) (match erased i _)))
                (let ((erased pyx) (erased nyx)) (plain-eq d x0 y e pl (nth-lt-length _ e x0 d y pxy le) pxy))
                (let-match erased (nth-fn _ e y x0 ea pyx pea) (Refl _ _))
                (InHere ea _))))
            (MkDiskN n f r c ea c iea (hyper-node d c a ea e n f h pf pea2) (DPNil n f r c))))))))

; nontrivial_ring_proper.
(def-fns _ $ (erased nontrivial-proper : (erased (Nat) d x0 m) (erased (List (Nat)) e n f p) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) gen)
    (erased (Bridgeless d e n f) b) (erased (AllOrder d e (Succ (Succ (Zero)))) pl) (erased (Connected d e n f) cn) (erased (Ring e f x0 p) rg)
    (erased (NonTrivial d e n f (Cons (Nat) x0 p) m) nt) -> (erased (Proper e (Cons (Nat) x0 p)) pr))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased rg1)) rg)
  (let-match erased rg1 (MkRing _ _ _ _ w ew rp pw sw sm))
  (match erased p (((Proper e (Cons (Nat) x0 p)) res))
    (absurd (Nil _)
      (let-match erased rp (RPNil _ _ _))
      (let-match erased (some-sym d ew x0 f fi pf sw (perm-val d x0 ew e nf pe pw)) (MkSomePath _ _ xs _ _ w2))
      (bridgeless-face d x0 ew e n f (Nil _) xs b pw w2))
    ((Cons _ y p1)
      (let-match erased rp (RPCons _ _ _ _ ex0 _ _ pex0 _ _))
      (let-match erased p1 (Nil _) ((Cons _ z p2) (ProperBig e p2 x0 y z)))
      (match erased (nat-eq ex0 y) _
        ((Unequal _ _ _ _ ne) (ProperTwo e x0 y ex0 pex0 ne))
        (absurd (Equal _ _ _)
          (let ((erased r)) (Cons _ x0 (Cons _ y (Nil _))))
          (let-match erased nt (MkNonTrivial _ _ _ _ _ _ hd zs xs ys ds lx ly sx sy px py))
          (let-match erased ly (LengthCons _ y0 ys1 _ ly1))
          (let ((erased iy0)) (sub-in ys zs y0 sy (InHere y0 ys1)))
          (let ((erased lx0)) (nth-lt-length _ e x0 d ex0 pex0 le))
          (let ((erased L) (erased cp)) (connected-clink d x0 y0 e n f h cn lx0 (ds-lt d y0 e n r hd zs ds (OrR _ _ iy0))))
          (ds-out d y0 x0 e n f p hd zs h gen rg (ring-under d x0 e n f p h rg) ds iy0
            (pair-disk d x0 y x0 y0 e n f L h pl pex0 cp (disk-ring d x0 n ni f r pn (InHere x0 _) lx0))))))))

; A dart off the diskN part hdX of one DiskSplit is in the other part zsB of any other.
(def-fns _ $ (erased ds-off : (erased (Nat) d x x0) (erased (List (Nat)) e n f p hdX zsX hdB zsB) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) gen)
    (erased (Ring e f x0 p) rg) (erased (Under (Cons (Nat) x0 p) d) ur) (erased (DiskSplit d e n (Cons (Nat) x0 p) hdX zsX) dsX)
    (erased (DiskSplit d e n (Cons (Nat) x0 p) hdB zsB) dsB) (erased (NotIn x hdX) o) (erased (Lt x d) lx) -> (erased (In x zsB) iz))
  (let ((erased ids) (erased io) (erased sp)) (ds-split d e n _ hdB zsB dsB))
  (match erased (split-cover hdB ids hdB zsB x sp (iota-in d x ids io lx)) _
    (absurd (OrL _ _ i)
      (apart-irrefl x (notin-in x x hdX o (ds-mem d x x0 e n f p hdX zsX h gen rg ur dsX (ds-in d x x0 e n f p hdB zsB h gen rg ur dsB i) lx))))
    ((OrR _ _ i) i)))

; Darts of diskN r are off diskN RR, and darts off diskN r are in diskN RR, whatever DiskSplits name them.
(def-fns _ $ (erased rev-sub-in : (erased (Nat) d) (erased (List (Nat)) e n f r RR hd hd2 hdA zsA hdB zsB) (erased (RevCtx d e n f r RR hd hd2) cx)
    (erased (Connected d e n f) cn) (erased (DiskSplit d e n r hdA zsA) dsA) (erased (DiskSplit d e n RR hdB zsB) dsB) (subterm erased (List (Nat)) xs)
    (erased (Sub xs hdA) sx) -> (erased (Sub xs zsB) res))
  (let-match erased sx (HSubCons x xs1 _ ix sx1) ((HSubNil _) (HSubNil zsB)))
  (let ((erased cx2)) cx)
  (let-match erased cx2 (MkRevCtx _ x0 y0 _ _ _ p Q er _ zs _ zs2 h gen pl rg pr ur ds rm ra rg2 pr2 ur2 ds2))
  (let ((erased lx)) (ds-lt d x e n r hdA zsA dsA (OrL _ _ ix)))
  (let ((erased dn)) (ds-in d x x0 e n f p hdA zsA h gen rg ur dsA ix))
  (HSubCons x xs1 zsB
    (match erased (rev-disk d x e n f r RR hd hd2 cx cn lx) (((In x zsB) res))
      ((TwoR _ _ _ _ _ _ _ _ o) (ds-off d x y0 e n f Q hd2 zs2 hdB zsB h gen rg2 ur2 ds2 dsB o lx))
      (absurd (TwoRR _ _ _ _ _ _ _ _ o) (apart-irrefl x (notin-in x x hd o (ds-mem d x x0 e n f p hd zs h gen rg ur ds dn lx)))))
    (rev-sub-in d e n f r RR hd hd2 hdA zsA hdB zsB cx cn dsA dsB xs1 sx1)))

(def-fns _ $ (erased rev-sub-out : (erased (Nat) d) (erased (List (Nat)) e n f r RR hd hd2 hdA zsA hdB zsB) (erased (RevCtx d e n f r RR hd hd2) cx)
    (erased (Connected d e n f) cn) (erased (DiskSplit d e n r hdA zsA) dsA) (erased (DiskSplit d e n RR hdB zsB) dsB) (subterm erased (List (Nat)) ys)
    (erased (Sub ys zsA) sy) -> (erased (Sub ys hdB) res))
  (let-match erased sy (HSubCons y ys1 _ iy sy1) ((HSubNil _) (HSubNil hdB)))
  (let ((erased cx2)) cx)
  (let-match erased cx2 (MkRevCtx _ x0 y0 _ _ _ p Q er _ zs _ zs2 h gen pl rg pr ur ds rm ra rg2 pr2 ur2 ds2))
  (let ((erased ly)) (ds-lt d y e n r hdA zsA dsA (OrR _ _ iy)))
  (HSubCons y ys1 hdB
    (match erased (rev-disk d y e n f r RR hd hd2 cx cn ly) (((In y hdB) res))
      (absurd (TwoR _ _ _ _ _ _ _ dn _) (ds-out d y x0 e n f p hdA zsA h gen rg ur dsA iy dn))
      ((TwoRR _ _ _ _ _ _ _ dn _) (ds-mem d y y0 e n f Q hdB zsB h gen rg2 ur2 dsB dn ly)))
    (rev-sub-out d e n f r RR hd hd2 hdA zsA hdB zsB cx cn dsA dsB ys1 sy1)))

; nontrivial_rev_ring.
(def-fns _ $ (erased nontrivial-rev : (erased (Nat) d m) (erased (List (Nat)) e n f r RR hd hd2) (erased (RevCtx d e n f r RR hd hd2) cx)
    (erased (Connected d e n f) cn) (erased (NonTrivial d e n f r m) nt) -> (erased (NonTrivial d e n f RR m) res))
  (let ((erased cx2)) cx)
  (let-match erased cx2 (MkRevCtx _ x0 y0 _ _ _ p Q er _ zs _ zs2 h gen pl rg pr ur ds rm ra rg2 pr2 ur2 ds2))
  (let-match erased nt (MkNonTrivial _ _ _ _ _ _ hdA zsA xs ys dsA lx ly sx sy px py))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased fa) (erased fb) (erased ur1) (erased uR)) (rev-subs d x0 e n f p er RR h pl rg rm ra))
  (MkNonTrivial d m e n f RR hd2 zs2 ys xs ds2 ly lx (rev-sub-out d e n f r RR hd hd2 hdA zsA hd2 zs2 cx cn dsA ds2 ys sy)
    (rev-sub-in d e n f r RR hd hd2 hdA zsA hd2 zs2 cx cn dsA ds2 xs sx) (scattered-sub f RR r ys d fa uR lf py) (scattered-sub f RR r xs d fa uR lf px)))

(def-fns _ $ (erased kernel-face : (erased (List (Nat)) f r) (erased (Nat) x y) (erased (Kernel f r x) k) (erased (Nth (Nat) f x y) pf) -> (erased (Kernel f r y) res))
  (let-match erased k (MkKernel _ _ lab ls _ l rf rp px ol))
  (MkKernel f r lab ls y l rf rp (respects-nth lab f lab x y l rf pf px) ol))

(def-fns _ $ (erased kernel-face-inv : (erased (Nat) d x y) (erased (List (Nat)) f r) (erased (Length (Nat) f d) lf) (erased (Kernel f r y) k) (erased (Nth (Nat) f x y) pf)
    -> (erased (Kernel f r x) res))
  (let-match erased k (MkKernel _ _ lab ls _ l rf rp py ol))
  (let ((erased l2) (erased px)) (nth-exists _ lab d x (respects-length lab f lab d rf lf) (nth-lt-length _ f x d y pf lf)))
  (let-match erased (nth-fn _ lab y l l2 py (respects-nth lab f lab x y l2 rf pf px)) (Refl _ _))
  (MkKernel f r lab ls x l rf rp px ol))

; diskFC_face, with diskFC r read as the darts zs off diskN r that are on no face of r: it is closed under face, both ways.
(def-fns _ $ (erased diskfc-face : (erased (Nat) d x y x0) (erased (List (Nat)) e n f p hd zs) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) gen)
    (erased (Ring e f x0 p) rg) (erased (DiskSplit d e n (Cons (Nat) x0 p) hd zs) ds) (erased (In x zs) iz) (erased (Kernel f (Cons (Nat) x0 p) x) k)
    (erased (Nth (Nat) f x y) pf) -> (erased (In y zs) iy) (erased (Kernel f (Cons (Nat) x0 p) y) ky))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pe) (erased pn) (erased pmf)) (hyper-core d e n f h))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased ur)) (ring-under d x0 e n f p h rg))
  (let ((erased ky)) (kernel-face f _ x y k pf))
  (let ((erased ly)) (perm-val d x y f fi pmf pf))
  (values
    (match erased (in-dec y hd) (((In y zs) res))
      (absurd (OrL _ _ i)
        (let-match erased (diskf-face-inv d x y n f fi _ pmf (MkDiskF n f _ y (ds-in d y x0 e n f p hd zs h gen rg ur ds i) ky) pf) (MkDiskF _ _ _ _ dx _))
        (ds-out d x x0 e n f p hd zs h gen rg ur ds iz dx))
      ((OrR _ _ o) (ds-off d y x0 e n f p hd zs hd zs h gen rg ur ds ds o ly)))
    ky))

(def-fns _ $ (erased diskfc-face-inv : (erased (Nat) d x y x0) (erased (List (Nat)) e n f p hd zs) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) gen)
    (erased (Ring e f x0 p) rg) (erased (DiskSplit d e n (Cons (Nat) x0 p) hd zs) ds) (erased (In y zs) iz) (erased (Kernel f (Cons (Nat) x0 p) y) k)
    (erased (Nth (Nat) f x y) pf) -> (erased (In x zs) ix) (erased (Kernel f (Cons (Nat) x0 p) x) kx))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased ur)) (ring-under d x0 e n f p h rg))
  (let ((erased kx)) (kernel-face-inv d x y f _ lf k pf))
  (let ((erased lx)) (nth-lt-length _ f x d y pf lf))
  (values
    (match erased (in-dec x hd) (((In x zs) res))
      (absurd (OrL _ _ i)
        (let-match erased (diskf-face n f _ x y (MkDiskF n f _ x (ds-in d x x0 e n f p hd zs h gen rg ur ds i) kx) pf) (MkDiskF _ _ _ _ dy _))
        (ds-out d y x0 e n f p hd zs h gen rg ur ds iz dy))
      ((OrR _ _ o) (ds-off d x x0 e n f p hd zs hd zs h gen rg ur ds ds o lx)))
    kx))

; diskN_rot and fband_rot: diskN and fband depend only on the darts of the ring.
(def-fns _ $ (erased dpath-move : (erased (List (Nat)) n f r s) (erased (Nat) x y) (subterm erased (DPath n f r x y) dp) (erased (Sub s r) sb) -> (erased (DPath n f s x y) res))
  (match erased dp _
    ((DPNil _ _ _ _) (DPNil n f s x))
    ((DPNode _ _ _ _ z _ o pn dp1) (DPNode n f s x z y (notin-sub x s r sb o) pn (dpath-move n f r s z y dp1 sb)))
    ((DPFace _ _ _ _ z _ o pf dp1) (DPFace n f s x z y (notin-sub x s r sb o) pf (dpath-move n f r s z y dp1 sb)))))

(def-fns _ $ (erased disk-move : (erased (List (Nat)) n f r s) (erased (Nat) x) (erased (DiskN n f r x) dn) (erased (Sub r s) rs) (erased (Sub s r) sr)
    -> (erased (DiskN n f s x) res))
  (let-match erased dn (MkDiskN _ _ _ _ y y2 iy pn dp))
  (MkDiskN n f s x y y2 (sub-in r s y rs iy) pn (dpath-move n f r s y2 x dp sr)))

(def-fns _ $ (erased fband-move : (erased (List (Nat)) f r s) (erased (Nat) x) (erased (Fband f r x) fb) (erased (Sub r s) rs) -> (erased (Fband f s x) res))
  (let-match erased fb (MkFband _ _ _ y iy w))
  (MkFband f s x y (sub-in r s y rs iy) w))
