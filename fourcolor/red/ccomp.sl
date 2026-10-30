; Every ring trace of a contract colouring of a configuration's map is in a computed list (the completeness half of
; ctree_mem_cpcolor of cfcolor.v, for contract colourings, after the contract steps of cfcontract.v). Load after cfred.sl.

(def-fns _ $ (erased respects-at : (erased (List (Nat)) lab xs ls) (erased (Nat) i j l) (subterm erased (Respects lab xs ls) rp)
    (erased (Nth (Nat) xs i j) p) (erased (Nth (Nat) lab j l) q) -> (erased (Nth (Nat) ls i l) r))
  (let-match erased rp (RespCons _ xs1 ls1 j1 l1 p1 rp1) (absurd (RespNil _) p))
  (let-match erased p (NthThere _ _ _ i1 _ p2)
    ((NthHere _ _ _) (let-match erased (nth-fn _ lab j l1 l p1 q) (Refl _ _)) (NthHere _ l1 ls1)))
  (NthThere _ l1 ls1 i1 l (respects-at lab xs1 ls1 i1 j l rp1 p2 q)))

(def-fns _ $ (erased addc-same : (erased (Col) a b c c2) (erased (AddC a b c) p) (erased (AddC a b c2) q) -> (erased (Eq (Col) c c2) e))
  (addc-fn a b c c2 (addc-k a b c p) (addc-k a b c2 q)))

; k is the first |k| entries of l.
(def-adts $ (Pre : ((List (Nat)) k l) -> Type)
  enum
  (many MkPre : (erased (List (Nat)) k l ids) (erased (Nat) d) (erased (Iota d ids) io) (erased (Respects l ids k) rp) -> (Pre k l)))

(def-fns _ $ (erased pre-nth : (erased (List (Nat)) k l) (erased (Nat) i x) (erased (Pre k l) p) (erased (Nth (Nat) k i x) q) -> (erased (Nth (Nat) l i x) r))
  (let-match erased p (MkPre _ _ ids d io rp))
  (let ((erased lk)) (respects-length l ids k d rp (iota-length d ids io)))
  (respects-nth l ids k i i x rp (iota-nth d i ids io (nth-lt-length _ k i d x q lk)) q))

(def-fns _ $ (erased pre-back : (erased (List (Nat)) k l) (erased (Nat) d i x) (erased (Pre k l) p) (erased (Length (Nat) k d) lk) (erased (Lt i d) lt)
    (erased (Nth (Nat) l i x) q) -> (erased (Nth (Nat) k i x) r))
  (let-match erased p (MkPre _ _ ids d2 io rp))
  (let-match erased (length-fn _ k d2 d (respects-length l ids k d2 rp (iota-length d2 ids io)) lk) (Refl _ _))
  (respects-at l ids k i i x rp (iota-nth d i ids io lt) q))

(def-fns _ $ (erased pre-unsnoc : (erased (List (Nat)) k k2 l) (erased (Nat) a) (erased (Pre k2 l) p) (erased (Snoc (Nat) k a k2) s) -> (erased (Pre k l) r))
  (let-match erased p (MkPre _ _ ids2 d2 io2 rp2))
  (let ((erased lk2)) (respects-length l ids2 k2 d2 rp2 (iota-length d2 ids2 io2)))
  (let-match erased io2 (IotaS d ids _ io s2) (absurd (IotaZ) (let-match erased s (SnocNil _ _) (absurd (SnocCons _ _ _ _ _ _) lk2)) lk2))
  (let ((erased k1) (erased c) (erased sc) (erased rp) (erased _)) (respects-unsnoc l ids ids2 k2 d s2 rp2))
  (let-match erased (snoc-inj _ k k1 k2 a c s sc) (Refl _ _))
  (MkPre k l ids d io rp))

(def-fns _ $ (erased pre-refl : (erased (List (Nat)) l) -> (erased (Pre l l) r))
  (let ((erased d) (erased ll)) (length-exists _ l))
  (let ((erased ids) (erased io)) (iota-exists d))
  (MkPre l l ids d io (respects-id-right d ids l io ll)))

; ks is constant along f on the darts of f.
(def-adts $ (FC : ((List (Nat)) ks f) -> Type)
  enum
  (many MkFC : (erased (List (Nat)) ks f k) (erased (Respects ks f k) rf) (erased (Pre k ks) pk) -> (FC ks f)))

(def-fns _ $ (erased fc-at : (erased (List (Nat)) ks f) (erased (Nat) x y c) (erased (FC ks f) fc) (erased (Nth (Nat) f x y) px) (erased (Nth (Nat) ks x c) pc)
    -> (erased (Nth (Nat) ks y c) r))
  (let-match erased fc (MkFC _ _ k rf pk))
  (let ((erased d) (erased lf)) (length-exists _ f))
  (let ((erased lk)) (respects-length ks f k d rf lf))
  (respects-nth ks f k x y c rf px (pre-back k ks d x c pk lk (nth-lt-length _ f x d y px lf) pc)))

(def-fns _ $ (erased fc-unsnoc : (erased (List (Nat)) ks f f2) (erased (Nat) a) (erased (FC ks f2) fc) (erased (Snoc (Nat) f a f2) s) -> (erased (FC ks f) r))
  (let-match erased fc (MkFC _ _ k2 rf2 pk2))
  (let ((erased k) (erased c) (erased sc) (erased rf) (erased _)) (respects-unsnoc ks f f2 k2 a s rf2))
  (MkFC ks f k rf (pre-unsnoc k k2 ks c pk2 sc)))

; Through an insertion of the new dart x after c.
(def-fns _ $ (erased fc-uninsert : (erased (List (Nat)) ks f f2) (erased (Nat) c x) (erased (FC ks f2) fc) (erased (Insert f c x f2) ins)
    (erased (Length (Nat) f x) lf) -> (erased (FC ks f) r))
  (let-match erased ins (MkInsert _ f1 _ _ _ v pv s1 s2))
  (let-match erased fc (MkFC _ _ k2 rf2 pk2))
  (let ((erased k) (erased l) (erased sc) (erased rf1) (erased _)) (respects-unsnoc ks f1 f2 k2 v s2 rf2))
  (let ((erased lc)) (nth-lt-length _ f c x v pv lf))
  (let ((erased lk2)) (respects-length ks f2 k2 (Succ x) rf2 (insert-length f f2 c x x ins lf)))
  (let ((erased lks) (erased q)) (nth-exists _ k2 (Succ x) c lk2 (lt-weaken c x lc)))
  (let ((erased px)) (respects-nth ks f2 k2 c x lks rf2 (insert-at f f2 c x ins) q))
  (let ((erased kv) (erased qv)) (nth-exists _ k2 (Succ x) x lk2 (lt-succ x)))
  (let-match erased (nth-fn _ ks x lks kv px (pre-nth k2 ks x kv pk2 qv)) (Refl _ _))
  (let ((erased pvk)) (respects-nth ks f2 k2 x v lks rf2 (insert-new f f2 c x x v ins lf pv) qv))
  (let ((erased f3) (erased s3)) (setnth-exists _ f1 x c v (setnth-length _ f c x x f1 s1 lf) lc))
  (let-match erased (setnth-same _ f c v f3 pv (setnth-twice _ f c x v f1 f3 s1 s3)) (Refl _ _))
  (MkFC ks f k (respects-setnth ks f1 f k c v lks rf1 s3 (respects-at ks f1 k c x lks rf1 (setnth-nth _ f c x f1 s1) px) pvk)
    (pre-unsnoc k k2 ks l pk2 sc)))

; The edge colour u of dart x is C0 exactly when x is a contract dart (in ie).
(def-adts $ (Flag : ((List (Nat)) ie) ((Nat) x) ((Col) u) -> Type)
  enum
  (many FlIn : (erased (List (Nat)) ie) (erased (Nat) x) (erased (In x ie) p) -> (Flag ie x (C0)))
  (many FlOut : (erased (List (Nat)) ie) (erased (Nat) x) (erased (Col) u) (erased (NotIn x ie) p) (erased (NZ u) nz) -> (Flag ie x u)))

(def-adts $ (EdgeAt : ((List (Nat)) ie) ((Nat) x a b) -> Type)
  enum
  (many EAIn : (erased (List (Nat)) ie) (erased (Nat) x a) (erased (In x ie) p) -> (EdgeAt ie x a a))
  (many EAOut : (erased (List (Nat)) ie) (erased (Nat) x a b) (erased (NotIn x ie) p) (erased (Apart (Nat) Lt a b) ne) -> (EdgeAt ie x a b)))

(def-fns _ $ (erased ccedge-nth : (erased (List (Nat)) ie ke ks) (erased (Nat) x j y a b) (subterm erased (CcEdge ie x ke ks) ce) (erased (Nth (Nat) ke j a) pa)
    (erased (Nth (Nat) ks j b) pb) (erased (Add j x y) ad) -> (erased (EdgeAt ie y a b) r))
  (match erased ce _
    (absurd (CENil _ _) pa)
    ((CEIn _ ke1 ks1 _ a1 p rest)
      (match erased pa _
        ((NthHere _ _ _) (let-match erased pb (NthHere _ _ _)) (let-match erased ad (AddZero _)) (EAIn ie x a p))
        ((NthThere _ _ _ j1 _ pa1) (let-match erased pb (NthThere _ _ _ _ _ pb1)) (let-match erased ad (AddSucc _ _ y1 ad1))
          (ccedge-nth ie ke1 ks1 (Succ x) j1 y a b rest pa1 pb1 (add-succ-right j1 x y1 ad1)))))
    ((CEOut _ ke1 ks1 _ a1 b1 p ne rest)
      (match erased pa _
        ((NthHere _ _ _) (let-match erased pb (NthHere _ _ _)) (let-match erased ad (AddZero _)) (EAOut ie x a b p ne))
        ((NthThere _ _ _ j1 _ pa1) (let-match erased pb (NthThere _ _ _ _ _ pb1)) (let-match erased ad (AddSucc _ _ y1 ad1))
          (ccedge-nth ie ke1 ks1 (Succ x) j1 y a b rest pa1 pb1 (add-succ-right j1 x y1 ad1)))))))

; A contract colouring ks of the map whose edges are E, seen from a map (e, f) whose darts are the first darts of it.
(def-adts $ (Ctx : ((List (Nat)) ie ks big e f) -> Type)
  enum
  (many MkCtx : (erased (List (Nat)) ie ks big e f ke) (erased (Nat) m) (erased (Pre e big) pe) (erased (FC ks f) fc) (erased (Respects ks big ke) rk)
      (erased (CcEdge ie (Zero) ke ks) ce) (erased (Under ks 4) four) (erased (Length (Nat) ks m) lk) (erased (Length (Nat) big m) lb) -> (Ctx ie ks big e f)))

; The colour of a dart x of e, below 4.
(def-fns _ $ (erased ctx-col : (erased (List (Nat)) ie ks big e f) (erased (Nat) x y) (erased (Ctx ie ks big e f) cx) (erased (Nth (Nat) e x y) p)
    -> (erased (Nat) k) (erased (Nth (Nat) ks x k) pk) (erased (Col) c) (erased (NCol k c) pc))
  (let-match erased cx (MkCtx _ _ _ _ _ ke m pe fc rk ce four lk lb))
  (let ((erased k) (erased pk)) (nth-exists _ ks m x lk (nth-lt-length _ big x m y (pre-nth e big x y pe p) lb)))
  (let ((erased c) (erased pc)) (ncol-ex k (under-nth ks x k 4 four pk)))
  (values k pk c pc))

; The edge colour of a dart x of e, whose edge image z has y after it on its face.
(def-fns _ $ (erased flag-of : (erased (List (Nat)) ie ks big e f) (erased (Nat) x z y kx ky) (erased (Col) cx cy u) (erased (Ctx ie ks big e f) ctx)
    (erased (Nth (Nat) e x z) pe) (erased (Nth (Nat) f z y) pf) (erased (Nth (Nat) ks x kx) px) (erased (Nth (Nat) ks y ky) py) (erased (NCol kx cx) qx)
    (erased (NCol ky cy) qy) (erased (AddC cx cy u) pu) -> (erased (Flag ie x u) r))
  (let-match erased ctx (MkCtx _ _ _ _ _ ke m pre fc rk ce four lk lb))
  (let ((erased pz)) (pre-nth e big x z pre pe))
  (let ((erased kz) (erased pkz)) (nth-exists _ ke m x (respects-length ks big ke m rk lb) (nth-lt-length _ big x m z pz lb)))
  (let ((erased qz)) (respects-nth ks big ke x z kz rk pz pkz))
  (let-match erased (nth-fn _ ks y kz ky (fc-at ks f z y kz fc pf qz) py) (Refl _ _))
  (let-match erased (ccedge-nth ie ke ks (Zero) x x kz kx ce pkz px (add-zero-right x)) (EAIn _ _ _ p)
    ((EAOut _ _ _ _ p ne) (FlOut ie x u p (addc-apart kx kz cx cy u qx qy pu (apart-sym kz kx ne)))))
  (let-match erased (ncol-fn kx cx cy qx qy) (Refl _ _))
  (let-match erased (addc-same cx cx u (C0) pu (addc-ii cx)) (Refl _ _))
  (FlIn ie x p))

; A U step at d puts u = colour of d+1 plus colour of d twice in front of the trace, u the edge colour of d+1.
(def-fns _ $ (erased u-trace : (erased (Nat) d) (erased (List (Nat)) e n f r e2 f2 r2 ie ks big rc) (erased (List (Col)) cs et) (erased (PointedMap d e n f r) pm)
    (erased (EcpU d e f r e2 f2 r2) st) (erased (Ctx ie ks big e2 f2) ctx) (erased (Respects ks r rc) rr) (erased (NCols rc cs) nc) (erased (Trace cs et) tr)
    -> (erased (Col) u) (erased (List (Nat)) rc2) (erased (List (Col)) cs2) (erased (Respects ks r2 rc2) rr2) (erased (NCols rc2 cs2) nc2)
    (erased (Trace cs2 (Cons (Col) u (Cons (Col) u et))) tr2) (erased (Flag ie (Succ d) u) fl))
  (let-match erased pm (MkPointedMap _ _ _ _ _ h cr))
  (let-match erased st (MkEcpU _ b c _ _ _ _ f0 _ lb pc g s ins))
  (let-match erased cr (MkCpring _ p a y rp back dp))
  (let-match erased (last-fn r b y lb (rpath-last n p a y rp)) (Refl _ _))
  (let ((erased v) (erased pv) (erased pfa)) (hyper-back d b a e n f h back))
  (let-match erased (nth-fn _ e b c v pc pv) (Refl _ _))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased ei) (erased ni) (erased fi) (erased _) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (let ((erased lc)) (perm-val d b c e ei pe pc))
  (let ((erased lf0)) (snoc-length _ f f0 d d s lf))
  (let ((erased fa)) (insert-new f0 f2 c (Succ d) (Succ d) a ins lf0 (snoc-old _ f f0 d a c s pfa)))
  (let ((erased fd)) (insert-other f0 f2 c (Succ d) d d ins (snoc-new _ f f0 d d s lf) (ApGt _ _ d c lc)))
  (let ((erased ed1)) (edge-high e e2 d g))
  (let ((erased k1) (erased pk1) (erased c1) (erased q1)) (ctx-col ie ks big e2 f2 (Succ d) d ctx ed1))
  (let ((erased kd) (erased pkd) (erased cd) (erased qd)) (ctx-col ie ks big e2 f2 d (Succ d) ctx (edge-low e e2 d g)))
  (let-match erased ctx (MkCtx _ _ _ _ _ ke m pre fc rk ce four lk lbg))
  (let-match erased rr (RespCons _ _ rc1 _ ka pka rr1))
  (let-match erased (nth-fn _ ks a k1 ka (fc-at ks f2 (Succ d) a k1 fc fa pk1) pka) (Refl _ _))
  (let-match erased nc (NCsCons _ ca _ cs1 pca nc1))
  (let-match erased (ncol-fn ka c1 ca q1 pca) (Refl _ _))
  (let-match erased tr (MkTrace _ _ _ ct))
  (let ((erased u) (erased pu)) (addc-c ca cd))
  (values u (Cons (Nat) ka (Cons (Nat) kd rc)) (Cons (Col) ca (Cons (Col) cd cs))
    (RespCons ks (Cons (Nat) d r) (Cons (Nat) kd rc) (Succ d) ka pk1 (RespCons ks r rc d kd pkd rr))
    (NCsCons ka ca (Cons (Nat) kd rc) (Cons (Col) cd cs) pca (NCsCons kd cd rc cs qd nc))
    (MkTrace ca (Cons (Col) cd cs) _ (CTStep ca ca cd u _ _ pu (CTStep ca cd ca u _ _ (addc-comm ca cd u pu) ct)))
    (flag-of ie ks big e2 f2 (Succ d) d d ka kd ca cd u ctx ed1 fd pk1 pkd q1 qd pu)))
