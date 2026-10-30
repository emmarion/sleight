; Geometry of the maps cpmap.sl builds for cubic programs (cfmap.v): the ring read forwards, connected, bridgeless and
; planar. Load after revsnip3.sl, with cfmap.sl loaded after hypcubic.sl and cpmap.sl after red/red.sl.

(def-fns _ $ (erased rpath-fpath : (erased (List (Nat)) n p A) (erased (Nat) x y z) (subterm erased (CRPath n x p y) rp) (erased (FPath n x A z) fp)
    -> (erased (List (Nat)) B) (erased (FPath n y B z) r) (erased (RevApp (Nat) (Cons (Nat) x p) A (Cons (Nat) y B)) ra))
  (let-match erased rp (CRPCons _ p1 _ w _ pw rp1)
    ((CRPNil _ _) (values A fp (RACons _ x (Nil (Nat)) A (Cons (Nat) x A) (RANil _ (Cons (Nat) x A))))))
  (let ((erased B) (erased fp2) (erased ra)) (rpath-fpath n p1 (Cons (Nat) x A) w y z rp1 (FPCons n A w x z pw fp)))
  (values B fp2 (RACons _ x (Cons (Nat) w p1) A (Cons (Nat) y B) ra)))

; rev r is a node cycle without repeats (cycle_rev_cpring, ucycle_rev_cpring).
(def-fns _ $ (erased ring-cycle : (erased (List (Nat)) n r) (erased (Cpring n r) cr)
    -> (erased (Nat) y) (erased (List (Nat)) B) (erased (RevApp (Nat) r (Nil (Nat)) (Cons (Nat) y B)) ra) (erased (NCyc n (Cons (Nat) y B)) nc)
    (erased (Distinct (Cons (Nat) y B)) dr))
  (let-match erased cr (MkCpring _ p a y rp back dp))
  (let ((erased B) (erased fp) (erased ra)) (rpath-fpath n p (Nil (Nat)) a y a rp (FPNil n a)))
  (values y B ra (NCCons n B y a fp back) (revapp-distinct r (Nil (Nat)) _ ra dp (DistNil) (off-nil r))))

(def-fns _ $ (erased cubics-off : (erased (List (Nat)) n r R xs) (subterm erased (Cubics n r xs) cs) (erased (RevApp (Nat) r (Nil (Nat)) R) ra)
    -> (erased (OrdersOff n 3 R xs) res))
  (unary 3)
  (let-match erased cs (CubsCons _ _ xs1 x c cs1) ((CubsNil _ _) (OONil n R 3)))
  (let ((erased rest)) (cubics-off n r R xs1 cs1 ra))
  (match erased c _
    ((CubOn _ _ _ i) (OOSkip n R xs1 3 x (revapp-in r (Nil (Nat)) R x ra (OrL _ _ i)) rest))
    ((CubThree _ _ _ o) (OOAt n R xs1 3 x o rest))))

; What quasicubic_Euler takes of a map: plain, connected, and a node cycle of m + 1 darts off which node has order 3.
(def-adts $ (QGeo : ((Nat) d m) ((List (Nat)) e n f) -> Type)
  enum
  (many MkQGeo : (erased (Nat) d m x0) (erased (List (Nat)) e n f q ids) (erased (Hypermap d e n f) h)
      (erased (AllOrder d e (Succ (Succ (Zero)))) pl) (erased (NCyc n (Cons (Nat) x0 q)) nc) (erased (Distinct (Cons (Nat) x0 q)) dq)
      (erased (Length (Nat) q m) lq) (erased (OrdersOff n 3 (Cons (Nat) x0 q) ids) oo) (erased (Iota d ids) io) (erased (Connected d e n f) cc)
      -> (QGeo d m e n f)))

(def-fns _ $ (erased cp-qgeo : (erased (Nat) d m) (erased (List (Nat)) e n f r) (erased (PointedMap d e n f r) pm) (erased (AllOrder d e (Succ (Succ (Zero)))) pl)
    (erased (CQuasiCubic d n r) qc) (erased (Connected d e n f) cc) (erased (Length (Nat) r (Succ m)) lr) -> (erased (QGeo d m e n f) res))
  (let-match erased pm (MkPointedMap _ _ _ _ _ h cr))
  (let-match erased qc (CMkQuasiCubic _ _ _ ids io cs))
  (let ((erased y) (erased B) (erased ra) (erased nc) (erased dr)) (ring-cycle n r cr))
  (let-match erased (revapp-length r (Nil (Nat)) _ (Succ m) (Zero) (Succ m) ra lr (LengthNil _) (add-zero-right (Succ m))) (LengthCons _ _ _ _ lb))
  (MkQGeo d m y e n f B ids h pl nc dr lb (cubics-off n r _ ids cs ra) io cc))

; 6 kf = d + 2 k + 6.
(def-adts $ (QEuler : ((Nat) d k kf) -> Type)
  enum
  (many MkQEuler : (erased (Nat) d k kf f6 m2 u) (erased (Mul kf 6 f6) mf) (erased (Mul k 2 m2) mm) (erased (Add d 6 u) du) (erased (Add m2 u f6) r)
      -> (QEuler d k kf)))

(def-fns _ $ (erased qgeo-euler : (erased (Nat) d m kf) (erased (List (Nat)) e n f) (erased (QGeo d m e n f) qg) (erased (Genus d e n f (Zero)) gn)
    (erased (Orbits d f kf) of) -> (erased (QEuler d (Succ m) kf) res))
  (let-match erased qg (MkQGeo _ _ x0 _ _ _ q ids h pl nc dq lq oo io cc))
  (let ((erased f6) (erased m2) (erased u) (erased mf) (erased mm) (erased du) (erased r))
    (quasicubic-planar d m x0 kf e n f q ids h pl nc dq lq oo io cc gn of))
  (MkQEuler d (Succ m) kf f6 m2 u mf mm du r))

(def-fns _ $ (erased euler-qgeo : (erased (Nat) d m kf) (erased (List (Nat)) e n f) (erased (QGeo d m e n f) qg) (erased (Orbits d f kf) of)
    (erased (QEuler d (Succ m) kf) qe) -> (erased (Genus d e n f (Zero)) res))
  (let-match erased qg (MkQGeo _ _ x0 _ _ _ q ids h pl nc dq lq oo io cc))
  (let-match erased qe (MkQEuler _ _ _ f6 m2 u mf mm du r))
  (let ((erased gen) (erased gn)) (even-genus d e n f h))
  (let-match erased (planar-quasicubic d m x0 kf gen f6 m2 u e n f q ids h pl nc dq lq oo io cc gn of mf mm du r) (Refl _ _))
  gn)

(def-fns _ $ (erased add-ss : (erased (Nat) a b c) (erased (Add a b c) p) -> (erased (Add (Succ (Succ a)) b (Succ (Succ c))) r))
  (AddSucc _ _ _ (AddSucc _ _ _ p)))

; The U step: two more darts, two more on the ring and one more face.
(def-fns _ $ (erased euler-u : (erased (Nat) d k kf) (erased (QEuler d k kf) qe) -> (erased (QEuler (Succ (Succ d)) (Succ (Succ k)) (Succ kf)) res))
  (unary 2)
  (unary 6)
  (let-match erased qe (MkQEuler _ _ _ f6 m2 u mf mm du r))
  (let ((erased F)) (Succ (Succ (Succ (Succ (Succ (Succ f6)))))))
  (let ((erased M1) (erased M)) (values (Succ (Succ m2)) (Succ (Succ (Succ (Succ m2))))))
  (MkQEuler _ _ _ F M (Succ (Succ u)) (MulSucc kf 6 f6 F mf (add-comm 6 f6 F (add-ss _ _ _ (add-ss _ _ _ (add-ss _ _ _ (AddZero f6))))))
    (MulSucc (Succ k) 2 M1 M (MulSucc k 2 m2 M1 mm (add-comm 2 m2 M1 (add-ss _ _ _ (AddZero m2)))) (add-comm 2 M1 M (add-ss _ _ _ (AddZero M1))))
    (add-ss d 6 u du) (add-succ-left2 _ u F (add-ss _ _ _ (add-ss _ _ _ (add-ss _ _ _ r))))))

; The N step: two more darts, one fewer on the ring, as many faces.
(def-fns _ $ (erased euler-n : (erased (Nat) d k kf) (erased (QEuler d (Succ k) kf) qe) -> (erased (QEuler (Succ (Succ d)) k kf) res))
  (unary 2)
  (let-match erased qe (MkQEuler _ _ _ f6 m2 u mf mm du r))
  (let-match erased mm (MulSucc _ _ M _ mk a2))
  (let-match erased (add-comm M 2 m2 a2) (AddSucc _ _ _ a1))
  (let-match erased a1 (AddSucc _ _ _ a0))
  (let-match erased a0 (AddZero _))
  (MkQEuler _ _ _ f6 M (Succ (Succ u)) mf mk (add-ss d 6 u du) (add-succ-left2 M u f6 r)))

; Where face changes in a U or N step: d is fixed (U) or inserted after a (N); then d + 1 is inserted after c.
(def-adts $ (FStep : ((List (Nat)) f) ((Nat) d) ((List (Nat)) f0) -> Type)
  enum
  (many FSFix : (erased (List (Nat)) f f0) (erased (Nat) d) (erased (HSnoc (Nat) f d f0) s) -> (FStep f d f0))
  (many FSIns : (erased (List (Nat)) f f0) (erased (Nat) d a) (erased (Insert f a d f0) i) (erased (Lt a d) la) -> (FStep f d f0)))

(def-fns _ $ (erased fstep-length : (erased (Nat) d) (erased (List (Nat)) f f0) (erased (FStep f d f0) fs) (erased (Length (Nat) f d) lf)
    -> (erased (Length (Nat) f0 (Succ d)) r))
  (match erased fs _ ((FSFix _ _ _ s) (snoc-length _ f f0 d d s lf)) ((FSIns _ _ _ a i _) (insert-length f f0 a d d i lf))))

(def-fns _ $ (erased fstep-spans : (erased (Nat) d c) (erased (List (Nat)) f f0 f2) (erased (List (Bond)) gf gf2) (erased (Graph d f gf) grf)
    (erased (FStep f d f0) fs) (erased (Insert f0 c (Succ d) f2) ins) (erased (Graph (Succ (Succ d)) f2 gf2) grf2) -> (erased (Spans gf2 gf) r))
  (let-match erased grf (MkGraph _ _ ids _ io lf z))
  (let ((erased lf0)) (fstep-length d f f0 fs lf))
  (let ((erased gf0) (erased grf0)) (graph-exists (Succ d) f0 lf0))
  (spans-trans gf2 gf0 gf
    (match erased fs (((Spans gf0 gf) r))
      ((FSFix _ _ _ s)
        (let ((erased g1) (erased sg) (erased gr1)) (graph-snoc d d f f0 gf grf s))
        (let-match erased (graph-fn (Succ d) f0 g1 gf0 gr1 grf0) (Refl _ _))
        (spans-snoc gf gf0 gf _ (spans-self gf) sg))
      ((FSIns _ _ _ a i _) (spans-insert-out d a f f0 gf gf0 (graph-fun d f gf grf) i lf grf0)))
    (spans-insert-out (Succ d) c f0 f2 gf0 gf2 (graph-fun (Succ d) f0 gf0 grf0) ins lf0 grf2)))

(def-fns _ $ (erased root-one : (erased (List (Bond)) g) (erased (Nat) d r) (erased (List (Nat)) ids lab) (erased (Nat) x)
    (erased (Rooted g (Cons (Nat) r (Nil (Nat))) ids lab) ro) (erased (Iota d ids) io) (erased (Length (Nat) lab d) ll) (erased (Lt x d) lx)
    -> (erased (Nth (Nat) lab x r) p) (erased (Conn g r x) c))
  (let ((erased l) (erased pl)) (nth-exists _ lab d x ll lx))
  (let ((erased i) (erased c)) (classes-root g d ids lab (Cons (Nat) r (Nil (Nat))) x l io ro pl lx))
  (let-match erased i (InHere _ _) (absurd (InThere _ _ _ i1) (match erased i1 _)))
  (values pl c))

(def-fns _ $ (erased const-one : (erased (List (Bond)) g h) (erased (Nat) d r) (erased (List (Nat)) ids lab) (subterm erased (Below h d) bh)
    (erased (Rooted g (Cons (Nat) r (Nil (Nat))) ids lab) ro) (erased (Iota d ids) io) (erased (Length (Nat) lab d) ll) -> (erased (Const lab h) res))
  (let-match erased bh (BelowCons h1 x y _ lx ly bh1) ((BelowNil _) (ConstNil lab)))
  (let ((erased px) (erased _)) (root-one g d r ids lab x ro io ll lx))
  (let ((erased py) (erased _)) (root-one g d r ids lab y ro io ll ly))
  (ConstCons lab h1 x y r px py (const-one g h1 d r ids lab bh1 ro io ll)))

; A map whose darts are all joined to r is connected.
(def-fns _ $ (erased connected-one : (erased (Nat) d r) (erased (List (Nat)) e n f ids lab) (erased (List (Bond)) g) (erased (Hypermap d e n f) h)
    (erased (Glink d e n f g) gl) (erased (Rooted g (Cons (Nat) r (Nil (Nat))) ids lab) ro) (erased (Iota d ids) io) (erased (Length (Nat) lab d) ll)
    (erased (Nth (Nat) lab r r) pr) -> (erased (Connected d e n f) res))
  (MkConnected d e n f g gl (MkClasses g d (Succ (Zero)) ids lab _ io ll (LengthCons _ r _ (Zero) (LengthNil _))
    (DistCons r (Nil (Nat)) (NotInNil r) (DistNil)) (RespCons lab (Nil (Nat)) (Nil (Nat)) r r pr (RespNil lab))
    (const-one g g d r ids lab (glink-below d e n f g h gl) ro io ll) ro)))

; A U or N step keeps the map connected (connected_ecpU, connected_ecpN).
(def-fns _ $ (erased grow-connected : (erased (Nat) d c) (erased (List (Nat)) e n f e2 n2 f2 f0) (erased (Hypermap d e n f) h)
    (erased (Hypermap (Succ (Succ d)) e2 n2 f2) h2) (erased (Connected d e n f) cc) (erased (EdgeGrow e d e2) gw) (erased (FStep f d f0) fs)
    (erased (Insert f0 c (Succ d) f2) ins) (erased (Lt c d) lc) -> (erased (Connected (Succ (Succ d)) e2 n2 f2) res))
  (let ((erased d1) (erased d2)) (values (Succ d) (Succ (Succ d))))
  (let-match erased cc (MkConnected _ _ _ _ g gl cs))
  (let-match erased gl (MkGlink _ _ _ _ ge gn gf gnf _ gre grn grf c1 c2))
  (let-match erased cs (MkClasses _ _ _ ids lab rs io ll lr dr fix cl ro))
  (let-match erased lr (LengthCons _ r0 rs1 _ lr1))
  (let-match erased lr1 (LengthNil _))
  (let ((erased nf2) (erased ni2) (erased fi2) (erased _) (erased pe2) (erased pn2) (erased pf2)) (hyper-core d2 e2 n2 f2 h2))
  (let ((erased geA) (erased ge2) (erased sgA) (erased sg2) (erased gre2) (erased se0)) (edge-graphs d e e2 ge gre gw))
  (let ((erased gn2) (erased grn2)) (perm-graph d2 n2 ni2 pn2))
  (let ((erased gf2) (erased grf2)) (perm-graph d2 f2 fi2 pf2))
  (let ((erased gnf2) (erased c12)) (cat-exists gn2 gf2))
  (let ((erased g2) (erased c22)) (cat-exists ge2 gnf2))
  (let ((erased gl2)) (MkGlink d2 e2 n2 f2 ge2 gn2 gf2 gnf2 g2 gre2 grn2 grf2 c12 c22))
  (let ((erased sf)) (spans-lift-r ge2 gnf2 g2 gf (spans-lift-r gn2 gf2 gnf2 gf (fstep-spans d c f f0 f2 gf gf2 grf fs ins grf2) c12) c22))
  (let ((erased se)) (spans-lift-l ge2 gnf2 g2 ge se0 c22))
  (let ((erased fe) (erased fi) (erased ei) (erased rfe) (erased pn) (erased pf) (erased pe)) (hyper-core d n f e (hyper-rot d e n f h)))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased gfe) (erased cfe)) (cat-exists gf ge))
  (let ((erased sn)) (spans-trans g2 gfe gn (spans-edge d n f e fe gn gf ge gfe (graph-fun d n gn grn) pn rfe le grf gre cfe) (spans-cat g2 gf ge gfe cfe sf se)))
  (let ((erased ro2)) (rooted-spans g g2 rs ids lab ro (glink-to d e n f g g2 ge gn gf gl gre grn grf se sn sf)))
  (let ((erased lab1) (erased sl1)) (snoc-exists _ lab r0))
  (let ((erased lab2) (erased sl2)) (snoc-exists _ lab1 r0))
  (let ((erased ids1) (erased si1)) (snoc-exists _ ids d))
  (let ((erased ids2) (erased si2)) (snoc-exists _ ids1 d1))
  (let ((erased _) (erased crc)) (root-one g2 d r0 ids lab c ro2 io ll lc))
  (let ((erased ccd1)) (conn-cat g2 r0 c d1 crc (conn-adj g2 c d1 (adj-cat-r ge2 gnf2 g2 c d1
    (adj-cat-r gn2 gf2 gnf2 c d1 (graph-adj d2 c d1 f2 gf2 grf2 (insert-at f0 f2 c d1 ins)) c12) c22))))
  (let ((erased ccd)) (conn-cat g2 r0 d1 d ccd1 (conn-adj g2 d1 d (adj-cat-l ge2 gnf2 g2 d1 d (graph-adj d2 d1 d e2 ge2 gre2 (edge-high e e2 d gw)) c22))))
  (let ((erased i0)) (InHere r0 (Nil (Nat))))
  (let-match erased fix (RespCons _ _ _ _ _ p0 _))
  (connected-one d2 r0 e2 n2 f2 ids2 lab2 g2 h2 gl2
    (rooted-snoc g2 rs ids1 ids2 lab1 lab2 d1 r0 (rooted-snoc g2 rs ids ids1 lab lab1 d r0 ro2 si1 sl1 i0 ccd) si2 sl2 i0 ccd1)
    (IotaS d1 ids1 ids2 (IotaS d ids ids1 io si1) si2) (snoc-length _ lab1 lab2 r0 d1 sl2 (snoc-length _ lab lab1 r0 d sl1 ll))
    (snoc-old _ lab1 lab2 r0 r0 r0 sl2 (snoc-old _ lab lab1 r0 r0 r0 sl1 p0))))
