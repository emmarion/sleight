; r: normq of q.
(def-adts $ (NormQ : ((Qn) q r) -> Type)
  enum
  (many NQ1 : (erased (Nat) a) -> (NormQ (Qask1 a) (QaskLR a (Qask0) (Qask0))))
  (many NQL : (erased (Nat) a) (erased (Qn) l) -> (NormQ (QaskL a l) (QaskLR a l (Qask0))))
  (many NQR : (erased (Nat) a) (erased (Qn) r) -> (NormQ (QaskR a r) (QaskLR a (Qask0) r)))
  (many NQLR : (erased (Nat) a) (erased (Qn) l r) -> (NormQ (QaskLR a l r) (QaskLR a l r))))

; r: the flip of q.
(def-adts $ (FlipQ : ((Qn) q r) -> Type)
  enum
  (many FlQ0 : -> (FlipQ (Qask0) (Qask0)))
  (many FlQ1 : (erased (Nat) a) -> (FlipQ (Qask1 a) (Qask1 a)))
  (many FlQL : (erased (Nat) a) (erased (Qn) q r) (erased (FlipQ q r) p) -> (FlipQ (QaskL a q) (QaskR a r)))
  (many FlQR : (erased (Nat) a) (erased (Qn) q r) (erased (FlipQ q r) p) -> (FlipQ (QaskR a q) (QaskL a r)))
  (many FlQLR : (erased (Nat) a) (erased (Qn) l r l2 r2) (erased (FlipQ l l2) pl) (erased (FlipQ r r2) pr) -> (FlipQ (QaskLR a l r) (QaskLR a r2 l2)))
  (many FlQLL : (erased (Nat) a) (erased (Qn) q r) (erased (FlipQ q r) p) -> (FlipQ (QaskLL a q) (QaskRR a r)))
  (many FlQRR : (erased (Nat) a) (erased (Qn) q r) (erased (FlipQ q r) p) -> (FlipQ (QaskRR a q) (QaskLL a r))))

(def-adts $ (FlipQz : ((Quiz) qz qz2) -> Type)
  enum
  (many MkFlipQz : (erased (Nat) a0 a1) (erased (Qn) q01 q10 r01 r10) (erased (FlipQ q01 r01) p1) (erased (FlipQ q10 r10) p2)
      -> (FlipQz (MkQuiz (QaskR a0 q01) (QaskR a1 q10)) (MkQuiz (QaskR a0 r10) (QaskR a1 r01)))))

(def-adts $ (Variant : ((Quiz) qz qz2) -> Type)
  enum
  (many VSame : (erased (Quiz) qz) -> (Variant qz qz))
  (many VFlip : (erased (Quiz) qz qz2) (erased (FlipQz qz qz2) p) -> (Variant qz qz2)))

; q1 q2 q3: what store_qz puts for qz under a1 a2 a3, before rotation.
(def-adts $ (QzTriple : ((Quiz) qz) ((Nat) a1 a2 a3) ((Qn) q1 q2 q3) -> Type)
  enum
  (many QT1 : (erased (Nat) a1 a2 a3) (erased (Qn) r1 q1 q2 q3) (erased (NormQ r1 (QaskLR a3 q1 q3)) p)
      -> (QzTriple (MkQuiz (QaskR a1 r1) (QaskR a2 q2)) a1 a2 a3 q1 q2 q3))
  (many QT2 : (erased (Nat) a1 a2 a3) (erased (Qn) r2 q1 q2 q3) (erased (NormQ r2 (QaskLR a2 q3 q2)) p)
      -> (QzTriple (MkQuiz (QaskR a1 q1) (QaskR a3 r2)) a1 a2 a3 q1 q2 q3)))

(def-adts $ (Rot3 : ((Nat) a1 a2 a3) ((Qn) q1 q2 q3) ((Nat) b1 b2 b3) ((Qn) r1 r2 r3) -> Type)
  enum
  (many Rt0 : (erased (Nat) a1 a2 a3) (erased (Qn) q1 q2 q3) -> (Rot3 a1 a2 a3 q1 q2 q3 a1 a2 a3 q1 q2 q3))
  (many Rt1 : (erased (Nat) a1 a2 a3) (erased (Qn) q1 q2 q3) -> (Rot3 a1 a2 a3 q1 q2 q3 a2 a3 a1 q2 q3 q1))
  (many Rt2 : (erased (Nat) a1 a2 a3) (erased (Qn) q1 q2 q3) -> (Rot3 a1 a2 a3 q1 q2 q3 a3 a1 a2 q3 q1 q2)))

; ps: the arities b1 b2 b3, listed backwards.
(def-adts $ (QEntry : ((List (Config)) cfs) ((List (Nat)) ps) ((Qn) r1 r2 r3) -> Type)
  enum
  (many MkQEntry : (erased (List (Config)) cfs) (erased (Config) cf) (erased (Quiz) qz qz2) (erased (Nat) a1 a2 a3 b1 b2 b3) (erased (Qn) q1 q2 q3 r1 r2 r3)
      (erased (Mem (Config) cf cfs) m) (erased (CfQz cf qz) c) (erased (Variant qz qz2) v) (erased (QzTriple qz2 a1 a2 a3 q1 q2 q3) t)
      (erased (Rot3 a1 a2 a3 q1 q2 q3 b1 b2 b3 r1 r2 r3) rt) -> (QEntry cfs (Cons (Nat) b3 (Cons (Nat) b2 (Cons (Nat) b1 (Nil (Nat))))) r1 r2 r3)))

; ps: the arities above t, listed backwards.
(def-adts $ (QInv : ((List (Config)) cfs) ((List (Nat)) ps) ((Qzt) t) -> Type)
  enum
  (many QINil : (erased (List (Config)) cfs) (erased (List (Nat)) ps) -> (QInv cfs ps (QztNil)))
  (many QILeaf : (erased (List (Config)) cfs) (erased (List (Nat)) ps) (erased (Qn) q1 q2 q3) (erased (Qzt) t) (erased (QEntry cfs ps q1 q2 q3) en)
      (erased (QInv cfs ps t) rest) -> (QInv cfs ps (QztLeaf q1 q2 q3 t)))
  (many QINode : (erased (List (Config)) cfs) (erased (List (Nat)) ps) (erased (Qzt) t5 t6 t7 t8) (erased (QInv cfs (Cons (Nat) 5 ps) t5) i5)
      (erased (QInv cfs (Cons (Nat) 6 ps) t6) i6) (erased (QInv cfs (Cons (Nat) 7 ps) t7) i7) (erased (QInv cfs (Cons (Nat) 8 ps) t8) i8)
      -> (QInv cfs ps (QztNode t5 t6 t7 t8)))
  (many QIHub : (erased (List (Config)) cfs) (erased (List (Nat)) ps) (erased (Qzt) t58 t9 t10 t11) (erased (QInv cfs ps t58) i58)
      (erased (QInv cfs (Cons (Nat) 9 ps) t9) i9) (erased (QInv cfs (Cons (Nat) 10 ps) t10) i10) (erased (QInv cfs (Cons (Nat) 11 ps) t11) i11)
      -> (QInv cfs ps (QztHub t58 t9 t10 t11))))

(def-fns _ $ (erased qinv-get : (erased (List (Config)) cfs) (erased (List (Nat)) ps) (erased (Nat) a) (erased (Qzt) t u) (erased (QInv cfs ps t) qi)
    (subterm erased (QGet a t u) g) -> (erased (QInv cfs (Cons (Nat) a ps) u) r))
  (match erased g _
    ((QG5 _ _ _ _) (let-match erased qi (QINode _ _ _ _ _ _ i5 _ _ _)) i5)
    ((QG6 _ _ _ _) (let-match erased qi (QINode _ _ _ _ _ _ _ i6 _ _)) i6)
    ((QG7 _ _ _ _) (let-match erased qi (QINode _ _ _ _ _ _ _ _ i7 _)) i7)
    ((QG8 _ _ _ _) (let-match erased qi (QINode _ _ _ _ _ _ _ _ _ i8)) i8)
    ((QG9 _ _ _ _) (let-match erased qi (QIHub _ _ _ _ _ _ _ i9 _ _)) i9)
    ((QG10 _ _ _ _) (let-match erased qi (QIHub _ _ _ _ _ _ _ _ i10 _)) i10)
    ((QG11 _ _ _ _) (let-match erased qi (QIHub _ _ _ _ _ _ _ _ _ i11)) i11)
    ((QGLo _ t58 _ _ _ _ _ g1) (let-match erased qi (QIHub _ _ _ _ _ _ i58 _ _ _)) (qinv-get cfs ps a t58 u i58 g1))))

(def-fns _ $ (erased qinv-leaf : (erased (List (Config)) cfs) (erased (List (Nat)) ps) (erased (Qzt) t) (erased (Qn) q1 q2 q3) (erased (QInv cfs ps t) qi)
    (subterm erased (QLeaf t q1 q2 q3) l) -> (erased (QEntry cfs ps q1 q2 q3) r))
  (match erased l _
    ((QLHere _ _ _ _) (let-match erased qi (QILeaf _ _ _ _ _ _ en _)) en)
    ((QLThere _ _ _ _ _ _ t1 l1) (let-match erased qi (QILeaf _ _ _ _ _ _ _ qi1)) (qinv-leaf cfs ps t1 q1 q2 q3 qi1 l1))))

; The darts of the node of x1 have arities a1 a2 a3 and fit q1 q2 q3 one qstepR away.
(def-adts $ (Fit3 : ((List (Nat)) e n ks) ((Nat) x1 a1 a2 a3) ((Qn) q1 q2 q3) -> Type)
  enum
  (many MkFit3 : (erased (List (Nat)) e n ks) (erased (Nat) x1 x2 x3 a1 a2 a3 z1 z2 z3) (erased (Qn) q1 q2 q3) (erased (Nth (Nat) n x1 x2) p2)
      (erased (Nth (Nat) n x2 x3) p3) (erased (Nth (Nat) ks x1 a1) k1) (erased (Nth (Nat) ks x2 a2) k2) (erased (Nth (Nat) ks x3 a3) k3)
      (erased (QStepR e n x1 z1) s1) (erased (FitQ e n ks z1 q1) f1) (erased (QStepR e n x2 z2) s2) (erased (FitQ e n ks z2 q2) f2)
      (erased (QStepR e n x3 z3) s3) (erased (FitQ e n ks z3 q3) f3) -> (Fit3 e n ks x1 a1 a2 a3 q1 q2 q3)))

(def-fns _ $ (erased qzt-entry : (erased (List (Config)) cfs) (erased (List (Nat)) e n ks) (erased (Qzt) qt) (erased (Nat) x1) (erased (QInv cfs (Nil (Nat)) qt) qi)
    (erased (QztFit e n ks qt x1) fit) -> (erased (Nat) a1 a2 a3) (erased (Qn) q1 q2 q3)
    (erased (QEntry cfs (Cons (Nat) a3 (Cons (Nat) a2 (Cons (Nat) a1 (Nil (Nat))))) q1 q2 q3) en) (erased (Fit3 e n ks x1 a1 a2 a3 q1 q2 q3) f))
  (let-match erased fit (MkQztFit _ _ _ _ t1 t2 t3 _ x2 x3 a1 a2 a3 z1 z2 z3 q1 q2 q3 p2 p3 k1 k2 k3 g1 g2 g3 lf s1 f1 s2 f2 s3 f3))
  (let ((erased i1)) (qinv-get cfs (Nil _) a1 qt t1 qi g1))
  (let ((erased i2)) (qinv-get cfs (Cons _ a1 (Nil _)) a2 t1 t2 i1 g2))
  (let ((erased i3)) (qinv-get cfs (Cons _ a2 (Cons _ a1 (Nil _))) a3 t2 t3 i2 g3))
  (values a1 a2 a3 q1 q2 q3 (qinv-leaf cfs _ t3 q1 q2 q3 i3 lf) (MkFit3 e n ks x1 x2 x3 a1 a2 a3 z1 z2 z3 q1 q2 q3 p2 p3 k1 k2 k3 s1 f1 s2 f2 s3 f3)))

(def-fns _ $ (erased arity-pre : (erased (Nat) d u v a) (erased (List (Nat)) e n f ks) (erased (Hypermap d e n f) h) (erased (OrderList d f ks) ol) (erased (Lt u d) lu)
    (erased (Nth (Nat) f u v) pu) (erased (Nth (Nat) ks v a) pa) -> (erased (Nth (Nat) ks u a) r))
  (let ((erased a1) (erased pa1) (erased _)) (arity-at d u f ks ol lu))
  (let ((erased v1) (erased pv1) (erased _) (erased pa2)) (face-step d u a1 e n f ks h ol lu pa1))
  (let-match erased (nth-fn (Nat) f u v v1 pu pv1) (Refl _ _))
  (let-match erased (nth-fn (Nat) ks v a a1 pa pa2) (Refl _ _))
  pa1)

(def-fns _ $ (erased fit3-rot1 : (erased (Nat) d x1 a1 a2 a3) (erased (List (Nat)) e n f ks) (erased (Qn) q1 q2 q3) (erased (Geo d e n f ks) g) (erased (Lt x1 d) lx)
    (erased (Fit3 e n ks x1 a2 a3 a1 q2 q3 q1) ft) -> (erased (Nat) y) (erased (Fit3 e n ks y a1 a2 a3 q1 q2 q3) r) (erased (Lt y d) ly))
  (let-match erased ft (MkFit3 _ _ _ _ x2 x3 _ _ _ z1 z2 z3 _ _ _ p2 p3 k1 k2 k3 s1 f1 s2 f2 s3 f3))
  (let-match erased g (MkGeo _ _ _ _ _ h _ cu _ _))
  (let ((erased _) (erased ni) (erased _) (erased _) (erased _) (erased pn) (erased _)) (hyper-core d e n f h))
  (let ((erased z) (erased pz) (erased pz2) (erased _) (erased _)) (cubic-eq d x1 x2 n cu lx p2))
  (let-match erased (nth-fn (Nat) n x2 x3 z p3 pz) (Refl _ _))
  (values x3 (MkFit3 e n ks x3 x1 x2 a1 a2 a3 z3 z1 z2 q1 q2 q3 pz2 p2 k3 k1 k2 s3 f3 s1 f1 s2 f2) (img-lt d x2 x3 n ni pn (img-lt d x1 x2 n ni pn lx p2) p3)))

(def-fns _ $ (erased fit3-rot2 : (erased (Nat) d x1 a1 a2 a3) (erased (List (Nat)) e n f ks) (erased (Qn) q1 q2 q3) (erased (Geo d e n f ks) g) (erased (Lt x1 d) lx)
    (erased (Fit3 e n ks x1 a3 a1 a2 q3 q1 q2) ft) -> (erased (Nat) y) (erased (Fit3 e n ks y a1 a2 a3 q1 q2 q3) r) (erased (Lt y d) ly))
  (let-match erased ft (MkFit3 _ _ _ _ x2 x3 _ _ _ z1 z2 z3 _ _ _ p2 p3 k1 k2 k3 s1 f1 s2 f2 s3 f3))
  (let-match erased g (MkGeo _ _ _ _ _ h _ cu _ _))
  (let ((erased _) (erased ni) (erased _) (erased _) (erased _) (erased pn) (erased _)) (hyper-core d e n f h))
  (let ((erased z) (erased pz) (erased pz2) (erased _) (erased _)) (cubic-eq d x1 x2 n cu lx p2))
  (let-match erased (nth-fn (Nat) n x2 x3 z p3 pz) (Refl _ _))
  (values x2 (MkFit3 e n ks x2 x3 x1 a1 a2 a3 z2 z3 z1 q1 q2 q3 p3 pz2 k2 k3 k1 s2 f2 s3 f3 s1 f1) (img-lt d x1 x2 n ni pn lx p2)))

(def-fns _ $ (erased fit3-a : (erased (Nat) d x1 a1 a2 a3) (erased (List (Nat)) e n f ks) (erased (Qn) q1 q2 q3) (erased (Geo d e n f ks) g) (erased (Lt x1 d) lx)
    (erased (Fit3 e n ks x1 a1 a2 a3 q1 q2 q3) ft) -> (erased (Nat) y) (erased (FitZ e n ks y (MkQuiz (QaskR a1 (QaskLR a3 q1 q3)) (QaskR a2 q2))) r) (erased (Lt y d) ly))
  (let-match erased ft (MkFit3 _ _ _ _ x2 x3 _ _ _ z1 z2 z3 _ _ _ p2 p3 k1 k2 k3 s1 f1 s2 f2 s3 f3))
  (let-match erased g (MkGeo _ _ _ _ _ h pl cu ol _))
  (let ((erased nf) (erased ni) (erased _) (erased _) (erased pe) (erased pn) (erased _)) (hyper-core d e n f h))
  (let ((erased lx2)) (img-lt d x1 x2 n ni pn lx p2))
  (let ((erased y) (erased py) (erased ly)) (perm-nth d x2 e nf pe lx2))
  (let ((erased pyx) (erased _)) (plain-eq d x2 y e pl lx2 py))
  (let ((erased z) (erased pz) (erased pz2) (erased _) (erased _)) (cubic-eq d x1 x2 n cu lx p2))
  (let-match erased (nth-fn (Nat) n x2 x3 z p3 pz) (Refl _ _))
  (let-match erased s1 (MkQStepR _ _ _ u1 _ pu1 pz1))
  (let ((erased ky)) (arity-pre d y x1 a1 e n f ks h ol ly (fen d x1 x2 y e n f h lx p2 py) k1))
  (values y (MkFitZ e n ks y x2 (QaskR a1 (QaskLR a3 q1 q3)) (QaskR a2 q2)
    (FQR e n ks y a1 x3 (QaskLR a3 q1 q3) ky (MkQStepR e n y x2 x3 pyx p3)
      (FQLR e n ks x3 a3 z1 z3 q1 q3 k3 (MkQStepL e n x3 x1 u1 z1 pz2 pu1 pz1) f1 s3 f3))
    pyx (FQR e n ks x2 a2 z2 q2 k2 s2 f2)) ly))

(def-fns _ $ (erased fit3-b : (erased (Nat) d x1 a1 a2 a3) (erased (List (Nat)) e n f ks) (erased (Qn) q1 q2 q3) (erased (Geo d e n f ks) g) (erased (Lt x1 d) lx)
    (erased (Fit3 e n ks x1 a1 a2 a3 q1 q2 q3) ft) -> (erased (FitZ e n ks x1 (MkQuiz (QaskR a1 q1) (QaskR a3 (QaskLR a2 q3 q2)))) r))
  (let-match erased ft (MkFit3 _ _ _ _ x2 x3 _ _ _ z1 z2 z3 _ _ _ p2 p3 k1 k2 k3 s1 f1 s2 f2 s3 f3))
  (let-match erased g (MkGeo _ _ _ _ _ h pl cu ol _))
  (let ((erased nf) (erased ni) (erased _) (erased _) (erased pe) (erased pn) (erased _)) (hyper-core d e n f h))
  (let-match erased s1 (MkQStepR _ _ _ u _ pu pz1))
  (let-match erased s3 (MkQStepR _ _ _ u3 _ pu3 pz3))
  (let ((erased z) (erased pz) (erased pz2) (erased _) (erased _)) (cubic-eq d x1 x2 n cu lx p2))
  (let-match erased (nth-fn (Nat) n x2 x3 z p3 pz) (Refl _ _))
  (let ((erased lx3)) (img-lt d x2 x3 n ni pn (img-lt d x1 x2 n ni pn lx p2) p3))
  (let ((erased lu)) (img-lt d x1 u e nf pe lx pu))
  (let ((erased pux) (erased _)) (plain-eq d x1 u e pl lx pu))
  (let ((erased ku)) (arity-pre d u x3 a3 e n f ks h ol lu (fen d x3 x1 u e n f h lx3 pz2 pu) k3))
  (MkFitZ e n ks x1 u (QaskR a1 q1) (QaskR a3 (QaskLR a2 q3 q2)) (FQR e n ks x1 a1 z1 q1 k1 s1 f1) pu
    (FQR e n ks u a3 x2 (QaskLR a2 q3 q2) ku (MkQStepR e n u x1 x2 pux p2)
      (FQLR e n ks x2 a2 z3 z2 q3 q2 k2 (MkQStepL e n x2 x3 u3 z3 p3 pu3 pz3) f3 s2 f2))))

(def-fns _ $ (erased normq-fit : (erased (List (Nat)) e n ks) (erased (Nat) x) (erased (Qn) p q) (erased (NormQ p q) nq) (erased (FitQ e n ks x q) fq)
    -> (erased (FitQ e n ks x p) r))
  (match erased nq _
    ((NQ1 a) (let-match erased fq (FQLR _ _ _ _ _ _ _ _ _ pa _ _ _ _)) (FQ1 e n ks x a pa))
    ((NQL a l) (let-match erased fq (FQLR _ _ _ _ _ yl _ _ _ pa sl fl _ _)) (FQL e n ks x a yl l pa sl fl))
    ((NQR a r) (let-match erased fq (FQLR _ _ _ _ _ _ yr _ _ pa _ _ sr fr)) (FQR e n ks x a yr r pa sr fr))
    ((NQLR _ _ _) fq)))

(def-fns _ $ (erased triple-fit : (erased (Nat) d x1 a1 a2 a3) (erased (List (Nat)) e n f ks) (erased (Qn) q1 q2 q3) (erased (Quiz) qz) (erased (Geo d e n f ks) g)
    (erased (Lt x1 d) lx) (erased (QzTriple qz a1 a2 a3 q1 q2 q3) tr) (erased (Fit3 e n ks x1 a1 a2 a3 q1 q2 q3) ft)
    -> (erased (Nat) y) (erased (FitZ e n ks y qz) r) (erased (Lt y d) ly))
  (match erased tr _
    ((QT1 _ _ _ r1 _ _ _ nq)
      (let ((erased y) (erased fz) (erased ly)) (fit3-a d x1 a1 a2 a3 e n f ks q1 q2 q3 g lx ft))
      (let-match erased fz (MkFitZ _ _ _ _ y1 _ _ f0 py f1))
      (let-match erased f0 (FQR _ _ _ _ _ x3 _ k0 s0 fx3))
      (values y (MkFitZ e n ks y y1 (QaskR a1 r1) (QaskR a2 q2) (FQR e n ks y a1 x3 r1 k0 s0 (normq-fit e n ks x3 r1 (QaskLR a3 q1 q3) nq fx3)) py f1) ly))
    ((QT2 _ _ _ r2 _ _ _ nq)
      (let-match erased (fit3-b d x1 a1 a2 a3 e n f ks q1 q2 q3 g lx ft) (MkFitZ _ _ _ _ u _ _ f0 pu f1))
      (let-match erased f1 (FQR _ _ _ _ _ x2 _ ku su fx2))
      (values x1 (MkFitZ e n ks x1 u (QaskR a1 q1) (QaskR a3 r2) f0 pu (FQR e n ks u a3 x2 r2 ku su (normq-fit e n ks x2 r2 (QaskLR a2 q3 q2) nq fx2))) lx))))

; A configuration of cfs with a certified quiz that, or whose mirror image, fits some dart.
(def-adts $ (QzHit : ((List (Config)) cfs) ((Nat) d) ((List (Nat)) e n ks) -> Type)
  enum
  (many MkQzHit : (erased (List (Config)) cfs) (erased (Nat) d y) (erased (List (Nat)) e n ks) (erased (Config) cf) (erased (Quiz) qz qz2)
      (erased (Mem (Config) cf cfs) m) (erased (CfQz cf qz) c) (erased (Variant qz qz2) v) (erased (FitZ e n ks y qz2) fz) (erased (Lt y d) ly)
      -> (QzHit cfs d e n ks)))

(def-fns _ $ (erased qzt-hit : (erased (List (Config)) cfs) (erased (Nat) d) (erased (List (Nat)) e n f ks) (erased (Qzt) qt) (erased (QInv cfs (Nil (Nat)) qt) qi)
    (erased (Geo d e n f ks) g) (erased (HasFit d e n ks qt) hf) -> (erased (QzHit cfs d e n ks) r))
  (let-match erased hf (MkHasFit _ x1 _ _ _ _ lx fit))
  (let ((erased b1) (erased b2) (erased b3) (erased r1) (erased r2) (erased r3) (erased en) (erased ft)) (qzt-entry cfs e n ks qt x1 qi fit))
  (let-match erased en (MkQEntry _ cf qz qz2 a1 a2 a3 _ _ _ q1 q2 q3 _ _ _ m c v tr rt))
  (let ((erased x) (erased ft2) (erased lx2))
    (match erased rt (((Nat) x) ((Fit3 e n ks x a1 a2 a3 q1 q2 q3) ft2) ((Lt x d) lx2))
      ((Rt0 _ _ _ _ _ _) (values x1 ft lx))
      ((Rt1 _ _ _ _ _ _) (fit3-rot1 d x1 a1 a2 a3 e n f ks q1 q2 q3 g lx ft))
      ((Rt2 _ _ _ _ _ _) (fit3-rot2 d x1 a1 a2 a3 e n f ks q1 q2 q3 g lx ft))))
  (let ((erased y) (erased fz) (erased ly)) (triple-fit d x a1 a2 a3 e n f ks q1 q2 q3 qz2 g lx2 tr ft2))
  (MkQzHit cfs d y e n ks cf qz qz2 m c v fz ly))

(def-adts $ (RevA : ((List (Nat)) path ps full) -> Type)
  enum
  (many RevNil : (erased (List (Nat)) ps) -> (RevA (Nil (Nat)) ps ps))
  (many RevCons : (erased (List (Nat)) rest ps full) (erased (Nat) a) (erased (RevA rest (Cons (Nat) a ps) full) r) -> (RevA (Cons (Nat) a rest) ps full)))

(def-fns _ $ (many put-c : (erased (List (Config)) cfs) (erased (List (Nat)) ps full) (subterm many (List (Nat)) path) (subterm many (Qzt) t) (many (Qn) q1 q2 q3)
    (erased (QEntry cfs full q1 q2 q3) en) (erased (RevA path ps full) ra) (erased (QInv cfs ps t) qi) -> (many (Qzt) r) (erased (QInv cfs ps r) qr))
  (let-match many path (Cons _ a rest) ((Nil _) (let-match erased ra (RevNil _)) (values (QztLeaf q1 q2 q3 t) (QILeaf cfs ps q1 q2 q3 t en qi))))
  (let-match erased ra (RevCons _ _ _ _ ra1))
  (match many t _
    ((QztNode t5 t6 t7 t8)
      (let-match erased qi (QINode _ _ _ _ _ _ i5 i6 i7 i8))
      (match many (nat-eq a 5) _
        ((Equal _ _ _)
          (let ((many r5) (erased j5)) (notail $ put-c cfs (Cons _ 5 ps) full rest t5 q1 q2 q3 en ra1 i5))
          (values (QztNode r5 t6 t7 t8) (QINode cfs ps r5 t6 t7 t8 j5 i6 i7 i8)))
        (else (match many (nat-eq a 6) _
          ((Equal _ _ _)
            (let ((many r6) (erased j6)) (notail $ put-c cfs (Cons _ 6 ps) full rest t6 q1 q2 q3 en ra1 i6))
            (values (QztNode t5 r6 t7 t8) (QINode cfs ps t5 r6 t7 t8 i5 j6 i7 i8)))
          (else (match many (nat-eq a 7) _
            ((Equal _ _ _)
              (let ((many r7) (erased j7)) (notail $ put-c cfs (Cons _ 7 ps) full rest t7 q1 q2 q3 en ra1 i7))
              (values (QztNode t5 t6 r7 t8) (QINode cfs ps t5 t6 r7 t8 i5 i6 j7 i8)))
            (else
              (let-match many (nat-eq a 8) (Equal _ _ _) (else (values t qi)))
              (let ((many r8) (erased j8)) (notail $ put-c cfs (Cons _ 8 ps) full rest t8 q1 q2 q3 en ra1 i8))
              (values (QztNode t5 t6 t7 r8) (QINode cfs ps t5 t6 t7 r8 i5 i6 i7 j8)))))))))
    ((QztHub t58 t9 t10 t11)
      (let-match erased qi (QIHub _ _ _ _ _ _ i58 i9 i10 i11))
      (match many (nat-eq a 9) _
        ((Equal _ _ _)
          (let ((many r9) (erased j9)) (notail $ put-c cfs (Cons _ 9 ps) full rest t9 q1 q2 q3 en ra1 i9))
          (values (QztHub t58 r9 t10 t11) (QIHub cfs ps t58 r9 t10 t11 i58 j9 i10 i11)))
        (else (match many (nat-eq a 10) _
          ((Equal _ _ _)
            (let ((many r10) (erased j10)) (notail $ put-c cfs (Cons _ 10 ps) full rest t10 q1 q2 q3 en ra1 i10))
            (values (QztHub t58 t9 r10 t11) (QIHub cfs ps t58 t9 r10 t11 i58 i9 j10 i11)))
          (else (match many (nat-eq a 11) _
            ((Equal _ _ _)
              (let ((many r11) (erased j11)) (notail $ put-c cfs (Cons _ 11 ps) full rest t11 q1 q2 q3 en ra1 i11))
              (values (QztHub t58 t9 t10 r11) (QIHub cfs ps t58 t9 t10 r11 i58 i9 i10 j11)))
            (else
              (let ((many r58) (erased j58)) (notail $ put-c cfs ps full path t58 q1 q2 q3 en ra i58))
              (values (QztHub r58 t9 t10 t11) (QIHub cfs ps r58 t9 t10 t11 j58 i9 i10 i11)))))))))
    (else (values t qi))))

(def-fns _ $ (many put3-c : (erased (List (Config)) cfs) (erased (Config) cf) (erased (Quiz) qz qz2) (erased (Nat) a1 a2 a3) (erased (Qn) q1 q2 q3)
    (many (Nat) b1 b2 b3) (many (Qn) r1 r2 r3) (erased (Mem (Config) cf cfs) m) (erased (CfQz cf qz) c) (erased (Variant qz qz2) v)
    (erased (QzTriple qz2 a1 a2 a3 q1 q2 q3) tr) (erased (Rot3 a1 a2 a3 q1 q2 q3 b1 b2 b3 r1 r2 r3) rt) (many (Qzt) t) (erased (QInv cfs (Nil (Nat)) t) qi)
    -> (many (Qzt) r) (erased (QInv cfs (Nil (Nat)) r) qr))
  (let ((erased full)) (Cons (Nat) b3 (Cons (Nat) b2 (Cons (Nat) b1 (Nil (Nat))))))
  (put-c cfs (Nil _) full (Cons _ b1 $ Cons _ b2 $ Cons _ b3 $ Nil _) t r1 r2 r3 (MkQEntry cfs cf qz qz2 a1 a2 a3 b1 b2 b3 q1 q2 q3 r1 r2 r3 m c v tr rt)
    (RevCons _ _ full b1 (RevCons _ _ full b2 (RevCons _ _ full b3 (RevNil full)))) qi))

(def-fns _ $ (many put-rot-c : (erased (List (Config)) cfs) (erased (Config) cf) (erased (Quiz) qz qz2) (many (Nat) a1 a2 a3) (many (Qn) q1 q2 q3)
    (erased (Mem (Config) cf cfs) m) (erased (CfQz cf qz) c) (erased (Variant qz qz2) v) (erased (QzTriple qz2 a1 a2 a3 q1 q2 q3) tr) (many (Qzt) t)
    (erased (QInv cfs (Nil (Nat)) t) qi) -> (many (Qzt) r) (erased (QInv cfs (Nil (Nat)) r) qr))
  (let ((erased (Rot3 a1 a2 a3 q1 q2 q3 a1 a2 a3 q1 q2 q3) r0)) (Rt0 a1 a2 a3 q1 q2 q3))
  (let-match many (nat-ltb 8 a1) (BFalse)
    ((BTrue) (put3-c cfs cf qz qz2 a1 a2 a3 q1 q2 q3 a1 a2 a3 q1 q2 q3 m c v tr r0 t qi)))
  (let ((many t2) (erased i2)) (put3-c cfs cf qz qz2 a1 a2 a3 q1 q2 q3 a3 a1 a2 q3 q1 q2 m c v tr (Rt2 a1 a2 a3 q1 q2 q3) t qi))
  (let ((many t1) (erased i1)) (put3-c cfs cf qz qz2 a1 a2 a3 q1 q2 q3 a2 a3 a1 q2 q3 q1 m c v tr (Rt1 a1 a2 a3 q1 q2 q3) t2 i2))
  (put3-c cfs cf qz qz2 a1 a2 a3 q1 q2 q3 a1 a2 a3 q1 q2 q3 m c v tr r0 t1 i1))

(def-adts $ (NormD : ((Qn) q) -> Type)
  enum
  (many NLR : (erased (Qn) q) (many (Nat) a) (many (Qn) l r) (erased (NormQ q (QaskLR a l r)) p) -> (NormD q))
  (many NOther : (erased (Qn) q) -> (NormD q)))

(def-fns _ $ (many normq-c : (many (Qn) q) -> (many (NormD q) r))
  (match many q _
    ((Qask1 a) (NLR q a (Qask0) (Qask0) (NQ1 a)))
    ((QaskL a l) (NLR q a l (Qask0) (NQL a l)))
    ((QaskR a r) (NLR q a (Qask0) r (NQR a r)))
    ((QaskLR a l r) (NLR q a l r (NQLR a l r)))
    (else (NOther q))))

(def-fns _ $ (many store-c : (erased (List (Config)) cfs) (erased (Config) cf) (erased (Quiz) qz) (erased (Nat) qa1 qa2) (many (Qn) p1 p2)
    (erased (Mem (Config) cf cfs) m) (erased (CfQz cf qz) c) (erased (Variant qz (MkQuiz (QaskR qa1 p1) (QaskR qa2 p2))) v) (many (Nat) ka1 ka2)
    (erased (Eq (Nat) ka1 qa1) e1) (erased (Eq (Nat) ka2 qa2) e2) (many (Qzt) t) (erased (QInv cfs (Nil (Nat)) t) qi) -> (many (Qzt) r) (erased (QInv cfs (Nil (Nat)) r) qr))
  (let-match erased e1 (Refl _ _))
  (let-match erased e2 (Refl _ _))
  (let ((erased qz2)) (MkQuiz (QaskR qa1 p1) (QaskR qa2 p2)))
  (match many (normq-c p1) _
    ((NLR _ qa1r q1l q1r n1)
      (let ((many (Qzt) t1) (erased (QInv cfs (Nil (Nat)) t1) i1))
        (put-rot-c cfs cf qz qz2 ka1 ka2 qa1r q1l p2 q1r m c v (QT1 qa1 qa2 qa1r p1 q1l p2 q1r n1) t qi))
      (let-match many (normq-c p2) (NLR _ qa2r q2l q2r n2)
        (else (values t1 i1)))
      (match many (nat-ltb qa1r qa2r) _
        ((BTrue) (values t1 i1))
        ((BFalse) (put-rot-c cfs cf qz qz2 ka1 qa2r ka2 p1 q2r q2l m c v (QT2 qa1 qa2r qa2 p2 p1 q2r q2l n2) t qi))))
    (else
      (match many (normq-c p2) _
        ((NLR _ qa2r q2l q2r n2) (put-rot-c cfs cf qz qz2 ka1 qa2r ka2 p1 q2r q2l m c v (QT2 qa1 qa2r qa2 p2 p1 q2r q2l n2) t qi))
        (else (values t qi))))))

(def-adts $ (FlipD : ((Qn) q) -> Type)
  enum
  (many MkFlipD : (erased (Qn) q) (many (Qn) r) (erased (FlipQ q r) p) -> (FlipD q)))

(def-fns _ $ (many flipq-c : (subterm many (Qn) q) -> (many (FlipD q) r))
  (match many q _
    ((Qask0) (MkFlipD q q (FlQ0)))
    ((Qask1 a) (MkFlipD q q (FlQ1 a)))
    ((QaskL a l) (let-match many (notail $ flipq-c l) (MkFlipD _ l2 p)) (MkFlipD q (QaskR a l2) (FlQL a l l2 p)))
    ((QaskR a r) (let-match many (notail $ flipq-c r) (MkFlipD _ r2 p)) (MkFlipD q (QaskL a r2) (FlQR a r r2 p)))
    ((QaskLR a l r)
      (let-match many (notail $ flipq-c l) (MkFlipD _ l2 pl))
      (let-match many (notail $ flipq-c r) (MkFlipD _ r2 pr))
      (MkFlipD q (QaskLR a r2 l2) (FlQLR a l r l2 r2 pl pr)))
    ((QaskLL a l) (let-match many (notail $ flipq-c l) (MkFlipD _ l2 p)) (MkFlipD q (QaskRR a l2) (FlQLL a l l2 p)))
    ((QaskRR a r) (let-match many (notail $ flipq-c r) (MkFlipD _ r2 p)) (MkFlipD q (QaskLL a r2) (FlQRR a r r2 p)))))

(def-fns _ $ (many store-cf-c : (erased (List (Config)) cfs) (many (Config) cf) (many (Quiz) qz) (many (Bool) sym) (erased (Mem (Config) cf cfs) m)
    (erased (CfQz cf qz) c) (many (Qzt) t) (erased (QInv cfs (Nil (Nat)) t) qi) -> (many (Qzt) r) (erased (QInv cfs (Nil (Nat)) r) qr))
  (let-match erased c (MkCfQz _ _ _ _ _ _ _ _ _ _ _ _ _ qc))
  (let-match erased qc (MkQzCert _ _ _ a0 a1 _ _ _ _ _ _ _ _ _ _ q01 q10 _ _ _ _ _ _ _ _ _ _ _))
  (let-match many qz (MkQuiz b0 b1))
  (let-match many b0 (QaskR k0 p01))
  (let-match many b1 (QaskR k1 p10))
  (let ((many (Qzt) t0) (erased (QInv cfs (Nil (Nat)) t0) i0))
    (match many sym _
      ((BTrue) (values t qi))
      ((BFalse)
        (let-match many (flipq-c p01) (MkFlipD _ r01 f01))
        (let-match many (flipq-c p10) (MkFlipD _ r10 f10))
        (store-c cfs cf qz a0 a1 r10 r01 m c (VFlip qz (MkQuiz (QaskR a0 r10) (QaskR a1 r01)) (MkFlipQz a0 a1 p01 p10 r01 r10 f01 f10)) k0 k1
          (Refl _ k0) (Refl _ k1) t qi))))
  (store-c cfs cf qz a0 a1 p01 p10 m c (VSame qz) k0 k1 (Refl _ k0) (Refl _ k1) t0 i0))

(def-adts $ (Suf : (Type A) ((List A) ys xs) -> Type)
  enum
  (many SfRefl : (erased Type A) (erased (List A) xs) -> (Suf A xs xs))
  (many SfStep : (erased Type A) (erased A y) (erased (List A) ys xs) (erased (Suf A (Cons A y ys) xs) p) -> (Suf A ys xs)))

(def-fns _ $ (erased suf-mem : (erased Type A) (erased A x) (erased (List A) zs xs) (subterm erased (Suf A zs xs) sf) (erased (Mem A x zs) m) -> (erased (Mem A x xs) r))
  (match erased sf _
    ((SfRefl _ _) m)
    ((SfStep _ y _ _ sf1) (suf-mem A x (Cons A y zs) xs sf1 (MemThere A x y zs m)))))

(def-fns _ $ (many tree-rec-c : (erased (List (Config)) cfs) (many (Qzt) qt) (erased (QInv cfs (Nil (Nat)) qt) qi) (subterm many (List (Config)) rest)
    (erased (Suf (Config) rest cfs) sf) -> (many (Qzt) r) (many (Checked (QInv cfs (Nil (Nat)) r)) c))
  (let-match many rest (Cons _ cf rest1) ((Nil _) (values qt (ChkYes _ qi))))
  (let ((many qz)) (cfquiz cf))
  (let-match many (cfqz-c cf qz) (ChkYes _ cq) ((ChkNo _) (values qt (ChkNo _))))
  (let-match many cf (MkConfig sym _ _))
  (let ((many qt1) (erased qi1)) (store-cf-c cfs cf qz sym (suf-mem (Config) cf rest cfs sf (MemHere (Config) cf rest1)) cq qt qi))
  (match many qt1 _
    ((QztHub _ _ _ _) (tail $ tree-rec-c cfs qt1 qi1 rest1 (SfStep (Config) cf rest1 cfs sf)))
    (else (values (QztNil) (ChkYes _ (QINil cfs (Nil _)))))))

(def-fns _ $ (erased qinv-n1 : (erased (List (Config)) cfs) (erased (List (Nat)) ps) -> (erased (QInv cfs ps (QztNode (QztNil) (QztNil) (QztNil) (QztNil))) r))
  (QINode cfs ps (QztNil) (QztNil) (QztNil) (QztNil) (QINil cfs _) (QINil cfs _) (QINil cfs _) (QINil cfs _)))

(def-fns _ $ (erased qinv-n2 : (erased (List (Config)) cfs) (erased (List (Nat)) ps) (erased (Qzt) n1) (erased (Eq (Qzt) n1 (QztNode (QztNil) (QztNil) (QztNil) (QztNil))) e)
    -> (erased (QInv cfs ps (QztNode n1 n1 n1 n1)) r))
  (let-match erased e (Refl _ _))
  (QINode cfs ps n1 n1 n1 n1 (qinv-n1 cfs _) (qinv-n1 cfs _) (qinv-n1 cfs _) (qinv-n1 cfs _)))

(def-fns _ $ (many quiz-tree-c : (many (List (Config)) cfs) -> (many (Qzt) r) (many (Checked (QInv cfs (Nil (Nat)) r)) c))
  (let ((many n1)) (QztNode (QztNil) (QztNil) (QztNil) (QztNil)))
  (let ((many n2)) (QztNode n1 n1 n1 n1))
  (let ((erased e1)) (Refl (Qzt) n1))
  (let ((erased i58)) (QINode cfs (Nil _) n2 n2 n2 n2 (qinv-n2 cfs _ n1 e1) (qinv-n2 cfs _ n1 e1) (qinv-n2 cfs _ n1 e1) (qinv-n2 cfs _ n1 e1)))
  (tree-rec-c cfs (QztHub (QztNode n2 n2 n2 n2) n2 n2 n2) (QIHub cfs (Nil _) (QztNode n2 n2 n2 n2) n2 n2 n2 i58 (qinv-n2 cfs _ n1 e1) (qinv-n2 cfs _ n1 e1)
    (qinv-n2 cfs _ n1 e1)) cfs (SfRefl (Config) cfs)))
