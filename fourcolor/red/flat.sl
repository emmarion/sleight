(let ((erased Cnt)) (Copy (U62)))

(def-fns _ $ (erased imm-cnt : (erased Cnt x) -> (erased (Imm Cnt x) r))
  (let-match erased x (MkCopy _ v))
  (let-match erased v (MkU62 n p))
  (ImmCoerce _ _ _ _ _ _ (coercible-wrap (Shared) MkCopy (U62) v) (ImmCoerce _ _ _ _ _ _ (coercible-wrap (Shared) MkU62 n p) (ImmNat n p))))

(def-adts $ (Try : (Type P) -> Type)
  enum
  (many TryOk : (erased Type P) (erased P p) -> (Try P))
  (many TryNo : (erased Type P) -> (Try P)))

; q is 3p.
(def-adts $ (Thrice : ((Nat) p) ((Nat) q) -> Type)
  enum
  (many TZ : -> (Thrice (Zero) (Zero)))
  (many TS : (erased (Nat) p q) (erased (Thrice p q) t) -> (Thrice (Succ p) (Succ (Succ (Succ q))))))

(def-fns _ $ (erased thrice-exists : (subterm erased (Nat) p) -> (erased (Nat) q) (erased (Thrice p q) t))
  (let-match erased p (Succ p1) ((Zero) (values (Zero) (TZ))))
  (let ((erased q1) (erased t1)) (thrice-exists p1))
  (values (Succ (Succ (Succ q1))) (TS p1 q1 t1)))

(def-fns _ $ (erased thrice-fn : (erased (Nat) p q r) (subterm erased (Thrice p q) s) (erased (Thrice p r) t) -> (erased (Eq (Nat) q r) e))
  (let-match erased s (TS p1 q1 s1) ((TZ) (let-match erased t (TZ)) (Refl _ q)))
  (let-match erased t (TS _ r1 t1))
  (let-match erased (thrice-fn p1 q1 r1 s1 t1) (Refl _ _))
  (Refl _ q))

(def-fns _ $ (erased thrice-adds : (erased (Nat) p q) (subterm erased (Thrice p q) t) ->
    (erased (Nat) d) (erased (Add p p d) a) (erased (Add d p q) b))
  (let-match erased t (TS p1 q1 t1) ((TZ) (values (Zero) (AddZero (Zero)) (AddZero (Zero)))))
  (let ((erased d1) (erased a1) (erased b1)) (thrice-adds p1 q1 t1))
  (values (Succ (Succ d1)) (AddSucc p1 p (Succ d1) (add-succ-right p1 p1 d1 a1))
    (AddSucc (Succ d1) p (Succ (Succ q1)) (AddSucc d1 p (Succ q1) (add-succ-right d1 p1 q1 b1)))))

(def-fns _ $ (erased adds-thrice : (erased (Nat) p d q) (erased (Add p p d) a) (erased (Add d p q) b) -> (erased (Thrice p q) t))
  (let ((erased q1) (erased t1)) (thrice-exists p))
  (let ((erased d1) (erased a1) (erased b1)) (thrice-adds p q1 t1))
  (let-match erased (add-fn p p d1 d a1 a) (Refl _ _))
  (let-match erased (add-fn d p q1 q b1 b) (Refl _ _))
  t1)

(def-fns _ $ (erased thrice-le : (erased (Nat) p q) (subterm erased (Thrice p q) t) -> (erased (Lt p (Succ q)) l))
  (let-match erased t (TS p1 q1 t1) ((TZ) (LtZ (Zero))))
  (LtS p1 (Succ (Succ (Succ q1))) (lt-weaken p1 (Succ (Succ q1)) (lt-weaken p1 (Succ q1) (thrice-le p1 q1 t1)))))

(def-fns _ $ (erased thrice-lt : (erased (Nat) p r q s) (subterm erased (Lt p r) l) (erased (Thrice p q) a) (erased (Thrice r s) b) ->
    (erased (Lt (Succ (Succ q)) s) c))
  (let-match erased b (TS r1 s1 b1) (absurd (TZ) l))
  (match erased l _
    ((LtZ _) (let-match erased a (TZ)) (LtS (Succ (Zero)) (Succ (Succ s1)) (LtS (Zero) (Succ s1) (LtZ s1))))
    ((LtS p1 _ l1)
      (let-match erased a (TS _ q1 a1))
      (LtS _ _ (LtS _ _ (LtS _ _ (thrice-lt p1 r1 q1 s1 l1 a1 b1)))))))

(def-fns _ $ (many thrice-c : (many (Nat) p) (erased (Nat) q) (erased (Thrice p q) t) (erased (Lt q u62-modulus) b) -> (many q is r))
  (let ((erased d) (erased a1) (erased a2)) (thrice-adds p q t))
  (let ((many d1)) (u62-add p p d a1 (lt-le-trans d (Succ q) u62-modulus (add-le-left d p q a2) (LtS q u62-modulus b))))
  (u62-add d1 p q a2 b))

; q is the prefix p followed by the colour e, as base-3 numbers with digit e - 1.
(def-adts $ (Kid : ((Nat) p) ((Col) e) ((Nat) q) -> Type)
  enum
  (many Ki1 : (erased (Nat) p q) (erased (Thrice p q) t) -> (Kid p (C1) q))
  (many Ki2 : (erased (Nat) p q) (erased (Thrice p q) t) -> (Kid p (C2) (Succ q)))
  (many Ki3 : (erased (Nat) p q) (erased (Thrice p q) t) -> (Kid p (C3) (Succ (Succ q)))))

(def-fns _ $ (erased kid-base : (erased (Nat) p q) (erased (Col) e) (erased (Kid p e q) k) ->
    (erased (Nat) q0) (erased (Thrice p q0) t) (erased (Lt q (Succ (Succ (Succ q0)))) hi) (erased (Lt q0 (Succ q)) lo))
  (match erased k _
    ((Ki1 _ _ t) (values q t (lt-weaken q (Succ (Succ q)) (lt-weaken q (Succ q) (lt-succ q))) (lt-succ q)))
    ((Ki2 _ q0 t) (values q0 t (LtS q0 (Succ (Succ q0)) (lt-weaken q0 (Succ q0) (lt-succ q0))) (lt-weaken q0 (Succ q0) (lt-succ q0))))
    ((Ki3 _ q0 t) (values q0 t (lt-succ q) (lt-weaken q0 (Succ (Succ q0)) (lt-weaken q0 (Succ q0) (lt-succ q0)))))))

(def-fns _ $ (erased kid-lt : (erased (Nat) p r a b) (erased (Col) e f) (erased (Lt p r) l) (erased (Kid p e a) ka) (erased (Kid r f b) kb) ->
    (erased (Lt a b) c))
  (let ((erased q) (erased tq) (erased hi) (erased _)) (kid-base p a e ka))
  (let ((erased s) (erased ts) (erased _) (erased lo)) (kid-base r b f kb))
  (lt-le-trans a s b (lt-le-trans a (Succ (Succ (Succ q))) s hi (LtS _ _ (thrice-lt p r q s l tq ts))) lo))

(def-fns _ $ (erased kid-apart : (erased (Nat) p r a b) (erased (Col) e f) (erased (Apart (Nat) Lt p r) ap) (erased (Kid p e a) ka)
    (erased (Kid r f b) kb) -> (erased (Apart (Nat) Lt a b) c))
  (match erased ap _
    ((ApLt _ _ _ _ l) (ApLt (Nat) Lt a b (kid-lt p r a b e f l ka kb)))
    ((ApGt _ _ _ _ l) (ApGt (Nat) Lt a b (kid-lt r p b a f e l kb ka)))))

(def-fns _ $ (many kid-c : (many (Nat) p) (many (Col) e) (erased (Nat) q) (erased (Kid p e q) k) (erased (Lt q u62-modulus) b) -> (many q is r))
  (let ((erased q0) (erased t) (erased _) (erased lo)) (kid-base p q e k))
  (let ((many r0)) (thrice-c p q0 t (lt-le-trans q0 (Succ q) u62-modulus lo (LtS q u62-modulus b))))
  (match many e _
    (absurd (C0) k)
    ((C1) (let-match erased k (Ki1 _ _ t1)) (let-match erased (thrice-fn p q0 q t t1) (Refl _ _)) r0)
    ((C2) (let-match erased k (Ki2 _ q1 t1)) (let-match erased (thrice-fn p q0 q1 t t1) (Refl _ _)) (u62-inc r0 b))
    ((C3)
      (let-match erased k (Ki3 _ q1 t1))
      (let-match erased (thrice-fn p q0 q1 t t1) (Refl _ _))
      (u62-inc (u62-inc r0 (lt-trans _ _ _ (lt-succ (Succ q0)) b)) b))))

; Reading the colours et from the prefix p gives the prefix q.
(def-adts $ (TIdx : ((Nat) p) ((List (Col)) et) ((Nat) q) -> Type)
  enum
  (many TINil : (erased (Nat) p) -> (TIdx p (Nil (Col)) p))
  (many TICons : (erased (Nat) p q r) (erased (Col) e) (erased (List (Col)) et) (erased (Kid p e q) k) (erased (TIdx q et r) t)
      -> (TIdx p (Cons (Col) e et) r)))

(def-fns _ $ (erased tidx-lt : (erased (Nat) p p2 ix iy j) (erased (List (Col)) et et2) (erased (Lt p p2) l) (subterm erased (TIdx p et ix) a)
    (erased (TIdx p2 et2 iy) b) (erased (Length (Col) et j) la) (erased (Length (Col) et2 j) lb) -> (erased (Lt ix iy) r))
  (match erased a _
    ((TINil _) (let-match erased la (LengthNil _)) (let-match erased lb (LengthNil _)) (let-match erased b (TINil _)) l)
    ((TICons _ q _ e et1 k a1)
      (let-match erased la (LengthCons _ _ _ j1 la1))
      (let-match erased lb (LengthCons _ e2 et3 _ lb1))
      (let-match erased b (TICons _ q2 _ _ _ k2 b1))
      (tidx-lt q q2 ix iy j1 et1 et3 (kid-lt p p2 q q2 e e2 l k k2) a1 b1 la1 lb1))))

; p is the prefix whose colours are those of pre reversed.
(def-adts $ (RIdx : ((List (Col)) pre) ((Nat) p) -> Type)
  enum
  (many RINil : -> (RIdx (Nil (Col)) (Zero)))
  (many RICons : (erased (List (Col)) pre) (erased (Nat) p q) (erased (Col) e) (erased (RIdx pre p) r) (erased (Kid p e q) k)
      -> (RIdx (Cons (Col) e pre) q)))

(def-fns _ $ (erased ridx-tidx : (erased (List (Col)) pre w et) (erased (Nat) p i) (subterm erased (RIdx pre p) r)
    (erased (RevApp (Col) pre w et) ra) (erased (TIdx p w i) ti) -> (erased (TIdx (Zero) et i) res))
  (match erased r _
    ((RINil) (let-match erased ra (RANil _ _)) ti)
    ((RICons pre1 p1 _ e r1 k)
      (let-match erased ra (RACons _ _ _ _ _ ra1))
      (ridx-tidx pre1 (Cons _ e w) et p1 i r1 ra1 (TICons p1 p i e w k ti)))))

(def-adts $ (Occ : ((Ctree) t) -> Type)
  enum
  (many OccN : (erased (Ctree) t1 t2 t3) -> (Occ (CNode t1 t2 t3)))
  (many OccL : (erased (Ctree) lf) -> (Occ (CLeaf lf))))

(def-adts $ (Occ3 : ((Ctree) t1) ((Ctree) t2) ((Ctree) t3) -> Type)
  enum
  (many Occ1 : (erased (Ctree) t1 t2 t3) (erased (Occ t1) o) -> (Occ3 t1 t2 t3))
  (many Occ2 : (erased (Ctree) t1 t2 t3) (erased (Occ t2) o) -> (Occ3 t1 t2 t3))
  (many Occ3c : (erased (Ctree) t1 t2 t3) (erased (Occ t3) o) -> (Occ3 t1 t2 t3)))

(def-adts $ (OccDec : ((Ctree) t) -> Type)
  enum
  (many OdE : -> (OccDec (CEmpty)))
  (many OdY : (erased (Ctree) t) (erased (Occ t) o) -> (OccDec t)))

(def-fns _ $ (many occ-c : (many (Ctree) t) -> (many (OccDec t) d))
  (match many t _ ((CEmpty) (OdE)) ((CNode a b c) (OdY t (OccN a b c))) ((CLeaf lf) (OdY t (OccL lf)))))

(def-fns _ $ (erased absurd occ3-empty : (erased (Occ3 (CEmpty) (CEmpty) (CEmpty)) o) -> (erased (False) f))
  (match erased o _ (absurd (Occ1 _ _ _ v) v) (absurd (Occ2 _ _ _ v) v) (absurd (Occ3c _ _ _ v) v)))

; t is the node of t1, t2 and t3, or empty when all three are.
(def-adts $ (Cn : ((Ctree) t1) ((Ctree) t2) ((Ctree) t3) ((Ctree) t) -> Type)
  enum
  (many CnE : -> (Cn (CEmpty) (CEmpty) (CEmpty) (CEmpty)))
  (many CnN : (erased (Ctree) t1 t2 t3) (erased (Occ3 t1 t2 t3) o) -> (Cn t1 t2 t3 (CNode t1 t2 t3))))

(def-fns _ $ (many cn-c : (many (Ctree) t1 t2 t3) -> (many (Ctree) t) (erased (Cn t1 t2 t3 t) c))
  (let-match many (occ-c t1) (OdE) ((OdY _ o) (values (CNode t1 t2 t3) (CnN t1 t2 t3 (Occ1 t1 t2 t3 o)))))
  (let-match many (occ-c t2) (OdE) ((OdY _ o) (values (CNode t1 t2 t3) (CnN t1 t2 t3 (Occ2 t1 t2 t3 o)))))
  (let-match many (occ-c t3) (OdE) ((OdY _ o) (values (CNode t1 t2 t3) (CnN t1 t2 t3 (Occ3c t1 t2 t3 o)))))
  (values (CEmpty) (CnE)))

(def-fns _ $ (erased cn-fn : (erased (Ctree) t1 t2 t3 t u) (erased (Cn t1 t2 t3 t) c) (erased (Cn t1 t2 t3 u) d) -> (erased (Eq (Ctree) t u) r))
  (match erased c _
    ((CnE) (let-match erased d (CnE) (absurd (CnN _ _ _ o) (occ3-empty o))) (Refl _ t))
    ((CnN _ _ _ o) (let-match erased d (CnN _ _ _ _) (absurd (CnE) (occ3-empty o))) (Refl _ t))))

(def-fns _ $ (erased cn-cons : (erased (Ctree) t1 t2 t3 t) (erased (Cn t1 t2 t3 t) c) -> (erased (CtCons t1 t2 t3 t) r))
  (match erased c _ ((CnE) (CCEmpty)) ((CnN _ _ _ _) (CCNode t1 t2 t3))))

(def-fns _ $ (erased cn-sel : (erased (Ctree) t1 t2 t3 t) (erased (Cn t1 t2 t3 t) c) ->
    (erased (CtSel t (C1) t1) s1) (erased (CtSel t (C2) t2) s2) (erased (CtSel t (C3) t3) s3))
  (match erased c _
    ((CnE) (values (SelE (C1)) (SelE (C2)) (SelE (C3))))
    ((CnN _ _ _ _) (values (SelN1 t1 t2 t3) (SelN2 t1 t2 t3) (SelN3 t1 t2 t3)))))

; t has height j and no node all of whose children are empty.
(def-adts $ (CtCanon : ((Nat) j) ((Ctree) t) -> Type)
  enum
  (many CanL : (erased (Ctree) t) (erased (CtH (Zero) t) k) -> (CtCanon (Zero) t))
  (many CanN : (erased (Nat) j) (erased (Ctree) t1 t2 t3 t) (erased (CtCanon j t1) c1) (erased (CtCanon j t2) c2) (erased (CtCanon j t3) c3)
      (erased (Cn t1 t2 t3 t) c) -> (CtCanon (Succ j) t)))

(def-fns _ $ (erased canon-h : (erased (Nat) j) (erased (Ctree) t) (subterm erased (CtCanon j t) c) -> (erased (CtH j t) k))
  (match erased c _
    ((CanL _ k) k)
    ((CanN j1 t1 t2 t3 _ c1 c2 c3 cn)
      (cons-h j1 t1 t2 t3 t (cn-cons t1 t2 t3 t cn) (canon-h j1 t1 c1) (canon-h j1 t2 c2) (canon-h j1 t3 c3)))))

(def-fns _ $ (erased canon-empty : (subterm erased (Nat) j) -> (erased (CtCanon j (CEmpty)) c))
  (let-match erased j (Succ j1) ((Zero) (CanL (CEmpty) (HE (Zero)))))
  (let ((erased c1)) (canon-empty j1))
  (CanN j1 (CEmpty) (CEmpty) (CEmpty) (CEmpty) c1 c1 c1 (CnE)))

(def-fns _ $ (erased cres-canon : (erased (Nat) h) (erased (Ctree) t keep gone) (erased (List RG) r) (subterm erased (CRes h t r keep gone) c)
    (erased (CtCanon (Succ h) t) ct) -> (erased (Ctree) keep2) (erased (CRes h t r keep2 gone) c2) (erased (CtCanon (Succ h) keep2) k2))
  (match erased c _
    ((CRNil _ _) (values t c ct))
    ((CRE _ _) (values t c ct))
    ((CRS h1 t1 t2 t3 a1 a2 a3 b1 b2 b3 _ _ _ r1 r2 r3 s1 s2 s3 c1 c2 c3 _ cg)
      (let-match erased ct (CanN _ _ _ _ _ q1 q2 q3 cn))
      (let-match erased cn (CnN _ _ _ _))
      (let ((erased e1) (erased d1) (erased k1)) (cres-canon h1 t1 a1 b1 r1 c1 q1))
      (let ((erased e2) (erased d2) (erased k2)) (cres-canon h1 t2 a2 b2 r2 c2 q2))
      (let ((erased e3) (erased d3) (erased k3)) (cres-canon h1 t3 a3 b3 r3 c3 q3))
      (let ((erased k) (erased kc)) (cn-c e1 e2 e3))
      (values k (CRS h1 t1 t2 t3 e1 e2 e3 b1 b2 b3 k gone r r1 r2 r3 s1 s2 s3 d1 d2 d3 (cn-cons e1 e2 e3 k kc) cg)
        (CanN (Succ h1) e1 e2 e3 k k1 k2 k3 kc)))
    ((CRZ t1 t2 t3 l1 l2 l3 g1 g2 g3 _ _ _ n1 n2 n3 p1 p2 p3 d1 d2 d3 _ f1 f2 f3 cg)
      (let-match erased d1 (MkDecrAll _ _ _ _ _ _ _ h1 _ _))
      (let-match erased d2 (MkDecrAll _ _ _ _ _ _ _ h2 _ _))
      (let-match erased d3 (MkDecrAll _ _ _ _ _ _ _ h3 _ _))
      (let ((erased k) (erased kc)) (cn-c l1 l2 l3))
      (values k (CRZ t1 t2 t3 l1 l2 l3 g1 g2 g3 k gone r n1 n2 n3 p1 p2 p3 d1 d2 d3 (cn-cons l1 l2 l3 k kc) f1 f2 f3 cg)
        (CanN (Zero) l1 l2 l3 k (CanL l1 h1) (CanL l2 h2) (CanL l3 h3) kc)))))

; The block of us for the prefix p, whose traces have j more colours, holds t: each trace's count at its index.
(def-adts $ (Tally : ((List Cnt) us) ((Nat) j) ((Nat) p) ((Ctree) t) -> Type)
  enum
  (many TaL : (erased (List Cnt) us) (erased (Nat) p n) (erased (Lt n u62-modulus) b) (erased (Ctree) t)
      (erased (Nth Cnt us p (MkCopy (U62) (MkU62 n b))) e) (erased (CtRoot t n) r) (erased (CtH (Zero) t) k) -> (Tally us (Zero) p t))
  (many TaN : (erased (List Cnt) us) (erased (Nat) j p q) (erased (Ctree) t1 t2 t3 t) (erased (Thrice p q) tq)
      (erased (Tally us j q t1) b1) (erased (Tally us j (Succ q) t2) b2) (erased (Tally us j (Succ (Succ q)) t3) b3) (erased (Cn t1 t2 t3 t) c)
      -> (Tally us (Succ j) p t)))

(def-adts $ (Fit : ((List Cnt) us) -> Type)
  enum
  (many MkFit : (erased (List Cnt) us) (erased (Nat) len) (erased (Length Cnt us len) l) (erased (Lt len u62-modulus) b) -> (Fit us)))

(def-adts $ (Packed : ((List Cnt) us) ((Nat) j) ((Ctree) t) -> Type)
  enum
  (many MkPacked : (erased (List Cnt) us) (erased (Nat) j) (erased (Ctree) t) (erased (Tally us j (Zero) t) b) (erased (Fit us) f)
      -> (Packed us j t)))

(def-fns _ $ (erased fit-set : (erased (List Cnt) us vs) (erased (Nat) i) (erased Cnt x) (erased (Fit us) f) (erased (SetNth Cnt us i x vs) s)
    -> (erased (Fit vs) g))
  (let-match erased f (MkFit _ len l b))
  (MkFit vs len (setnth-length _ us i len x vs s l) b))

(def-fns _ $ (erased tally-canon : (erased (List Cnt) us) (erased (Nat) j p) (erased (Ctree) t) (subterm erased (Tally us j p t) b)
    -> (erased (CtCanon j t) c))
  (match erased b _
    ((TaL _ _ _ _ _ _ _ k) (CanL t k))
    ((TaN _ j1 _ q t1 t2 t3 _ _ b1 b2 b3 cn)
      (CanN j1 t1 t2 t3 t (tally-canon us j1 q t1 b1) (tally-canon us j1 (Succ q) t2 b2) (tally-canon us j1 (Succ (Succ q)) t3 b3) cn))))

(def-fns _ $ (erased leaf-fn : (erased (Ctree) t u) (erased (Nat) n) (subterm erased (CtRoot t n) r) (erased (CtH (Zero) t) k)
    (erased (CtRoot u n) s) (erased (CtH (Zero) u) m) -> (erased (Eq (Ctree) t u) e))
  (match erased r _
    ((RootE) (let-match erased m (HE _) (absurd (HL _ _) s)) (Refl _ t))
    (absurd (RootN _ _ _) k)
    ((RootL lf n1 r1)
      (let-match erased k (HL _ k1))
      (let-match erased m (HL lf2 m1) (absurd (HE _) s))
      (let-match erased s (RootL _ _ s1))
      (let-match erased (leaf-fn lf lf2 n1 r1 k1 s1 m1) (Refl _ _))
      (Refl _ t))))

(def-fns _ $ (erased tally-fn : (erased (List Cnt) us) (erased (Nat) j p) (erased (Ctree) t u) (subterm erased (Tally us j p t) b)
    (erased (Tally us j p u) c) -> (erased (Eq (Ctree) t u) e))
  (match erased b _
    ((TaL _ _ n _ _ x rt k)
      (let-match erased c (TaL _ _ _ _ _ y ru m))
      (let-match erased (nth-fn _ us p _ _ x y) (Refl _ _))
      (leaf-fn t u n rt k ru m))
    ((TaN _ j1 _ q t1 t2 t3 _ tq b1 b2 b3 cn)
      (let-match erased c (TaN _ _ _ q2 u1 u2 u3 _ tq2 c1 c2 c3 cm))
      (let-match erased (thrice-fn p q q2 tq tq2) (Refl _ _))
      (let-match erased (tally-fn us j1 q t1 u1 b1 c1) (Refl _ _))
      (let-match erased (tally-fn us j1 (Succ q) t2 u2 b2 c2) (Refl _ _))
      (let-match erased (tally-fn us j1 (Succ (Succ q)) t3 u3 b3 c3) (Refl _ _))
      (cn-fn t1 t2 t3 t u cn cm))))

(def-fns _ $ (erased tally-lt : (erased (List Cnt) us) (erased (Nat) j p len) (erased (Ctree) t) (subterm erased (Tally us j p t) b)
    (erased (Length Cnt us len) l) -> (erased (Lt p len) r))
  (match erased b _
    ((TaL _ _ _ _ _ x _ _) (nth-lt-length _ us p len _ x l))
    ((TaN _ j1 _ q t1 _ _ _ tq b1 _ _ _) (lt-le-trans p (Succ q) len (thrice-le p q tq) (LtS q len (tally-lt us j1 q len t1 b1 l))))))

(def-fns _ $ (erased tally-u62 : (erased (List Cnt) us) (erased (Nat) j p) (erased (Ctree) t) (erased (Tally us j p t) b) (erased (Fit us) f)
    -> (erased (Lt p u62-modulus) r))
  (let-match erased f (MkFit _ len l lb))
  (lt-trans p len u62-modulus (tally-lt us j p len t b l) lb))

(def-fns _ $ (erased tally-down : (erased (List Cnt) us) (erased (Nat) j p a) (erased (Ctree) t) (erased (Col) e) (erased (Tally us (Succ j) p t) b)
    (erased (Kid p e a) k) -> (erased (Ctree) u) (erased (Tally us j a u) c) (erased (CtSel t e u) s))
  (let-match erased b (TaN _ _ _ q t1 t2 t3 _ tq b1 b2 b3 cn))
  (let ((erased s1) (erased s2) (erased s3)) (cn-sel t1 t2 t3 t cn))
  (match erased k _
    ((Ki1 _ _ tk) (let-match erased (thrice-fn p q a tq tk) (Refl _ _)) (values t1 b1 s1))
    ((Ki2 _ a0 tk) (let-match erased (thrice-fn p q a0 tq tk) (Refl _ _)) (values t2 b2 s2))
    ((Ki3 _ a0 tk) (let-match erased (thrice-fn p q a0 tq tk) (Refl _ _)) (values t3 b3 s3))))

(def-fns _ $ (erased tally-sub : (erased (List Cnt) us) (erased (Nat) j p i) (erased (Ctree) t) (subterm erased (List (Col)) et)
    (erased (Tally us j p t) b) (erased (TIdx p et i) ti) (erased (Length (Col) et j) le) ->
    (erased (Nat) n) (erased (Lt n u62-modulus) nb) (erased (Nth Cnt us i (MkCopy (U62) (MkU62 n nb))) x) (erased (CtSub t et n) s))
  (match erased et _
    ((Nil _)
      (let-match erased le (LengthNil _))
      (let-match erased ti (TINil _))
      (let-match erased b (TaL _ _ n nb _ x rt _))
      (values n nb x (SubNil t n rt)))
    ((Cons _ e et1)
      (let-match erased le (LengthCons _ _ _ j1 le1))
      (let-match erased ti (TICons _ a _ _ _ k ti1))
      (let ((erased u) (erased c) (erased sl)) (tally-down us j1 p a t e b k))
      (let ((erased n) (erased nb) (erased x) (erased s)) (tally-sub us j1 a i u et1 c ti1 le1))
      (values n nb x (SubCons t u e et1 n sl s)))))

(def-fns _ $ (erased tally-set : (erased (List Cnt) us vs) (erased (Nat) j p p2 i) (erased Cnt x) (erased (List (Col)) et) (erased (Ctree) t)
    (subterm erased (Tally us j p t) b) (erased (SetNth Cnt us i x vs) s) (erased (TIdx p2 et i) ti) (erased (Length (Col) et j) le)
    (erased (Apart (Nat) Lt p p2) ap) -> (erased (Tally vs j p t) r))
  (match erased b _
    ((TaL _ _ n nb _ y rt k)
      (let-match erased le (LengthNil _))
      (let-match erased ti (TINil _))
      (TaL vs p n nb t
        (match erased ap _
          ((ApLt _ _ _ _ l) (setnth-nth-lt _ us i p x _ vs s y l))
          ((ApGt _ _ _ _ l) (setnth-nth-gt _ us i p x _ vs s y l)))
        rt k))
    ((TaN _ j1 _ q t1 t2 t3 _ tq b1 b2 b3 cn)
      (let-match erased le (LengthCons _ e et1 _ le1))
      (let-match erased ti (TICons _ q2 _ _ _ k ti1))
      (TaN vs j1 p q t1 t2 t3 t tq
        (tally-set us vs j1 q q2 i x et1 t1 b1 s ti1 le1 (kid-apart p p2 q q2 (C1) e ap (Ki1 p q tq) k))
        (tally-set us vs j1 (Succ q) q2 i x et1 t2 b2 s ti1 le1 (kid-apart p p2 (Succ q) q2 (C2) e ap (Ki2 p q tq) k))
        (tally-set us vs j1 (Succ (Succ q)) q2 i x et1 t3 b3 s ti1 le1 (kid-apart p p2 (Succ (Succ q)) q2 (C3) e ap (Ki3 p q tq) k))
        cn))))

; vs is us with entries set only at the indices of the block of the prefix p with j more colours.
(def-adts $ (Inside : ((List Cnt) us) ((List Cnt) vs) ((Nat) j) ((Nat) p) -> Type)
  enum
  (many InNil : (erased (List Cnt) us) (erased (Nat) j p) -> (Inside us us j p))
  (many InSet : (erased (List Cnt) us ws vs) (erased (Nat) j p i) (erased Cnt x) (erased (List (Col)) et) (erased (Inside us ws j p) w)
      (erased (SetNth Cnt ws i x vs) s) (erased (TIdx p et i) ti) (erased (Length (Col) et j) le) -> (Inside us vs j p)))

(def-fns _ $ (erased inside-up : (erased (List Cnt) us vs) (erased (Nat) j p q) (erased (Col) e) (subterm erased (Inside us vs j q) w)
    (erased (Kid p e q) k) -> (erased (Inside us vs (Succ j) p) r))
  (match erased w _
    ((InNil _ _ _) (InNil us (Succ j) p))
    ((InSet _ ws _ _ _ i x et w1 s ti le)
      (InSet us ws vs (Succ j) p i x (Cons _ e et) (inside-up us ws j p q e w1 k) s (TICons p q i e et k ti) (LengthCons _ e et j le)))))

(def-fns _ $ (erased inside-cat : (erased (List Cnt) us ws vs) (erased (Nat) j p) (erased (Inside us ws j p) w1) (subterm erased (Inside ws vs j p) w2)
    -> (erased (Inside us vs j p) r))
  (match erased w2 _
    ((InNil _ _ _) w1)
    ((InSet _ xs _ _ _ i x et w3 s ti le) (InSet us xs vs j p i x et (inside-cat us ws xs j p w1 w3) s ti le))))

(def-fns _ $ (erased tally-inside : (erased (List Cnt) us vs) (erased (Nat) j p p2) (erased (Ctree) t) (erased (Tally us j p t) b)
    (subterm erased (Inside us vs j p2) w) (erased (Apart (Nat) Lt p p2) ap) -> (erased (Tally vs j p t) r))
  (match erased w _
    ((InNil _ _ _) b)
    ((InSet _ ws _ _ _ i x et w1 s ti le) (tally-set ws vs j p p2 i x et t (tally-inside us ws j p p2 t b w1 ap) s ti le ap))))

(def-fns _ $ (many split-c : (erased (Nat) j) (many (Ctree) t) (erased (CtH (Succ j) t) k) ->
    (many (Ctree) t1 t2 t3) (erased (CtH j t1) k1) (erased (CtH j t2) k2) (erased (CtH j t3) k3) (many (Try (Cn t1 t2 t3 t)) c))
  (let-match many t (CNode a1 a2 a3)
    ((CEmpty) (values t t t (HE j) (HE j) (HE j) (TryOk _ (CnE))))
    (absurd (CLeaf _) k))
  (let-match erased k (HN _ _ _ _ h1 h2 h3))
  (let ((many t4) (erased c4)) (cn-c a1 a2 a3))
  (values a1 a2 a3 h1 h2 h3 (match many t4 _ ((CNode _ _ _) (let-match erased c4 (CnN _ _ _ _)) (TryOk _ c4)) (else (TryNo _)))))

(def-fns _ $ (many fill : (subterm many (Nat) j) (many (Nat) p) (many (Ctree) t) (erased (CtH j t) k) (many (Nat) len) (erased (List Cnt) us)
    (unique (Array Cnt us) a) (erased (Length Cnt us len) l) ->
    (erased (List Cnt) vs) (unique (Array Cnt vs) a2 at a) (erased (Inside us vs j p) w) (erased (Length Cnt vs len) l2)
    (many (Try (Tally vs j p t)) r))
  (match many j _
    ((Zero)
      (let ((many n) (erased rt)) (root-exists t))
      (let-match many (nat-fits-u62 n) (Yes _ _ _ _ nb) ((No _ _ _ _ _) (values us a (InNil us j p) l (TryNo _))))
      (let-match many (lt-dec p len) (Yes _ _ _ _ pl) ((No _ _ _ _ _) (values us a (InNil us j p) l (TryNo _))))
      (let ((erased old) (erased nth)) (nth-exists _ us len p l pl))
      (let ((unique x)) (MkCopy (U62) (MkU62 n nb)))
      (let ((erased vs) (unique a2) (erased s)) (array-place-imm _ us a p x old nth (imm-cnt old) (imm-cnt x)))
      (values vs a2 (InSet us us vs j p p x (Nil _) (InNil us j p) s (TINil p) (LengthNil _)) (setnth-length _ us p len x vs s l)
        (TryOk _ (TaL vs p n nb t (setnth-nth _ us p x vs s) rt k))))
    ((Succ j1)
      (let ((many t1) (many t2) (many t3) (erased k1) (erased k2) (erased k3) (many c)) (split-c j1 t k))
      (let ((many d) (erased ad)) (add p p))
      (let ((many q) (erased aq)) (add d p))
      (let ((erased tq)) (adds-thrice p d q ad aq))
      (let ((erased u1) (unique a1) (erased w1) (erased l1) (many r1)) (notail $ fill j1 q t1 k1 len us a l))
      (let ((erased u2) (unique a2) (erased w2) (erased l2) (many r2)) (notail $ fill j1 (Succ q) t2 k2 len u1 a1 l1))
      (let ((erased u3) (unique a3) (erased w3) (erased l3) (many r3)) (notail $ fill j1 (Succ (Succ q)) t3 k3 len u2 a2 l2))
      (let ((erased w))
        (inside-cat us u2 u3 (Succ j1) p
          (inside-cat us u1 u2 (Succ j1) p (inside-up us u1 j1 p q (C1) w1 (Ki1 p q tq)) (inside-up u1 u2 j1 p (Succ q) (C2) w2 (Ki2 p q tq)))
          (inside-up u2 u3 j1 p (Succ (Succ q)) (C3) w3 (Ki3 p q tq))))
      (let-match many r1 (TryOk _ b1) ((TryNo _) (values u3 a3 w l3 (TryNo _))))
      (let-match many r2 (TryOk _ b2) ((TryNo _) (values u3 a3 w l3 (TryNo _))))
      (let-match many r3 (TryOk _ b3) ((TryNo _) (values u3 a3 w l3 (TryNo _))))
      (let-match many c (TryOk _ cn) ((TryNo _) (values u3 a3 w l3 (TryNo _))))
      (let ((erased s1)) (Succ q))
      (let ((erased s2)) (Succ s1))
      (values u3 a3 w l3
        (TryOk _ (TaN u3 j1 p q t1 t2 t3 t tq
          (tally-inside u2 u3 j1 q s2 t1 (tally-inside u1 u2 j1 q s1 t1 b1 w2 (ApLt (Nat) Lt q s1 (lt-succ q))) w3
            (ApLt (Nat) Lt q s2 (lt-weaken q s1 (lt-succ q))))
          (tally-inside u2 u3 j1 s1 s2 t2 b2 w3 (ApLt (Nat) Lt s1 s2 (lt-succ s1)))
          b3 cn))))))

(def-fns _ $ (many pow3 : (subterm many (Nat) k) -> (many (Nat) v))
  (let-match many k (Succ k1) ((Zero) (Succ (Zero))))
  (let ((many v1)) (notail $ pow3 k1))
  (let ((many d) (erased _)) (add v1 v1))
  (let ((many v) (erased _)) (add d v1))
  v)

(def-fns _ $ (many ctree-tally : (many (Nat) j) (many (Ctree) t) (erased (CtH j t) k) ->
    (erased (List Cnt) us) (unique (Array Cnt us) a) (many (Try (Packed us j t)) r))
  (let ((many n)) (pow3 j))
  (let ((erased us) (unique a) (erased rp)) (array-make (U62) n (MkU62 (Zero) u62-modulus-pos)))
  (let-match many (nat-fits-u62 n) (Yes _ _ _ _ lb) ((No _ _ _ _ _) (values us a (TryNo _))))
  (let ((erased vs) (unique a2) (erased _) (erased l2) (many r)) (fill j (Zero) t k n us a (repeat-length _ n _ us rp)))
  (let-match many r (TryOk _ b) ((TryNo _) (values vs a2 (TryNo _))))
  (values vs a2 (TryOk _ (MkPacked vs j t b (MkFit vs n l2 lb)))))

; t is the subtree of top after the reversed prefix pre.
(def-adts $ (CtAt : ((Ctree) top) ((List (Col)) pre) ((Ctree) t) -> Type)
  enum
  (many AtNil : (erased (Ctree) top) -> (CtAt top (Nil (Col)) top))
  (many AtCons : (erased (Ctree) top u t) (erased (List (Col)) pre) (erased (Col) e) (erased (CtAt top pre u) a) (erased (CtSel u e t) s)
      -> (CtAt top (Cons (Col) e pre) t)))

(def-fns _ $ (erased at-sub : (erased (Ctree) top t) (erased (List (Col)) pre w et) (erased (Nat) n) (subterm erased (CtAt top pre t) a)
    (erased (RevApp (Col) pre w et) ra) (erased (CtSub t w n) s) -> (erased (CtSub top et n) r))
  (match erased a _
    ((AtNil _) (let-match erased ra (RANil _ _)) s)
    ((AtCons _ u _ pre1 e a1 sl)
      (let-match erased ra (RACons _ _ _ _ _ ra1))
      (at-sub top u pre1 (Cons _ e w) et n a1 ra1 (SubCons u t e w n sl s)))))

; Each trace of length j after the reversed prefix pre, from the prefix p, has its count in top as its entry in us.
(def-adts $ (Pointwise : ((List Cnt) us) ((Ctree) top) ((Nat) j) ((Nat) p) ((List (Col)) pre) -> Type)
  enum
  (many PwL : (erased (List Cnt) us) (erased (Ctree) top) (erased (Nat) p n) (erased (Lt n u62-modulus) nb) (erased (List (Col)) pre et)
      (erased (RevApp (Col) pre (Nil (Col)) et) ra) (erased (CtSub top et n) s) (erased (Nth Cnt us p (MkCopy (U62) (MkU62 n nb))) x)
      -> (Pointwise us top (Zero) p pre))
  (many PwN : (erased (List Cnt) us) (erased (Ctree) top) (erased (Nat) j p q) (erased (List (Col)) pre) (erased (Thrice p q) tq)
      (erased (Pointwise us top j q (Cons (Col) (C1) pre)) a1) (erased (Pointwise us top j (Succ q) (Cons (Col) (C2) pre)) a2)
      (erased (Pointwise us top j (Succ (Succ q)) (Cons (Col) (C3) pre)) a3) -> (Pointwise us top (Succ j) p pre)))

(def-fns _ $ (erased tally-of-pointwise : (erased (List Cnt) us) (erased (Ctree) top t) (erased (Nat) j p) (erased (List (Col)) pre)
    (subterm erased (Pointwise us top j p pre) pw) (erased (CtCanon j t) c) (erased (CtAt top pre t) sa) -> (erased (Tally us j p t) b))
  (match erased pw _
    ((PwL _ _ _ n nb _ et ra s x)
      (let-match erased c (CanL _ k))
      (let ((erased m) (erased sm)) (sub-exists t (Nil _)))
      (let-match erased (sub-fn top et m n (at-sub top t pre (Nil _) et m sa ra sm) s) (Refl _ _))
      (let-match erased sm (SubNil _ _ rt))
      (TaL us p n nb t x rt k))
    ((PwN _ _ j1 _ q _ tq a1 a2 a3)
      (let-match erased c (CanN _ t1 t2 t3 _ c1 c2 c3 cn))
      (let ((erased s1) (erased s2) (erased s3)) (cn-sel t1 t2 t3 t cn))
      (TaN us j1 p q t1 t2 t3 t tq
        (tally-of-pointwise us top t1 j1 q (Cons _ (C1) pre) a1 c1 (AtCons top t t1 pre (C1) sa s1))
        (tally-of-pointwise us top t2 j1 (Succ q) (Cons _ (C2) pre) a2 c2 (AtCons top t t2 pre (C2) sa s2))
        (tally-of-pointwise us top t3 j1 (Succ (Succ q)) (Cons _ (C3) pre) a3 c3 (AtCons top t t3 pre (C3) sa s3))
        cn))))

; Trie node n, whose children are 3n + 1 to 3n + 3, holds t of height j: its entry is 0 when t is empty and 1 otherwise.
(def-adts $ (Flags : ((List Cnt) us) ((Nat) j) ((Nat) n) ((Ctree) t) -> Type)
  enum
  (many FlE : (erased (List Cnt) us) (erased (Nat) j n) (erased (Lt (Zero) u62-modulus) b)
      (erased (Nth Cnt us n (MkCopy (U62) (MkU62 (Zero) b))) x) -> (Flags us j n (CEmpty)))
  (many FlL : (erased (List Cnt) us) (erased (Nat) n) (erased (Ctree) lf) (erased (Lt (Succ (Zero)) u62-modulus) b)
      (erased (Nth Cnt us n (MkCopy (U62) (MkU62 (Succ (Zero)) b))) x) -> (Flags us (Zero) n (CLeaf lf)))
  (many FlN : (erased (List Cnt) us) (erased (Nat) j n q) (erased (Ctree) t1 t2 t3) (erased (Lt (Succ (Zero)) u62-modulus) b)
      (erased (Nth Cnt us n (MkCopy (U62) (MkU62 (Succ (Zero)) b))) x) (erased (Thrice n q) tq)
      (erased (Flags us j (Succ q) t1) f1) (erased (Flags us j (Succ (Succ q)) t2) f2) (erased (Flags us j (Succ (Succ (Succ q))) t3) f3)
      (erased (Occ3 t1 t2 t3) o) -> (Flags us (Succ j) n (CNode t1 t2 t3))))

; What Flags us j n t says once the entry v at n is known.
(def-adts $ (FlagInv : ((List Cnt) us) ((Nat) j) ((Nat) n) ((Nat) v) ((Ctree) t) -> Type)
  enum
  (many FiE : (erased (List Cnt) us) (erased (Nat) j n) -> (FlagInv us j n (Zero) (CEmpty)))
  (many FiL : (erased (List Cnt) us) (erased (Nat) n) (erased (Ctree) lf) -> (FlagInv us (Zero) n (Succ (Zero)) (CLeaf lf)))
  (many FiN : (erased (List Cnt) us) (erased (Nat) j n q) (erased (Ctree) t1 t2 t3) (erased (Thrice n q) tq)
      (erased (Flags us j (Succ q) t1) f1) (erased (Flags us j (Succ (Succ q)) t2) f2) (erased (Flags us j (Succ (Succ (Succ q))) t3) f3)
      (erased (Occ3 t1 t2 t3) o) -> (FlagInv us (Succ j) n (Succ (Zero)) (CNode t1 t2 t3))))

(def-fns _ $ (erased flags-inv : (erased (List Cnt) us) (erased (Nat) j n v) (erased (Ctree) t) (erased (Lt v u62-modulus) vb)
    (erased (Flags us j n t) c) (erased (Nth Cnt us n (MkCopy (U62) (MkU62 v vb))) x) -> (erased (FlagInv us j n v t) r))
  (match erased c _
    ((FlE _ _ _ _ y) (let-match erased (nth-fn _ _ _ _ _ x y) (Refl _ _)) (FiE us j n))
    ((FlL _ _ lf _ y) (let-match erased (nth-fn _ _ _ _ _ x y) (Refl _ _)) (FiL us n lf))
    ((FlN _ j1 _ q t1 t2 t3 _ y tq f1 f2 f3 o)
      (let-match erased (nth-fn _ _ _ _ _ x y) (Refl _ _))
      (FiN us j1 n q t1 t2 t3 tq f1 f2 f3 o))))

(def-fns _ $ (erased flags-mem : (erased (List Cnt) us) (erased (Nat) j n) (erased (Ctree) t) (subterm erased (Flags us j n t) c) (erased (Occ t) o)
    -> (erased (List (Col)) et) (erased (CtMem t et) m))
  (let-match erased c (FlN _ j1 _ q t1 t2 t3 _ _ _ f1 f2 f3 o3)
    (absurd (FlE _ _ _ _ _) o)
    ((FlL _ _ lf _ _) (values (Nil _) (leaf-mem lf))))
  (match erased o3 _
    ((Occ1 _ _ _ o1)
      (let ((erased et) (erased m)) (flags-mem us j1 (Succ q) t1 f1 o1))
      (values (Cons _ (C1) et) (mem-cons t t1 (C1) et (SelN1 t1 t2 t3) m)))
    ((Occ2 _ _ _ o1)
      (let ((erased et) (erased m)) (flags-mem us j1 (Succ (Succ q)) t2 f2 o1))
      (values (Cons _ (C2) et) (mem-cons t t2 (C2) et (SelN2 t1 t2 t3) m)))
    ((Occ3c _ _ _ o1)
      (let ((erased et) (erased m)) (flags-mem us j1 (Succ (Succ (Succ q))) t3 f3 o1))
      (values (Cons _ (C3) et) (mem-cons t t3 (C3) et (SelN3 t1 t2 t3) m)))))

(let ((many flag-um)) (u62-modulus-many))
(comptime-match many (lt-dec (Succ (Zero)) flag-um) (Yes _ _ _ _ flag-one-lt))
(comptime-match many (lt-dec (Succ (Succ (Succ (Zero)))) flag-um) (Yes _ _ _ _ three-lt))

; Every trie node in the j levels from n has its index below len.
(def-adts $ (TrieFit : ((Nat) len) ((Nat) j) ((Nat) n) -> Type)
  enum
  (many TfL : (erased (Nat) len n) (erased (Lt n len) b) -> (TrieFit len (Zero) n))
  (many TfN : (erased (Nat) len j n q) (erased (Lt n len) b) (erased (Thrice n q) tq) (erased (TrieFit len j (Succ q)) h1)
      (erased (TrieFit len j (Succ (Succ q))) h2) (erased (TrieFit len j (Succ (Succ (Succ q)))) h3) -> (TrieFit len (Succ j) n)))

(def-fns _ $ (erased tfit-lt : (erased (Nat) len j n) (erased (TrieFit len j n) hf) -> (erased (Lt n len) r))
  (match erased hf _ ((TfL _ _ b) b) ((TfN _ _ _ _ b _ _ _ _) b)))

(def-fns _ $ (many tfit-c : (subterm many (Nat) j) (many (Nat) n len) -> (many (Try (TrieFit len j n)) r))
  (let-match many (lt-dec n len) (Yes _ _ _ _ b) ((No _ _ _ _ _) (TryNo _)))
  (let-match many j (Succ j1) ((Zero) (TryOk _ (TfL len n b))))
  (let ((many d) (erased ad)) (add n n))
  (let ((many q) (erased aq)) (add d n))
  (let-match many (notail $ tfit-c j1 (Succ q) len) (TryOk _ h1) ((TryNo _) (TryNo _)))
  (let-match many (notail $ tfit-c j1 (Succ (Succ q)) len) (TryOk _ h2) ((TryNo _) (TryNo _)))
  (let-match many (notail $ tfit-c j1 (Succ (Succ (Succ q))) len) (TryOk _ h3) ((TryNo _) (TryNo _)))
  (TryOk _ (TfN len j1 n q b (adds-thrice n d q ad aq) h1 h2 h3)))

(def-fns _ $ (many heap-size : (subterm many (Nat) j) -> (many (Nat) n))
  (let-match many j (Succ j1) ((Zero) (Succ (Zero))))
  (let ((many k)) (notail $ heap-size j1))
  (let ((many d) (erased _)) (add k k))
  (let ((many v) (erased _)) (add d k))
  (Succ v))

(def-fns _ $ (many base3 : (many (Nat) p) (erased (Nat) q) (erased (Thrice p q) t) (erased (Lt (Succ (Succ q)) u62-modulus) b) ->
    (many q is a) (many (Succ q) is c) (many (Succ (Succ q)) is d))
  (let ((erased b1)) (lt-trans _ _ _ (lt-succ (Succ q)) b))
  (let ((many a)) (thrice-c p q t (lt-trans _ _ _ (lt-succ q) b1)))
  (let ((many c)) (u62-inc a b1))
  (values a c (u62-inc c b)))

(def-fns _ $ (many node-kids : (many (Nat) n) (erased (Nat) q) (erased (Thrice n q) t) (erased (Lt (Succ (Succ (Succ q))) u62-modulus) b) ->
    (many (Succ q) is c1) (many (Succ (Succ q)) is c2) (many (Succ (Succ (Succ q))) is c3))
  (let ((many _) (many c1) (many c2)) (base3 n q t (lt-trans _ _ _ (lt-succ (Succ (Succ q))) b)))
  (values c1 c2 (u62-inc c2 b)))

; ms has room for a trie of j levels below the root, at index 0.
(def-adts $ (Room : ((List Cnt) ms) ((Nat) j) -> Type)
  enum
  (many MkRoom : (erased (List Cnt) ms) (erased (Nat) j len) (erased (Length Cnt ms len) l) (erased (Lt len u62-modulus) b)
      (erased (TrieFit len j (Zero)) hf) -> (Room ms j)))

(def-fns _ $ (erased room-fit : (erased (List Cnt) ms) (erased (Nat) j) (erased (Room ms j) rm) -> (erased (Fit ms) f))
  (let-match erased rm (MkRoom _ _ len l b _))
  (MkFit ms len l b))

(def-fns _ $ (many room-new : (many (Nat) j) -> (erased (List Cnt) ms) (unique (Array Cnt ms) m) (many (Try (Room ms j)) r))
  (let ((many n)) (heap-size j))
  (let ((erased ms) (unique m) (erased rp)) (array-make (U62) n (MkU62 (Zero) u62-modulus-pos)))
  (let-match many (nat-fits-u62 n) (Yes _ _ _ _ lb) ((No _ _ _ _ _) (values ms m (TryNo _))))
  (let-match many (tfit-c j (Zero) n) (TryOk _ hf) ((TryNo _) (values ms m (TryNo _))))
  (values ms m (TryOk _ (MkRoom ms j n (repeat-length _ n _ ms rp) lb hf))))
