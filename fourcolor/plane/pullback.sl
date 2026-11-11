(def-adts $ (RN : ((Level) M) -> Type)
  enum
  (many MkRN : (erased (Level) M) (erased (RPoint M) u) (erased (Point) v) -> (RN M)))

(def-adts $ (EqApart : ((Level) M) ((RN M) x) ((RN M) y) -> Type)
  enum
  (many EAEq : (erased (Level) M) (erased (RPoint M) u w) (erased (Point) v) (erased (RPointEq M u w) e)
      -> (EqApart M (MkRN M u v) (MkRN M w v)))
  (many EAApart : (erased (Level) M) (erased (RPoint M) u w) (erased (Point) v z) (erased (RPointApart M u w) d)
      -> (EqApart M (MkRN M u v) (MkRN M w z))))

(def-adts $ (AllEA : ((Level) M) ((RN M) x) ((List (RN M)) ys) -> Type)
  enum
  (many AENil : (erased (Level) M) (erased (RN M) x) -> (AllEA M x (Nil (RN M))))
  (many AECons : (erased (Level) M) (erased (RN M) x y) (erased (List (RN M)) ys)
      (erased (EqApart M x y) h) (erased (AllEA M x ys) rest) -> (AllEA M x (Cons (RN M) y ys))))

(def-adts $ (Coh : ((Level) M) ((List (RN M)) xs) -> Type)
  enum
  (many CohNil : (erased (Level) M) -> (Coh M (Nil (RN M))))
  (many CohCons : (erased (Level) M) (erased (RPoint M) u) (erased (Point) v) (erased (List (RN M)) xs)
      (erased (RPointEq M u u) refl) (erased (AllEA M (MkRN M u v) xs) here) (erased (Coh M xs) rest)
      -> (Coh M (Cons (RN M) (MkRN M u v) xs))))

(def-adts $ (Ends : ((Level) M) ((List (REdge M)) es) ((List (Edge)) ns) ((List (RN M)) xs) -> Type)
  enum
  (many EndsNil : (erased (Level) M) -> (Ends M (Nil (REdge M)) (Nil (Edge)) (Nil (RN M))))
  (many EndsCons : (erased (Level) M) (erased (RPoint M) a b) (erased (Point) a2 b2) (erased (List (REdge M)) es)
      (erased (List (Edge)) ns) (erased (List (RN M)) xs) (erased (Ends M es ns xs) rest)
      -> (Ends M (Cons (REdge M) (MkREdge M a b) es) (Cons (Edge) (MkEdge a2 b2) ns)
            (Cons (RN M) (MkRN M a a2) (Cons (RN M) (MkRN M b b2) xs)))))

(def-adts $ (Painted : ((Level) M) ((List (Paint)) ks) ((List (RN M)) xs) ((List (RPaint M)) ps) -> Type)
  enum
  (many PdNil : (erased (Level) M) (erased (List (Paint)) ks) -> (Painted M ks (Nil (RN M)) (Nil (RPaint M))))
  (many PdCons : (erased (Level) M) (erased (List (Paint)) ks) (erased (RPoint M) u) (erased (Point) v) (erased (Nat) c)
      (erased (List (RN M)) xs) (erased (List (RPaint M)) ps) (erased (ColorOf ks v c) k) (erased (Painted M ks xs ps) rest)
      -> (Painted M ks (Cons (RN M) (MkRN M u v) xs) (Cons (RPaint M) (MkRPaint M u c) ps))))

(def-fns _ $ (erased absurd point-apart-irrefl : (erased (Point) p) (erased (PointApart p p) d) -> (erased (False) f))
  (match erased d _
    (absurd (ApartX px _ _ _ a) (apart-irrefl px a))
    (absurd (ApartY _ py _ _ a) (apart-irrefl py a))))

(def-fns _ $ (erased colorof-fn : (erased (List (Paint)) ks) (erased (Point) p) (erased (Nat) c d)
    (subterm erased (ColorOf ks p c) k1) (erased (ColorOf ks p d) k2) -> (erased (Eq (Nat) c d) e))
  (match erased k1 _
    ((ColorHere _ _ _)
      (let-match erased k2 (ColorHere _ _ _) (absurd (ColorThere _ _ _ _ _ skip _) (point-apart-irrefl p skip)))
      (Refl _ c))
    ((ColorThere ks1 _ q _ c0 skip r1)
      (let-match erased k2 (ColorThere _ _ _ _ _ _ r2) (absurd (ColorHere _ _ _) (point-apart-irrefl p skip)))
      (colorof-fn ks1 p c d r1 r2))))

(def-fns _ $ (erased rpointeq-sym : (erased (Level) M) (erased (RPoint M) p q) (erased (RPointEq M p q) e)
    -> (erased (RPointEq M q p) r))
  (let-match erased e (MkRPointEq _ px py qx qy xp yp xq yq ex ey))
  (let-match erased ex (MkCRealEq _ _ ex1 ex2))
  (let-match erased ey (MkCRealEq _ _ ey1 ey2))
  (MkRPointEq M qx qy px py xq yq xp yp (MkCRealEq qx px ex2 ex1) (MkCRealEq qy py ey2 ey1)))

(def-fns _ $ (erased appart-sym : (erased (Spec) x y) (erased (CRealAppart x y) d) -> (erased (CRealAppart y x) r))
  (match erased d _
    ((AppartLt _ _ lt) (AppartGt y x lt))
    ((AppartGt _ _ gt) (AppartLt y x gt))))

(def-fns _ $ (erased rpointapart-sym : (erased (Level) M) (erased (RPoint M) p q) (erased (RPointApart M p q) d)
    -> (erased (RPointApart M q p) r))
  (match erased d _
    ((RApartX _ px py qx qy xp yp xq yq a) (RApartX M qx qy px py xq yq xp yp (appart-sym px qx a)))
    ((RApartY _ px py qx qy xp yp xq yq a) (RApartY M qx qy px py xq yq xp yp (appart-sym py qy a)))))

(def-fns _ $ (erased allea-elem : (erased (Level) M) (erased (RN M) x y) (erased (List (RN M)) ys)
    (subterm erased (AllEA M x ys) a) (erased (Elem (RN M) y ys) el) -> (erased (EqApart M x y) h))
  (let-match erased a (AECons _ _ y0 ys1 h0 rest) (absurd (AENil _ _) el))
  (match erased el _
    ((ElHere _ _ _) h0)
    ((ElThere _ _ _ _ el1) (allea-elem M x y ys1 rest el1))))

(def-fns _ $ (erased find-color : (erased (Level) M) (erased (List (Paint)) ks) (erased (List (RN M)) xs) (erased (List (RPaint M)) ps)
    (erased (RPoint M) u) (erased (Point) v) (erased (Nat) c)
    (subterm erased (Coh M xs) coh) (erased (Painted M ks xs ps) pd) (erased (Elem (RN M) (MkRN M u v) xs) el)
    (erased (ColorOf ks v c) k) -> (erased (RColorOf M ps u c) r))
  (let-match erased coh (CohCons _ u0 v0 xs1 refl here rest) (absurd (CohNil _) el))
  (let-match erased pd (PdCons _ _ _ _ c0 _ ps1 k0 pd1))
  (match erased el _
    ((ElHere _ _ _)
      (let-match erased (colorof-fn ks v c0 c k0 k) (Refl _ _))
      (RColorHere M ps1 u u c refl))
    ((ElThere _ _ _ _ el1)
      (let-match erased (allea-elem M (MkRN M u0 v0) (MkRN M u v) xs1 here el1) (EAEq _ _ _ _ e)
        ((EAApart _ _ _ _ _ d)
          (RColorThere M ps1 u u0 c c0 (rpointapart-sym M u0 u d)
            (find-color M ks xs1 ps1 u v c rest pd1 el1 k))))
      (let-match erased (colorof-fn ks v c0 c k0 k) (Refl _ _))
      (RColorHere M ps1 u u0 c (rpointeq-sym M u0 u e)))))

(def-fns _ $ (erased painted-of : (erased (Level) M) (erased (List (Paint)) ks) (erased (List (REdge M)) es) (erased (List (Edge)) ns)
    (erased (List (RN M)) xs) (subterm erased (Ends M es ns xs) en) (erased (Proper ks ns) pr)
    -> (erased (List (RPaint M)) ps) (erased (Painted M ks xs ps) pd))
  (let-match erased en (EndsCons _ a b a2 b2 es1 ns1 xs1 en1) ((EndsNil _) (values (Nil _) (PdNil M ks))))
  (let-match erased pr (ProperCons _ _ _ ca cb _ ka kb _ _ _ pr1))
  (let ((erased ps1) (erased pd1)) (painted-of M ks es1 ns1 xs1 en1 pr1))
  (values (Cons _ (MkRPaint M a ca) $ Cons _ (MkRPaint M b cb) ps1)
    (PdCons M ks a a2 ca _ _ ka $ PdCons M ks b b2 cb xs1 ps1 kb pd1)))

(def-fns _ $ (erased rproper-of : (erased (Level) M) (erased (List (Paint)) ks) (erased (List (RN M)) xs ys) (erased (List (RPaint M)) ps)
    (erased (List (REdge M)) es) (erased (List (Edge)) ns)
    (erased (Coh M xs) coh) (erased (Painted M ks xs ps) pd) (subterm erased (Ends M es ns ys) en)
    (erased (Suffix (RN M) ys xs) suf) (erased (Proper ks ns) pr) -> (erased (RProper M ps es) r))
  (let-match erased en (EndsCons _ a b a2 b2 es1 ns1 ys1 en1) ((EndsNil _) (RProperNil M ps)))
  (let-match erased pr (ProperCons _ _ _ ca cb _ ka kb ba bb differ pr1))
  (let ((erased ya) (erased yb)) (values (MkRN M a a2) (MkRN M b b2)))
  (let ((erased sufb)) (SufNext _ ya (Cons _ yb ys1) xs suf))
  (let ((erased ela)) (suffix-elem _ ya ys xs suf (ElHere _ ya (Cons _ yb ys1))))
  (let ((erased elb)) (suffix-elem _ yb (Cons _ yb ys1) xs sufb (ElHere _ yb ys1)))
  (RProperCons M ps a b ca cb es1
    (find-color M ks xs ps a a2 ca coh pd ela ka) (find-color M ks xs ps b b2 cb coh pd elb kb)
    ba bb differ (rproper-of M ks xs ys1 ps es1 ns1 coh pd en1 (SufNext _ yb ys1 xs sufb) pr1)))

(def-fns _ $ (erased pullback : (erased (Level) M) (erased (List (REdge M)) es) (erased (List (Edge)) ns) (erased (List (RN M)) xs)
    (erased (Ends M es ns xs) en) (erased (Coh M xs) coh) (erased (List (Paint)) ks) (erased (Proper ks ns) pr)
    -> (erased (List (RPaint M)) ps) (erased (RProper M ps es) r))
  (let ((erased ps) (erased pd)) (painted-of M ks es ns xs en pr))
  (values ps (rproper-of M ks xs xs ps es ns coh pd en (SufHere _ xs) pr)))
