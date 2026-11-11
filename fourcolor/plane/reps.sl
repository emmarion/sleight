(def-adts $ (PointKit : ((Level) M) ((Level) N) ((Level) P) -> Type)
  enum
  (many MkPointKit : (erased (Level) M N P)
      (erased (Fn P (erased (RPoint M) x y z) (erased (RPointEq M N x y) a) (erased (RPointApart M y z) b)
          -> (erased (RPointApart M x z) r)) compat)
      (erased (Fn P (erased (RPoint M) x) (erased (RPointApart M x x) a) -> (erased (False) f)) irrefl)
      -> (PointKit M N P)))

(def-adts $ (EqSame : ((Level) M) ((Level) N) ((RPoint M) x) ((RPoint M) y) -> Type)
  enum
  (many ESEq : (erased (Level) M N) (erased (RPoint M) x y) (erased (RPointEq M N x y) e) -> (EqSame M N x y))
  (many ESSame : (erased (Level) M N) (erased (RPoint M) x) -> (EqSame M N x x)))

(def-adts $ (Dich : ((Level) M) ((Level) N) ((RPoint M) x) ((RPoint M) y) -> Type)
  enum
  (many DichEq : (erased (Level) M N) (erased (RPoint M) x y) (erased (EqSame M N x y) e) -> (Dich M N x y))
  (many DichAp : (erased (Level) M N) (erased (RPoint M) x y) (erased (RPointApart M x y) a) -> (Dich M N x y)))

(def-adts $ (DichAll : ((Level) M) ((Level) N) ((RPoint M) x) ((List (RPoint M)) ys) -> Type)
  enum
  (many DchNil : (erased (Level) M N) (erased (RPoint M) x) -> (DichAll M N x (Nil (RPoint M))))
  (many DchCons : (erased (Level) M N) (erased (RPoint M) x y) (erased (List (RPoint M)) ys)
      (erased (Dich M N x y) d) (erased (DichAll M N x ys) rest) -> (DichAll M N x (Cons (RPoint M) y ys))))

(def-adts $ (DichTab : ((Level) M) ((Level) N) ((List (RPoint M)) us) -> Type)
  enum
  (many DtbNil : (erased (Level) M N) -> (DichTab M N (Nil (RPoint M))))
  (many DtbCons : (erased (Level) M N) (erased (RPoint M) x) (erased (List (RPoint M)) us)
      (erased (DichAll M N x us) here) (erased (DichTab M N us) rest) -> (DichTab M N (Cons (RPoint M) x us))))

(def-adts $ (FirstEq : ((Level) M) ((Level) N) ((List (RPoint M)) hs) ((RPoint M) u) ((RPoint M) r) -> Type)
  enum
  (many FEHere : (erased (Level) M N) (erased (RPoint M) h u) (erased (List (RPoint M)) hs) (erased (EqSame M N h u) e)
      -> (FirstEq M N (Cons (RPoint M) h hs) u h))
  (many FENext : (erased (Level) M N) (erased (RPoint M) h u r) (erased (List (RPoint M)) hs)
      (erased (RPointApart M h u) a) (erased (FirstEq M N hs u r) rest)
      -> (FirstEq M N (Cons (RPoint M) h hs) u r)))

(def-fns _ $ (erased dichall-elem : (erased (Level) M N) (erased (RPoint M) x y) (erased (List (RPoint M)) ys)
    (subterm erased (DichAll M N x ys) d) (erased (Elem (RPoint M) y ys) el) -> (erased (Dich M N x y) r))
  (let-match erased d (DchCons _ _ _ _ ys1 d0 rest) (absurd (DchNil _ _ _) el))
  (match erased el _
    ((ElHere _ _ _) d0)
    ((ElThere _ _ _ _ el1) (dichall-elem M N x y ys1 rest el1))))

(def-fns _ $ (erased eqsame-sym : (erased (Level) M N) (erased (RPoint M) x y) (erased (EqSame M N x y) e) -> (erased (EqSame M N y x) r))
  (match erased e _
    ((ESEq _ _ _ _ q) (ESEq M N y x (rpointeq-sym M N x y q)))
    ((ESSame _ _ _) (ESSame M N x))))

(def-fns _ $ (erased dich-sym : (erased (Level) M N) (erased (RPoint M) x y) (erased (Dich M N x y) d) -> (erased (Dich M N y x) r))
  (match erased d _
    ((DichEq _ _ _ _ e) (DichEq M N y x (eqsame-sym M N x y e)))
    ((DichAp _ _ _ _ a) (DichAp M N y x (rpointapart-sym M x y a)))))

(def-fns _ $ (erased fe-eq : (erased (Level) M N) (erased (List (RPoint M)) hs) (erased (RPoint M) u r)
    (subterm erased (FirstEq M N hs u r) fe) -> (erased (EqSame M N u r) e))
  (match erased fe _
    ((FEHere _ _ _ _ _ e) (eqsame-sym M N r u e))
    ((FENext _ _ _ _ _ hs1 _ fe1) (fe-eq M N hs1 u r fe1))))

(def-fns _ $ (erased dich-of : (erased (Level) M N) (erased (List (RPoint M)) us) (erased (RPoint M) x y)
    (subterm erased (DichTab M N us) tab) (erased (Elem (RPoint M) x us) ex) (erased (Elem (RPoint M) y us) ey)
    -> (erased (Dich M N x y) d))
  (let-match erased tab (DtbCons _ _ h us1 here rest) (absurd (DtbNil _ _) ex))
  (match erased ex _
    ((ElHere _ _ _)
      (match erased ey _
        ((ElHere _ _ _) (DichEq M N x x (ESSame M N x)))
        ((ElThere _ _ _ _ ey1) (dichall-elem M N x y us1 here ey1))))
    ((ElThere _ _ _ _ ex1)
      (match erased ey _
        ((ElHere _ _ _) (dich-sym M N y x (dichall-elem M N y x us1 here ex1)))
        ((ElThere _ _ _ _ ey1) (dich-of M N us1 x y rest ex1 ey1))))))

(def-fns _ $ (erased rep-kit : (erased (Level) M N P) -> (erased (Level) L)
    (erased (Fn L (erased (PointKit M N P) k) (erased (List (RPoint M)) us hs) (erased (RPoint M) u)
        (erased (DichTab M N us) tab) (erased (Suffix (RPoint M) hs us) suf) (subterm erased (Elem (RPoint M) u hs) uh)
        (erased (Elem (RPoint M) u us) uu) -> (erased (RPoint M) r) (erased (FirstEq M N hs u r) fe)) first-eq)
    (erased (Fn L (erased (PointKit M N P) k) (erased (List (RPoint M)) hs) (erased (RPoint M) u w r s)
        (subterm erased (FirstEq M N hs u r) fu) (erased (FirstEq M N hs w s) fw) (erased (EqSame M N u w) e)
        -> (erased (Eq (RPoint M) r s) q)) same))
  (def-fns _ $ (erased es-compat : (erased (PointKit M N P) k) (erased (RPoint M) x y z) (erased (EqSame M N x y) e)
      (erased (RPointApart M y z) a) -> (erased (RPointApart M x z) r))
    (let-match erased k (MkPointKit _ _ _ compat _))
    (match erased e _
      ((ESEq _ _ _ _ q) (compat x y z q a))
      ((ESSame _ _ _) a)))
  (def-lvl L)
  (def-fns L
    ((erased first-eq : (erased (PointKit M N P) k) (erased (List (RPoint M)) us hs) (erased (RPoint M) u)
        (erased (DichTab M N us) tab) (erased (Suffix (RPoint M) hs us) suf) (subterm erased (Elem (RPoint M) u hs) uh)
        (erased (Elem (RPoint M) u us) uu) -> (erased (RPoint M) r) (erased (FirstEq M N hs u r) fe))
      (let-match erased k (MkPointKit _ _ _ _ irrefl))
      (let-match erased uh (ElThere _ _ h hs1 uh1) ((ElHere _ _ hs1)
        (let ((erased hu)) (suffix-elem _ u hs us suf (ElHere _ u hs1)))
        (let-match erased (dich-of M N us u u tab hu uu) (DichEq _ _ _ _ e) (absurd (DichAp _ _ _ _ a) (irrefl u a)))
        (values u (FEHere M N u u hs1 e))))
      (let ((erased hh)) (suffix-elem _ h hs us suf (ElHere _ h hs1)))
      (let-match erased (dich-of M N us h u tab hh uu) (DichAp _ _ _ _ a)
        ((DichEq _ _ _ _ e) (values h (FEHere M N h u hs1 e))))
      (let ((erased r) (erased fe)) (first-eq k us hs1 u tab (SufNext _ h hs1 us suf) uh1 uu))
      (values r (FENext M N h u r hs1 a fe)))
    ((erased same : (erased (PointKit M N P) k) (erased (List (RPoint M)) hs) (erased (RPoint M) u w r s)
        (subterm erased (FirstEq M N hs u r) fu) (erased (FirstEq M N hs w s) fw) (erased (EqSame M N u w) e)
        -> (erased (Eq (RPoint M) r s) q))
      (let-match erased k (MkPointKit _ _ _ _ irrefl))
      (match erased fu _
        ((FEHere _ _ h _ _ ehu)
          (match erased fw _
            ((FEHere _ _ _ _ _ _) (Refl _ h))
            (absurd (FENext _ _ _ _ _ _ ahw _)
              (irrefl w (es-compat k w u w (eqsame-sym M N u w e) (es-compat k u h w (eqsame-sym M N h u ehu) ahw))))))
        ((FENext _ _ h _ _ hs1 ahu fu1)
          (match erased fw _
            (absurd (FEHere _ _ _ _ _ ehw)
              (irrefl u (es-compat k u w u e (es-compat k w h u (eqsame-sym M N h w ehw) ahu))))
            ((FENext _ _ _ _ _ _ _ fw1) (same k hs1 u w r s fu1 fw1 e)))))))
  (values L first-eq same))
