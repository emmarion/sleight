(def-adts $ (PointKit : ((Level) M) ((Level) P) -> Type)
  enum
  (many MkPointKit : (erased (Level) M P)
      (erased (Fn P (erased (RPoint M) x) -> (erased (RPointEq M x x) r)) refl)
      (erased (Fn P (erased (RPoint M) x y z) (erased (RPointEq M x y) a) (erased (RPointEq M y z) b)
          -> (erased (RPointEq M x z) r)) trans)
      (erased (Fn P (erased (RPoint M) x y z) (erased (RPointEq M x y) a) (erased (RPointApart M y z) b)
          -> (erased (RPointApart M x z) r)) compat)
      (erased (Fn P (erased (RPoint M) x) (erased (RPointApart M x x) a) -> (erased (False) f)) irrefl)
      -> (PointKit M P)))

(def-adts $ (Dich : ((Level) M) ((RPoint M) x) ((RPoint M) y) -> Type)
  enum
  (many DichEq : (erased (Level) M) (erased (RPoint M) x y) (erased (RPointEq M x y) e) -> (Dich M x y))
  (many DichAp : (erased (Level) M) (erased (RPoint M) x y) (erased (RPointApart M x y) a) -> (Dich M x y)))

(def-adts $ (DichAll : ((Level) M) ((RPoint M) x) ((List (RPoint M)) ys) -> Type)
  enum
  (many DANil : (erased (Level) M) (erased (RPoint M) x) -> (DichAll M x (Nil (RPoint M))))
  (many DACons : (erased (Level) M) (erased (RPoint M) x y) (erased (List (RPoint M)) ys)
      (erased (Dich M x y) d) (erased (DichAll M x ys) rest) -> (DichAll M x (Cons (RPoint M) y ys))))

(def-adts $ (DichTab : ((Level) M) ((List (RPoint M)) us) -> Type)
  enum
  (many DTNil : (erased (Level) M) -> (DichTab M (Nil (RPoint M))))
  (many DTCons : (erased (Level) M) (erased (RPoint M) x) (erased (List (RPoint M)) us)
      (erased (DichAll M x us) here) (erased (DichTab M us) rest) -> (DichTab M (Cons (RPoint M) x us))))

(def-adts $ (FirstEq : ((Level) M) ((List (RPoint M)) hs) ((RPoint M) u) ((RPoint M) r) -> Type)
  enum
  (many FEHere : (erased (Level) M) (erased (RPoint M) h u) (erased (List (RPoint M)) hs) (erased (RPointEq M h u) e)
      -> (FirstEq M (Cons (RPoint M) h hs) u h))
  (many FENext : (erased (Level) M) (erased (RPoint M) h u r) (erased (List (RPoint M)) hs)
      (erased (RPointApart M h u) a) (erased (FirstEq M hs u r) rest)
      -> (FirstEq M (Cons (RPoint M) h hs) u r)))

(def-fns _ $ (erased dichall-elem : (erased (Level) M) (erased (RPoint M) x y) (erased (List (RPoint M)) ys)
    (subterm erased (DichAll M x ys) d) (erased (Elem (RPoint M) y ys) el) -> (erased (Dich M x y) r))
  (let-match erased d (DACons _ _ _ ys1 d0 rest) (absurd (DANil _ _) el))
  (match erased el _
    ((ElHere _ _ _) d0)
    ((ElThere _ _ _ _ el1) (dichall-elem M x y ys1 rest el1))))

(def-fns _ $ (erased dich-sym : (erased (Level) M) (erased (RPoint M) x y) (erased (Dich M x y) d) -> (erased (Dich M y x) r))
  (match erased d _
    ((DichEq _ _ _ e) (DichEq M y x (rpointeq-sym M x y e)))
    ((DichAp _ _ _ a) (DichAp M y x (rpointapart-sym M x y a)))))

(def-fns _ $ (erased rep-kit : (erased (Level) M P) -> (erased (Level) L)
    (erased (Fn L (erased (PointKit M P) k) (erased (List (RPoint M)) us hs) (erased (RPoint M) u)
        (erased (DichTab M us) tab) (erased (Suffix (RPoint M) hs us) suf) (subterm erased (Elem (RPoint M) u hs) uh)
        (erased (Elem (RPoint M) u us) uu) -> (erased (RPoint M) r) (erased (FirstEq M hs u r) fe)) first-eq)
    (erased (Fn L (erased (PointKit M P) k) (erased (List (RPoint M)) hs) (erased (RPoint M) u w r s)
        (subterm erased (FirstEq M hs u r) fu) (erased (FirstEq M hs w s) fw) (erased (RPointEq M u w) e)
        -> (erased (Eq (RPoint M) r s) q)) same))
  (def-fns _ $ (erased dich-of : (erased (PointKit M P) k) (erased (List (RPoint M)) us) (erased (RPoint M) x y)
        (subterm erased (DichTab M us) tab) (erased (Elem (RPoint M) x us) ex) (erased (Elem (RPoint M) y us) ey)
        -> (erased (Dich M x y) d))
      (let-match erased k (MkPointKit _ _ refl _ _ _))
      (let-match erased tab (DTCons _ h us1 here rest) (absurd (DTNil _) ex))
      (match erased ex _
        ((ElHere _ _ _)
          (match erased ey _
            ((ElHere _ _ _) (DichEq M x x (refl x)))
            ((ElThere _ _ _ _ ey1) (dichall-elem M x y us1 here ey1))))
        ((ElThere _ _ _ _ ex1)
          (match erased ey _
            ((ElHere _ _ _) (dich-sym M y x (dichall-elem M y x us1 here ex1)))
            ((ElThere _ _ _ _ ey1) (dich-of k us1 x y rest ex1 ey1))))))
  (def-lvl L)
  (def-fns L
    ((erased first-eq : (erased (PointKit M P) k) (erased (List (RPoint M)) us hs) (erased (RPoint M) u)
        (erased (DichTab M us) tab) (erased (Suffix (RPoint M) hs us) suf) (subterm erased (Elem (RPoint M) u hs) uh)
        (erased (Elem (RPoint M) u us) uu) -> (erased (RPoint M) r) (erased (FirstEq M hs u r) fe))
      (let-match erased k (MkPointKit _ _ _ _ _ irrefl))
      (let-match erased uh (ElThere _ _ h hs1 uh1) ((ElHere _ _ hs1)
        (let ((erased hu)) (suffix-elem _ u hs us suf (ElHere _ u hs1)))
        (let-match erased (dich-of k us u u tab hu uu) (DichEq _ _ _ e) (absurd (DichAp _ _ _ a) (irrefl u a)))
        (values u (FEHere M u u hs1 e))))
      (let ((erased hh)) (suffix-elem _ h hs us suf (ElHere _ h hs1)))
      (let-match erased (dich-of k us h u tab hh uu) (DichAp _ _ _ a)
        ((DichEq _ _ _ e) (values h (FEHere M h u hs1 e))))
      (let ((erased r) (erased fe)) (first-eq k us hs1 u tab (SufNext _ h hs1 us suf) uh1 uu))
      (values r (FENext M h u r hs1 a fe)))
    ((erased same : (erased (PointKit M P) k) (erased (List (RPoint M)) hs) (erased (RPoint M) u w r s)
        (subterm erased (FirstEq M hs u r) fu) (erased (FirstEq M hs w s) fw) (erased (RPointEq M u w) e)
        -> (erased (Eq (RPoint M) r s) q))
      (let-match erased k (MkPointKit _ _ _ trans compat irrefl))
      (match erased fu _
        ((FEHere _ h _ _ ehu)
          (match erased fw _
            ((FEHere _ _ _ _ _) (Refl _ h))
            (absurd (FENext _ _ _ _ _ ahw _)
              (irrefl w (compat w h w (rpointeq-sym M h w (trans h u w ehu e)) ahw)))))
        ((FENext _ h _ _ hs1 ahu fu1)
          (match erased fw _
            (absurd (FEHere _ _ _ _ ehw)
              (irrefl u (compat u h u (rpointeq-sym M h u (trans h w u ehw (rpointeq-sym M u w e))) ahu)))
            ((FENext _ _ _ _ _ _ fw1) (same k hs1 u w r s fu1 fw1 e)))))))
  (values L first-eq same))

(def-fns _ $ (erased fe-eq : (erased (Level) M) (erased (List (RPoint M)) hs) (erased (RPoint M) u r)
    (subterm erased (FirstEq M hs u r) fe) -> (erased (RPointEq M u r) e))
  (match erased fe _
    ((FEHere _ _ _ _ e) (rpointeq-sym M r u e))
    ((FENext _ _ _ _ hs1 _ fe1) (fe-eq M hs1 u r fe1))))
