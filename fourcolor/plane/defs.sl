(def-adts $ (RPoint : ((Level) M) -> Type)
  enum
  (many MkRPoint : (erased (Level) M) (erased (Spec) sx sy) (many (CReal M sx) x) (many (CReal M sy) y) -> (RPoint M)))

(def-adts $ (REdge : ((Level) M) -> Type)
  enum
  (many MkREdge : (erased (Level) M) (many (RPoint M) a) (many (RPoint M) b) -> (REdge M)))

(def-adts $ (RPointEq : ((Level) M) ((Level) N) ((RPoint M) p) ((RPoint M) q) -> Type)
  enum
  (many MkRPointEq : (erased (Level) M N) (erased (Spec) px py qx qy)
      (erased (CReal M px) xp) (erased (CReal M py) yp) (erased (CReal M qx) xq) (erased (CReal M qy) yq)
      (erased (CRealEq N px qx) ex) (erased (CRealEq N py qy) ey)
      -> (RPointEq M N (MkRPoint M px py xp yp) (MkRPoint M qx qy xq yq))))

(def-adts $ (RPointApart : ((Level) M) ((RPoint M) p) ((RPoint M) q) -> Type)
  enum
  (many RApartX : (erased (Level) M) (erased (Spec) px py qx qy)
      (erased (CReal M px) xp) (erased (CReal M py) yp) (erased (CReal M qx) xq) (erased (CReal M qy) yq)
      (erased (CRealAppart px qx) d)
      -> (RPointApart M (MkRPoint M px py xp yp) (MkRPoint M qx qy xq yq)))
  (many RApartY : (erased (Level) M) (erased (Spec) px py qx qy)
      (erased (CReal M px) xp) (erased (CReal M py) yp) (erased (CReal M qx) xq) (erased (CReal M qy) yq)
      (erased (CRealAppart py qy) d)
      -> (RPointApart M (MkRPoint M px py xp yp) (MkRPoint M qx qy xq yq))))

(def-adts $ (RShoelace : ((Level) M) ((RPoint M) p) ((RPoint M) q) ((RPoint M) r) ((Spec) s) -> Type)
  enum
  (many MkRShoelace : (erased (Level) M) (erased (Spec) px py qx qy rx ry m1 m2 m3 m12 s)
      (erased (CReal M px) xp) (erased (CReal M py) yp) (erased (CReal M qx) xq) (erased (CReal M qy) yq)
      (erased (CReal M rx) xr) (erased (CReal M ry) yr)
      (erased (CRealMult px qy m1) p1) (erased (CRealMult qx ry m2) p2) (erased (CRealMult rx py m3) p3)
      (erased (CRealPlus m1 m2 m12) q1) (erased (CRealPlus m12 m3 s) q2)
      -> (RShoelace M (MkRPoint M px py xp yp) (MkRPoint M qx qy xq yq) (MkRPoint M rx ry xr yr) s)))

(def-adts $ (RLeft : ((Level) M) ((RPoint M) p) ((RPoint M) q) ((RPoint M) r) -> Type)
  enum
  (many MkRLeft : (erased (Level) M) (erased (RPoint M) p q r) (erased (Spec) s1 s2)
      (erased (RShoelace M p q r s1) h1) (erased (RShoelace M r q p s2) h2) (erased (CRealLt s2 s1) l)
      -> (RLeft M p q r)))

(def-adts $ (ROffLine : ((Level) M) ((RPoint M) a) ((RPoint M) b) ((RPoint M) r) -> Type)
  enum
  (many ROffLeft : (erased (Level) M) (erased (RPoint M) a b r) (erased (RLeft M a b r) l) -> (ROffLine M a b r))
  (many ROffRight : (erased (Level) M) (erased (RPoint M) a b r) (erased (RLeft M b a r) l) -> (ROffLine M a b r)))

(def-adts $ (RSameSide : ((Level) M) ((RPoint M) a) ((RPoint M) b) ((RPoint M) c) ((RPoint M) d) -> Type)
  enum
  (many RBothLeft : (erased (Level) M) (erased (RPoint M) a b c d) (erased (RLeft M a b c) lc) (erased (RLeft M a b d) ld)
      -> (RSameSide M a b c d))
  (many RBothRight : (erased (Level) M) (erased (RPoint M) a b c d) (erased (RLeft M b a c) lc) (erased (RLeft M b a d) ld)
      -> (RSameSide M a b c d)))

(def-adts $ (RCompatible : ((Level) M) ((Level) N) ((RPoint M) a) ((RPoint M) b) ((RPoint M) c) ((RPoint M) d) -> Type)
  enum
  (many RShareCA : (erased (Level) M N) (erased (RPoint M) a b c d) (erased (RPointEq M N c a) e) (erased (ROffLine M a b d) o)
      -> (RCompatible M N a b c d))
  (many RShareCB : (erased (Level) M N) (erased (RPoint M) a b c d) (erased (RPointEq M N c b) e) (erased (ROffLine M a b d) o)
      -> (RCompatible M N a b c d))
  (many RShareDA : (erased (Level) M N) (erased (RPoint M) a b c d) (erased (RPointEq M N d a) e) (erased (ROffLine M a b c) o)
      -> (RCompatible M N a b c d))
  (many RShareDB : (erased (Level) M N) (erased (RPoint M) a b c d) (erased (RPointEq M N d b) e) (erased (ROffLine M a b c) o)
      -> (RCompatible M N a b c d))
  (many RSplitByAB : (erased (Level) M N) (erased (RPoint M) a b c d)
      (erased (RSameSide M a b c d) cd) (erased (ROffLine M c d a) oa) (erased (ROffLine M c d b) ob)
      -> (RCompatible M N a b c d))
  (many RSplitByCD : (erased (Level) M N) (erased (RPoint M) a b c d)
      (erased (ROffLine M a b c) oc) (erased (ROffLine M a b d) od) (erased (RSameSide M c d a b) ab)
      -> (RCompatible M N a b c d)))

(def-adts $ (RCompatibleAll : ((Level) M) ((Level) N) ((RPoint M) a) ((RPoint M) b) ((List (REdge M)) es) -> Type)
  enum
  (many RCANil : (erased (Level) M N) (erased (RPoint M) a b) -> (RCompatibleAll M N a b (Nil (REdge M))))
  (many RCACons : (erased (Level) M N) (erased (RPoint M) a b c d) (erased (List (REdge M)) es)
      (erased (RCompatible M N a b c d) h) (erased (RCompatibleAll M N a b es) rest)
      -> (RCompatibleAll M N a b (Cons (REdge M) (MkREdge M c d) es))))

(def-adts $ (RDrawing : ((Level) M) ((Level) N) ((List (REdge M)) es) -> Type)
  enum
  (many RDrawNil : (erased (Level) M N) -> (RDrawing M N (Nil (REdge M))))
  (many RDrawCons : (erased (Level) M N) (erased (RPoint M) a b) (erased (List (REdge M)) es)
      (erased (RPointApart M a b) nondegenerate) (erased (RCompatibleAll M N a b es) compatible) (erased (RDrawing M N es) rest)
      -> (RDrawing M N (Cons (REdge M) (MkREdge M a b) es))))

(def-adts $ (RPaint : ((Level) M) -> Type)
  enum
  (many MkRPaint : (erased (Level) M) (many (RPoint M) p) (many (Nat) c) -> (RPaint M)))

(def-adts $ (RColorOf : ((Level) M) ((List (RPaint M)) ks) ((RPoint M) p) ((Nat) c) -> Type)
  enum
  (many RColorHere : (erased (Level) M N) (erased (List (RPaint M)) ks) (erased (RPoint M) p q) (erased (Nat) c)
      (erased (RPointEq M N p q) e)
      -> (RColorOf M (Cons (RPaint M) (MkRPaint M q c) ks) p c))
  (many RColorThere : (erased (Level) M) (erased (List (RPaint M)) ks) (erased (RPoint M) p q) (erased (Nat) c d)
      (erased (RPointApart M p q) skip) (erased (RColorOf M ks p c) rest)
      -> (RColorOf M (Cons (RPaint M) (MkRPaint M q d) ks) p c)))

(def-adts $ (RProper : ((Level) M) ((List (RPaint M)) ks) ((List (REdge M)) es) -> Type)
  enum
  (many RProperNil : (erased (Level) M) (erased (List (RPaint M)) ks) -> (RProper M ks (Nil (REdge M))))
  (many RProperCons : (erased (Level) M) (erased (List (RPaint M)) ks) (erased (RPoint M) a b) (erased (Nat) ca cb)
      (erased (List (REdge M)) es)
      (erased (RColorOf M ks a ca) ka) (erased (RColorOf M ks b cb) kb)
      (erased (Lt ca 4) ba) (erased (Lt cb 4) bb) (erased (Apart (Nat) Lt ca cb) differ)
      (erased (RProper M ks es) rest)
      -> (RProper M ks (Cons (REdge M) (MkREdge M a b) es))))

(def-adts $ (FourColorR : -> Type)
  enum
  (many MkFourColorR : (erased (Level) K)
      (erased (Fn K (erased (Level) M N) -> (erased (Level) L)
          (erased (Fn L (erased (List (REdge M)) es) (erased (RDrawing M N es) drawn) ->
              (erased (List (RPaint M)) ks) (erased (RProper M ks es) proper)) thm)) thms)
      -> (FourColorR)))
