(def-adts $ (Point : -> Type)
  enum
  (many MkPoint : (many (Nat) x) (many (Nat) y) -> (Point)))

(def-adts $ (Edge : -> Type)
  enum
  (many MkEdge : (many (Point) a) (many (Point) b) -> (Edge)))

; p and q differ in their x or their y coordinate.
(def-adts $ (PointApart : ((Point) p) ((Point) q) -> Type)
  enum
  (many ApartX : (erased (Nat) px py qx qy) (erased (Apart (Nat) Lt px qx) d)
      -> (PointApart (MkPoint px py) (MkPoint qx qy)))
  (many ApartY : (erased (Nat) px py qx qy) (erased (Apart (Nat) Lt py qy) d)
      -> (PointApart (MkPoint px py) (MkPoint qx qy))))

; s = px*qy + qx*ry + rx*py, one half of the shoelace formula for the triangle pqr.
(def-adts $ (Shoelace : ((Point) p) ((Point) q) ((Point) r) ((Nat) s) -> Type)
  enum
  (many MkShoelace : (erased (Nat) px py qx qy rx ry m1 m2 m3 m12 s)
      (erased (Mul px qy m1) p1) (erased (Mul qx ry m2) p2) (erased (Mul rx py m3) p3)
      (erased (Add m1 m2 m12) q1) (erased (Add m12 m3 s) q2)
      -> (Shoelace (MkPoint px py) (MkPoint qx qy) (MkPoint rx ry) s)))

; r is strictly left of the line from p to q: the triangle pqr is counter-clockwise.
(def-adts $ (Left : ((Point) p) ((Point) q) ((Point) r) -> Type)
  enum
  (many MkLeft : (erased (Point) p q r) (erased (Nat) s1 s2)
      (erased (Shoelace p q r s1) h1) (erased (Shoelace r q p s2) h2) (erased (Lt s2 s1) l)
      -> (Left p q r)))

; r is not on the line through a and b.
(def-adts $ (OffLine : ((Point) a) ((Point) b) ((Point) r) -> Type)
  enum
  (many OffLeft : (erased (Point) a b r) (erased (Left a b r) l) -> (OffLine a b r))
  (many OffRight : (erased (Point) a b r) (erased (Left b a r) l) -> (OffLine a b r)))

; c and d are strictly on the same side of the line through a and b.
(def-adts $ (SameSide : ((Point) a) ((Point) b) ((Point) c) ((Point) d) -> Type)
  enum
  (many BothLeft : (erased (Point) a b c d) (erased (Left a b c) lc) (erased (Left a b d) ld) -> (SameSide a b c d))
  (many BothRight : (erased (Point) a b c d) (erased (Left b a c) lc) (erased (Left b a d) ld) -> (SameSide a b c d)))

; The segments ab and cd meet at most at a shared endpoint, and no unshared endpoint of either is on the other's line.
(def-adts $ (Compatible : ((Point) a) ((Point) b) ((Point) c) ((Point) d) -> Type)
  enum
  (many ShareCA : (erased (Point) a b d) (erased (OffLine a b d) o) -> (Compatible a b a d))
  (many ShareCB : (erased (Point) a b d) (erased (OffLine a b d) o) -> (Compatible a b b d))
  (many ShareDA : (erased (Point) a b c) (erased (OffLine a b c) o) -> (Compatible a b c a))
  (many ShareDB : (erased (Point) a b c) (erased (OffLine a b c) o) -> (Compatible a b c b))
  (many SplitByAB : (erased (Point) a b c d)
      (erased (SameSide a b c d) cd) (erased (OffLine c d a) oa) (erased (OffLine c d b) ob)
      -> (Compatible a b c d))
  (many SplitByCD : (erased (Point) a b c d)
      (erased (OffLine a b c) oc) (erased (OffLine a b d) od) (erased (SameSide c d a b) ab)
      -> (Compatible a b c d)))

; The segment ab is compatible with every edge of es.
(def-adts $ (CompatibleAll : ((Point) a) ((Point) b) ((List (Edge)) es) -> Type)
  enum
  (many CANil : (erased (Point) a b) -> (CompatibleAll a b (Nil (Edge))))
  (many CACons : (erased (Point) a b c d) (erased (List (Edge)) es)
      (erased (Compatible a b c d) h) (erased (CompatibleAll a b es) rest)
      -> (CompatibleAll a b (Cons (Edge) (MkEdge c d) es))))

; Each edge of es has distinct endpoints and is compatible with every edge after it.
(def-adts $ (Drawing : ((List (Edge)) es) -> Type)
  enum
  (many DrawNil : -> (Drawing (Nil (Edge))))
  (many DrawCons : (erased (Point) a b) (erased (List (Edge)) es)
      (erased (PointApart a b) nondegenerate) (erased (CompatibleAll a b es) compatible) (erased (Drawing es) rest)
      -> (Drawing (Cons (Edge) (MkEdge a b) es))))

(def-adts $ (Paint : -> Type)
  enum
  (many MkPaint : (many (Point) p) (many (Nat) c) -> (Paint)))

; c is the color of the first pair in ks whose point is p.
(def-adts $ (ColorOf : ((List (Paint)) ks) ((Point) p) ((Nat) c) -> Type)
  enum
  (many ColorHere : (erased (List (Paint)) ks) (erased (Point) p) (erased (Nat) c)
      -> (ColorOf (Cons (Paint) (MkPaint p c) ks) p c))
  (many ColorThere : (erased (List (Paint)) ks) (erased (Point) p q) (erased (Nat) c d)
      (erased (PointApart p q) skip) (erased (ColorOf ks p c) rest)
      -> (ColorOf (Cons (Paint) (MkPaint q d) ks) p c)))

; Every edge of es has endpoints with different colors, each below 4, under ks.
(def-adts $ (Proper : ((List (Paint)) ks) ((List (Edge)) es) -> Type)
  enum
  (many ProperNil : (erased (List (Paint)) ks) -> (Proper ks (Nil (Edge))))
  (many ProperCons : (erased (List (Paint)) ks) (erased (Point) a b) (erased (Nat) ca cb) (erased (List (Edge)) es)
      (erased (ColorOf ks a ca) ka) (erased (ColorOf ks b cb) kb)
      (erased (Lt ca 4) ba) (erased (Lt cb 4) bb) (erased (Apart (Nat) Lt ca cb) differ)
      (erased (Proper ks es) rest)
      -> (Proper ks (Cons (Edge) (MkEdge a b) es))))

; Every straight-line drawing of a graph has a proper coloring with 4 colors.
(def-adts $ (FourColor : -> Type)
  enum
  (many MkFourColor : (erased (Level) L)
      (erased (Fn L (erased (List (Edge)) es) (erased (Drawing es) drawn) ->
          (erased (List (Paint)) ks) (erased (Proper ks es) proper)) thm)
      -> (FourColor)))
