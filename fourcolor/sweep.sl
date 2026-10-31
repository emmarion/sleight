(def-adts $ (LApp : (Type A) ((List A) xs) ((List A) ys) ((List A) zs) -> Type)
  enum
  (many LAppNil : (erased Type A) (erased (List A) ys) -> (LApp A (Nil A) ys ys))
  (many LAppCons : (erased Type A) (erased A x) (erased (List A) xs ys zs) (erased (LApp A xs ys zs) p)
      -> (LApp A (Cons A x xs) ys (Cons A x zs))))

(def-adts $ (Closed : -> Type)
  enum
  (many MkClosed : (many (Nat) t) (many (List (Nat)) r) -> (Closed)))

; A sweep from step t on, over the active items xs, each item being the label it starts at, in sweep order.
; Step t removes a run r of consecutive items, which start at distinct labels, and puts k new items, labelled t, in
; its place.
(def-adts $ (Trace : ((Nat) t) ((List (Nat)) xs) ((List (Closed)) cs) -> Type)
  enum
  (many TrDone : (erased (Nat) t) -> (Trace t (Nil (Nat)) (Nil (Closed))))
  (many TrStep : (erased (Nat) t k) (erased (List (Nat)) xs p r q pr ns pn ys) (erased (List (Closed)) cs)
      (erased (LApp (Nat) p r pr) a1) (erased (LApp (Nat) pr q xs) a2) (erased (Distinct r) dr)
      (erased (Repeat (Nat) k t ns) rk) (erased (LApp (Nat) p ns pn) a3) (erased (LApp (Nat) pn q ys) a4)
      (erased (Trace (Succ t) ys cs) rest)
      -> (Trace t xs (Cons (Closed) (MkClosed t r) cs))))

; Some step t of cs closes an item that started at s.
(def-adts $ (Closes : ((List (Closed)) cs) ((Nat) s) ((Nat) t) -> Type)
  enum
  (many ClosesHere : (erased (List (Closed)) cs) (erased (List (Nat)) r) (erased (Nat) s t) (erased (In s r) p)
      -> (Closes (Cons (Closed) (MkClosed t r) cs) s t))
  (many ClosesThere : (erased (List (Closed)) cs) (erased (Closed) c) (erased (Nat) s t) (erased (Closes cs s t) p)
      -> (Closes (Cons (Closed) c cs) s t)))

; Each edge of es joins two listed points whose labels some step joins.
(def-adts $ (Covered : ((List (Point)) pts) ((List (Closed)) cs) ((List (Edge)) es) -> Type)
  enum
  (many CovNil : (erased (List (Point)) pts) (erased (List (Closed)) cs) -> (Covered pts cs (Nil (Edge))))
  (many CovCons : (erased (List (Point)) pts) (erased (List (Closed)) cs) (erased (List (Edge)) es) (erased (Point) a b)
      (erased (Nat) i j) (erased (Nth (Point) pts i a) pa) (erased (Nth (Point) pts j b) pb)
      (erased (Or (Closes cs (Succ i) (Succ j)) (Closes cs (Succ j) (Succ i))) c) (erased (Covered pts cs es) rest)
      -> (Covered pts cs (Cons (Edge) (MkEdge a b) es))))

; Each point is apart from every later one.
(def-adts $ (AllApart : ((Point) p) ((List (Point)) ps) -> Type)
  enum
  (many AANil : (erased (Point) p) -> (AllApart p (Nil (Point))))
  (many AACons : (erased (Point) p q) (erased (List (Point)) ps) (erased (PointApart p q) d) (erased (AllApart p ps) rest)
      -> (AllApart p (Cons (Point) q ps))))

(def-adts $ (PtsApart : ((List (Point)) ps) -> Type)
  enum
  (many PANil : -> (PtsApart (Nil (Point))))
  (many PACons : (erased (Point) p) (erased (List (Point)) ps) (erased (AllApart p ps) d) (erased (PtsApart ps) rest)
      -> (PtsApart (Cons (Point) p ps))))

(def-adts $ (SweepPlan : ((List (Edge)) es) -> Type)
  enum
  (many MkSweepPlan : (erased (List (Edge)) es) (erased (List (Point)) pts) (erased (List (Closed)) cs)
      (erased (PtsApart pts) ap) (erased (Trace (Succ (Zero)) (Nil (Nat)) cs) tr) (erased (Covered pts cs es) cov)
      -> (SweepPlan es)))
