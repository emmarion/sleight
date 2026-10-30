; A face walk from a to b whose every step leaves through an edge image outside s: the corners after the
; darts of s are never passed.
(def-adts $ (Walk : ((List (Nat)) e) ((List (Nat)) nd) ((List (Nat)) s) ((Nat) a) ((Nat) b) -> Type)
  enum
  (many WalkHere : (erased (List (Nat)) e nd s) (erased (Nat) a) -> (Walk e nd s a a))
  (many WalkStep : (erased (List (Nat)) e nd s) (erased (Nat) a q c b)
      (erased (Nth (Nat) e a q) pe) (erased (Nth (Nat) nd q c) pn) (erased (NotIn q s) out) (erased (Walk e nd s c b) w)
      -> (Walk e nd s a b)))

(def-fns _ $ (erased walk-face : (erased (List (Nat)) e nd s) (erased (Nat) a b) (subterm erased (Walk e nd s a b) w) ->
    (erased (FaceReach e nd a b) r))
  (let-match erased w (WalkStep _ _ _ _ q c _ pe pn _ w1) ((WalkHere _ _ _ _) (FRHere e nd a)))
  (FRStep e nd a q c b pe pn (walk-face e nd s c b w1)))

(def-fns _ $ (erased walk-cat : (erased (List (Nat)) e nd s) (erased (Nat) a b c) (subterm erased (Walk e nd s a b) w)
    (erased (Walk e nd s b c) v) -> (erased (Walk e nd s a c) r))
  (let-match erased w (WalkStep _ _ _ _ q c1 _ pe pn out w1) ((WalkHere _ _ _ _) v))
  (WalkStep e nd s a q c1 c pe pn out (walk-cat e nd s c1 b c w1 v)))

; nd2 agrees with nd at every dart outside s.
(def-adts $ (Agree : ((List (Nat)) nd) ((List (Nat)) nd2) ((List (Nat)) s) -> Type)
  enum
  (many AgRefl : (erased (List (Nat)) nd s) -> (Agree nd nd s))
  (many AgSnoc : (erased (List (Nat)) nd nd2 s) (erased (Nat) c) (erased (Snoc (Nat) nd c nd2) p) -> (Agree nd nd2 s))
  (many AgInsert : (erased (List (Nat)) nd nd2 s) (erased (Nat) d x) (erased (Insert nd d x nd2) p) (erased (In d s) m)
      -> (Agree nd nd2 s))
  (many AgTrans : (erased (List (Nat)) nd nd1 nd2 s) (erased (Agree nd nd1 s) p) (erased (Agree nd1 nd2 s) q)
      -> (Agree nd nd2 s)))

(def-fns _ $ (erased agree-nth : (erased (List (Nat)) nd nd2 s) (erased (Nat) q c) (subterm erased (Agree nd nd2 s) g)
    (erased (Nth (Nat) nd q c) p) (erased (NotIn q s) out) -> (erased (Nth (Nat) nd2 q c) r))
  (match erased g _
    ((AgRefl _ _) p)
    ((AgSnoc _ _ _ c1 sn) (snoc-old _ nd nd2 c1 c q sn p))
    ((AgInsert _ _ _ d x i m) (insert-other nd nd2 d x q c i p (notin-in q d s out m)))
    ((AgTrans _ nd1 _ _ g1 g2) (agree-nth nd1 nd2 s q c g2 (agree-nth nd nd1 s q c g1 p out) out))))

; Every element of m is in s.
(def-adts $ (Sub : ((List (Nat)) m) ((List (Nat)) s) -> Type)
  enum
  (many SubNil : (erased (List (Nat)) s) -> (Sub (Nil (Nat)) s))
  (many SubCons : (erased (Nat) x) (erased (List (Nat)) m s) (erased (In x s) p) (erased (Sub m s) rest) -> (Sub (Cons (Nat) x m) s)))

; Every element of s2 is in s or at least n.
(def-adts $ (SubFresh : ((List (Nat)) s2) ((List (Nat)) s) ((Nat) n) -> Type)
  enum
  (many SFNil : (erased (List (Nat)) s) (erased (Nat) n) -> (SubFresh (Nil (Nat)) s n))
  (many SFOld : (erased (Nat) x n) (erased (List (Nat)) s2 s) (erased (In x s) p) (erased (SubFresh s2 s n) rest)
      -> (SubFresh (Cons (Nat) x s2) s n))
  (many SFNew : (erased (Nat) x n) (erased (List (Nat)) s2 s) (erased (Lt n (Succ x)) p) (erased (SubFresh s2 s n) rest)
      -> (SubFresh (Cons (Nat) x s2) s n)))

(def-fns _ $ (erased notin-sub : (erased (Nat) q) (erased (List (Nat)) m s) (subterm erased (Sub m s) sb) (erased (NotIn q s) out) ->
    (erased (NotIn q m) r))
  (let-match erased sb (SubCons x m1 _ p sb1) ((SubNil _) (NotInNil q)))
  (NotInCons q x m1 (notin-in q x s out p) (notin-sub q m1 s sb1 out)))

(def-fns _ $ (erased notin-fresh : (erased (Nat) q n) (erased (List (Nat)) s2 s) (subterm erased (SubFresh s2 s n) sf)
    (erased (NotIn q s) out) (erased (Lt q n) bq) -> (erased (NotIn q s2) r))
  (match erased sf _
    ((SFNil _ _) (NotInNil q))
    ((SFOld x _ s3 _ p sf1) (NotInCons q x s3 (notin-in q x s out p) (notin-fresh q n s3 s sf1 out bq)))
    ((SFNew x _ s3 _ p sf1) (NotInCons q x s3 (ApLt _ _ q x (lt-le-trans q n x bq p)) (notin-fresh q n s3 s sf1 out bq)))))

; A walk in a plane map of size n survives a growth that changes nd only at corners it avoids, and may then
; avoid any set of old avoided corners and new darts.
(def-fns _ $ (erased walk-move : (erased (List (Nat)) e nd e2 nd2 s s2 m) (erased (Nat) a b n) (subterm erased (Walk e nd s a b) w)
    (erased (PlaneMap e nd) pm) (erased (Length (Nat) e n) l) (erased (SubFresh s2 s n) sf)
    (erased (Agree e e2 (Nil (Nat))) ge) (erased (Agree nd nd2 m) gn) (erased (Sub m s) sb) -> (erased (Walk e2 nd2 s2 a b) r))
  (let-match erased w (WalkStep _ _ _ _ q c _ pe pn out w1) ((WalkHere _ _ _ _) (WalkHere e2 nd2 s2 a)))
  (WalkStep e2 nd2 s2 a q c b (agree-nth e e2 (Nil (Nat)) a q ge pe (NotInNil a))
    (agree-nth nd nd2 m q c gn pn (notin-sub q m s sb out))
    (notin-fresh q n s2 s sf out (pm-edge-bound e nd a q n pm pe l))
    (walk-move e nd e2 nd2 s s2 m c b n w1 pm l sf ge gn sb)))

(def-fns _ $ (erased apart-sym : (erased (Nat) a b) (erased (Apart (Nat) Lt a b) p) -> (erased (Apart (Nat) Lt b a) q))
  (match erased p _ ((ApLt _ _ _ _ l) (ApGt _ _ b a l)) ((ApGt _ _ _ _ l) (ApLt _ _ b a l))))

(def-fns _ $ (erased notin-head : (erased (Nat) x y) (erased (List (Nat)) s) (erased (NotIn x (Cons (Nat) y s)) p) ->
    (erased (Apart (Nat) Lt x y) ne) (erased (NotIn x s) rest))
  (let-match erased p (NotInCons _ _ _ ne rest))
  (values ne rest))

(def-fns _ $ (erased sub-cons : (erased (Nat) y) (erased (List (Nat)) m s) (subterm erased (Sub m s) sb) -> (erased (Sub m (Cons (Nat) y s)) r))
  (let-match erased sb (SubCons x m1 _ p sb1) ((SubNil _) (SubNil _)))
  (SubCons x m1 (Cons _ y s) (InThere x y s p) (sub-cons y m1 s sb1)))

(def-fns _ $ (erased sub-refl : (subterm erased (List (Nat)) s) -> (erased (Sub s s) r))
  (let-match erased s (Cons _ x s1) ((Nil _) (SubNil _)))
  (SubCons x s1 s (InHere x s1) (sub-cons x s1 s1 (sub-refl s1))))

(def-fns _ $ (erased sf-of-sub : (erased (List (Nat)) m s) (erased (Nat) n) (subterm erased (Sub m s) sb) -> (erased (SubFresh m s n) r))
  (let-match erased sb (SubCons x m1 _ p sb1) ((SubNil _) (SFNil s n)))
  (SFOld x n m1 s p (sf-of-sub m1 s n sb1)))

(def-fns _ $ (erased walk-weaken : (erased (List (Nat)) e nd s s2) (erased (Nat) a b) (subterm erased (Walk e nd s a b) w)
    (erased (Sub s2 s) sb) -> (erased (Walk e nd s2 a b) r))
  (let-match erased w (WalkStep _ _ _ _ q c _ pe pn out w1) ((WalkHere _ _ _ _) (WalkHere e nd s2 a)))
  (WalkStep e nd s2 a q c b pe pn (notin-sub q s2 s sb out) (walk-weaken e nd s s2 c b w1 sb)))
