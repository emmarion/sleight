(def-adts $ (NotIn : ((Nat) x) ((List (Nat)) s) -> Type)
  enum
  (many NotInNil : (erased (Nat) x) -> (NotIn x (Nil (Nat))))
  (many NotInCons : (erased (Nat) x y) (erased (List (Nat)) s) (erased (Apart (Nat) Lt x y) ne) (erased (NotIn x s) rest)
      -> (NotIn x (Cons (Nat) y s))))

(def-adts $ (In : ((Nat) x) ((List (Nat)) s) -> Type)
  enum
  (many InHere : (erased (Nat) x) (erased (List (Nat)) s) -> (In x (Cons (Nat) x s)))
  (many InThere : (erased (Nat) x y) (erased (List (Nat)) s) (erased (In x s) p) -> (In x (Cons (Nat) y s))))

(def-fns _ $ (erased notin-in : (erased (Nat) x y) (erased (List (Nat)) s) (subterm erased (NotIn x s) p) (erased (In y s) q) ->
    (erased (Apart (Nat) Lt x y) ne))
  (let-match erased p (NotInCons _ z s1 ne1 p1) (absurd (NotInNil _) q))
  (let-match erased q (InThere _ _ _ q1) ((InHere _ _) ne1))
  (notin-in x y s1 p1 q1))

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
  (many AgSnoc : (erased (List (Nat)) nd nd2 s) (erased (Nat) c) (erased (Snoc (Nat) nd c nd2) p) -> (Agree nd nd2 s))
  (many AgInsert : (erased (List (Nat)) nd nd2 s) (erased (Nat) d x) (erased (Insert nd d x nd2) p) (erased (In d s) m)
      -> (Agree nd nd2 s))
  (many AgTrans : (erased (List (Nat)) nd nd1 nd2 s) (erased (Agree nd nd1 s) p) (erased (Agree nd1 nd2 s) q)
      -> (Agree nd nd2 s)))

(def-fns _ $ (erased agree-nth : (erased (List (Nat)) nd nd2 s) (erased (Nat) q c) (subterm erased (Agree nd nd2 s) g)
    (erased (Nth (Nat) nd q c) p) (erased (NotIn q s) out) -> (erased (Nth (Nat) nd2 q c) r))
  (match erased g _
    ((AgSnoc _ _ _ c1 sn) (snoc-old _ nd nd2 c1 c q sn p))
    ((AgInsert _ _ _ d x i m) (insert-other nd nd2 d x q c i p (notin-in q d s out m)))
    ((AgTrans _ nd1 _ _ g1 g2) (agree-nth nd1 nd2 s q c g2 (agree-nth nd nd1 s q c g1 p out) out))))

(def-fns _ $ (erased walk-grow : (erased (List (Nat)) e nd e2 nd2 s) (erased (Nat) a b) (subterm erased (Walk e nd s a b) w)
    (erased (Agree e e2 (Nil (Nat))) ge) (erased (Agree nd nd2 s) gn) -> (erased (Walk e2 nd2 s a b) r))
  (let-match erased w (WalkStep _ _ _ _ q c _ pe pn out w1) ((WalkHere _ _ _ _) (WalkHere e2 nd2 s a)))
  (WalkStep e2 nd2 s a q c b (agree-nth e e2 (Nil (Nat)) a q ge pe (NotInNil a)) (agree-nth nd nd2 s q c gn pn out) out
    (walk-grow e nd e2 nd2 s c b w1 ge gn)))
