; The corner after dart d, with the active items there, in sweep order.
(def-adts $ (Group : -> Type)
  enum
  (many MkGroup : (many (Nat) d) (many (List (Nat)) items) -> (Group)))

(def-adts $ (Darts : ((List (Group)) gs) ((List (Nat)) s) -> Type)
  enum
  (many DartsNil : -> (Darts (Nil (Group)) (Nil (Nat))))
  (many DartsCons : (erased (Nat) d) (erased (List (Nat)) xs s) (erased (List (Group)) gs) (erased (Darts gs s) p)
      -> (Darts (Cons (Group) (MkGroup d xs) gs) (Cons (Nat) d s))))

(def-adts $ (Distinct : ((List (Nat)) s) -> Type)
  enum
  (many DistNil : -> (Distinct (Nil (Nat))))
  (many DistCons : (erased (Nat) x) (erased (List (Nat)) s) (erased (NotIn x s) p) (erased (Distinct s) rest)
      -> (Distinct (Cons (Nat) x s))))

; Every element of s xs outside m.
(def-adts $ (Disj : ((List (Nat)) s) ((List (Nat)) m) -> Type)
  enum
  (many DisjNil : (erased (List (Nat)) m) -> (Disj (Nil (Nat)) m))
  (many DisjCons : (erased (Nat) x) (erased (List (Nat)) s m) (erased (NotIn x m) p) (erased (Disj s m) rest)
      -> (Disj (Cons (Nat) x s) m)))

; The walk from the corner after d1 to the step into the corner after d2.
(def-adts $ (Link : ((List (Nat)) e) ((List (Nat)) nd) ((List (Nat)) s) ((Nat) d1) ((Nat) d2) -> Type)
  enum
  (many MkLink : (erased (List (Nat)) e nd s) (erased (Nat) d1 d2 c p)
      (erased (Nth (Nat) nd d1 c) pc) (erased (Nth (Nat) e d2 p) pp) (erased (Walk e nd s c p) w)
      -> (Link e nd s d1 d2)))

; The groups gs linked one after another, the last one to the corner after dn.
(def-adts $ (Chain : ((List (Nat)) e) ((List (Nat)) nd) ((List (Nat)) s) ((List (Group)) gs) ((Nat) dn) -> Type)
  enum
  (many ChainOne : (erased (List (Nat)) e nd s xs) (erased (Nat) d dn) (erased (Link e nd s d dn) k)
      -> (Chain e nd s (Cons (Group) (MkGroup d xs) (Nil (Group))) dn))
  (many ChainCons : (erased (List (Nat)) e nd s xs ys) (erased (List (Group)) gs) (erased (Nat) d d2 dn)
      (erased (Link e nd s d d2) k) (erased (Chain e nd s (Cons (Group) (MkGroup d2 ys) gs) dn) rest)
      -> (Chain e nd s (Cons (Group) (MkGroup d xs) (Cons (Group) (MkGroup d2 ys) gs)) dn)))

(def-fns _ $ (erased disj-notin : (erased (Nat) x) (erased (List (Nat)) s m) (subterm erased (Disj s m) dj) (erased (In x s) p) ->
    (erased (NotIn x m) r))
  (let-match erased dj (DisjCons y s1 _ q dj1) (absurd (DisjNil _) p))
  (let-match erased p (InThere _ _ _ p1) ((InHere _ _) q))
  (disj-notin x s1 m dj1 p1))

(def-fns _ $ (erased link-move : (erased (List (Nat)) e nd e2 nd2 s s2 m) (erased (Nat) d1 d2 n) (erased (Link e nd s d1 d2) k)
    (erased (PlaneMap e nd) pm) (erased (Length (Nat) e n) l) (erased (SubFresh s2 s n) sf)
    (erased (Agree e e2 (Nil (Nat))) ge) (erased (Agree nd nd2 m) gn) (erased (Sub m s) sb) (erased (NotIn d1 m) keep)
    -> (erased (Link e2 nd2 s2 d1 d2) r))
  (let-match erased k (MkLink _ _ _ _ _ c p pc pp w))
  (MkLink e2 nd2 s2 d1 d2 c p (agree-nth nd nd2 m d1 c gn pc keep) (agree-nth e e2 (Nil (Nat)) d2 p ge pp (NotInNil d2))
    (walk-move e nd e2 nd2 s s2 m c p n w pm l sf ge gn sb)))

(def-fns _ $ (erased chain-move : (erased (List (Nat)) e nd e2 nd2 s s2 m sg) (erased (List (Group)) gs) (erased (Nat) dn n)
    (subterm erased (Chain e nd s gs dn) ch) (erased (Darts gs sg) ds) (erased (Disj sg m) dj)
    (erased (PlaneMap e nd) pm) (erased (Length (Nat) e n) l) (erased (SubFresh s2 s n) sf)
    (erased (Agree e e2 (Nil (Nat))) ge) (erased (Agree nd nd2 m) gn) (erased (Sub m s) sb)
    -> (erased (Chain e2 nd2 s2 gs dn) r))
  (match erased ch _
    ((ChainOne _ _ _ xs d _ k)
      (let-match erased ds (DartsCons _ _ _ _ _))
      (ChainOne e2 nd2 s2 xs d dn
        (link-move e nd e2 nd2 s s2 m d dn n k pm l sf ge gn sb (disj-notin d sg m dj (InHere d _)))))
    ((ChainCons _ _ _ xs ys gs1 d d2 _ k rest)
      (let-match erased ds (DartsCons _ _ sg1 _ ds1))
      (let-match erased dj (DisjCons _ _ _ keep dj1))
      (ChainCons e2 nd2 s2 xs ys gs1 d d2 dn
        (link-move e nd e2 nd2 s s2 m d d2 n k pm l sf ge gn sb keep)
        (chain-move e nd e2 nd2 s s2 m sg1 (Cons _ (MkGroup d2 ys) gs1) dn n rest ds1 dj1 pm l sf ge gn sb)))))
