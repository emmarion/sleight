(def-adts $ (EdgeBack : ((List (Nat)) e) ((Nat) n) ((Nat) a) ((Nat) b) -> Type)
  enum
  (many EBOld : (erased (List (Nat)) e) (erased (Nat) n a b) (erased (Nth (Nat) e a b) p) -> (EdgeBack e n a b))
  (many EBLow : (erased (List (Nat)) e) (erased (Nat) n) -> (EdgeBack e n n (Succ n)))
  (many EBHigh : (erased (List (Nat)) e) (erased (Nat) n) -> (EdgeBack e n (Succ n) n)))

(def-fns _ $ (erased edge-back : (erased (List (Nat)) e e2) (erased (Nat) n a b) (erased (EdgeGrow e n e2) g)
    (erased (Nth (Nat) e2 a b) p) -> (erased (EdgeBack e n a b) r))
  (let-match erased g (MkEdgeGrow _ e1 _ _ len s1 s2))
  (let ((erased len1)) (snoc-length _ e e1 (Succ n) n s1 len))
  (let-match erased (snoc-back _ e1 e2 n b a (Succ n) s2 len1 p) (OrL _ _ p1)
    ((OrR _ _ q)
      (let-match erased q (Refl _ _))
      (let-match erased (nth-fn _ e2 (Succ n) b n p (snoc-new _ e1 e2 n (Succ n) s2 len1)) (Refl _ _))
      (EBHigh e n)))
  (let-match erased (snoc-back _ e e1 (Succ n) b a n s1 len p1) (OrL _ _ p2)
    ((OrR _ _ q)
      (let-match erased q (Refl _ _))
      (let-match erased (nth-fn _ e1 n b (Succ n) p1 (snoc-new _ e e1 (Succ n) n s1 len)) (Refl _ _))
      (EBLow e n)))
  (EBOld e n a b p2))

(def-fns _ $ (erased edge-old : (erased (List (Nat)) e e2) (erased (Nat) n a b) (erased (EdgeGrow e n e2) g)
    (erased (Nth (Nat) e a b) p) -> (erased (Nth (Nat) e2 a b) r))
  (let-match erased g (MkEdgeGrow _ e1 _ _ _ s1 s2))
  (snoc-old _ e1 e2 n b a s2 (snoc-old _ e e1 (Succ n) b a s1 p)))

(def-fns _ $ (erased edge-low : (erased (List (Nat)) e e2) (erased (Nat) n) (erased (EdgeGrow e n e2) g) ->
    (erased (Nth (Nat) e2 n (Succ n)) r))
  (let-match erased g (MkEdgeGrow _ e1 _ _ len s1 s2))
  (snoc-old _ e1 e2 n (Succ n) n s2 (snoc-new _ e e1 (Succ n) n s1 len)))

(def-fns _ $ (erased edge-high : (erased (List (Nat)) e e2) (erased (Nat) n) (erased (EdgeGrow e n e2) g) ->
    (erased (Nth (Nat) e2 (Succ n) n) r))
  (let-match erased g (MkEdgeGrow _ e1 _ _ len s1 s2))
  (snoc-new _ e1 e2 n (Succ n) s2 (snoc-length _ e e1 (Succ n) n s1 len)))

(def-fns _ $ (erased grow-length : (erased (List (Nat)) e e2) (erased (Nat) n) (erased (EdgeGrow e n e2) g) ->
    (erased (Length (Nat) e n) l) (erased (Length (Nat) e2 (Succ (Succ n))) l2))
  (let-match erased g (MkEdgeGrow _ e1 _ _ len s1 s2))
  (values len (snoc-length _ e1 e2 n (Succ n) s2 (snoc-length _ e e1 (Succ n) n s1 len))))

(def-fns _ $ (erased insert-length : (erased (List (Nat)) nd nd2) (erased (Nat) d x n) (erased (Insert nd d x nd2) p)
    (erased (Length (Nat) nd n) l) -> (erased (Length (Nat) nd2 (Succ n)) l2))
  (let-match erased p (MkInsert _ nd1 _ _ _ c _ s q))
  (snoc-length _ nd1 nd2 c n q (setnth-length _ nd d n x nd1 s l)))



(def-fns _ $ (erased pm-last : (erased (List (Nat)) e nd) (erased (Nat) a b) (erased (PlaneMap e nd) m) (erased (Nth (Nat) e a b) p) ->
    (erased (List (Nat)) e0 nd0) (erased (Nat) n) (erased (EdgeGrow e0 n e) g) (erased (PlaneMap e0 nd0) m0)
    (erased (Subterm (PlaneMap e0 nd0) m0 (PlaneMap e nd) m) sm))
  (match erased m _
    (absurd (PMNil) p)
    ((PMIsolated e0 nd0 _ _ _ n m0 g _ _) (values e0 nd0 n g m0 (prove-subterm m0 m)))
    ((PMPendant e0 nd0 _ _ _ n _ m0 g _ _ _) (values e0 nd0 n g m0 (prove-subterm m0 m)))
    ((PMChord e0 nd0 _ _ _ _ n _ _ m0 g _ _ _ _ _ _) (values e0 nd0 n g m0 (prove-subterm m0 m)))))

(def-fns _ $ (erased pm-edge-inv : (erased (List (Nat)) e nd) (erased (Nat) a b) (subterm erased (PlaneMap e nd) m)
    (erased (Nth (Nat) e a b) p) -> (erased (Nth (Nat) e b a) r))
  (let ((erased e0) (erased nd0) (erased n) (erased g) (erased m0) (erased sm)) (pm-last e nd a b m p))
  (match erased (edge-back e0 e n a b g p) _
    ((EBOld _ _ _ _ q) (edge-old e0 e n b a g (pm-edge-inv e0 nd0 a b (subterm sm) m0 q)))
    ((EBLow _ _) (edge-high e0 e n g))
    ((EBHigh _ _) (edge-low e0 e n g))))

(def-fns _ $ (erased pm-edge-bound : (erased (List (Nat)) e nd) (erased (Nat) a b n) (subterm erased (PlaneMap e nd) m)
    (erased (Nth (Nat) e a b) p) (erased (Length (Nat) e n) l) -> (erased (Lt b n) r))
  (let ((erased e0) (erased nd0) (erased n0) (erased g) (erased m0) (erased sm)) (pm-last e nd a b m p))
  (let ((erased l0) (erased l2)) (grow-length e0 e n0 g))
  (let-match erased (length-fn _ e n (Succ (Succ n0)) l l2) (Refl _ _))
  (match erased (edge-back e0 e n0 a b g p) _
    ((EBOld _ _ _ _ q) (lt-weaken b (Succ n0) (lt-weaken b n0 (pm-edge-bound e0 nd0 a b n0 (subterm sm) m0 q l0))))
    ((EBLow _ _) (lt-succ (Succ n0)))
    ((EBHigh _ _) (lt-weaken n0 (Succ n0) (lt-succ n0)))))

(def-fns _ $ (erased grow-exists : (erased (List (Nat)) e) (erased (Nat) n) (erased (Length (Nat) e n) l) ->
    (erased (List (Nat)) e2) (erased (EdgeGrow e n e2) g))
  (let ((erased e1) (erased s1)) (snoc-exists _ e (Succ n)))
  (let ((erased e2) (erased s2)) (snoc-exists _ e1 n))
  (values e2 (MkEdgeGrow e e1 e2 n l s1 s2)))

(def-fns _ $ (erased insert-exists : (erased (List (Nat)) nd) (erased (Nat) d x c) (erased (Nth (Nat) nd d c) p) ->
    (erased (List (Nat)) nd2) (erased (Insert nd d x nd2) i))
  (let ((erased k) (erased l)) (length-exists _ nd))
  (let ((erased nd1) (erased s)) (setnth-exists _ nd k d x l (nth-lt-length _ nd d k c p l)))
  (let ((erased nd2) (erased q)) (snoc-exists _ nd1 c))
  (values nd2 (MkInsert nd nd1 nd2 d x c p s q)))

(def-fns _ $ (erased fr-snoc : (erased (List (Nat)) e nd) (erased (Nat) a b q c) (subterm erased (FaceReach e nd a b) r)
    (erased (Nth (Nat) e b q) pe) (erased (Nth (Nat) nd q c) pn) -> (erased (FaceReach e nd a c) r2))
  (let-match erased r (FRStep _ _ _ q1 c1 _ pe1 pn1 r1)
    ((FRHere _ _ _) (FRStep e nd a q c c pe pn (FRHere e nd c))))
  (FRStep e nd a q1 c1 c pe1 pn1 (fr-snoc e nd c1 b q c r1 pe pn)))
