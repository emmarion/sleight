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
  (let-match erased g (MkEdgeGrow _ e1 _ _ len s1 s2))
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

(def-fns _ $ (erased pm-length : (erased (List (Nat)) e nd) (subterm erased (PlaneMap e nd) m) ->
    (erased (Nat) n) (erased (Length (Nat) e n) le) (erased (Length (Nat) nd n) ln))
  (match erased m _
    ((PMNil) (values (Zero) (LengthNil _) (LengthNil _)))
    ((PMIsolated e0 nd0 _ nd1 _ n0 m0 g sn1 sn2)
      (let ((erased k) (erased le0) (erased ln0)) (pm-length e0 nd0 m0))
      (let ((erased le1) (erased le2)) (grow-length e0 e n0 g))
      (let-match erased (length-fn _ e0 n0 k le1 le0) (Refl _ _))
      (values (Succ (Succ n0)) le2 (snoc-length _ nd1 nd (Succ n0) (Succ n0) sn2 (snoc-length _ nd0 nd1 n0 n0 sn1 ln0))))
    ((PMPendant e0 nd0 _ nd1 _ n0 d m0 g bd i1 sn2)
      (let ((erased k) (erased le0) (erased ln0)) (pm-length e0 nd0 m0))
      (let ((erased le1) (erased le2)) (grow-length e0 e n0 g))
      (let-match erased (length-fn _ e0 n0 k le1 le0) (Refl _ _))
      (values (Succ (Succ n0)) le2 (snoc-length _ nd1 nd (Succ n0) (Succ n0) sn2 (insert-length nd0 nd1 d n0 n0 i1 ln0))))
    ((PMChord e0 nd0 _ nd1 _ vl n0 d1 d2 m0 g b1 b2 ll j i1 i2)
      (let ((erased k) (erased le0) (erased ln0)) (pm-length e0 nd0 m0))
      (let ((erased le1) (erased le2)) (grow-length e0 e n0 g))
      (let-match erased (length-fn _ e0 n0 k le1 le0) (Refl _ _))
      (values (Succ (Succ n0)) le2 (insert-length nd1 nd d2 (Succ n0) (Succ n0) i2 (insert-length nd0 nd1 d1 n0 n0 i1 ln0))))))



; Every non-empty plane map is a smaller one with one more edge.
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
