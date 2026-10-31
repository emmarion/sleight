(def-fns _ $ (erased colored-at-nd : (erased (List (Nat)) ks e nd cs) (erased (Nat) i b) (subterm erased (Colored ks e nd cs) col)
    (erased (Nth (Nat) nd i b) p) -> (erased (Nat) c) (erased (Nth (Nat) cs i c) pc) (erased (Nth (Nat) ks b c) pb))
  (let-match erased col (ColoredCons _ e1 nd1 cs1 a b0 c0 c2 _ pn _ _ rest) (absurd (ColoredNil _) p))
  (let-match erased p (NthThere _ _ _ i1 _ p1) ((NthHere _ _ _) (values c0 (NthHere _ c0 cs1) pn)))
  (let ((erased c) (erased pc) (erased pb)) (colored-at-nd ks e1 nd1 cs1 i1 b rest p1))
  (values c (NthThere _ c0 cs1 i1 c pc) pb))

(def-fns _ $ (erased colored-at-e : (erased (List (Nat)) ks e nd cs) (erased (Nat) i a) (subterm erased (Colored ks e nd cs) col)
    (erased (Nth (Nat) e i a) p) -> (erased (Nat) c c2) (erased (Nth (Nat) cs i c) pc) (erased (Nth (Nat) ks a c2) pa)
    (erased (Apart (Nat) Lt c c2) d) (erased (Lt c 4) bd))
  (let-match erased col (ColoredCons _ e1 nd1 cs1 a0 b0 c0 c3 bd0 _ pe d0 rest) (absurd (ColoredNil _) p))
  (let-match erased p (NthThere _ _ _ i1 _ p1) ((NthHere _ _ _) (values c0 c3 (NthHere _ c0 cs1) pe d0 bd0)))
  (let ((erased c) (erased c2) (erased pc) (erased pa) (erased d) (erased bd)) (colored-at-e ks e1 nd1 cs1 i1 a rest p1))
  (values c c2 (NthThere _ c0 cs1 i1 c pc) pa d bd))

(def-fns _ $ (erased nr-color : (erased (List (Nat)) ks e nd) (erased (Nat) r x c) (erased (Colored ks e nd ks) col)
    (subterm erased (NodeReach nd r x) reach) (erased (Nth (Nat) ks x c) px) -> (erased (Nth (Nat) ks r c) pr))
  (let-match erased reach (NRStep _ _ r1 _ pn reach1) ((NRHere _ _) px))
  (let ((erased c0) (erased pc0) (erased pb0)) (colored-at-nd ks e nd ks r r1 col pn))
  (let-match erased (nth-fn _ ks r1 c0 c pb0 (nr-color ks e nd r1 x c col reach1 px)) (Refl _ _))
  pc0)

; xs has an element at i, or is too short.
(def-adts $ (NthDec : ((List (Nat)) xs) ((Nat) i) -> Type)
  enum
  (many NDHas : (erased (List (Nat)) xs) (erased (Nat) i x) (erased (Nth (Nat) xs i x) p) -> (NthDec xs i))
  (many NDShort : (erased (List (Nat)) xs) (erased (Nat) i m) (erased (Length (Nat) xs m) l) (erased (Lt m (Succ i)) s) -> (NthDec xs i)))

(def-fns _ $ (erased nth-dec : (subterm erased (List (Nat)) xs) (erased (Nat) i) -> (erased (NthDec xs i) r))
  (let-match erased xs (Cons _ x xs1) ((Nil _) (NDShort xs i (Zero) (LengthNil _) (LtZ i))))
  (let-match erased i (Succ i1) ((Zero) (NDHas xs i x (NthHere _ x xs1))))
  (match erased (nth-dec xs1 i1) _
    ((NDHas _ _ y p) (NDHas xs i y (NthThere _ x xs1 i1 y p)))
    ((NDShort _ _ m l s) (NDShort xs i (Succ m) (LengthCons _ x xs1 m l) (LtS m (Succ i1) s)))))

(def-fns _ $ (erased absurd nth-short : (erased (List (Nat)) xs) (erased (Nat) i m x) (erased (Nth (Nat) xs i x) p)
    (erased (Length (Nat) xs m) l) (erased (Lt m (Succ i)) s) -> (erased (False) f))
  (lt-asym i m (nth-lt-length _ xs i m x p l) s))

; The colour of label l: that of its representative dart, or 0 when there is none.
(def-adts $ (ColorFor : ((List (Nat)) rep) ((List (Nat)) ks) ((Nat) l) ((Nat) c) -> Type)
  enum
  (many CFHas : (erased (List (Nat)) rep ks) (erased (Nat) l r c) (erased (Nth (Nat) rep l r) pr) (erased (Nth (Nat) ks r c) pc)
      -> (ColorFor rep ks l c))
  (many CFNoRep : (erased (List (Nat)) rep ks) (erased (Nat) l m) (erased (Length (Nat) rep m) lm) (erased (Lt m (Succ l)) s)
      -> (ColorFor rep ks l (Zero)))
  (many CFNoKs : (erased (List (Nat)) rep ks) (erased (Nat) l r m) (erased (Nth (Nat) rep l r) pr) (erased (Length (Nat) ks m) lm)
      (erased (Lt m (Succ r)) s) -> (ColorFor rep ks l (Zero))))

(def-fns _ $ (erased color-for : (erased (List (Nat)) rep ks) (erased (Nat) l) -> (erased (Nat) c) (erased (ColorFor rep ks l c) cf))
  (let-match erased (nth-dec rep l) (NDHas _ _ r pr) ((NDShort _ _ m lm s) (values (Zero) (CFNoRep rep ks l m lm s))))
  (match erased (nth-dec ks r) _
    ((NDHas _ _ c pc) (values c (CFHas rep ks l r c pr pc)))
    ((NDShort _ _ m lm s) (values (Zero) (CFNoKs rep ks l r m pr lm s)))))

(def-fns _ $ (erased color-for-fn : (erased (List (Nat)) rep ks) (erased (Nat) l r c c2) (erased (ColorFor rep ks l c) cf)
    (erased (Nth (Nat) rep l r) pr) (erased (Nth (Nat) ks r c2) pc) -> (erased (Eq (Nat) c c2) q))
  (match erased cf _
    ((CFHas _ _ _ r1 _ pr1 pc1)
      (let-match erased (nth-fn _ rep l r1 r pr1 pr) (Refl _ _))
      (nth-fn _ ks r c c2 pc1 pc))
    (absurd (CFNoRep _ _ _ m lm s) (nth-short rep l m r pr lm s))
    (absurd (CFNoKs _ _ _ r1 m pr1 lm s)
      (let-match erased (nth-fn _ rep l r1 r pr1 pr) (Refl _ _))
      (nth-short ks r m c2 pc lm s))))

; kp paints the points pts, the first with label l, each with its label's colour.
(def-adts $ (Paints : ((List (Nat)) rep) ((List (Nat)) ks) ((List (Point)) pts) ((Nat) l) ((List (Paint)) kp) -> Type)
  enum
  (many PaintsNil : (erased (List (Nat)) rep ks) (erased (Nat) l) -> (Paints rep ks (Nil (Point)) l (Nil (Paint))))
  (many PaintsCons : (erased (List (Nat)) rep ks) (erased (Point) p) (erased (List (Point)) pts) (erased (Nat) l c) (erased (List (Paint)) kp)
      (erased (ColorFor rep ks l c) cf) (erased (Paints rep ks pts (Succ l) kp) rest)
      -> (Paints rep ks (Cons (Point) p pts) l (Cons (Paint) (MkPaint p c) kp))))

(def-fns _ $ (erased paints-exist : (erased (List (Nat)) rep ks) (subterm erased (List (Point)) pts) (erased (Nat) l) ->
    (erased (List (Paint)) kp) (erased (Paints rep ks pts l kp) p))
  (let-match erased pts (Cons _ q pts1) ((Nil _) (values (Nil _) (PaintsNil rep ks l))))
  (let ((erased c) (erased cf)) (color-for rep ks l))
  (let ((erased kp1) (erased p1)) (paints-exist rep ks pts1 (Succ l)))
  (values (Cons _ (MkPaint q c) kp1) (PaintsCons rep ks q pts1 l c kp1 cf p1)))

(def-fns _ $ (erased apart-point-sym : (erased (Point) p q) (erased (PointApart p q) d) -> (erased (PointApart q p) r))
  (match erased d _
    ((ApartX px py qx qy a) (ApartX qx qy px py (apart-sym px qx a)))
    ((ApartY px py qx qy a) (ApartY qx qy px py (apart-sym py qy a)))))

(def-fns _ $ (erased allapart-nth : (erased (Point) p a) (erased (List (Point)) ps) (erased (Nat) i) (subterm erased (AllApart p ps) aa)
    (erased (Nth (Point) ps i a) q) -> (erased (PointApart p a) r))
  (let-match erased aa (AACons _ b ps1 d aa1) (absurd (AANil _) q))
  (let-match erased q (NthThere _ _ _ i1 _ q1) ((NthHere _ _ _) d))
  (allapart-nth p a ps1 i1 aa1 q1))

; Point i of pts is painted with the colour of label i + l.
(def-fns _ $ (erased paints-colorof : (erased (List (Nat)) rep ks) (erased (List (Point)) pts) (erased (List (Paint)) kp) (erased (Point) a)
    (erased (Nat) i l j) (subterm erased (Paints rep ks pts l kp) pa) (erased (PtsApart pts) ap) (erased (Nth (Point) pts i a) q)
    (erased (Add i l j) s) -> (erased (Nat) c) (erased (ColorOf kp a c) co) (erased (ColorFor rep ks j c) cf))
  (let-match erased pa (PaintsCons _ _ p pts1 _ c0 kp1 cf0 pa1) (absurd (PaintsNil _ _ _) q))
  (let-match erased ap (PACons _ _ aa ap1))
  (let-match erased q (NthThere _ _ _ i1 _ q1)
    ((NthHere _ _ _) (let-match erased s (AddZero _)) (values c0 (ColorHere kp1 a c0) cf0)))
  (let-match erased s (AddSucc _ _ j1 s1))
  (let ((erased c) (erased co) (erased cf)) (paints-colorof rep ks pts1 kp1 a i1 (Succ l) j pa1 ap1 q1 (add-succ-right i1 l j1 s1)))
  (values c (ColorThere kp1 a p c c0 (apart-point-sym p a (allapart-nth p a pts1 i1 aa q1)) co) cf))

(def-fns _ $ (erased alljoined-in : (erased (List (Nat)) e pl r) (erased (Nat) s t) (subterm erased (AllJoined e pl r t) j) (erased (In s r) p) ->
    (erased (Joined e pl s t) q))
  (let-match erased j (AJCons _ _ r1 s0 _ j0 j1) (absurd (AJNil _ _ _) p))
  (let-match erased p (InThere _ _ _ p1) ((InHere _ _) j0))
  (alljoined-in e pl r1 s t j1 p1))

(def-fns _ $ (erased closes-joined : (erased (List (Nat)) e pl) (erased (List (Closed)) cs) (erased (Nat) s t) (subterm erased (AllClosed e pl cs) ac)
    (erased (Closes cs s t) c) -> (erased (Joined e pl s t) q))
  (let-match erased ac (ACCons _ _ r cs1 t0 j ac1) (absurd (ACNil _ _) c))
  (match erased c _
    ((ClosesHere _ _ _ _ p) (alljoined-in e pl r s t j p))
    ((ClosesThere _ _ _ _ c1) (closes-joined e pl cs1 s t ac1 c1))))

(def-fns _ $ (erased joined-colors : (erased (List (Nat)) e nd pl rep ks) (erased (Nat) s t ca cb) (erased (PlaneMap e nd) pm)
    (erased (Joined e pl s t) j) (erased (Reps nd rep (Zero) pl) rs) (erased (Colored ks e nd ks) col)
    (erased (ColorFor rep ks s ca) fa) (erased (ColorFor rep ks t cb) fb) ->
    (erased (Lt ca 4) la) (erased (Lt cb 4) lb) (erased (Apart (Nat) Lt ca cb) d))
  (let-match erased j (MkJoined _ _ _ _ x y pe ps pt))
  (let ((erased cx) (erased cy) (erased px) (erased py) (erased d) (erased lx)) (colored-at-e ks e nd ks x y col pe))
  (let ((erased cy2) (erased _) (erased py2) (erased _) (erased _) (erased ly)) (colored-at-e ks e nd ks y x col (pm-edge-inv e nd x y pm pe)))
  (let-match erased (nth-fn _ ks y cy2 cy py2 py) (Refl _ _))
  (let ((erased rx) (erased prx) (erased rcx)) (reps-at nd rep pl (Zero) x x s rs ps (add-zero-right x)))
  (let ((erased ry) (erased pry) (erased rcy)) (reps-at nd rep pl (Zero) y y t rs pt (add-zero-right y)))
  (let-match erased (color-for-fn rep ks s rx ca cx fa prx (nr-color ks e nd rx x cx col rcx px)) (Refl _ _))
  (let-match erased (color-for-fn rep ks t ry cb cy fb pry (nr-color ks e nd ry y cy col rcy py)) (Refl _ _))
  (values lx ly d))

(def-fns _ $ (erased proper-of : (erased (List (Nat)) e nd pl rep ks) (erased (List (Point)) pts) (erased (List (Closed)) cs) (erased (List (Edge)) es)
    (erased (List (Paint)) kp) (erased (PlaneMap e nd) pm) (erased (Reps nd rep (Zero) pl) rs) (erased (AllClosed e pl cs) ac)
    (erased (Colored ks e nd ks) col) (erased (Paints rep ks pts (Succ (Zero)) kp) pa) (erased (PtsApart pts) ap)
    (subterm erased (Covered pts cs es) cov) -> (erased (Proper kp es) pr))
  (let-match erased cov (CovCons _ _ es1 a b i j pai pbj c cov1) ((CovNil _ _) (ProperNil kp)))
  (let ((erased ca) (erased coa) (erased fa)) (paints-colorof rep ks pts kp a i (Succ (Zero)) (Succ i) pa ap pai (add-succ-right i (Zero) i (add-zero-right i))))
  (let ((erased cb) (erased cob) (erased fb)) (paints-colorof rep ks pts kp b j (Succ (Zero)) (Succ j) pa ap pbj (add-succ-right j (Zero) j (add-zero-right j))))
  (let ((erased rest)) (proper-of e nd pl rep ks pts cs es1 kp pm rs ac col pa ap cov1))
  (match erased c _
    ((OrL _ _ cl)
      (let ((erased la) (erased lb) (erased d)) (joined-colors e nd pl rep ks (Succ i) (Succ j) ca cb pm (closes-joined e pl cs (Succ i) (Succ j) ac cl) rs col fa fb))
      (ProperCons kp a b ca cb es1 coa cob la lb d rest))
    ((OrR _ _ cl)
      (let ((erased lb) (erased la) (erased d)) (joined-colors e nd pl rep ks (Succ j) (Succ i) cb ca pm (closes-joined e pl cs (Succ j) (Succ i) ac cl) rs col fb fa))
      (ProperCons kp a b ca cb es1 coa cob la lb (apart-sym cb ca d) rest))))

; What part A keeps between building the map and reading a colouring back.
(def-adts $ (MapFor : ((List (Edge)) es) ((List (Nat)) e) ((List (Nat)) nd) -> Type)
  enum
  (many MkMapFor : (erased (List (Edge)) es) (erased (List (Nat)) e nd pl rep) (erased (List (Point)) pts) (erased (List (Closed)) cs)
      (erased (Reps nd rep (Zero) pl) rs) (erased (AllClosed e pl cs) ac) (erased (PtsApart pts) ap) (erased (Covered pts cs es) cov)
      -> (MapFor es e nd)))

(def-fns _ $ (erased plan-map : (erased (List (Edge)) es) (erased (SweepPlan es) sp) ->
    (erased (List (Nat)) e nd) (erased (PlaneMap e nd) pm) (erased (MapFor es e nd) mf))
  (let-match erased sp (MkSweepPlan _ pts cs ap tr cov))
  (let-match erased (build cs tr) (MkBuilt _ e nd pl rep pm _ rs ac))
  (values e nd pm (MkMapFor es e nd pl rep pts cs rs ac ap cov)))

(def-fns _ $ (erased plan-paint : (erased (List (Edge)) es) (erased (List (Nat)) e nd ks) (erased (PlaneMap e nd) pm) (erased (MapFor es e nd) mf)
    (erased (Colored ks e nd ks) col) -> (erased (List (Paint)) kp) (erased (Proper kp es) pr))
  (let-match erased mf (MkMapFor _ _ _ pl rep pts cs rs ac ap cov))
  (let ((erased kp) (erased pa)) (paints-exist rep ks pts (Succ (Zero))))
  (values kp (proper-of e nd pl rep ks pts cs es kp pm rs ac col pa ap cov)))
