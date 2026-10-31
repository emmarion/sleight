(def-adts $ (OtherStep : ((Step) s) -> Type)
  enum
  (many OsRr : -> (OtherStep (SRr)))
  (many OsU : -> (OtherStep (SU)))
  (many OsK : -> (OtherStep (SK)))
  (many OsA : -> (OtherStep (SA))))

; xs lists the darts of a transversal of the kernel edges of the map of cp, the newest first: the foot a of each Y step but the
; first, and for each H step its crossbar d + 2 and its feet a and x0, the map before the step having d darts and its ring
; starting a, x0.
(def-adts $ (Ctrenum : ((List (Step)) cp) ((List (Nat)) xs) -> Type)
  enum
  (many CeNil : -> (Ctrenum (Nil (Step)) (Nil (Nat))))
  (many CeR : (erased (Nat) k) (erased (List (Step)) cp) (erased (List (Nat)) xs) (erased (Ctrenum cp xs) p) -> (Ctrenum (Cons (Step) (SR k) cp) xs))
  (many CeY1 : -> (Ctrenum (Cons (Step) (SY) (Nil (Step))) (Nil (Nat))))
  (many CeY : (erased (Step) s) (erased (List (Step)) cp) (erased (Nat) d a) (erased (List (Nat)) e f p xs)
      (erased (Cpmap (Cons (Step) s cp) d e f (Cons (Nat) a p)) c) (erased (Ctrenum (Cons (Step) s cp) xs) q)
      -> (Ctrenum (Cons (Step) (SY) (Cons (Step) s cp)) (Cons (Nat) a xs)))
  (many CeH : (erased (List (Step)) cp) (erased (Nat) d a x0) (erased (List (Nat)) e f p xs) (erased (Cpmap cp d e f (Cons (Nat) a p)) c)
      (erased (Ptr (Cons (Nat) a p) x0) px) (erased (Ctrenum cp xs) q)
      -> (Ctrenum (Cons (Step) (SH) cp) (Cons (Nat) (Succ (Succ d)) (Cons (Nat) a (Cons (Nat) x0 xs)))))
  (many CeOther : (erased (Step) s) (erased (List (Step)) cp) (erased (OtherStep s) o) -> (Ctrenum (Cons (Step) s cp) (Nil (Nat)))))

; cc lists the darts of xs at the positions i, i + 1, ... that cci lists.
(def-adts $ (Pick : ((List (Nat)) cci) ((Nat) i) ((List (Nat)) xs cc) -> Type)
  enum
  (many PkNil : (erased (List (Nat)) cci) (erased (Nat) i) -> (Pick cci i (Nil (Nat)) (Nil (Nat))))
  (many PkIn : (erased (List (Nat)) cci xs cc) (erased (Nat) i x) (erased (In i cci) p) (erased (Pick cci (Succ i) xs cc) rest)
      -> (Pick cci i (Cons (Nat) x xs) (Cons (Nat) x cc)))
  (many PkOut : (erased (List (Nat)) cci xs cc) (erased (Nat) i x) (erased (NotIn i cci) p) (erased (Pick cci (Succ i) xs cc) rest)
      -> (Pick cci i (Cons (Nat) x xs) cc)))

; cc is the contract of the configuration with program cp and contract indices cci.
(def-adts $ (CfContract : ((List (Step)) cp) ((List (Nat)) cci cc) -> Type)
  enum
  (many MkCfContract : (erased (List (Step)) cp) (erased (List (Nat)) cci xs cc) (erased (Ctrenum cp xs) ce) (erased (Pick cci (Zero) xs cc) pk)
      -> (CfContract cp cci cc)))

(def-fns _ $ (erased pointed-cons : (erased (List (Step)) cp) (erased (Nat) d) (erased (List (Nat)) e f r) (erased (Cpmap cp d e f r) c)
    -> (erased (Nat) a) (erased (List (Nat)) p) (erased (Eq (List (Nat)) r (Cons (Nat) a p)) q))
  (let ((erased n) (erased pm)) (cpmap-map cp d e f r c))
  (pointed-ring d e n f r pm))

(def-fns _ $ (many ctrenum-c : (subterm many (List (Step)) cp) (erased (NoA cp) na) -> (many (List (Nat)) xs) (erased (Ctrenum cp xs) p))
  (let-match many cp (Cons _ s rest) ((Nil _) (values (Nil _) (CeNil))))
  (let ((erased na1)) (noa-tail s rest na))
  (match many s _
    ((SR k) (let ((many xs) (erased p)) (tail $ ctrenum-c rest na1)) (values xs (CeR k rest xs p)))
    ((SY)
      (let-match many rest (Cons _ s1 rest1) ((Nil _) (values (Nil _) (CeY1))))
      (let ((many xs) (erased p)) (notail $ ctrenum-c rest na1))
      (let ((erased d) (erased e) (erased f) (many r) (erased c)) (cpmap-c rest na1))
      (let ((erased _) (erased _) (erased q)) (pointed-cons rest d e f r c))
      (let-match erased q (Refl _ _))
      (let-match many r (Cons _ a p1))
      (values (Cons _ a xs) (CeY s1 rest1 d a e f p1 xs c p)))
    ((SH)
      (let ((many xs) (erased p)) (notail $ ctrenum-c rest na1))
      (let ((many d) (erased e) (erased f) (many r) (erased c)) (cpmap-c rest na1))
      (let ((erased _) (erased _) (erased q)) (pointed-cons rest d e f r c))
      (let-match erased q (Refl _ _))
      (let-match many r (Cons _ a p1))
      (let ((many x0) (erased px)) (ptr-c a p1))
      (values (Cons _ (Succ (Succ d)) (Cons _ a (Cons _ x0 xs))) (CeH rest d a x0 e f p1 xs c px p)))
    ((SRr) (values (Nil _) (CeOther s rest (OsRr))))
    ((SU) (values (Nil _) (CeOther s rest (OsU))))
    ((SK) (values (Nil _) (CeOther s rest (OsK))))
    (absurd (SA) na)))

(def-fns _ $ (many pick-c : (many (List (Nat)) cci) (many (Nat) i) (subterm many (List (Nat)) xs) -> (many (List (Nat)) cc) (erased (Pick cci i xs cc) p))
  (let-match many xs (Cons _ x rest) ((Nil _) (values (Nil _) (PkNil cci i))))
  (let ((many cc) (erased p)) (notail $ pick-c cci (Succ i) rest))
  (match many (in-dec-c i cci) _
    ((IDIn _ _ q) (values (Cons _ x cc) (PkIn cci rest cc i x q p)))
    ((IDOut _ _ q) (values cc (PkOut cci rest cc i x q p)))))

(def-adts $ (NthD : ((List (Nat)) xs) ((Nat) i) -> Type)
  enum
  (many NthYes : (erased (List (Nat)) xs) (erased (Nat) i) (many (Nat) x) (erased (Nth (Nat) xs i x) p) -> (NthD xs i))
  (many NthNo : (erased (List (Nat)) xs) (erased (Nat) i) -> (NthD xs i)))

(def-fns _ $ (many nth-d : (subterm many (List (Nat)) xs) (many (Nat) i) -> (many (NthD xs i) r))
  (let-match many xs (Cons _ y rest) ((Nil _) (NthNo xs i)))
  (let-match many i (Succ i1) ((Zero) (NthYes xs i y (NthHere _ y rest))))
  (match many (notail $ nth-d rest i1) _
    ((NthYes _ _ x p) (NthYes xs i x (NthThere _ y rest i1 x p)))
    ((NthNo _ _) (NthNo xs i))))

(def-adts $ (InsertED : ((List (Nat)) e cc) -> Type)
  enum
  (many IEYes : (erased (List (Nat)) e cc) (many (List (Nat)) ie) (erased (InsertE e cc ie) p) -> (InsertED e cc))
  (many IENo : (erased (List (Nat)) e cc) -> (InsertED e cc)))

(def-fns _ $ (many inserte-c : (many (List (Nat)) e) (subterm many (List (Nat)) cc) -> (many (InsertED e cc) r))
  (let-match many cc (Cons _ y rest) ((Nil _) (IEYes e cc (Nil _) (IENil e))))
  (let-match many (nth-d e y) (NthYes _ _ z pz) ((NthNo _ _) (IENo e cc)))
  (let-match many (notail $ inserte-c e rest) (IEYes _ _ ie p) ((IENo _ _) (IENo e cc)))
  (IEYes e cc (Cons _ y (Cons _ z ie)) (IECons e rest ie y z pz p)))

(def-adts $ (RespD : ((List (Nat)) lab xs) -> Type)
  enum
  (many RsYes : (erased (List (Nat)) lab xs) (many (List (Nat)) ls) (erased (Respects lab xs ls) p) -> (RespD lab xs))
  (many RsNo : (erased (List (Nat)) lab xs) -> (RespD lab xs)))

(def-fns _ $ (many respects-c : (many (List (Nat)) lab) (subterm many (List (Nat)) xs) -> (many (RespD lab xs) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (RsYes lab xs (Nil _) (RespNil lab))))
  (let-match many (nth-d lab x) (NthYes _ _ l p) ((NthNo _ _) (RsNo lab xs)))
  (let-match many (notail $ respects-c lab rest) (RsYes _ _ ls q) ((RsNo _ _) (RsNo lab xs)))
  (RsYes lab xs (Cons _ l ls) (RespCons lab rest ls x l p q)))

(def-fns _ $ (many leq-c : (subterm many (List (Nat)) xs) (many (List (Nat)) ys) -> (many (Chk (Eq (List (Nat)) xs ys)) r))
  (let-match many xs (Cons _ x xs1) ((Nil _) (match many ys _ ((Nil _) (CkY _ (Refl _ xs))) (else (CkN _)))))
  (let-match many ys (Cons _ y ys1) ((Nil _) (CkN _)))
  (let-match many (nat-eq x y) (Equal _ _ _) (else (CkN _)))
  (let-match many (notail $ leq-c xs1 ys1) (CkY _ q) ((CkN _) (CkN _)))
  (let-match erased q (Refl _ _))
  (CkY _ (Refl _ xs)))

(def-fns _ $ (many distinct-c : (subterm many (List (Nat)) s) -> (many (Chk (Distinct s)) r))
  (let-match many s (Cons _ x rest) ((Nil _) (CkY _ (DistNil))))
  (let-match many (in-dec-c x rest) (IDOut _ _ p) ((IDIn _ _ _) (CkN _)))
  (let-match many (notail $ distinct-c rest) (CkY _ q) ((CkN _) (CkN _)))
  (CkY _ (DistCons x rest p q)))

(def-fns _ $ (many disj-c : (subterm many (List (Nat)) s) (many (List (Nat)) m) -> (many (Chk (Disj s m)) r))
  (let-match many s (Cons _ x rest) ((Nil _) (CkY _ (DisjNil m))))
  (let-match many (in-dec-c x m) (IDOut _ _ p) ((IDIn _ _ _) (CkN _)))
  (let-match many (notail $ disj-c rest m) (CkY _ q) ((CkN _) (CkN _)))
  (CkY _ (DisjCons x rest m p q)))

(def-fns _ $ (many orbit-min : (many (List (Nat)) p) (many (Nat) x cur lo) (subterm many (Nat) fuel) -> (many (Nat) r))
  (let-match many fuel (Succ fuel1) ((Zero) lo))
  (let-match many (nth-d p cur) (NthYes _ _ nx _) ((NthNo _ _) lo))
  (let-match many (nat-eq nx x) (Unequal _ _ _ _ _) ((Equal _ _ _) lo))
  (tail $ orbit-min p x nx (bif _ (nat-ltb nx lo) nx lo) fuel1))

(def-fns _ $ (many labels : (many (List (Nat)) p) (many (Nat) d i) (subterm many (Nat) k) -> (many (List (Nat)) lab))
  (let-match many k (Succ k1) ((Zero) (Nil _)))
  (Cons _ (orbit-min p i i i d) (notail $ labels p d (Succ i) k1)))

(def-fns _ $ (many flab-c : (many (List (Nat)) p) (many (Nat) d) -> (many (List (Nat)) lab) (many (Chk (Respects lab p lab)) r))
  (let ((many lab)) (labels p d 0 d))
  (let-match many (respects-c lab p) (RsYes _ _ ls q) ((RsNo _ _) (values lab (CkN _))))
  (let-match many (leq-c ls lab) (CkY _ eq) ((CkN _) (values lab (CkN _))))
  (let-match erased eq (Refl _ _))
  (values lab (CkY _ q)))

(def-fns _ $ (erased node-labels : (erased (Nat) d) (erased (List (Nat)) e n f fe lab) (erased (Hypermap d e n f) h) (erased (Respects f e fe) rfe)
    (erased (Respects lab fe lab) rl) -> (erased (Respects lab n lab) r))
  (let-match erased h (MkHypermap _ _ _ _ ids _ en _ io _ _ cen kn _ _))
  (let ((erased le) (erased _) (erased _)) (hyper-lengths d e n f h))
  (let ((erased lfe)) (respects-length f e fe d rfe le))
  (let ((erased ll)) (respects-length lab fe lab d rl lfe))
  (respects-assoc n fe lab ids lab lab d (respects-assoc n e f en fe ids d cen kn rfe lfe le) (respects-id-right d ids lab io ll) rl ll lfe))

(def-fns _ $ (many simple-c : (erased (List (Nat)) p) (many (List (Nat)) lab ie) (erased (Respects lab p lab) rf) -> (many (Chk (Simple p ie)) r))
  (let-match many (respects-c lab ie) (RsYes _ _ ls rp) ((RsNo _ _) (CkN _)))
  (let-match many (distinct-c ls) (CkY _ dl) ((CkN _) (CkN _)))
  (CkY _ (MkSimple p ie lab ls rf rp dl)))

(def-fns _ $ (many kernel-c : (erased (List (Nat)) f) (many (List (Nat)) r lab) (many (Nat) x) (erased (Respects lab f lab) rf) -> (many (Chk (Kernel f r x)) res))
  (let-match many (respects-c lab r) (RsYes _ _ ls rp) ((RsNo _ _) (CkN _)))
  (let-match many (nth-d lab x) (NthYes _ _ l px) ((NthNo _ _) (CkN _)))
  (let-match many (in-dec-c l ls) (IDOut _ _ out) ((IDIn _ _ _) (CkN _)))
  (CkY _ (MkKernel f r lab ls x l rf rp px out)))

(def-adts $ (WalkD : ((List (Nat)) p s) ((Nat) x y) -> Type)
  enum
  (many WkYes : (erased (List (Nat)) p s) (erased (Nat) x y) (many (List (Nat)) xs) (erased (Path p s x y xs) w) -> (WalkD p s x y))
  (many WkNo : (erased (List (Nat)) p s) (erased (Nat) x y) -> (WalkD p s x y)))

(def-fns _ $ (many walk-c : (many (List (Nat)) p s) (many (Nat) x y) (subterm many (Nat) fuel) -> (many (WalkD p s x y) r))
  (let-match many (nat-eq x y) (Unequal _ _ _ _ _) ((Equal _ _ _) (WkYes p s x y (Nil _) (PathHere p s x))))
  (let-match many fuel (Succ fuel1) ((Zero) (WkNo p s x y)))
  (let-match many (in-dec-c x s) (IDOut _ _ out) ((IDIn _ _ _) (WkNo p s x y)))
  (let-match many (nth-d p x) (NthYes _ _ z pz) ((NthNo _ _) (WkNo p s x y)))
  (let-match many (notail $ walk-c p s z y fuel1) (WkYes _ _ _ _ xs w) ((WkNo _ _ _ _) (WkNo p s x y)))
  (WkYes p s x y (Cons _ x xs) (PathStep p s xs x z y pz out w)))

(def-adts $ (OrbitD : ((List (Nat)) p) ((Nat) x) -> Type)
  enum
  (many OrYes : (erased (List (Nat)) p) (erased (Nat) x) (many (List (Nat)) os) (erased (Orbit p x os) o) -> (OrbitD p x))
  (many OrNo : (erased (List (Nat)) p) (erased (Nat) x) -> (OrbitD p x)))

(def-fns _ $ (many orbit-c : (many (List (Nat)) p) (many (Nat) x d) -> (many (OrbitD p x) r))
  (let-match many (nth-d p x) (NthYes _ _ y px) ((NthNo _ _) (OrNo p x)))
  (let-match many (walk-c p (Cons _ x (Nil _)) y x d) (WkYes _ _ _ _ xs w) ((WkNo _ _ _ _) (OrNo p x)))
  (OrYes p x (Cons _ x xs) (MkOrbit p xs x y px w)))

(def-fns _ $ (many fband-c : (many (List (Nat)) f p) (many (Nat) x) (subterm many (Nat) fuel) -> (many (Chk (Fband f p x)) r))
  (let-match many (in-dec-c x p) (IDOut _ _ _) ((IDIn _ _ i) (CkY _ (MkFband f p x x i (MkSomePath f (Nil _) (Nil _) x x (PathHere f (Nil _) x))))))
  (let-match many fuel (Succ fuel1) ((Zero) (CkN _)))
  (let-match many (nth-d f x) (NthYes _ _ z pz) ((NthNo _ _) (CkN _)))
  (let-match many (notail $ fband-c f p z fuel1) (CkY _ fb) ((CkN _) (CkN _)))
  (let-match erased fb (MkFband _ _ _ y iy sp))
  (let-match erased sp (MkSomePath _ _ xs _ _ w))
  (CkY _ (MkFband f p x y iy (MkSomePath f (Nil _) (Cons _ x xs) x y (PathStep f (Nil _) xs x z y pz (NotInNil x) w)))))

; Each dart of ys is in os and has its edge image on a face of p.
(def-adts $ (EBs : ((List (Nat)) e f p os ys) -> Type)
  enum
  (many EBNil : (erased (List (Nat)) e f p os) -> (EBs e f p os (Nil (Nat))))
  (many EBCons : (erased (List (Nat)) e f p os ys) (erased (Nat) y) (erased (In y os) i) (erased (EBand e f p y) b) (erased (EBs e f p os ys) rest)
      -> (EBs e f p os (Cons (Nat) y ys))))

(def-fns _ $ (erased ebs-lift : (erased (List (Nat)) e f p os ys) (erased (Nat) x) (subterm erased (EBs e f p os ys) q) -> (erased (EBs e f p (Cons (Nat) x os) ys) r))
  (let-match erased q (EBCons _ _ _ _ ys1 y i b rest) ((EBNil _ _ _ _) (EBNil e f p (Cons (Nat) x os))))
  (EBCons e f p (Cons (Nat) x os) ys1 y (InThere y x os i) b (ebs-lift e f p os ys1 x rest)))

(def-fns _ $ (many ebs-c : (many (List (Nat)) e f p) (subterm many (List (Nat)) os) (many (Nat) d) -> (many (List (Nat)) ys) (erased (EBs e f p os ys) q))
  (let-match many os (Cons _ y rest) ((Nil _) (values (Nil _) (EBNil e f p os))))
  (let ((many ys) (erased q)) (notail $ ebs-c e f p rest d))
  (let ((erased q1)) (ebs-lift e f p rest ys y q))
  (let-match many (nth-d e y) (NthYes _ _ z pz) ((NthNo _ _) (values ys q1)))
  (let-match many (fband-c f p z d) (CkY _ fb) ((CkN _) (values ys q1)))
  (values (Cons _ y ys) (EBCons e f p os ys y (InHere y rest) (MkEBand e f p y z pz fb) q1)))

(def-adts $ (AdjD : ((List (Nat)) e f os t) -> Type)
  enum
  (many AdYes : (erased (List (Nat)) e f os t) (erased (Nat) y) (erased (In y t) i) (erased (NotAdj e f os y) na) -> (AdjD e f os t))
  (many AdNo : (erased (List (Nat)) e f os t) -> (AdjD e f os t)))

(def-fns _ $ (many notadj-c : (many (List (Nat)) e f os lab eos ls) (erased (Respects lab f lab) rf) (erased (Respects e os eos) re) (erased (Respects lab eos ls) rl)
    (subterm many (List (Nat)) t) -> (many (AdjD e f os t) r))
  (let-match many t (Cons _ y t1) ((Nil _) (AdNo e f os t)))
  (let ((many (AdjD e f os t1) r1)) (notail $ notadj-c e f os lab eos ls rf re rl t1))
  (let ((many (AdjD e f os t) next)) (match many r1 _ ((AdYes _ _ _ _ y1 i na) (AdYes e f os t y1 (InThere y1 y t1 i) na)) ((AdNo _ _ _ _) (AdNo e f os t))))
  (let-match many (nth-d lab y) (NthYes _ _ l py) ((NthNo _ _) next))
  (match many (in-dec-c l ls) _
    ((IDOut _ _ out) (AdYes e f os t y (InHere y t1) (MkNotAdj e f os lab eos ls y l rf re rl py out)))
    ((IDIn _ _ _) next)))

(def-fns _ $ (many triad-c : (many (List (Nat)) e f p lab) (many (Nat) x d) (erased (Respects lab f lab) rf) -> (many (Chk (Triad e f p x)) r))
  (let-match many (orbit-c f x d) (OrYes _ _ os o) ((OrNo _ _) (CkN _)))
  (let ((many ys) (erased q)) (ebs-c e f p os d))
  (let-match many ys (Cons _ y1 ys1) ((Nil _) (CkN _)))
  (let-match many ys1 (Cons _ y2 ys2) ((Nil _) (CkN _)))
  (let-match many ys2 (Cons _ y3 _) ((Nil _) (CkN _)))
  (let-match erased q (EBCons _ _ _ _ _ _ i1 b1 q2))
  (let-match erased q2 (EBCons _ _ _ _ _ _ i2 b2 q3))
  (let-match erased q3 (EBCons _ _ _ _ _ _ i3 b3 _))
  (let-match many (distinct-c (Cons _ y1 (Cons _ y2 (Cons _ y3 (Nil _))))) (CkY _ dy) ((CkN _) (CkN _)))
  (let-match many (respects-c e os) (RsYes _ _ eos re) ((RsNo _ _) (CkN _)))
  (let-match many (respects-c lab eos) (RsYes _ _ ls rl) ((RsNo _ _) (CkN _)))
  (let-match many (notadj-c e f os lab eos ls rf re rl p) (AdYes _ _ _ _ y iy na) ((AdNo _ _ _ _) (CkN _)))
  (CkY _ (MkTriad e f p os x y1 y2 y3 y o i1 i2 i3 dy b1 b2 b3 iy na)))

; Some dart below i is in the kernel of r and a triad for p.
(def-adts $ (TriadD : ((List (Nat)) e f r p) -> Type)
  enum
  (many TrYes : (erased (List (Nat)) e f r p) (erased (Nat) x) (erased (Kernel f r x) kx) (erased (Triad e f p x) t) -> (TriadD e f r p))
  (many TrNo : (erased (List (Nat)) e f r p) -> (TriadD e f r p)))

(def-fns _ $ (many find-triad : (many (List (Nat)) e f r p lab) (many (Nat) d) (erased (Respects lab f lab) rf) (subterm many (Nat) i) -> (many (TriadD e f r p) res))
  (let-match many i (Succ x) ((Zero) (TrNo e f r p)))
  (let ((many (TriadD e f r p) next)) (notail $ find-triad e f r p lab d rf x))
  (let-match many (kernel-c f r lab x rf) (CkY _ kx) ((CkN _) next))
  (let-match many (triad-c e f p lab x d rf) (CkY _ t) ((CkN _) next))
  (TrYes e f r p x kx t))

(def-fns _ $ (many ccsize-c : (many (List (Nat)) e f r ie cc lab) (many (Nat) d) (erased (Respects lab f lab) rf) -> (many (Chk (CcSize e f r ie cc)) res))
  (let ((many k) (erased l)) (size-c _ cc))
  (let-match many k (Succ k1) ((Zero) (CkN _)))
  (let ((erased lo)) (LtZ k1))
  (let-match many k1 (Succ k2) ((Zero) (CkY _ (CsSmall e f r ie cc k l lo (LtS (Zero) (Succ (Succ (Succ (Zero)))) (LtZ (Succ (Succ (Zero)))))))))
  (let-match many k2 (Succ k3) ((Zero) (CkY _ (CsSmall e f r ie cc k l lo (LtS (Succ (Zero)) (Succ (Succ (Succ (Zero)))) (LtS (Zero) (Succ (Succ (Zero))) (LtZ (Succ (Zero)))))))))
  (let-match many k3 (Succ k4)
    ((Zero) (CkY _ (CsSmall e f r ie cc k l lo (LtS (Succ (Succ (Zero))) (Succ (Succ (Succ (Zero)))) (LtS (Succ (Zero)) (Succ (Succ (Zero)))
      (LtS (Zero) (Succ (Zero)) (LtZ (Zero)))))))))
  (let-match many k4 (Zero) ((Succ _) (CkN _)))
  (let-match many (find-triad e f r ie lab d rf d) (TrYes _ _ _ _ x kx t) ((TrNo _ _ _ _) (CkN _)))
  (CkY _ (CsTriad e f r ie cc x l kx t)))

(def-fns _ $ (many valid-c : (many (Nat) d) (many (List (Nat)) e f r cc ie) (erased (List (Nat)) n) (erased (Hypermap d e n f) h) (erased (InsertE e cc ie) pi)
    -> (many (Chk (ValidContract e n f r cc)) res))
  (let-match many (disj-c r ie) (CkY _ off) ((CkN _) (CkN _)))
  (let-match many (respects-c f e) (RsYes _ _ fe rfe) ((RsNo _ _) (CkN _)))
  (let ((many nlab) (many cn)) (flab-c fe d))
  (let-match many cn (CkY _ rn) ((CkN _) (CkN _)))
  (let-match many (simple-c n nlab ie (node-labels d e n f fe nlab h rfe rn)) (CkY _ sp) ((CkN _) (CkN _)))
  (let ((many flab) (many cf)) (flab-c f d))
  (let-match many cf (CkY _ rf) ((CkN _) (CkN _)))
  (let-match many (ccsize-c e f r ie cc flab d rf) (CkY _ sz) ((CkN _) (CkN _)))
  (CkY _ (MkValidContract e n f r cc ie pi off sp sz)))

; The configuration cf is C-reducible with its contract, by a function at level X.
(def-adts $ (Reducible : ((Level) X) ((Config) cf) -> Type)
  enum
  (many MkReducible : (erased (Level) X) (erased (Bool) sym) (erased (List (Nat)) cci cc) (erased (List (Step)) cp) (erased (CfContract cp cci cc) pc) (erased (CRed X cp cc) red)
      -> (Reducible X (MkConfig sym cci cp))))

(def-lvl CRX)

(def-fns _ $ (many red-c : (many (Config) cf) (many (List (InitE)) cache) -> (many (Chk (Reducible CRX cf)) r) (many (List (InitE)) cache2))
  (let-match many cf (MkConfig sym cci cp))
  (let-match many (noa-dec cp) (NoAYes _ na) ((NoANo _) (values (CkN _) cache)))
  (let ((many d) (many e) (many f) (many r) (erased c)) (cpmap-c cp na))
  (let ((erased n) (erased pm)) (cpmap-map cp d e f r c))
  (let ((erased h)) (pointed-hyper d e n f r pm))
  (let ((many xs) (erased pce)) (ctrenum-c cp na))
  (let ((many cc) (erased pk)) (pick-c cci (Zero) xs))
  (let-match many (inserte-c e cc) (IEYes _ _ ie pi) ((IENo _ _) (values (CkN _) cache)))
  (let-match many (valid-c d e f r cc ie n h pi) (CkY _ v) ((CkN _) (values (CkN _) cache)))
  (let ((many kc) (many cache2)) (kempe-tree-chk cp cache))
  (let-match many kc (KCYes _ h0 kt ks cs _) ((KCNo _) (values (CkN _) cache2)))
  (let-match many (ryh-c cp) (CkY _ ry) ((CkN _) (values (CkN _) cache2)))
  (let ((many rp) (erased rs)) (revs-c cp))
  (let-match many (dfs-c kt ie (Cons _ (SU) rp) all-cols (Zero) (Nil _)) (CkY _ df) ((CkN _) (values (CkN _) cache2)))
  (values (CkY _ (MkReducible CRX sym cci cc cp (MkCfContract cp cci xs cc pce pk)
    (check-reducible-valid CRX CGL (prove-predates KHL CRX) (prove-predates CGL CRX) cp cc kt
      (kempe-half cp h0 kt ks cs) (contract-ok cp cc kt d e n f r ie rp c h v pi ry rs (dfe-good kt ie (Cons _ (SU) rp) (Zero) (Nil _) df))))) cache2))

(def-adts $ (AllRed : ((Level) X) ((List (Config)) cfs) -> Type)
  enum
  (many ARNil : (erased (Level) X) -> (AllRed X (Nil (Config))))
  (many ARCons : (erased (Level) X) (erased (Config) cf) (erased (List (Config)) cfs) (erased (Reducible X cf) p) (erased (AllRed X cfs) rest)
      -> (AllRed X (Cons (Config) cf cfs))))

(def-fns _ $ (many red-all-c : (subterm many (List (Config)) cfs) (many (List (InitE)) cache) -> (many (Chk (AllRed CRX cfs)) r))
  (let-match many cfs (Cons _ cf rest) ((Nil _) (CkY _ (ARNil CRX))))
  (let ((many b) (many cache2)) (red-c cf cache))
  (let-match many b (CkY _ p) ((CkN _) (CkN _)))
  (let-match many (notail $ red-all-c rest cache2) (CkY _ q) ((CkN _) (CkN _)))
  (CkY _ (ARCons CRX cf rest p q)))

(def-adts $ (AllRedC : ((Level) X) ((List (List (Config))) css) -> Type)
  enum
  (many ARCNil : (erased (Level) X) -> (AllRedC X (Nil (List (Config)))))
  (many ARCCons : (erased (Level) X) (erased (List (Config)) cs) (erased (List (List (Config))) css) (erased (AllRed X cs) p) (erased (AllRedC X css) rest)
      -> (AllRedC X (Cons (List (Config)) cs css))))
