; The contract of a configuration (cfcontract.v on these dart numbers) and the certified check that it is C-reducible.
; Load after ccomp.sl.

(def-adts $ (OtherStep : ((Step) s) -> Type)
  enum
  (many OsRr : -> (OtherStep (SRr)))
  (many OsU : -> (OtherStep (SU)))
  (many OsK : -> (OtherStep (SK)))
  (many OsA : -> (OtherStep (SA))))

; xs lists the darts of a transversal of the kernel edges of the map of cp, the newest first (Gonthier's ctrenum, on these
; dart numbers): the foot a of each Y step but the first, and for each H step its crossbar d + 2 and its feet a and x0, the
; map before the step having d darts and its ring starting a, x0.
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

; cc lists the darts of xs at the positions i, i + 1, ... that cci lists (Gonthier's mask of ctrmask).
(def-adts $ (Pick : ((List (Nat)) cci) ((Nat) i) ((List (Nat)) xs cc) -> Type)
  enum
  (many PkNil : (erased (List (Nat)) cci) (erased (Nat) i) -> (Pick cci i (Nil (Nat)) (Nil (Nat))))
  (many PkIn : (erased (List (Nat)) cci xs cc) (erased (Nat) i x) (erased (In i cci) p) (erased (Pick cci (Succ i) xs cc) rest)
      -> (Pick cci i (Cons (Nat) x xs) (Cons (Nat) x cc)))
  (many PkOut : (erased (List (Nat)) cci xs cc) (erased (Nat) i x) (erased (NotIn i cci) p) (erased (Pick cci (Succ i) xs cc) rest)
      -> (Pick cci i (Cons (Nat) x xs) cc)))

; cc is the contract of the configuration with program cp and contract indices cci (Gonthier's cfcontract).
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
    ((SR k) (let ((many xs) (erased p)) (ctrenum-c rest na1)) (values xs (CeR k rest xs p)))
    ((SY)
      (let-match many rest (Cons _ s1 rest1) ((Nil _) (values (Nil _) (CeY1))))
      (let ((many xs) (erased p)) (ctrenum-c rest na1))
      (let ((many d) (many e) (many f) (many r) (erased c)) (cpmap-c rest na1))
      (let ((erased _) (erased _) (erased q)) (pointed-cons rest d e f r c))
      (let-match erased q (Refl _ _))
      (let-match many r (Cons _ a p1))
      (values (Cons _ a xs) (CeY s1 rest1 d a e f p1 xs c p)))
    ((SH)
      (let ((many xs) (erased p)) (ctrenum-c rest na1))
      (let ((many d) (many e) (many f) (many r) (erased c)) (cpmap-c rest na1))
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
  (let ((many cc) (erased p)) (pick-c cci (Succ i) rest))
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
  (match many (nth-d rest i1) _
    ((NthYes _ _ x p) (NthYes xs i x (NthThere _ y rest i1 x p)))
    ((NthNo _ _) (NthNo xs i))))

(def-adts $ (InsertED : ((List (Nat)) e cc) -> Type)
  enum
  (many IEYes : (erased (List (Nat)) e cc) (many (List (Nat)) ie) (erased (InsertE e cc ie) p) -> (InsertED e cc))
  (many IENo : (erased (List (Nat)) e cc) -> (InsertED e cc)))

(def-fns _ $ (many inserte-c : (many (List (Nat)) e) (subterm many (List (Nat)) cc) -> (many (InsertED e cc) r))
  (let-match many cc (Cons _ y rest) ((Nil _) (IEYes e cc (Nil _) (IENil e))))
  (let-match many (nth-d e y) (NthYes _ _ z pz) ((NthNo _ _) (IENo e cc)))
  (let-match many (inserte-c e rest) (IEYes _ _ ie p) ((IENo _ _) (IENo e cc)))
  (IEYes e cc (Cons _ y (Cons _ z ie)) (IECons e rest ie y z pz p)))

(def-fns _ $ (erased lrel-d : (erased (List (Nat)) ie) (erased (List (Step)) cp) (erased (Nat) d d2) (erased (List (Nat)) e f r) (erased (List (List (Col))) ls)
    (subterm erased (Cpmap cp d e f r) c) (erased (LRel ie cp d2 ls) lr) -> (erased (Eq (Nat) d d2) q))
  (match erased c _
    ((CmNil) (let-match erased lr (LrNil _ _ _)) (Refl _ d))
    ((CmR _ _ cp1 _ _ r1 _ c1 _) (let-match erased lr (LrR _ _ _ _ ls1 _ lr1 _)) (lrel-d ie cp1 d d2 e f r1 ls1 c1 lr1))
    (absurd (CmRr _ _ _ _ _ _ _ _ _ _) lr)
    (absurd (CmU _ _ _ _ _ _ _ _ _ _) lr)
    (absurd (CmK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) lr)
    ((CmY d0 cp1 e0 f0 r0 _ _ _ _ _ _ c1 _ _)
      (let-match erased lr (LrY _ d3 _ ls1 _ lr1 _))
      (let-match erased (lrel-d ie cp1 d0 d3 e0 f0 r0 ls1 c1 lr1) (Refl _ _))
      (Refl _ d))
    ((CmH d0 cp1 e0 f0 r0 _ _ _ _ _ _ _ _ _ c1 _ _ _)
      (let-match erased lr (LrH _ d3 _ ls1 _ lr1 _))
      (let-match erased (lrel-d ie cp1 d0 d3 e0 f0 r0 ls1 c1 lr1) (Refl _ _))
      (Refl _ d))))
