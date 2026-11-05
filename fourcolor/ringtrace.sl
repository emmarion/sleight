; R relates the entries of xs and ys at each position.
(def-adts $ (All2 : (Type A) (Type B) ((TyCtor (A a) (B b) -> Type) R) ((List A) xs) ((List B) ys) -> Type)
  enum
  (many All2Nil : (erased Type A B) (erased (TyCtor (A a) (B b) -> Type) R) -> (All2 A B R (Nil A) (Nil B)))
  (many All2Cons : (erased Type A B) (erased (TyCtor (A a) (B b) -> Type) R) (erased A x) (erased B y) (erased (List A) xs) (erased (List B) ys)
      (erased (R x y) p) (erased (All2 A B R xs ys) rest) -> (All2 A B R (Cons A x xs) (Cons B y ys))))

(def-fns _ $ (erased all2-length : (erased Type A B) (erased (TyCtor (A a) (B b) -> Type) R) (erased (List A) xs) (erased (List B) ys) (erased (Nat) n)
    (subterm erased (All2 A B R xs ys) al) (erased (Length A xs n) l) -> (erased (Length B ys n) r))
  (let-match erased al (All2Cons _ _ _ _ y xs1 ys1 _ al1) ((All2Nil _ _ _) (let-match erased l (LengthNil _)) (LengthNil B)))
  (let-match erased l (LengthCons _ _ _ n1 l1))
  (LengthCons B y ys1 n1 (all2-length A B R xs1 ys1 n1 al1 l1)))

(def-fns _ $ (erased natof-exists : (erased (Col) c) -> (erased (Nat) k) (erased (NCol k c) p))
  (match erased c _
    ((C0) (values (Zero) (NC0)))
    ((C1) (values (Succ (Zero)) (NC1)))
    ((C2) (values (Succ (Succ (Zero))) (NC2)))
    ((C3) (values (Succ (Succ (Succ (Zero)))) (NC3)))))

(def-fns _ $ (erased colof-lt : (erased (Nat) k) (erased (Col) c) (erased (NCol k c) p) -> (erased (Lt k 4) l))
  (let-match erased (unary-4) (Refl _ _))
  (match erased p _
    ((NC0) (LtZ _))
    ((NC1) (LtS _ _ (LtZ _)))
    ((NC2) (LtS _ _ (LtS _ _ (LtZ _))))
    ((NC3) (LtS _ _ (LtS _ _ (LtS _ _ (LtZ _)))))))

(def-fns _ $ (erased colof-apart : (erased (Nat) k k2) (erased (Col) c) (erased (Apart (Nat) Lt k k2) ne) (erased (NCol k c) p) (erased (NCol k2 c) q)
    -> (erased (False) r))
  (let-match erased (ncol-inj k k2 c p q) (Refl _ _))
  (apart-irrefl k ne))

(def-fns _ $ (erased cols-exists : (erased (List (Nat)) ks) (subterm erased (Under ks 4) u) -> (erased (List (Col)) cs) (erased (All2 (Nat) (Col) NCol ks cs) r))
  (let-match erased u (UnderCons k _ ks1 l u1) ((UnderNil _) (values (Nil _) (All2Nil _ _ NCol))))
  (let ((erased c) (erased p)) (ncol-ex k l))
  (let ((erased cs1) (erased r1)) (cols-exists ks1 u1))
  (values (Cons _ c cs1) (All2Cons _ _ NCol k c ks1 cs1 p r1)))

(def-fns _ $ (erased cols-fn : (erased (List (Nat)) ks) (erased (List (Col)) cs cs2) (subterm erased (All2 (Nat) (Col) NCol ks cs) p)
    (erased (All2 (Nat) (Col) NCol ks cs2) q) -> (erased (Eq (List (Col)) cs cs2) e))
  (let-match erased p (All2Cons _ _ _ k c ks1 cs1 p1 r1) ((All2Nil _ _ _) (let-match erased q (All2Nil _ _ _)) (Refl _ cs)))
  (let-match erased q (All2Cons _ _ _ _ c2 _ cs3 q1 r2))
  (let-match erased (ncol-fn k c c2 p1 q1) (Refl _ _))
  (let-match erased (cols-fn ks1 cs1 cs3 r1 r2) (Refl _ _))
  (Refl _ cs))

; et lists the sums of consecutive colours of c :: lc, the last with c0.
(def-adts $ (TraceFrom : ((Col) c0 c) ((List (Col)) lc et) -> Type)
  enum
  (many TFEnd : (erased (Col) c0 c s) (erased (AddK c c0 s) a) -> (TraceFrom c0 c (Nil (Col)) (Cons (Col) s (Nil (Col)))))
  (many TFCons : (erased (Col) c0 c c2 s) (erased (List (Col)) lc et) (erased (AddK c c2 s) a) (erased (TraceFrom c0 c2 lc et) t)
      -> (TraceFrom c0 c (Cons (Col) c2 lc) (Cons (Col) s et))))

(def-adts $ (Trace : ((List (Col)) lc et) -> Type)
  enum
  (many TrNil : -> (Trace (Nil (Col)) (Nil (Col))))
  (many TrCons : (erased (Col) c) (erased (List (Col)) lc et) (erased (TraceFrom c c lc et) t) -> (Trace (Cons (Col) c lc) et)))

(def-fns _ $ (erased tracefrom-exists : (erased (Col) c0 c) (subterm erased (List (Col)) lc) -> (erased (List (Col)) et) (erased (TraceFrom c0 c lc et) t))
  (let-match erased lc (Cons _ c2 lc1) ((Nil _) (let ((erased s) (erased a)) (addc-total c c0)) (values (Cons _ s (Nil _)) (TFEnd c0 c s a))))
  (let ((erased s) (erased a)) (addc-total c c2))
  (let ((erased et) (erased t)) (tracefrom-exists c0 c2 lc1))
  (values (Cons _ s et) (TFCons c0 c c2 s lc1 et a t)))

(def-fns _ $ (erased trace-exists : (erased (List (Col)) lc) -> (erased (List (Col)) et) (erased (Trace lc et) t))
  (let-match erased lc (Cons _ c lc1) ((Nil _) (values (Nil _) (TrNil))))
  (let ((erased et) (erased t)) (tracefrom-exists c c lc1))
  (values et (TrCons c lc1 et t)))

(def-fns _ $ (erased tracefrom-fn : (erased (Col) c0 c) (erased (List (Col)) lc et et2) (subterm erased (TraceFrom c0 c lc et) p)
    (erased (TraceFrom c0 c lc et2) q) -> (erased (Eq (List (Col)) et et2) e))
  (match erased p _
    ((TFEnd _ _ s a) (let-match erased q (TFEnd _ _ s2 a2)) (let-match erased (addc-fn c c0 s s2 a a2) (Refl _ _)) (Refl _ et))
    ((TFCons _ _ c2 s lc1 et1 a p1)
      (let-match erased q (TFCons _ _ _ s2 _ et3 a2 q1))
      (let-match erased (addc-fn c c2 s s2 a a2) (Refl _ _))
      (let-match erased (tracefrom-fn c0 c2 lc1 et1 et3 p1 q1) (Refl _ _))
      (Refl _ et))))

(def-fns _ $ (erased trace-fn : (erased (List (Col)) lc et et2) (erased (Trace lc et) p) (erased (Trace lc et2) q) -> (erased (Eq (List (Col)) et et2) e))
  (match erased p _
    ((TrNil) (let-match erased q (TrNil)) (Refl _ et))
    ((TrCons c lc1 _ t) (let-match erased q (TrCons _ _ _ t2)) (tracefrom-fn c c lc1 et et2 t t2))))

(def-fns _ $ (erased tracefrom-perm : (erased (Perm) g) (erased (IsPerm g) ip) (erased (Col) c0 c d0 d) (erased (List (Col)) lc lc2 et et2)
    (erased (PermC g c0 d0) p0) (erased (PermC g c d) pc) (subterm erased (PermT g lc lc2) pt) (erased (TraceFrom c0 c lc et) t)
    (erased (TraceFrom d0 d lc2 et2) t2) -> (erased (PermT g et et2) r))
  (match erased pt _
    ((PTNil _)
      (let-match erased t (TFEnd _ _ s a))
      (let-match erased t2 (TFEnd _ _ s2 a2))
      (PTCons g s s2 _ _ (perm-add g c c0 s d d0 s2 ip pc p0 a a2) (PTNil g)))
    ((PTCons _ c2 d2 lc1 lc3 pc2 pt1)
      (let-match erased t (TFCons _ _ _ s _ et1 a t1))
      (let-match erased t2 (TFCons _ _ _ s2 _ et3 a2 t3))
      (PTCons g s s2 et1 et3 (perm-add g c c2 s d d2 s2 ip pc pc2 a a2) (tracefrom-perm g ip c0 c2 d0 d2 lc1 lc3 et1 et3 p0 pc2 pt1 t1 t3)))))

(def-fns _ $ (erased trace-perm : (erased (Perm) g) (erased (IsPerm g) ip) (erased (List (Col)) lc lc2 et et2) (erased (PermT g lc lc2) pt)
    (erased (Trace lc et) t) (erased (Trace lc2 et2) t2) -> (erased (PermT g et et2) r))
  (match erased pt _
    ((PTNil _) (let-match erased t (TrNil)) (let-match erased t2 (TrNil)) (PTNil g))
    ((PTCons _ c d lc1 lc3 pc pt1)
      (let-match erased t (TrCons _ _ _ t1))
      (let-match erased t2 (TrCons _ _ _ t3))
      (tracefrom-perm g ip c c d d lc1 lc3 et et2 pc pc pt1 t1 t3))))

(def-fns _ $ (erased permn-exists : (erased (Perm) g) (erased (Nat) k) (erased (Lt k 4) l) -> (erased (Nat) k2) (erased (NPerm g k k2) r))
  (let ((erased c) (erased p)) (ncol-ex k l))
  (let ((erased c2) (erased q)) (permc-total g c))
  (let ((erased k2) (erased r)) (natof-exists c2))
  (values k2 (MkNPerm g k k2 c c2 p q r)))

(def-fns _ $ (erased permns-exists : (erased (Perm) g) (erased (List (Nat)) ks) (subterm erased (Under ks 4) u)
    -> (erased (List (Nat)) ks2) (erased (NPermL g ks ks2) r))
  (let-match erased u (UnderCons k _ ks1 l u1) ((UnderNil _) (values (Nil _) (NPLNil g))))
  (let ((erased k2) (erased p)) (permn-exists g k l))
  (let ((erased ks3) (erased r1)) (permns-exists g ks1 u1))
  (values (Cons _ k2 ks3) (NPLCons g k k2 ks1 ks3 p r1)))

(def-fns _ $ (erased coloring-perm : (erased (Perm) g) (erased (IsPerm g) ip) (erased (List (Nat)) e f ks) (erased (FourColoring e f ks) c)
    -> (erased (List (Nat)) ks2) (erased (FourColoring e f ks2) c2) (erased (NPermL g ks ks2) a))
  (let-match erased c (MkFourColoring _ _ _ ke rf re df u))
  (let ((erased ks2) (erased a)) (permns-exists g ks u))
  (let ((erased kf) (erased rf2) (erased af)) (respects-perm g ks ks2 f ks rf a))
  (let-match erased (npl-fn g ks ks2 kf a af) (Refl _ _))
  (let ((erased ke2) (erased re2) (erased ae)) (respects-perm g ks ks2 e ke re a))
  (values ks2 (MkFourColoring e f ks2 ke2 rf2 re2 (differ-perm g ke ks ke2 ks2 ip df ae a) (under-perm g ks ks2 a)) a))

(def-fns _ $ (erased permns-cols : (erased (Perm) g) (erased (List (Nat)) ks ks2) (erased (List (Col)) cs cs2)
    (subterm erased (NPermL g ks ks2) p) (erased (All2 (Nat) (Col) NCol ks cs) q) (erased (All2 (Nat) (Col) NCol ks2 cs2) q2)
    -> (erased (PermT g cs cs2) r))
  (let-match erased p (NPLCons _ k k2 ks1 ks3 p1 r1)
    ((NPLNil _) (let-match erased q (All2Nil _ _ _)) (let-match erased q2 (All2Nil _ _ _)) (PTNil g)))
  (let-match erased q (All2Cons _ _ _ _ c _ cs1 o1 q1))
  (let-match erased q2 (All2Cons _ _ _ _ c2 _ cs3 o2 q3))
  (let-match erased p1 (MkNPerm _ _ _ d d2 o3 pc o4))
  (let-match erased (ncol-fn k c d o1 o3) (Refl _ _))
  (let-match erased (ncol-fn k2 c2 d2 o2 o4) (Refl _ _))
  (PTCons g c c2 cs1 cs3 pc (permns-cols g ks1 ks3 cs1 cs3 r1 q1 q3)))

; et is the trace of the colours of the darts r under a four-colouring.
(def-adts $ (RingTrace : ((List (Nat)) e f r) ((List (Col)) et) -> Type)
  enum
  (many MkRingTrace : (erased (List (Nat)) e f r ks lc) (erased (List (Col)) cs et) (erased (FourColoring e f ks) c) (erased (Respects ks r lc) rl)
      (erased (All2 (Nat) (Col) NCol lc cs) co) (erased (Trace cs et) t) -> (RingTrace e f r et)))

(def-fns _ $ (erased ring-trace-perm : (erased (List (Nat)) e f r) (erased (List (Col)) et et2) (erased (Perm) g) (erased (IsPerm g) ip)
    (erased (PermT g et et2) pt) (erased (RingTrace e f r et) rt) -> (erased (RingTrace e f r et2) r2))
  (let-match erased rt (MkRingTrace _ _ _ ks lc cs _ c rl co t))
  (let ((erased ks2) (erased c2) (erased a)) (coloring-perm g ip e f ks c))
  (let ((erased lc2) (erased rl2) (erased al)) (respects-perm g ks ks2 r lc rl a))
  (let-match erased c2 (MkFourColoring _ _ _ _ _ _ _ u2))
  (let ((erased cs2) (erased co2)) (cols-exists lc2 (respects-under-out ks2 r lc2 4 rl2 u2)))
  (let ((erased et3) (erased t2)) (trace-exists cs2))
  (let ((erased pt2)) (trace-perm g ip cs cs2 et et3 (permns-cols g lc lc2 cs cs2 al co co2) t t2))
  (let-match erased (permt-fn g et et2 et3 pt pt2) (Refl _ _))
  (MkRingTrace e f r ks2 lc2 cs2 et2 c2 rl2 co2 t2))

; ks gives the two ends of each bond x-y of g the same colour when x is in ins, and different colours otherwise.
(def-adts $ (EdgeCC : ((List (Nat)) ins ks) ((List (Bond)) g) -> Type)
  enum
  (many ECNil : (erased (List (Nat)) ins ks) -> (EdgeCC ins ks (Nil (Bond))))
  (many ECIn : (erased (List (Nat)) ins ks) (erased (List (Bond)) g) (erased (Nat) x y l) (erased (In x ins) px) (erased (Nth (Nat) ks x l) p1)
      (erased (Nth (Nat) ks y l) p2) (erased (EdgeCC ins ks g) rest) -> (EdgeCC ins ks (Cons (Bond) (MkBond x y) g)))
  (many ECOut : (erased (List (Nat)) ins ks) (erased (List (Bond)) g) (erased (Nat) x y l1 l2) (erased (NotIn x ins) px) (erased (Nth (Nat) ks x l1) p1)
      (erased (Nth (Nat) ks y l2) p2) (erased (Apart (Nat) Lt l1 l2) ne) (erased (EdgeCC ins ks g) rest) -> (EdgeCC ins ks (Cons (Bond) (MkBond x y) g))))

; ks is constant on faces and on the edges of ins, and proper on the other edges.
(def-adts $ (CCColoring : ((Nat) d) ((List (Nat)) e f cc ks) -> Type)
  enum
  (many MkCCColoring : (erased (Nat) d) (erased (List (Nat)) e f cc ks ins) (erased (List (Bond)) ge) (erased (InsertE e cc ins) ie)
      (erased (Graph d e ge) gr) (erased (Respects ks f ks) rf) (erased (EdgeCC ins ks ge) ec) (erased (Under ks 4) u) (erased (Length (Nat) ks d) lk)
      -> (CCColoring d e f cc ks)))
