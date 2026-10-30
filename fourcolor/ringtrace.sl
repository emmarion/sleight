; Ring traces of four-colourings, after coloring.v and the traces of color.v: the colours below 4 of FourColoring read as
; the colours of red/red.sl, and the trace of the colours of the darts of a ring.

; R relates the entries of xs and ys at each position.
(def-adts $ (All2 : (Type A) (Type B) ((TyCtor (A a) (B b) -> Type) R) ((List A) xs) ((List B) ys) -> Type)
  enum
  (many All2Nil : (erased Type A B) (erased (TyCtor (A a) (B b) -> Type) R) -> (All2 A B R (Nil A) (Nil B)))
  (many All2Cons : (erased Type A B) (erased (TyCtor (A a) (B b) -> Type) R) (erased A x) (erased B y) (erased (List A) xs) (erased (List B) ys)
      (erased (R x y) p) (erased (All2 A B R xs ys) rest) -> (All2 A B R (Cons A x xs) (Cons B y ys))))

(def-fns _ $ (erased all2-nth : (erased Type A B) (erased (TyCtor (A a) (B b) -> Type) R) (erased (List A) xs) (erased (List B) ys) (erased (Nat) i)
    (erased A x) (subterm erased (Nth A xs i x) p) (erased (All2 A B R xs ys) al) -> (erased B y) (erased (Nth B ys i y) q) (erased (R x y) r))
  (let-match erased al (All2Cons _ _ _ x1 y1 xs1 ys1 r1 al1) (absurd (All2Nil _ _ _) p))
  (let-match erased p (NthThere _ _ _ i1 _ p1) ((NthHere _ _ _) (values y1 (NthHere B y1 ys1) r1)))
  (let ((erased y) (erased q) (erased r)) (all2-nth A B R xs1 ys1 i1 x p1 al1))
  (values y (NthThere B y1 ys1 i1 y q) r))

(def-fns _ $ (erased all2-length : (erased Type A B) (erased (TyCtor (A a) (B b) -> Type) R) (erased (List A) xs) (erased (List B) ys) (erased (Nat) n)
    (subterm erased (All2 A B R xs ys) al) (erased (Length A xs n) l) -> (erased (Length B ys n) r))
  (let-match erased al (All2Cons _ _ _ x y xs1 ys1 _ al1) ((All2Nil _ _ _) (let-match erased l (LengthNil _)) (LengthNil B)))
  (let-match erased l (LengthCons _ _ _ n1 l1))
  (LengthCons B y ys1 n1 (all2-length A B R xs1 ys1 n1 al1 l1)))

; k is the colour of red/red.sl that the number k below 4 names.
(def-adts $ (ColOf : ((Nat) k) ((Col) c) -> Type)
  enum
  (many CO0 : -> (ColOf (Zero) (C0)))
  (many CO1 : -> (ColOf (Succ (Zero)) (C1)))
  (many CO2 : -> (ColOf (Succ (Succ (Zero))) (C2)))
  (many CO3 : -> (ColOf (Succ (Succ (Succ (Zero)))) (C3))))

(def-fns _ $ (erased colof-exists : (erased (Nat) k) (erased (Lt k 4) l) -> (erased (Col) c) (erased (ColOf k c) p))
  (unary 4)
  (let-match erased l (LtS _ _ l1) ((LtZ _) (values (C0) (CO0))))
  (let-match erased l1 (LtS _ _ l2) ((LtZ _) (values (C1) (CO1))))
  (let-match erased l2 (LtS _ _ l3) ((LtZ _) (values (C2) (CO2))))
  (let-match erased l3 (LtZ _) (absurd (LtS _ _ l4) l4))
  (values (C3) (CO3)))

(def-fns _ $ (erased natof-exists : (erased (Col) c) -> (erased (Nat) k) (erased (ColOf k c) p))
  (match erased c _
    ((C0) (values (Zero) (CO0)))
    ((C1) (values (Succ (Zero)) (CO1)))
    ((C2) (values (Succ (Succ (Zero))) (CO2)))
    ((C3) (values (Succ (Succ (Succ (Zero)))) (CO3)))))

(def-fns _ $ (erased colof-lt : (erased (Nat) k) (erased (Col) c) (erased (ColOf k c) p) -> (erased (Lt k 4) l))
  (unary 4)
  (match erased p _
    ((CO0) (LtZ _))
    ((CO1) (LtS _ _ (LtZ _)))
    ((CO2) (LtS _ _ (LtS _ _ (LtZ _))))
    ((CO3) (LtS _ _ (LtS _ _ (LtS _ _ (LtZ _)))))))

(def-fns _ $ (erased colof-fn : (erased (Nat) k) (erased (Col) c c2) (erased (ColOf k c) p) (erased (ColOf k c2) q) -> (erased (Eq (Col) c c2) e))
  (match erased p _
    ((CO0) (let-match erased q (CO0)) (Refl _ c))
    ((CO1) (let-match erased q (CO1)) (Refl _ c))
    ((CO2) (let-match erased q (CO2)) (Refl _ c))
    ((CO3) (let-match erased q (CO3)) (Refl _ c))))

(def-fns _ $ (erased colof-inj : (erased (Nat) k k2) (erased (Col) c) (erased (ColOf k c) p) (erased (ColOf k2 c) q) -> (erased (Eq (Nat) k k2) e))
  (match erased p _
    ((CO0) (let-match erased q (CO0)) (Refl _ k))
    ((CO1) (let-match erased q (CO1)) (Refl _ k))
    ((CO2) (let-match erased q (CO2)) (Refl _ k))
    ((CO3) (let-match erased q (CO3)) (Refl _ k))))

(def-fns _ $ (erased colof-apart : (erased (Nat) k k2) (erased (Col) c) (erased (Apart (Nat) Lt k k2) ne) (erased (ColOf k c) p) (erased (ColOf k2 c) q)
    -> (erased (False) r))
  (let-match erased (colof-inj k k2 c p q) (Refl _ _))
  (apart-irrefl k ne))

(def-fns _ $ (erased cols-exists : (erased (List (Nat)) ks) (subterm erased (Under ks 4) u) -> (erased (List (Col)) cs) (erased (All2 (Nat) (Col) ColOf ks cs) r))
  (let-match erased u (UnderCons ks1 k _ l u1) ((UnderNil _) (values (Nil _) (All2Nil _ _ ColOf))))
  (let ((erased c) (erased p)) (colof-exists k l))
  (let ((erased cs1) (erased r1)) (cols-exists ks1 u1))
  (values (Cons _ c cs1) (All2Cons _ _ ColOf k c ks1 cs1 p r1)))

(def-fns _ $ (erased cols-fn : (erased (List (Nat)) ks) (erased (List (Col)) cs cs2) (subterm erased (All2 (Nat) (Col) ColOf ks cs) p)
    (erased (All2 (Nat) (Col) ColOf ks cs2) q) -> (erased (Eq (List (Col)) cs cs2) e))
  (let-match erased p (All2Cons _ _ _ k c ks1 cs1 p1 r1) ((All2Nil _ _ _) (let-match erased q (All2Nil _ _ _)) (Refl _ cs)))
  (let-match erased q (All2Cons _ _ _ _ c2 _ cs3 q1 r2))
  (let-match erased (colof-fn k c c2 p1 q1) (Refl _ _))
  (let-match erased (cols-fn ks1 cs1 cs3 r1 r2) (Refl _ _))
  (Refl _ cs))

; et lists the sums of consecutive colours of c :: lc, the last with c0: Gonthier's trace (c0 :: lc) is TraceFrom c0 c0 lc.
(def-adts $ (TraceFrom : ((Col) c0 c) ((List (Col)) lc et) -> Type)
  enum
  (many TFEnd : (erased (Col) c0 c s) (erased (AddK c c0 s) a) -> (TraceFrom c0 c (Nil (Col)) (Cons (Col) s (Nil (Col)))))
  (many TFCons : (erased (Col) c0 c c2 s) (erased (List (Col)) lc et) (erased (AddK c c2 s) a) (erased (TraceFrom c0 c2 lc et) t)
      -> (TraceFrom c0 c (Cons (Col) c2 lc) (Cons (Col) s et))))

; Gonthier's trace.
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

; trace_permt: permuting the colours permutes the trace.
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

(def-fns _ $ (erased permc-inj : (erased (Perm) g) (erased (IsPerm g) ip) (erased (Col) c c2 d) (erased (PermC g c d) p) (erased (PermC g c2 d) q)
    -> (erased (Eq (Col) c c2) e))
  (match erased ip _
    ((IP123) (match erased p _ ((PC0 _) (let-match erased q (PC0 _)) (Refl _ c)) ((PC1 _ _ _) (let-match erased q (PC1 _ _ _)) (Refl _ c))
      ((PC2 _ _ _) (let-match erased q (PC2 _ _ _)) (Refl _ c)) ((PC3 _ _ _) (let-match erased q (PC3 _ _ _)) (Refl _ c))))
    ((IP132) (match erased p _ ((PC0 _) (let-match erased q (PC0 _)) (Refl _ c)) ((PC1 _ _ _) (let-match erased q (PC1 _ _ _)) (Refl _ c))
      ((PC2 _ _ _) (let-match erased q (PC2 _ _ _)) (Refl _ c)) ((PC3 _ _ _) (let-match erased q (PC3 _ _ _)) (Refl _ c))))
    ((IP213) (match erased p _ ((PC0 _) (let-match erased q (PC0 _)) (Refl _ c)) ((PC1 _ _ _) (let-match erased q (PC1 _ _ _)) (Refl _ c))
      ((PC2 _ _ _) (let-match erased q (PC2 _ _ _)) (Refl _ c)) ((PC3 _ _ _) (let-match erased q (PC3 _ _ _)) (Refl _ c))))
    ((IP231) (match erased p _ ((PC0 _) (let-match erased q (PC0 _)) (Refl _ c)) ((PC1 _ _ _) (let-match erased q (PC1 _ _ _)) (Refl _ c))
      ((PC2 _ _ _) (let-match erased q (PC2 _ _ _)) (Refl _ c)) ((PC3 _ _ _) (let-match erased q (PC3 _ _ _)) (Refl _ c))))
    ((IP312) (match erased p _ ((PC0 _) (let-match erased q (PC0 _)) (Refl _ c)) ((PC1 _ _ _) (let-match erased q (PC1 _ _ _)) (Refl _ c))
      ((PC2 _ _ _) (let-match erased q (PC2 _ _ _)) (Refl _ c)) ((PC3 _ _ _) (let-match erased q (PC3 _ _ _)) (Refl _ c))))
    ((IP321) (match erased p _ ((PC0 _) (let-match erased q (PC0 _)) (Refl _ c)) ((PC1 _ _ _) (let-match erased q (PC1 _ _ _)) (Refl _ c))
      ((PC2 _ _ _) (let-match erased q (PC2 _ _ _)) (Refl _ c)) ((PC3 _ _ _) (let-match erased q (PC3 _ _ _)) (Refl _ c))))))

; The colour permutation g on the colours below 4.
(def-adts $ (PermN : ((Perm) g) ((Nat) k k2) -> Type)
  enum
  (many MkPermN : (erased (Perm) g) (erased (Nat) k k2) (erased (Col) c c2) (erased (ColOf k c) p) (erased (PermC g c c2) q)
      (erased (ColOf k2 c2) r) -> (PermN g k k2)))

(def-adts $ (PermNs : ((Perm) g) ((List (Nat)) ks ks2) -> Type)
  enum
  (many PNNil : (erased (Perm) g) -> (PermNs g (Nil (Nat)) (Nil (Nat))))
  (many PNCons : (erased (Perm) g) (erased (Nat) k k2) (erased (List (Nat)) ks ks2) (erased (PermN g k k2) p) (erased (PermNs g ks ks2) rest)
      -> (PermNs g (Cons (Nat) k ks) (Cons (Nat) k2 ks2))))

(def-fns _ $ (erased permns-nth : (erased (Perm) g) (erased (List (Nat)) xs ys) (erased (Nat) i x) (subterm erased (Nth (Nat) xs i x) p)
    (erased (PermNs g xs ys) al) -> (erased (Nat) y) (erased (Nth (Nat) ys i y) q) (erased (PermN g x y) r))
  (let-match erased al (PNCons _ x1 y1 xs1 ys1 r1 al1) (absurd (PNNil _) p))
  (let-match erased p (NthThere _ _ _ i1 _ p1) ((NthHere _ _ _) (values y1 (NthHere _ y1 ys1) r1)))
  (let ((erased y) (erased q) (erased r)) (permns-nth g xs1 ys1 i1 x p1 al1))
  (values y (NthThere _ y1 ys1 i1 y q) r))

(def-fns _ $ (erased permn-exists : (erased (Perm) g) (erased (Nat) k) (erased (Lt k 4) l) -> (erased (Nat) k2) (erased (PermN g k k2) r))
  (let ((erased c) (erased p)) (colof-exists k l))
  (let ((erased c2) (erased q)) (permc-total g c))
  (let ((erased k2) (erased r)) (natof-exists c2))
  (values k2 (MkPermN g k k2 c c2 p q r)))

(def-fns _ $ (erased permn-fn : (erased (Perm) g) (erased (Nat) k a b) (erased (PermN g k a) p) (erased (PermN g k b) q) -> (erased (Eq (Nat) a b) e))
  (let-match erased p (MkPermN _ _ _ c c2 p1 q1 r1))
  (let-match erased q (MkPermN _ _ _ c3 c4 p2 q2 r2))
  (let-match erased (colof-fn k c c3 p1 p2) (Refl _ _))
  (let-match erased (permc-fn g c c2 c4 q1 q2) (Refl _ _))
  (colof-inj a b c2 r1 r2))

(def-fns _ $ (erased permn-apart : (erased (Perm) g) (erased (IsPerm g) ip) (erased (Nat) a b a2 b2) (erased (Apart (Nat) Lt a b) ne)
    (erased (PermN g a a2) p) (erased (PermN g b b2) q) -> (erased (Apart (Nat) Lt a2 b2) r))
  (let-match erased (nat-eq a2 b2) (Unequal _ _ _ _ r)
    (absurd (Equal _ _ _)
      (let-match erased p (MkPermN _ _ _ c c2 p1 q1 r1))
      (let-match erased q (MkPermN _ _ _ c3 c4 p2 q2 r2))
      (let-match erased (colof-fn a2 c2 c4 r1 r2) (Refl _ _))
      (let-match erased (permc-inj g ip c c3 c2 q1 q2) (Refl _ _))
      (colof-apart a b c ne p1 p2)))
  r)

(def-fns _ $ (erased permn-lt : (erased (Perm) g) (erased (Nat) k k2) (erased (PermN g k k2) p) -> (erased (Lt k2 4) l))
  (let-match erased p (MkPermN _ _ _ c c2 _ _ r))
  (colof-lt k2 c2 r))

(def-fns _ $ (erased permns-exists : (erased (Perm) g) (erased (List (Nat)) ks) (subterm erased (Under ks 4) u)
    -> (erased (List (Nat)) ks2) (erased (PermNs g ks ks2) r))
  (let-match erased u (UnderCons ks1 k _ l u1) ((UnderNil _) (values (Nil _) (PNNil g))))
  (let ((erased k2) (erased p)) (permn-exists g k l))
  (let ((erased ks3) (erased r1)) (permns-exists g ks1 u1))
  (values (Cons _ k2 ks3) (PNCons g k k2 ks1 ks3 p r1)))

(def-fns _ $ (erased permns-fn : (erased (Perm) g) (erased (List (Nat)) ks a b) (subterm erased (PermNs g ks a) p)
    (erased (PermNs g ks b) q) -> (erased (Eq (List (Nat)) a b) e))
  (let-match erased p (PNCons _ k x ks1 a1 p1 r1) ((PNNil _) (let-match erased q (PNNil _)) (Refl _ a)))
  (let-match erased q (PNCons _ _ y _ b1 q1 r2))
  (let-match erased (permn-fn g k x y p1 q1) (Refl _ _))
  (let-match erased (permns-fn g ks1 a1 b1 r1 r2) (Refl _ _))
  (Refl _ a))

(def-fns _ $ (erased permns-under : (erased (Perm) g) (erased (List (Nat)) ks ks2) (subterm erased (PermNs g ks ks2) p)
    -> (erased (Under ks2 4) u))
  (let-match erased p (PNCons _ k k2 ks1 ks3 p1 r1) ((PNNil _) (UnderNil 4)))
  (UnderCons ks3 k2 4 (permn-lt g k k2 p1) (permns-under g ks1 ks3 r1)))

(def-fns _ $ (erased permns-differ : (erased (Perm) g) (erased (IsPerm g) ip) (erased (List (Nat)) xs ys xs2 ys2) (subterm erased (Differ xs ys) df)
    (erased (PermNs g xs xs2) px) (erased (PermNs g ys ys2) py) -> (erased (Differ xs2 ys2) r))
  (let-match erased df (DifferCons xs1 ys1 x y ne df1) ((DifferNil) (let-match erased px (PNNil _)) (let-match erased py (PNNil _)) (DifferNil)))
  (let-match erased px (PNCons _ _ x2 _ xs3 p1 px1))
  (let-match erased py (PNCons _ _ y2 _ ys3 q1 py1))
  (DifferCons xs3 ys3 x2 y2 (permn-apart g ip x y x2 y2 ne p1 q1) (permns-differ g ip xs1 ys1 xs3 ys3 df1 px1 py1)))

(def-fns _ $ (erased respects-permn : (erased (Perm) g) (erased (List (Nat)) lab lab2 xs ls) (subterm erased (Respects lab xs ls) rp)
    (erased (PermNs g lab lab2) al) -> (erased (List (Nat)) ls2) (erased (Respects lab2 xs ls2) r) (erased (PermNs g ls ls2) a))
  (let-match erased rp (RespCons _ xs1 ls1 j l p rp1) ((RespNil _) (values (Nil _) (RespNil lab2) (PNNil g))))
  (let ((erased l2) (erased q) (erased pl)) (permns-nth g lab lab2 j l p al))
  (let ((erased ls3) (erased r1) (erased a1)) (respects-permn g lab lab2 xs1 ls1 rp1 al))
  (values (Cons _ l2 ls3) (RespCons lab2 xs1 ls3 j l2 q r1) (PNCons g l l2 ls1 ls3 pl a1)))

; coloring_inj for a colour permutation.
(def-fns _ $ (erased coloring-perm : (erased (Perm) g) (erased (IsPerm g) ip) (erased (List (Nat)) e f ks) (erased (FourColoring e f ks) c)
    -> (erased (List (Nat)) ks2) (erased (FourColoring e f ks2) c2) (erased (PermNs g ks ks2) a))
  (let-match erased c (MkFourColoring _ _ _ ke rf re df u))
  (let ((erased ks2) (erased a)) (permns-exists g ks u))
  (let ((erased kf) (erased rf2) (erased af)) (respects-permn g ks ks2 f ks rf a))
  (let-match erased (permns-fn g ks ks2 kf a af) (Refl _ _))
  (let ((erased ke2) (erased re2) (erased ae)) (respects-permn g ks ks2 e ke re a))
  (values ks2 (MkFourColoring e f ks2 ke2 rf2 re2 (permns-differ g ip ke ks ke2 ks2 df ae a) (permns-under g ks ks2 a)) a))

(def-fns _ $ (erased permns-cols : (erased (Perm) g) (erased (List (Nat)) ks ks2) (erased (List (Col)) cs cs2)
    (subterm erased (PermNs g ks ks2) p) (erased (All2 (Nat) (Col) ColOf ks cs) q) (erased (All2 (Nat) (Col) ColOf ks2 cs2) q2)
    -> (erased (PermT g cs cs2) r))
  (let-match erased p (PNCons _ k k2 ks1 ks3 p1 r1)
    ((PNNil _) (let-match erased q (All2Nil _ _ _)) (let-match erased q2 (All2Nil _ _ _)) (PTNil g)))
  (let-match erased q (All2Cons _ _ _ _ c _ cs1 o1 q1))
  (let-match erased q2 (All2Cons _ _ _ _ c2 _ cs3 o2 q3))
  (let-match erased p1 (MkPermN _ _ _ d d2 o3 pc o4))
  (let-match erased (colof-fn k c d o1 o3) (Refl _ _))
  (let-match erased (colof-fn k2 c2 d2 o2 o4) (Refl _ _))
  (PTCons g c c2 cs1 cs3 pc (permns-cols g ks1 ks3 cs1 cs3 r1 q1 q3)))

(def-fns _ $ (erased permt-fn : (erased (Perm) g) (erased (List (Col)) et a b) (subterm erased (PermT g et a) p) (erased (PermT g et b) q)
    -> (erased (Eq (List (Col)) a b) e))
  (let-match erased p (PTCons _ c x et1 a1 p1 r1) ((PTNil _) (let-match erased q (PTNil _)) (Refl _ a)))
  (let-match erased q (PTCons _ _ y _ b1 q1 r2))
  (let-match erased (permc-fn g c x y p1 q1) (Refl _ _))
  (let-match erased (permt-fn g et1 a1 b1 r1 r2) (Refl _ _))
  (Refl _ a))

; ring_trace: et is the trace of the colours of the darts r under a four-colouring.
(def-adts $ (RingTrace : ((List (Nat)) e f r) ((List (Col)) et) -> Type)
  enum
  (many MkRingTrace : (erased (List (Nat)) e f r ks lc) (erased (List (Col)) cs et) (erased (FourColoring e f ks) c) (erased (Respects ks r lc) rl)
      (erased (All2 (Nat) (Col) ColOf lc cs) co) (erased (Trace cs et) t) -> (RingTrace e f r et)))

(def-fns _ $ (erased ring-trace-of : (erased (List (Nat)) e f r ks lc) (erased (FourColoring e f ks) c) (erased (Respects ks r lc) rl)
    -> (erased (List (Col)) et) (erased (RingTrace e f r et) rt))
  (let-match erased c (MkFourColoring _ _ _ _ _ _ _ u))
  (let ((erased cs) (erased co)) (cols-exists lc (respects-under-out ks r lc 4 rl u)))
  (let ((erased et) (erased t)) (trace-exists cs))
  (values et (MkRingTrace e f r ks lc cs et c rl co t)))

; The first half of Kempe_closed (ring_trace r): ring traces are closed under colour permutations.
(def-fns _ $ (erased ring-trace-perm : (erased (List (Nat)) e f r) (erased (List (Col)) et et2) (erased (Perm) g) (erased (IsPerm g) ip)
    (erased (PermT g et et2) pt) (erased (RingTrace e f r et) rt) -> (erased (RingTrace e f r et2) r2))
  (let-match erased rt (MkRingTrace _ _ _ ks lc cs _ c rl co t))
  (let ((erased ks2) (erased c2) (erased a)) (coloring-perm g ip e f ks c))
  (let ((erased lc2) (erased rl2) (erased al)) (respects-permn g ks ks2 r lc rl a))
  (let-match erased c2 (MkFourColoring _ _ _ _ _ _ _ u2))
  (let ((erased cs2) (erased co2)) (cols-exists lc2 (respects-under-out ks2 r lc2 4 rl2 u2)))
  (let ((erased et3) (erased t2)) (trace-exists cs2))
  (let ((erased pt2)) (trace-perm g ip cs cs2 et et3 (permns-cols g lc lc2 cs cs2 al co co2) t t2))
  (let-match erased (permt-fn g et et2 et3 pt pt2) (Refl _ _))
  (MkRingTrace e f r ks2 lc2 cs2 et2 c2 rl2 co2 t2))

; ins lists each dart x of cc followed by e x (Gonthier's insertE cc).
(def-adts $ (InsertE : ((List (Nat)) e cc ins) -> Type)
  enum
  (many IENil : (erased (List (Nat)) e) -> (InsertE e (Nil (Nat)) (Nil (Nat))))
  (many IECons : (erased (List (Nat)) e cc ins) (erased (Nat) x y) (erased (Nth (Nat) e x y) px) (erased (InsertE e cc ins) rest)
      -> (InsertE e (Cons (Nat) x cc) (Cons (Nat) x (Cons (Nat) y ins)))))

; ks gives the two ends of each bond x-y of g the same colour when x is in ins, and different colours otherwise.
(def-adts $ (EdgeCC : ((List (Nat)) ins ks) ((List (Bond)) g) -> Type)
  enum
  (many ECNil : (erased (List (Nat)) ins ks) -> (EdgeCC ins ks (Nil (Bond))))
  (many ECIn : (erased (List (Nat)) ins ks) (erased (List (Bond)) g) (erased (Nat) x y l) (erased (In x ins) px) (erased (Nth (Nat) ks x l) p1)
      (erased (Nth (Nat) ks y l) p2) (erased (EdgeCC ins ks g) rest) -> (EdgeCC ins ks (Cons (Bond) (MkBond x y) g)))
  (many ECOut : (erased (List (Nat)) ins ks) (erased (List (Bond)) g) (erased (Nat) x y l1 l2) (erased (NotIn x ins) px) (erased (Nth (Nat) ks x l1) p1)
      (erased (Nth (Nat) ks y l2) p2) (erased (Apart (Nat) Lt l1 l2) ne) (erased (EdgeCC ins ks g) rest) -> (EdgeCC ins ks (Cons (Bond) (MkBond x y) g))))

; cc_coloring cc ks: a colouring constant on faces and on the edges of insertE cc, and proper on the other edges.
(def-adts $ (CCColoring : ((Nat) d) ((List (Nat)) e f cc ks) -> Type)
  enum
  (many MkCCColoring : (erased (Nat) d) (erased (List (Nat)) e f cc ks ins) (erased (List (Bond)) ge) (erased (InsertE e cc ins) ie)
      (erased (Graph d e ge) gr) (erased (Respects ks f ks) rf) (erased (EdgeCC ins ks ge) ec) (erased (Under ks 4) u) (erased (Length (Nat) ks d) lk)
      -> (CCColoring d e f cc ks)))

; cc_ring_trace cc r et.
(def-adts $ (CCRingTrace : ((Nat) d) ((List (Nat)) e f cc r) ((List (Col)) et) -> Type)
  enum
  (many MkCCRingTrace : (erased (Nat) d) (erased (List (Nat)) e f cc r ks lc) (erased (List (Col)) cs et) (erased (CCColoring d e f cc ks) c)
      (erased (Respects ks r lc) rl) (erased (All2 (Nat) (Col) ColOf lc cs) co) (erased (Trace cs et) t) -> (CCRingTrace d e f cc r et)))

; cc_colorable cc.
(def-adts $ (CCColorable : ((Nat) d) ((List (Nat)) e f cc) -> Type)
  enum
  (many MkCCColorable : (erased (Nat) d) (erased (List (Nat)) e f cc ks) (erased (CCColoring d e f cc ks) c) -> (CCColorable d e f cc)))

; minimal_counter_example: a planar bridgeless plain precubic hypermap with no four-colouring, all of whose smaller such
; hypermaps have one.
(def-adts $ (MinimalCounterExample : ((Nat) d) ((List (Nat)) e n f) -> Type)
  enum
  (many MkMinimalCounterExample : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) g)
      (erased (Bridgeless d e n f) b) (erased (AllOrder d e (Succ (Succ (Zero)))) pl) (erased (Precubic d n) pc) (erased (Level) L1)
      (erased (Fn L1 (erased (List (Nat)) ks) (erased (FourColoring e f ks) c) -> (erased (False) r)) noncol)
      (erased (Level) L2)
      (erased (Fn L2 (erased (Nat) d2) (erased (List (Nat)) e2 n2 f2) (erased (Hypermap d2 e2 n2 f2) h2) (erased (Genus d2 e2 n2 f2 (Zero)) g2)
          (erased (Bridgeless d2 e2 n2 f2) b2) (erased (AllOrder d2 e2 (Succ (Succ (Zero)))) pl2) (erased (Precubic d2 n2) pc2) (erased (Lt d2 d) lt)
          -> (erased (List (Nat)) ks) (erased (FourColoring e2 f2 ks) c)) minimal)
      -> (MinimalCounterExample d e n f)))

(def-fns _ $ (erased proper-cc : (erased (List (Nat)) ks) (erased (List (Bond)) g) (subterm erased (Proper ks g) pr) -> (erased (EdgeCC (Nil (Nat)) ks g) r))
  (let-match erased pr (ProperCons _ g1 x y l1 l2 p1 p2 ne pr1) ((ProperNil _) (ECNil _ ks)))
  (ECOut _ ks g1 x y l1 l2 (NotInNil x) p1 p2 ne (proper-cc ks g1 pr1)))

(def-fns _ $ (erased cc-proper : (erased (List (Nat)) ks) (erased (List (Bond)) g) (subterm erased (EdgeCC (Nil (Nat)) ks g) ec) -> (erased (Proper ks g) r))
  (match erased ec _
    ((ECNil _ _) (ProperNil ks))
    (absurd (ECIn _ _ _ _ _ _ ix _ _ _) ix)
    ((ECOut _ _ g1 x y l1 l2 _ p1 p2 ne ec1) (ProperCons ks g1 x y l1 l2 p1 p2 ne (cc-proper ks g1 ec1)))))

; With no contract edge, a contract colouring is a four-colouring.
(def-fns _ $ (erased four-cc : (erased (Nat) d) (erased (List (Nat)) e n f ks) (erased (Hypermap d e n f) h) (erased (FourColoring e f ks) c)
    -> (erased (CCColoring d e f (Nil (Nat)) ks) r))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased ids) (erased io)) (iota-exists d))
  (let ((erased ge) (erased gr)) (graph-exists d e le))
  (let-match erased c (MkFourColoring _ _ _ ke rf re df u))
  (let ((erased lk)) (respects-length ks f ks d rf lf))
  (MkCCColoring d e f _ ks _ ge (IENil e) gr rf (proper-cc ks ge (coloring-proper d e f ks ids ge c gr io lk)) u lk))

(def-fns _ $ (erased cc-four : (erased (Nat) d) (erased (List (Nat)) e n f ks) (erased (Hypermap d e n f) h) (erased (CCColoring d e f (Nil (Nat)) ks) c)
    -> (erased (FourColoring e f ks) r))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (let ((erased ids) (erased io)) (iota-exists d))
  (let-match erased c (MkCCColoring _ _ _ _ _ ins ge ie gr rf ec u lk))
  (let-match erased ie (IENil _))
  (proper-coloring d e f ks ids ge (cc-proper ks ge ec) gr io rf u lk (perm-under d e nf pe)))
