; decide_ring_trace of coloring.v: whether et is a ring trace of r is decided, by the search of coloring.sl for each
; colouring of r that a first colour and et allow. Load after ringtrace.sl.

; The colours lc after c that a trace et from c determines, its last entry left unchecked.
(def-adts $ (UF : ((Col) c) ((List (Col)) et lc) -> Type)
  enum
  (many UFEnd : (erased (Col) c s) -> (UF c (Cons (Col) s (Nil (Col))) (Nil (Col))))
  (many UFCons : (erased (Col) c c2 s) (erased (List (Col)) et lc) (erased (AddK c c2 s) a) (erased (UF c2 et lc) u)
      -> (UF c (Cons (Col) s et) (Cons (Col) c2 lc))))

(def-fns _ $ (erased addk-swap : (erased (Col) a b c) (erased (AddK a b c) p) -> (erased (AddK a c b) q))
  (match erased p _ ((AZL _) (AZL b)) ((AZR _) (ASame a)) ((ASame _) (AZR a)) ((AThird _ _ _ t) (AThird a c b (third-23 a b c t)))))

(def-fns _ $ (erased tf-uf : (erased (Col) c0 c) (erased (List (Col)) lc et) (subterm erased (TraceFrom c0 c lc et) t) -> (erased (UF c et lc) u))
  (match erased t _
    ((TFEnd _ _ s _) (UFEnd c s))
    ((TFCons _ _ c2 s lc1 et1 a t1) (UFCons c c2 s et1 lc1 a (tf-uf c0 c2 lc1 et1 t1)))))

(def-fns _ $ (erased uf-fn : (erased (Col) c) (erased (List (Col)) et lc lc2) (subterm erased (UF c et lc) u) (erased (UF c et lc2) v)
    -> (erased (Eq (List (Col)) lc lc2) e))
  (match erased u _
    ((UFEnd _ s) (match erased v _ ((UFEnd _ _) (Refl _ lc)) (absurd (UFCons _ _ _ _ _ _ v1) v1)))
    ((UFCons _ c2 s et1 lc1 a u1)
      (let-match erased v (UFCons _ c3 _ _ lc3 b v1) (absurd (UFEnd _ _) u1))
      (let-match erased (addc-fn c s c2 c3 (addk-swap c c2 s a) (addk-swap c c3 s b)) (Refl _ _))
      (let-match erased (uf-fn c2 et1 lc1 lc3 u1 v1) (Refl _ _))
      (Refl _ lc))))

(def-fns _ $ (erased uf-exists : (erased (Col) c s) (subterm erased (List (Col)) et) -> (erased (List (Col)) lc) (erased (UF c (Cons (Col) s et) lc) u))
  (let-match erased et (Cons _ s2 et1) ((Nil _) (values (Nil _) (UFEnd c s))))
  (let ((erased c2) (erased a)) (addc-total c s))
  (let ((erased lc) (erased u)) (uf-exists c2 s2 et1))
  (values (Cons _ c2 lc) (UFCons c c2 s et lc (addk-swap c s c2 a) u)))

; Two lists of colours differ somewhere.
(def-adts $ (CLNe : ((List (Col)) xs ys) -> Type)
  enum
  (many CNHead : (erased (Col) x y z) (erased (List (Col)) xs ys) (erased (AddK x y z) a) (erased (NonZero z) nz) -> (CLNe (Cons (Col) x xs) (Cons (Col) y ys)))
  (many CNTail : (erased (Col) x y) (erased (List (Col)) xs ys) (erased (CLNe xs ys) p) -> (CLNe (Cons (Col) x xs) (Cons (Col) y ys)))
  (many CNL : (erased (Col) x) (erased (List (Col)) xs) -> (CLNe (Cons (Col) x xs) (Nil (Col))))
  (many CNR : (erased (Col) y) (erased (List (Col)) ys) -> (CLNe (Nil (Col)) (Cons (Col) y ys))))

(def-fns _ $ (erased absurd clne-irrefl : (erased (List (Col)) xs) (subterm erased (CLNe xs xs) p) -> (erased (False) f))
  (match erased p _
    (absurd (CNHead x _ z _ _ a nz) (let-match erased (addc-fn x x z (C0) a (ASame x)) (Refl _ _)) nz)
    (absurd (CNTail _ _ xs1 _ p1) (clne-irrefl xs1 p1))))

(def-fns _ $ (erased addk-zero : (erased (Col) x y) (erased (AddK x y (C0)) a) -> (erased (Eq (Col) x y) e))
  (match erased a _ ((AZL _) (Refl _ x)) ((AZR _) (Refl _ x)) ((ASame _) (Refl _ x)) (absurd (AThird _ _ _ t) t)))

(def-fns _ $ (erased cl-dec : (subterm erased (List (Col)) xs) (erased (List (Col)) ys) -> (erased (Or (Eq (List (Col)) xs ys) (CLNe xs ys)) r))
  (match erased xs _
    ((Nil _) (match erased ys _ ((Nil _) (InL _ _ (Refl _ xs))) ((Cons _ y ys1) (InR _ _ (CNR y ys1)))))
    ((Cons _ x xs1)
      (let-match erased ys (Cons _ y ys1) ((Nil _) (InR _ _ (CNL x xs1))))
      (let ((erased z) (erased a)) (addc-total x y))
      (let-match erased z (C0)
        ((C1) (InR _ _ (CNHead x y z xs1 ys1 a (NZ1))))
        ((C2) (InR _ _ (CNHead x y z xs1 ys1 a (NZ2))))
        ((C3) (InR _ _ (CNHead x y z xs1 ys1 a (NZ3)))))
      (let-match erased (addk-zero x y a) (Refl _ _))
      (let-match erased (cl-dec xs1 ys1) (InL _ _ q) ((InR _ _ p) (InR _ _ (CNTail x y xs1 ys1 p))))
      (let-match erased q (Refl _ _))
      (InL _ _ (Refl _ xs)))))

(def-fns _ $ (erased nats-exists : (subterm erased (List (Col)) cs) -> (erased (List (Nat)) ks) (erased (All2 (Nat) (Col) ColOf ks cs) a))
  (let-match erased cs (Cons _ c cs1) ((Nil _) (values (Nil _) (All2Nil (Nat) (Col) ColOf))))
  (let ((erased k) (erased p)) (natof-exists c))
  (let ((erased ks) (erased a)) (nats-exists cs1))
  (values (Cons _ k ks) (All2Cons (Nat) (Col) ColOf k c ks cs1 p a)))

(def-fns _ $ (erased nats-fn : (erased (List (Nat)) ks ks2) (erased (List (Col)) cs) (subterm erased (All2 (Nat) (Col) ColOf ks cs) p)
    (erased (All2 (Nat) (Col) ColOf ks2 cs) q) -> (erased (Eq (List (Nat)) ks ks2) e))
  (let-match erased p (All2Cons _ _ _ k c ks1 cs1 p1 r1) ((All2Nil _ _ _) (let-match erased q (All2Nil _ _ _)) (Refl _ ks)))
  (let-match erased q (All2Cons _ _ _ k2 _ ks3 _ q1 r2))
  (let-match erased (colof-inj k k2 c p1 q1) (Refl _ _))
  (let-match erased (nats-fn ks1 ks3 cs1 r1 r2) (Refl _ _))
  (Refl _ ks))

; Why the colours cs, numbered lcn, give r no ring trace et: their trace differs from et, lcn and r differ in length, or no
; four-colouring gives r the colours lcn.
(def-adts $ (MissWhy : ((List (Nat)) e f r lcn) ((List (Col)) cs et) -> Type)
  enum
  (many MWTrace : (erased (List (Nat)) e f r lcn) (erased (List (Col)) cs et et2) (erased (Trace cs et2) tr) (erased (CLNe et2 et) ne)
      -> (MissWhy e f r lcn cs et))
  (many MWLength : (erased (List (Nat)) e f r lcn) (erased (List (Col)) cs et) (erased (Nat) kn k) (erased (Length (Nat) lcn kn) ln)
      (erased (Length (Nat) r k) lr) (erased (Apart (Nat) Lt kn k) ne) -> (MissWhy e f r lcn cs et))
  (many MWSearch : (erased (List (Nat)) e f r lcn) (erased (List (Col)) cs et) (erased (Nat) d) (erased (Length (Nat) f d) lf)
      (erased (NoExt d e f r lcn (Nil (Nat))) ne) -> (MissWhy e f r lcn cs et)))

; No ring trace of r is et with first colour c0: c0 :: cs1 are the only colours from c0 that et allows.
(def-adts $ (RTMiss : ((List (Nat)) e f r) ((List (Col)) et) ((Col) c0) -> Type)
  enum
  (many MkRTMiss : (erased (List (Nat)) e f r lcn) (erased (Col) c0 s) (erased (List (Col)) et1 cs1) (erased (UF c0 (Cons (Col) s et1) cs1) uf)
      (erased (All2 (Nat) (Col) ColOf lcn (Cons (Col) c0 cs1)) al) (erased (MissWhy e f r lcn (Cons (Col) c0 cs1) (Cons (Col) s et1)) w)
      -> (RTMiss e f r (Cons (Col) s et1) c0)))

(def-fns _ $ (erased rtmiss-sound : (erased (List (Nat)) e f r ks lc) (erased (List (Col)) et cs2) (erased (Col) c0) (erased (RTMiss e f r et c0) m)
    (erased (FourColoring e f ks) c) (erased (Respects ks r lc) rl) (erased (All2 (Nat) (Col) ColOf lc (Cons (Col) c0 cs2)) co)
    (erased (Trace (Cons (Col) c0 cs2) et) t) -> (erased (False) res))
  (let-match erased m (MkRTMiss _ _ _ lcn _ s et1 cs1 uf al w))
  (let-match erased t (TrCons _ _ _ t1))
  (let-match erased (uf-fn c0 et cs2 cs1 (tf-uf c0 c0 cs2 et t1) uf) (Refl _ _))
  (let-match erased (nats-fn lc lcn _ co al) (Refl _ _))
  (match erased w _
    ((MWTrace _ _ _ _ cs _ et2 tr ne)
      (let-match erased (trace-fn cs et2 et tr t) (Refl _ _))
      (clne-irrefl et2 ne))
    ((MWLength _ _ _ _ _ _ kn k ln lr ne)
      (let-match erased (length-fn (Nat) lcn kn k ln (respects-length ks r lc k rl lr)) (Refl _ _))
      (apart-irrefl kn ne))
    ((MWSearch _ _ _ _ _ _ d lf ne)
      (let-match erased c (MkFourColoring _ _ _ _ rf _ _ _))
      (noext-sound d e f r lcn (Nil _) ks ks ne (JoinNil ks) (respects-length ks f ks d rf lf) c rl))))

; The ring traces of r whose first colour is c0: one is found, or there is none.
(def-adts $ (RTTry : ((List (Nat)) e f r) ((List (Col)) et) ((Col) c0) -> Type)
  enum
  (many RTHit : (erased (List (Nat)) e f r) (erased (List (Col)) et) (erased (Col) c0) (erased (RingTrace e f r et) rt) -> (RTTry e f r et c0))
  (many RTMissed : (erased (List (Nat)) e f r) (erased (List (Col)) et) (erased (Col) c0) (erased (RTMiss e f r et c0) m) -> (RTTry e f r et c0)))

(def-fns _ $ (erased rt-try : (erased (Nat) d k) (erased (List (Nat)) e n f r) (erased (Hypermap d e n f) h) (erased (Under r d) ur) (erased (Length (Nat) r k) lr)
    (erased (Col) s c0) (erased (List (Col)) et1) -> (erased (RTTry e f r (Cons (Col) s et1) c0) res))
  (let ((erased et)) (Cons (Col) s et1))
  (let ((erased lf)) (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h)) lf)
  (let ((erased cs1) (erased uf)) (uf-exists c0 s et1))
  (let ((erased cs)) (Cons (Col) c0 cs1))
  (let ((erased et2) (erased tr)) (trace-exists cs))
  (let ((erased lcn) (erased al)) (nats-exists cs))
  (let ((erased kn) (erased ln)) (length-exists (Nat) lcn))
  (let-match erased (cl-dec et2 et) (InL _ _ q)
    ((InR _ _ ne) (RTMissed e f r et c0 (MkRTMiss e f r lcn c0 s et1 cs1 uf al (MWTrace e f r lcn cs et et2 tr ne)))))
  (let-match erased q (Refl _ _))
  (let-match erased (nat-eq kn k) (Equal _ _ _)
    ((Unequal _ _ _ _ ne) (RTMissed e f r et c0 (MkRTMiss e f r lcn c0 s et1 cs1 uf al (MWLength e f r lcn cs et kn k ln lr ne)))))
  (let-match erased (search-ring d k e n f r lcn h ur lr ln) (NotFound _ _ _ _ _ _ ne)
    ((Found _ _ _ _ _ _ ks c rl) (RTHit e f r et c0 (MkRingTrace e f r ks lcn cs et c rl al tr))))
  (RTMissed e f r et c0 (MkRTMiss e f r lcn c0 s et1 cs1 uf al (MWSearch e f r lcn cs et d lf ne))))

; No ring trace of r is et: every first colour misses, r has darts and et none, or the map has no four-colouring.
(def-adts $ (RTNo : ((List (Nat)) e f r) ((List (Col)) et) -> Type)
  enum
  (many RNCons : (erased (List (Nat)) e f r) (erased (Col) s) (erased (List (Col)) et1) (erased (RTMiss e f r (Cons (Col) s et1) (C0)) m0)
      (erased (RTMiss e f r (Cons (Col) s et1) (C1)) m1) (erased (RTMiss e f r (Cons (Col) s et1) (C2)) m2)
      (erased (RTMiss e f r (Cons (Col) s et1) (C3)) m3) -> (RTNo e f r (Cons (Col) s et1)))
  (many RNRing : (erased (List (Nat)) e f r) (erased (Nat) x) -> (RTNo e f (Cons (Nat) x r) (Nil (Col))))
  (many RNMap : (erased (List (Nat)) e f) (erased (Nat) d) (erased (Length (Nat) f d) lf) (erased (NoExt d e f (Nil (Nat)) (Nil (Nat)) (Nil (Nat))) ne)
      -> (RTNo e f (Nil (Nat)) (Nil (Col)))))

(def-fns _ $ (erased rtno-sound : (erased (List (Nat)) e f r) (erased (List (Col)) et) (erased (RTNo e f r et) no) (erased (RingTrace e f r et) rt)
    -> (erased (False) res))
  (let-match erased rt (MkRingTrace _ _ _ ks lc cs _ c rl co t))
  (match erased no _
    ((RNCons _ _ _ s et1 m0 m1 m2 m3)
      (let-match erased t (TrCons c0 cs1 _ t1))
      (match erased c0 _
        ((C0) (rtmiss-sound e f r ks lc et cs1 c0 m0 c rl co t))
        ((C1) (rtmiss-sound e f r ks lc et cs1 c0 m1 c rl co t))
        ((C2) (rtmiss-sound e f r ks lc et cs1 c0 m2 c rl co t))
        ((C3) (rtmiss-sound e f r ks lc et cs1 c0 m3 c rl co t))))
    (absurd (RNRing _ _ r1 x)
      (let-match erased t (TrNil) (absurd (TrCons _ _ _ t1) (match erased t1 _)))
      (let-match erased co (All2Nil _ _ _))
      rl)
    ((RNMap _ _ d lf ne)
      (let-match erased t (TrNil) (absurd (TrCons _ _ _ t1) (match erased t1 _)))
      (let-match erased co (All2Nil _ _ _))
      (let-match erased c (MkFourColoring _ _ _ _ rf _ _ _))
      (noext-sound d e f (Nil _) (Nil _) (Nil _) ks ks ne (JoinNil ks) (respects-length ks f ks d rf lf) c rl))))

; decide_ring_trace.
(def-adts $ (RingDec : ((List (Nat)) e f r) ((List (Col)) et) -> Type)
  enum
  (many RDYes : (erased (List (Nat)) e f r) (erased (List (Col)) et) (erased (RingTrace e f r et) rt) -> (RingDec e f r et))
  (many RDNo : (erased (List (Nat)) e f r) (erased (List (Col)) et) (erased (RTNo e f r et) no) -> (RingDec e f r et)))

(def-fns _ $ (erased decide-ring-trace : (erased (Nat) d) (erased (List (Nat)) e n f r) (erased (Hypermap d e n f) h) (erased (Under r d) ur)
    (erased (List (Col)) et) -> (erased (RingDec e f r et) res))
  (let ((erased k) (erased lr)) (length-exists (Nat) r))
  (let-match erased et (Cons _ s et1)
    ((Nil _)
      (let-match erased r (Nil _) ((Cons _ x r1) (RDNo e f r et (RNRing e f r1 x))))
      (let-match erased (search-ring d (Zero) e n f r (Nil _) h ur (LengthNil _) (LengthNil _)) (NotFound _ _ _ _ _ _ ne)
        ((Found _ _ _ _ _ _ ks c rl) (RDYes e f r et (MkRingTrace e f r ks (Nil _) (Nil _) et c rl (All2Nil (Nat) (Col) ColOf) (TrNil)))))
      (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
      (RDNo e f r et (RNMap e f d lf ne))))
  (let-match erased (rt-try d k e n f r h ur lr s (C0) et1) (RTMissed _ _ _ _ _ m0) ((RTHit _ _ _ _ _ rt) (RDYes e f r et rt)))
  (let-match erased (rt-try d k e n f r h ur lr s (C1) et1) (RTMissed _ _ _ _ _ m1) ((RTHit _ _ _ _ _ rt) (RDYes e f r et rt)))
  (let-match erased (rt-try d k e n f r h ur lr s (C2) et1) (RTMissed _ _ _ _ _ m2) ((RTHit _ _ _ _ _ rt) (RDYes e f r et rt)))
  (let-match erased (rt-try d k e n f r h ur lr s (C3) et1) (RTMissed _ _ _ _ _ m3) ((RTHit _ _ _ _ _ rt) (RDYes e f r et rt)))
  (RDNo e f r et (RNCons e f r s et1 m0 m1 m2 m3)))
