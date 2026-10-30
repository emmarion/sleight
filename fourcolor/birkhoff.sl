; The Birkhoff theorem of birkhoff.v: Birkhoff_valid, from the certified check of red/bcheck.sl, and its use for rings of
; at most five faces. Load after cpgeom.sl and ringdec.sl, in the order of PLAN.md.

; A trace from c0, read up to its last entry, is a ctrace from c0 + c.
(def-fns _ $ (erased tracefrom-ctr : (erased (Col) c0 c s) (erased (List (Col)) lc et) (subterm erased (TraceFrom c0 c lc et) t) (erased (AddK c0 c s) a)
    -> (erased (List (Col)) et1) (erased (Ctr s et1 et) r))
  (match erased t _
    ((TFEnd _ _ s1 a1) (let-match erased (addc-fn c0 c s s1 a (addc-comm c c0 s1 a1)) (Refl _ _)) (values (Nil _) (CtrNil s)))
    ((TFCons _ _ c2 s1 lc1 et2 a1 t1)
      (let ((erased s2) (erased a2)) (addc-total c0 c2))
      (let ((erased et3) (erased r)) (tracefrom-ctr c0 c2 s2 lc1 et2 t1 a2))
      (values (Cons _ s1 et3) (CtrCons s s1 s2 et3 et2 (addc-tri c0 c c2 s s1 s2 a a1 a2) r)))))

(def-fns _ $ (erased ctr-length : (erased (Col) s) (erased (List (Col)) et1 et) (erased (Nat) k) (subterm erased (Ctr s et1 et) c)
    (erased (Length (Col) et (Succ k)) l) -> (erased (Length (Col) et1 k) r))
  (match erased c _
    ((CtrNil _) (let-match erased l (LengthCons _ _ _ _ l1)) (let-match erased l1 (LengthNil _)) (LengthNil _))
    ((CtrCons _ x s2 et2 ct a c1)
      (let-match erased l (LengthCons _ _ _ _ l1))
      (let-match erased l1 (LengthCons _ _ _ k1 _) (absurd (LengthNil _) (match erased c1 _)))
      (LengthCons _ x et2 k1 (ctr-length s2 et2 ct k1 c1 l1)))))

(def-fns _ $ (erased tracefrom-length : (erased (Col) c0 c) (erased (List (Col)) lc et) (erased (Nat) k) (subterm erased (TraceFrom c0 c lc et) t)
    (erased (Length (Col) lc k) l) -> (erased (Length (Col) et (Succ k)) r))
  (match erased t _
    ((TFEnd _ _ s _) (let-match erased l (LengthNil _)) (LengthCons _ s _ _ (LengthNil _)))
    ((TFCons _ _ c2 s lc1 et1 _ t1)
      (let-match erased l (LengthCons _ _ _ k1 l1))
      (LengthCons _ s et1 k (tracefrom-length c0 c2 lc1 et1 k1 t1 l1)))))

; The ring trace of a ring of k + 1 darts is the ctrace of k colours.
(def-fns _ $ (erased rt-ctr : (erased (List (Nat)) e f r) (erased (List (Col)) et) (erased (Nat) k) (erased (RingTrace e f r et) rt)
    (erased (Length (Nat) r (Succ k)) lr) -> (erased (List (Col)) et1) (erased (Ctr (C0) et1 et) c) (erased (Length (Col) et1 k) l))
  (let-match erased rt (MkRingTrace _ _ _ ks lc cs _ col rl co t))
  (let ((erased lcs)) (all2-length (Nat) (Col) ColOf lc cs (Succ k) co (respects-length ks r lc (Succ k) rl lr)))
  (let-match erased lcs (LengthCons _ c cs1 _ lcs1))
  (let-match erased t (TrCons _ _ _ tf))
  (let ((erased et1) (erased cr)) (tracefrom-ctr c c (C0) cs1 et tf (ASame c)))
  (values et1 cr (ctr-length (C0) et1 et k cr (tracefrom-length c c cs1 et k tf lcs1))))

(def-fns _ $ (erased notin-revapp : (erased (Nat) a) (erased (List (Nat)) p w q) (subterm erased (RevApp (Nat) p w q) ra) (erased (NotIn a p) o)
    (erased (NotIn a w) ow) -> (erased (NotIn a q) r))
  (let-match erased ra (RACons _ s p1 _ _ ra1) ((RANil _ _) ow))
  (let-match erased o (NotInCons _ _ _ ne o1))
  (notin-revapp a p1 (Cons _ s w) q ra1 o1 (NotInCons a s w ne ow)))

(def-fns _ $ (erased rpath-br : (erased (List (Nat)) n p) (erased (Nat) a y) (erased (CRPath n a p y) rp) (erased (Nth (Nat) n a y) back)
    -> (erased (List (Nat)) q) (erased (RevApp (Nat) p (Nil (Nat)) q) ra) (erased (NCyc n (Cons (Nat) a q)) nc))
  (let-match erased rp (CRPCons _ p1 _ z1 _ pz rp1) ((CRPNil _ _) (values (Nil _) (RANil _ (Nil _)) (NCCons n (Nil _) a a (FPNil n a) back))))
  (let ((erased B) (erased fp) (erased ra1)) (rpath-fpath n p1 (Nil _) z1 y z1 rp1 (FPNil n z1)))
  (values (Cons _ y B) ra1 (NCCons n (Cons _ y B) a z1 (FPCons n B a y z1 back fp) pz)))

; The ring a :: p of a configuration map, read as the node cycle a :: rev p (Coq's rotr 1 (rev (cpring G))).
(def-fns _ $ (erased cpring-br : (erased (List (Nat)) n r) (erased (Cpring n r) cr)
    -> (erased (Nat) a) (erased (List (Nat)) p q) (erased (Eq (List (Nat)) r (Cons (Nat) a p)) eq) (erased (RevApp (Nat) p (Nil (Nat)) q) ra)
    (erased (NCyc n (Cons (Nat) a q)) nc) (erased (Distinct (Cons (Nat) a q)) dq))
  (let-match erased cr (MkCpring _ p a y rp back dp))
  (let-match erased dp (DistCons _ _ o dp1))
  (let ((erased q) (erased ra) (erased nc)) (rpath-br n p a y rp back))
  (values a p q (Refl _ r) ra nc
    (DistCons a q (notin-revapp a p (Nil _) q ra o (NotInNil a)) (revapp-distinct p (Nil _) q ra dp1 (DistNil) (off-nil p)))))

; Node order 3 off the ring a :: p, read off the node cycle a :: rev p.
(def-fns _ $ (erased cubics-turn : (erased (List (Nat)) n p q xs) (erased (Nat) a) (subterm erased (Cubics n (Cons (Nat) a p) xs) cs)
    (erased (RevApp (Nat) p (Nil (Nat)) q) ra) -> (erased (OrdersOff n 3 (Cons (Nat) a q) xs) res))
  (unary 3)
  (let-match erased cs (CubsCons _ _ xs1 x c cs1) ((CubsNil _ _) (OONil n _ 3)))
  (let ((erased rest)) (cubics-turn n p q xs1 a cs1 ra))
  (match erased c _
    ((CubOn _ _ _ i)
      (OOSkip n _ xs1 3 x (match erased i (((In x (Cons (Nat) a q)) res))
        ((InHere _ _) (InHere a q))
        ((InThere _ _ _ i1) (InThere x a q (revapp-in p (Nil _) q x ra (OrL _ _ i1))))) rest))
    ((CubThree _ _ _ o) (OOAt n _ xs1 3 x o rest))))

(def-fns _ $ (erased rotrev-sym : (erased (List (Col)) a b) (erased (RotRev a b) rr) -> (erased (RotRev b a) r))
  (let-match erased rr (RRCons _ E1 _ c ra sn) ((RRNil) (RRNil)))
  (let ((erased R1) (erased r1)) (revapp-exists (Col) E1 (Nil _)))
  (let ((erased rb)) (revapp-snoc-l (Col) c E1 b (Nil _) R1 sn r1))
  (let ((erased ra2)) (revapp-flip (Col) a (Nil _) (Cons _ c E1) a ra (RANil _ a)))
  (let-match erased ra2 (RACons _ _ _ _ _ ra3))
  (let ((erased A2) (erased ra4)) (revapp-exists (Col) E1 (Cons _ c (Nil _))))
  (let-match erased (revapp-fn (Col) E1 (Cons _ c (Nil _)) a A2 ra3 ra4) (Refl _ _))
  (RRCons b R1 a c rb (revapp-snoc (Col) c E1 (Nil _) (Cons _ c (Nil _)) R1 a r1 (SnocNil _ c) ra4)))

; From a ring trace et2 = rot 1 (rev et) of a :: rev p to the ring trace rotr 1 et of a :: p.
(def-fns _ $ (erased rt-revtail : (erased (List (Nat)) e f p q) (erased (Nat) a) (erased (List (Col)) et et2) (erased (RevApp (Nat) p (Nil (Nat)) q) ra)
    (erased (RingTrace e f (Cons (Nat) a q) et2) rt) (erased (RotRev et et2) rr)
    -> (erased (Col) s) (erased (List (Col)) E) (erased (HSnoc (Col) E s et) se) (erased (RingTrace e f (Cons (Nat) a p) (Cons (Col) s E)) r))
  (let-match erased rt (MkRingTrace _ _ _ ks lc cs _ col rl co t))
  (let-match erased rl (RespCons _ _ lq _ la pa rlq))
  (let-match erased co (All2Cons _ _ _ _ ca _ csq pca coq))
  (let ((erased lp) (erased rlp) (erased rpl))
    (respects-revapp ks q (Nil _) p lq (Nil _) rlq (RespNil ks) (revapp-flip (Nat) p (Nil _) q p ra (RANil _ p))))
  (let ((erased csp) (erased rcs) (erased cop)) (all2-revapp (Nat) (Col) ColOf lq (Nil _) lp csq (Nil _) coq (All2Nil _ _ ColOf) rlp))
  (let ((erased lc2) (erased r2)) (revapp-exists (Col) csq (Cons _ ca (Nil _))))
  (let ((erased sn)) (revapp-snoc (Col) ca csq (Nil _) (Cons _ ca (Nil _)) csp lc2 rcs (SnocNil _ ca) r2))
  (let ((erased t2)) (trace-rev (Cons _ ca csq) lc2 et2 et t (RACons _ ca csq (Nil _) lc2 r2) (rotrev-sym et et2 rr)))
  (let ((erased et4) (erased t4)) (trace-exists (Cons _ ca csp)))
  (let ((erased s) (erased E) (erased et5) (erased eq) (erased se) (erased t5)) (trace-rot ca csp lc2 et4 t4 sn))
  (let-match erased (trace-fn lc2 et5 et t5 t2) (Refl _ _))
  (let-match erased eq (Refl _ _))
  (values s E se (MkRingTrace e f _ ks (Cons _ la lp) (Cons _ ca csp) et4 col (RespCons ks p lp a la pa rpl) (All2Cons _ _ ColOf la ca lp csp pca cop) t4)))

(def-fns _ $ (erased ncols-of : (erased (List (Nat)) lc) (erased (List (Col)) cs) (subterm erased (All2 (Nat) (Col) ColOf lc cs) co) -> (erased (NCols lc cs) r))
  (let-match erased co (All2Cons _ _ _ k c lc1 cs1 p co1) ((All2Nil _ _ _) (NCsNil)))
  (NCsCons k c lc1 cs1 (match erased p (((NCol k c) res)) ((CO0) (NC0)) ((CO1) (NC1)) ((CO2) (NC2)) ((CO3) (NC3))) (ncols-of lc1 cs1 co1)))

(def-fns _ $ (erased k-addc : (erased (Col) a b c) (erased (AddK a b c) p) -> (erased (AddC a b c) q))
  (let ((erased c2) (erased q)) (addc-c a b))
  (let-match erased (addc-fn a b c c2 p (addc-k a b c2 q)) (Refl _ _))
  q)

(def-fns _ $ (erased ctr-of-tf : (erased (Col) c0 c) (erased (List (Col)) lc et) (subterm erased (TraceFrom c0 c lc et) t) -> (erased (CTr c0 c lc et) r))
  (match erased t _
    ((TFEnd _ _ s a) (CTLast c0 c s (k-addc c c0 s a)))
    ((TFCons _ _ c2 s lc1 et1 a t1) (CTStep c0 c c2 s lc1 et1 (k-addc c c2 s a) (ctr-of-tf c0 c2 lc1 et1 t1)))))

; A ring trace of the map of cp, on its own ring, is a CpCol of cp.
(def-fns _ $ (erased cpcol-of : (erased (List (Step)) cp) (erased (Nat) d a) (erased (List (Nat)) e f p) (erased (List (Col)) et)
    (erased (Cpmap cp d e f (Cons (Nat) a p)) cm) (erased (RingTrace e f (Cons (Nat) a p) et) rt) -> (erased (CpCol cp et) r))
  (let-match erased rt (MkRingTrace _ _ _ ks lc cs _ col rl co t))
  (let-match erased rl (RespCons _ _ lp _ la pa rlp))
  (let-match erased co (All2Cons _ _ _ _ c _ cs1 pc co1))
  (let-match erased t (TrCons _ _ _ tf))
  (MkCpCol cp d e f _ ks lc cs et cm col rl (ncols-of lc cs co) (MkTrace c cs1 et (ctr-of-tf c c cs1 et tf))))
