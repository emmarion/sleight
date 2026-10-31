(def-fns _ $ (erased ncols-of : (erased (List (Nat)) lc) (erased (List (Col)) cs) (subterm erased (All2 (Nat) (Col) ColOf lc cs) co) -> (erased (NCols lc cs) r))
  (let-match erased co (All2Cons _ _ _ k c lc1 cs1 p co1) ((All2Nil _ _ _) (NCsNil)))
  (NCsCons k c lc1 cs1 (match erased p (((NCol k c) res)) ((CO0) (NC0)) ((CO1) (NC1)) ((CO2) (NC2)) ((CO3) (NC3))) (ncols-of lc1 cs1 co1)))

(def-fns _ $ (erased colof-of : (erased (List (Nat)) lc) (erased (List (Col)) cs) (subterm erased (NCols lc cs) nc) -> (erased (All2 (Nat) (Col) ColOf lc cs) r))
  (let-match erased nc (NCsCons k c lc1 cs1 p nc1) ((NCsNil) (All2Nil _ _ ColOf)))
  (All2Cons _ _ ColOf k c lc1 cs1 (match erased p (((ColOf k c) res)) ((NC0) (CO0)) ((NC1) (CO1)) ((NC2) (CO2)) ((NC3) (CO3))) (colof-of lc1 cs1 nc1)))

(def-fns _ $ (erased k-addc : (erased (Col) a b c) (erased (AddK a b c) p) -> (erased (AddC a b c) q))
  (let ((erased c2) (erased q)) (addc-c a b))
  (let-match erased (addc-fn a b c c2 p (addc-k a b c2 q)) (Refl _ _))
  q)

(def-fns _ $ (erased ctr-of-tf : (erased (Col) c0 c) (erased (List (Col)) lc et) (subterm erased (TraceFrom c0 c lc et) t) -> (erased (CTr c0 c lc et) r))
  (match erased t _
    ((TFEnd _ _ s a) (CTLast c0 c s (k-addc c c0 s a)))
    ((TFCons _ _ c2 s lc1 et1 a t1) (CTStep c0 c c2 s lc1 et1 (k-addc c c2 s a) (ctr-of-tf c0 c2 lc1 et1 t1)))))

(def-fns _ $ (erased tf-of-ctr : (erased (Col) c0 c) (erased (List (Col)) lc et) (subterm erased (CTr c0 c lc et) t) -> (erased (TraceFrom c0 c lc et) r))
  (match erased t _
    ((CTLast _ _ s a) (TFEnd c0 c s (addc-k c c0 s a)))
    ((CTStep _ _ c2 s lc1 et1 a t1) (TFCons c0 c c2 s lc1 et1 (addc-k c c2 s a) (tf-of-ctr c0 c2 lc1 et1 t1)))))

(def-fns _ $ (erased cpcol-of : (erased (List (Step)) cp) (erased (Nat) d a) (erased (List (Nat)) e f p) (erased (List (Col)) et)
    (erased (Cpmap cp d e f (Cons (Nat) a p)) cm) (erased (RingTrace e f (Cons (Nat) a p) et) rt) -> (erased (CpCol cp et) r))
  (let-match erased rt (MkRingTrace _ _ _ ks lc cs _ col rl co t))
  (let-match erased rl (RespCons _ _ _ _ _ _ _))
  (let-match erased co (All2Cons _ _ _ _ c _ cs1 _ _))
  (let-match erased t (TrCons _ _ _ tf))
  (MkCpCol cp d e f _ ks lc cs et cm col rl (ncols-of lc cs co) (MkTrace c cs1 et (ctr-of-tf c c cs1 et tf))))

(def-fns _ $ (erased cpcol-rt : (erased (List (Step)) cp) (erased (List (Col)) et) (erased (CpCol cp et) cc)
    -> (erased (Nat) d) (erased (List (Nat)) e f r) (erased (Cpmap cp d e f r) cm) (erased (RingTrace e f r et) rt))
  (let-match erased cc (MkCpCol _ d e f r ks rc cs _ cm col rr nc tr))
  (let-match erased tr (MkTrace c cs1 _ ct))
  (values d e f r cm (MkRingTrace e f r ks rc cs et col rr (colof-of rc cs nc) (TrCons c cs1 et (tf-of-ctr c c cs1 et ct)))))
