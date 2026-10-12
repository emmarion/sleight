; work/u62imm.sl: the Copy (Nat) <-> Copy (U62) coercion machinery that lets the
; sort's two array writes use the -imm forms (array-swap-imm / array-place-imm).
; The array is typed `Array (Copy (Nat))` (the spec's content type), but -imm
; writes need an `Immediate` element, and `Copy (Nat)` has none (Immediate (Nat)
; is uninhabited). `Copy (U62)` does: (ImmCopy (U62) (ImmU62)). Both element types
; are newtype chains over the same Nat word, so `coerce` relabels the array at no
; runtime cost. Everything here except the coerce + the two -imm calls is
; erased and never runs.
;
; `Uw ds us` is the pointwise relation between the Nat copy list `ds` and the U62
; copy list `us`: each `MkCopy (Nat) v` matches `MkCopy (U62) (MkU62 v p)` for the
; element bound `p`. It is what the Coercible witness is built from, and what the
; SetNth writes are transported across. The per-element bound `p` is threaded
; through the Uw (via uw-nth's output) rather than recomputed: `MkU62 v p1` and
; `MkU62 v p2` are NOT definitionally equal for two erased bounds p1, p2, so one
; consistent source for p is required.

(def-adts
  ((Uw : ((List (Copy (Nat))) ds) ((List (Copy (U62))) us) -> Type)
    enum
    (many UwNil : -> (Uw (Nil (Copy (Nat))) (Nil (Copy (U62)))))
    (many UwCons : (erased (Nat) v) (erased (Lt v u62-modulus) p) (erased (List (Copy (Nat))) ds)
       (erased (List (Copy (U62))) us) (erased (Uw ds us) rest)
       -> (Uw (Cons (Copy (Nat)) (MkCopy (Nat) v) ds) (Cons (Copy (U62)) (MkCopy (U62) (MkU62 v p)) us)))))

; uw-of-copies: build `Uw ds us` (and us) from the Nat content `ys`, its `Copies`
; link to `ds`, and the per-element bounds. Recurses on the Copies.
(def-fns _ $ (erased uw-of-copies : (erased (List (Nat)) ys) (erased (List (Copy (Nat))) ds)
    (subterm erased (Copies (Nat) ys ds) rel) (erased (AllTo (Nat) Lt ys u62-modulus) bnd)
    -> (erased (List (Copy (U62))) us) (erased (Uw ds us) uw))
  (let-match erased rel (CopiesCons _ x rest ds1 rel1)
    ((CopiesNil _)
      (let-match erased bnd (AllToNil _ _ _))
      (values (Nil (Copy (U62))) (UwNil))))
  (let-match erased bnd (AllToCons _ _ x2 rest2 _ p brest))
  (let ((erased us1) (erased uw1)) (uw-of-copies rest ds1 rel1 brest))
  (values (Cons (Copy (U62)) (MkCopy (U62) (MkU62 x p)) us1) (UwCons x p ds1 us1 uw1)))

; uw-nth: a read at position i on the Nat list gives the matching U62 read, and
; reveals the Uw's bound p at that position (returned so the caller uses the SAME
; bound in every MkU62 it builds). Recurses on the Uw.
(def-fns _ $ (erased uw-nth : (erased (List (Copy (Nat))) ds) (erased (List (Copy (U62))) us)
    (subterm erased (Uw ds us) uw) (erased (Nat) i) (erased (Nat) v)
    (erased (Nth (Copy (Nat)) ds i (MkCopy (Nat) v)) nth)
    -> (erased (Lt v u62-modulus) pv) (erased (Nth (Copy (U62)) us i (MkCopy (U62) (MkU62 v pv))) out))
  (let-match erased uw (UwCons v0 p0 ds0 us0 rest) (absurd (UwNil) nth))
  (let-match erased nth (NthThere _ _ _ i1 _ nth1)
    ((NthHere _ _ _) (values p0 (NthHere (Copy (U62)) (MkCopy (U62) (MkU62 v0 p0)) us0))))
  (let ((erased pv) (erased out1)) (uw-nth ds0 us0 rest i1 v nth1))
  (values pv (NthThere (Copy (U62)) (MkCopy (U62) (MkU62 v0 p0)) us0 i1 (MkCopy (U62) (MkU62 v pv)) out1)))

; uw-setnth: transport one U62 write into the matching Nat write, rebuilding the
; content lists and the Uw link for the new state. Recurses on the Uw. `pv` is
; the bound carried by the written value MkCopy (MkU62 v pv).
(def-fns _ $ (erased uw-setnth : (erased (List (Copy (Nat))) ds) (erased (List (Copy (U62))) us)
    (subterm erased (Uw ds us) uw) (erased (Nat) v) (erased (Lt v u62-modulus) pv)
    (erased (Nat) i) (erased (List (Copy (U62))) us1) (erased (SetNth (Copy (U62)) us i (MkCopy (U62) (MkU62 v pv)) us1) st)
    -> (erased (List (Copy (Nat))) ds1) (erased (SetNth (Copy (Nat)) ds i (MkCopy (Nat) v) ds1) s1) (erased (Uw ds1 us1) uw1))
  (let-match erased st (SetThere _ _ _ i1 _ us1x st1)
    ((SetHere _ _ _ _)
      (let-match erased uw (UwCons v0 p0 ds0 us0 rest))
      (values (Cons (Copy (Nat)) (MkCopy (Nat) v) ds0) (SetHere (Copy (Nat)) (MkCopy (Nat) v0) (MkCopy (Nat) v) ds0)
        (UwCons v pv ds0 us0 rest))))
  (let-match erased uw (UwCons v0 p0 ds0 us0 rest))
  (let ((erased ds1x) (erased s1x) (erased uw1x)) (uw-setnth ds0 us0 rest v pv i1 us1x st1))
  (values (Cons (Copy (Nat)) (MkCopy (Nat) v0) ds1x) (SetThere (Copy (Nat)) (MkCopy (Nat) v0) ds0 i1 (MkCopy (Nat) v) ds1x s1x)
    (UwCons v0 p0 ds1x us1x uw1x)))

; uw-array-fwd: the forward Coercible, `Array (Copy (Nat)) ds a` to
; `Array (Copy (U62)) us b`, built by destructuring the Nat array (as
; init-witness does). Erased; the runtime `coerce` is what relabels.
(def-fns _ $ (erased uw-array-fwd : (erased (List (Copy (Nat))) ds) (erased (List (Copy (U62))) us)
    (subterm erased (Uw ds us) uw) (erased (Array (Copy (Nat)) ds) a)
    -> (erased (Array (Copy (U62)) us) b) (erased (Coercible (Unique) (Array (Copy (Nat)) ds) a (Unique) (Array (Copy (U62)) us) b) c))
  (let-match erased uw (UwCons v p ds0 us0 rest)
    ((UwNil)
      (let-match erased a (ANil _))
      (values (ANil _) (coercible-ctor _ ANil (Copy (Nat)) (Copy (U62))))))
  (let-match erased a (ACons _ _ hd rest_a))
  (let ((erased b1) (erased c1)) (uw-array-fwd ds0 us0 rest rest_a))
  (values (ACons _ _ (MkCopy (U62) (MkU62 v p)) b1)
          (coercible-ctor _ ACons (Copy (Nat)) (Copy (U62)) ds0 us0
             (coercible-ctor _ MkCopy (Nat) (U62) (coercible-wrap _ MkU62 v p)) c1)))

; uw-array-bwd: the back Coercible, `Array (Copy (U62)) us b` to
; `Array (Copy (Nat)) ds a` (the mirror of uw-array-fwd).
(def-fns _ $ (erased uw-array-bwd : (erased (List (Copy (Nat))) ds) (erased (List (Copy (U62))) us)
    (subterm erased (Uw ds us) uw) (erased (Array (Copy (U62)) us) b)
    -> (erased (Array (Copy (Nat)) ds) a) (erased (Coercible (Unique) (Array (Copy (U62)) us) b (Unique) (Array (Copy (Nat)) ds) a) c))
  (let-match erased uw (UwCons v p ds0 us0 rest)
    ((UwNil)
      (let-match erased b (ANil _))
      (values (ANil _) (coercible-ctor _ ANil (Copy (U62)) (Copy (Nat))))))
  (let-match erased b (ACons _ _ hd rest_b))
  (let ((erased a1) (erased c1)) (uw-array-bwd ds0 us0 rest rest_b))
  (values (ACons _ _ (MkCopy (Nat) v) a1)
          (coercible-ctor _ ACons (Copy (U62)) (Copy (Nat)) us0 ds0
             (coercible-sym (coercible-ctor _ MkCopy (Nat) (U62) (coercible-wrap _ MkU62 v p))) c1)))

; swap2-imm: the sift step's two writes (the child value at i, the old i-value
; at m) done as -imm writes on the coerced U62 array, returning the two Nat-side
; SetNth proofs that swap-plumb consumes and the final Nat array. The per-element
; bounds are read off the Uw (via uw-nth) so every MkU62 is built with a bound
; that is definitionally the one in `us`. Both words to write are passed in by
; the caller (many u, many v), which has already read them -- each is wrapped as
; (MkCopy (U62) (MkU62 _ p)) here, a newtype chain over the same Nat word -- so
; the swap is two array-place-imms: no read and no allocation at runtime.
(def-fns _ $ (many swap2-imm :
    (erased (List (Nat)) ys) (erased (List (Copy (Nat))) ds) (erased (Copies (Nat) ys ds) rel)
    (erased (AllTo (Nat) Lt ys u62-modulus) bnd)
    (unique (Array (Copy (Nat)) ds) a)
    (many (Nat) i) (many (Nat) m)
    (many (Nat) u) (erased (Nth (Nat) ys i u) nyu) (erased (Nth (Copy (Nat)) ds i (MkCopy (Nat) u)) ndu)
    (many (Nat) v) (erased (Nth (Nat) ys m v) nym) (erased (Nth (Copy (Nat)) ds m (MkCopy (Nat) v)) ndm)
    ->
    (erased (List (Copy (Nat))) ds1) (erased (SetNth (Copy (Nat)) ds i (MkCopy (Nat) v) ds1) s1)
    (erased (List (Copy (Nat))) ds2) (erased (SetNth (Copy (Nat)) ds1 m (MkCopy (Nat) u) ds2) s2)
    (unique (Array (Copy (Nat)) ds2) r at a))
  (let ((erased us) (erased uw)) (uw-of-copies ys ds rel bnd))
  (let ((erased p_m) (erased ndm62)) (uw-nth ds us uw m v ndm))
  (let ((erased p_i) (erased ndu62)) (uw-nth ds us uw i u ndu))
  (let ((erased bu) (erased cw)) (uw-array-fwd ds us uw a))
  (let ((unique au)) (coerce a cw))
  (let ((erased us1) (unique au2) (erased stU1))
    (array-place-imm (Copy (U62)) us au i (MkCopy (U62) (MkU62 v p_m)) (MkCopy (U62) (MkU62 u p_i)) ndu62 (ImmCopy (U62) (ImmU62))))
  (let ((erased ds1) (erased s1) (erased uwA)) (uw-setnth ds us uw v p_m i us1 stU1))
  (let ((erased ndm1_62)) (setnth-nth-same (Copy (U62)) us i (MkCopy (U62) (MkU62 v p_m)) us1 stU1 m ndm62))
  (let ((erased us2) (unique au3) (erased stU2))
    (array-place-imm (Copy (U62)) us1 au2 m (MkCopy (U62) (MkU62 u p_i)) (MkCopy (U62) (MkU62 v p_m)) ndm1_62 (ImmCopy (U62) (ImmU62))))
  (let ((erased ds2) (erased s2) (erased uwB)) (uw-setnth ds1 us1 uwA u p_i m us2 stU2))
  (let ((erased bn) (erased cw2)) (uw-array-bwd ds2 us2 uwB au3))
  (let ((unique r)) (coerce au3 cw2))
  (values ds1 s1 ds2 s2 r))
