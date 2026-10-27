; work/heap.sl: transporting an unchanged heap subtree across one write, and
; heap-replace (milestone 3). All erased.
;
; congr-top: a write ABOVE the subtree root leaves the subtree a heap (every
;   node of the subtree is at/above the root, hence differs from the write
;   position; each Nth travels across the write with setnth-nth-diff).
; congr-sib: a write inside the LEFT sibling subtree leaves this (right) subtree
;   a heap (each node differs from the write position by tree.sl's sib-ne).
; congr-sib2: mirror (the write is in the RIGHT sibling subtree).
; heap-here: replacing the root's value when the new one fits (the sift exit).
; heap-replace: changing node h's value from v to w inside subtree(i) keeps
;   subtree(i) a max-heap, provided w <= v and w fits at h; it returns the new
;   value at i and its NatLe to the old one so the caller can re-establish the
;   parent edge.

; ---- congr-top: the write position is strictly above the subtree root ----

(def-fns _ $ (erased congr-top : (erased (Nat) h) (erased (Nat) i) (erased (Nat) d)
    (erased (Lt h i) up) (erased (List (Nat)) ys) (erased (Nat) hi)
    (subterm erased (HeapOn ys hi i d) H) (erased (Nat) w) (erased (List (Nat)) ys')
    (erased (SetNth (Nat) ys h w ys') st) -> (erased (HeapOn ys' hi i d) out))
  (match erased H _
    ((HLeaf _ _ _ _ dd nl) (HLeaf ys' hi i d dd nl))
    ((HOne _ _ _ _ dd d2 dd2 x y nx ny lin nron le subl)
      (let ((erased up2)) (lt-trans h i (Succ d) up (double-lt i d dd)))
      (HOne ys' hi i d dd d2 dd2 x y
        (setnth-nth-diff (Nat) ys h w ys' st i x nx (NeGT i h up))
        (setnth-nth-diff (Nat) ys h w ys' st (Succ d) y ny (NeGT (Succ d) h up2))
        lin nron le
        (congr-top h (Succ d) d2 up2 ys hi subl w ys' st)))
    ((HTwo _ _ _ _ dd d2 dd2 d3 dd3 x y z nx ny nz rin le1 le2 subl subr)
      (let ((erased up2)) (lt-trans h i (Succ d) up (double-lt i d dd)))
      (let ((erased up3)) (lt-trans h i (Succ (Succ d)) up (lt-weaken i (Succ d) (double-lt i d dd))))
      (HTwo ys' hi i d dd d2 dd2 d3 dd3 x y z
        (setnth-nth-diff (Nat) ys h w ys' st i x nx (NeGT i h up))
        (setnth-nth-diff (Nat) ys h w ys' st (Succ d) y ny (NeGT (Succ d) h up2))
        (setnth-nth-diff (Nat) ys h w ys' st (Succ (Succ d)) z nz (NeGT (Succ (Succ d)) h up3))
        rin le1 le2
        (congr-top h (Succ d) d2 up2 ys hi subl w ys' st)
        (congr-top h (Succ (Succ d)) d3 up3 ys hi subr w ys' st)))))

; ---- congr-sib: the write position is inside the left sibling subtree ----

; bl says h is in subtree(2mp+1); bi says i is in subtree(2mp+2). Every node of
; subtree(i) differs from h (tree.sl's sib-ne), so each Nth travels across the
; write unchanged.
(def-fns _ $ (erased congr-sib :
    (erased (Nat) mp) (erased (Nat) dp) (erased (Double mp dp) ddp)
    (erased (Nat) h) (erased (Nat) d1) (erased (Below (Succ dp) d1 h) bl)
    (erased (Nat) di) (erased (Nat) i) (erased (Below (Succ (Succ dp)) di i) bi)
    (erased (List (Nat)) ys) (erased (Nat) hi) (erased (Nat) dx) (subterm erased (HeapOn ys hi i dx) H)
    (erased (Nat) w) (erased (List (Nat)) ys') (erased (SetNth (Nat) ys h w ys') st)
    -> (erased (HeapOn ys' hi i dx) out))
  (match erased H _
    ((HLeaf _ _ _ _ ddx nl) (HLeaf ys' hi i dx ddx nl))
    ((HOne _ _ _ _ ddx d2 dd2 x y nx ny lin nron le subl)
      (let ((erased d2x) (erased dd2x)) (double (Succ dx)))
      (let ((erased ib2)) (values (BLeft i dx ddx d2x dd2x (Succ dx) (BHere (Succ dx) d2x dd2x))))
      (let ((erased bi2)) (below-trans (Succ (Succ dp)) di i bi dx (Succ dx) ib2))
      (HOne ys' hi i dx ddx d2 dd2 x y
        (setnth-nth-diff (Nat) ys h w ys' st i x nx (sib-ne mp dp ddp d1 h bl di i bi))
        (setnth-nth-diff (Nat) ys h w ys' st (Succ dx) y ny (sib-ne mp dp ddp d1 h bl di (Succ dx) bi2))
        lin nron le
        (congr-sib mp dp ddp h d1 bl di (Succ dx) bi2 ys hi d2 subl w ys' st)))
    ((HTwo _ _ _ _ ddx d2 dd2 d3 dd3 x y z nx ny nz rin le1 le2 subl subr)
      (let ((erased d2x) (erased dd2x)) (double (Succ dx)))
      (let ((erased ib2)) (values (BLeft i dx ddx d2x dd2x (Succ dx) (BHere (Succ dx) d2x dd2x))))
      (let ((erased bi2)) (below-trans (Succ (Succ dp)) di i bi dx (Succ dx) ib2))
      (let ((erased d3x) (erased dd3x)) (double (Succ (Succ dx))))
      (let ((erased ib3)) (values (BRight i dx ddx d3x dd3x (Succ (Succ dx)) (BHere (Succ (Succ dx)) d3x dd3x))))
      (let ((erased bi3)) (below-trans (Succ (Succ dp)) di i bi dx (Succ (Succ dx)) ib3))
      (HTwo ys' hi i dx ddx d2 dd2 d3 dd3 x y z
        (setnth-nth-diff (Nat) ys h w ys' st i x nx (sib-ne mp dp ddp d1 h bl di i bi))
        (setnth-nth-diff (Nat) ys h w ys' st (Succ dx) y ny (sib-ne mp dp ddp d1 h bl di (Succ dx) bi2))
        (setnth-nth-diff (Nat) ys h w ys' st (Succ (Succ dx)) z nz (sib-ne mp dp ddp d1 h bl di (Succ (Succ dx)) bi3))
        rin le1 le2
        (congr-sib mp dp ddp h d1 bl di (Succ dx) bi2 ys hi d2 subl w ys' st)
        (congr-sib mp dp ddp h d1 bl di (Succ (Succ dx)) bi3 ys hi d3 subr w ys' st)))))

; ---- congr-sib2: mirror of congr-sib (the write is in the RIGHT sibling) ----

(def-fns _ $ (erased congr-sib2 :
    (erased (Nat) mp) (erased (Nat) dp) (erased (Double mp dp) ddp)
    (erased (Nat) h) (erased (Nat) d1) (erased (Below (Succ (Succ dp)) d1 h) bl)
    (erased (Nat) di) (erased (Nat) i) (erased (Below (Succ dp) di i) bi)
    (erased (List (Nat)) ys) (erased (Nat) hi) (erased (Nat) dx) (subterm erased (HeapOn ys hi i dx) H)
    (erased (Nat) w) (erased (List (Nat)) ys') (erased (SetNth (Nat) ys h w ys') st)
    -> (erased (HeapOn ys' hi i dx) out))
  (match erased H _
    ((HLeaf _ _ _ _ ddx nl) (HLeaf ys' hi i dx ddx nl))
    ((HOne _ _ _ _ ddx d2 dd2 x y nx ny lin nron le subl)
      (let ((erased d2x) (erased dd2x)) (double (Succ dx)))
      (let ((erased ib2)) (values (BLeft i dx ddx d2x dd2x (Succ dx) (BHere (Succ dx) d2x dd2x))))
      (let ((erased bi2)) (below-trans (Succ dp) di i bi dx (Succ dx) ib2))
      (HOne ys' hi i dx ddx d2 dd2 x y
        (setnth-nth-diff (Nat) ys h w ys' st i x nx (ne-flip h i (sib-ne mp dp ddp di i bi d1 h bl)))
        (setnth-nth-diff (Nat) ys h w ys' st (Succ dx) y ny (ne-flip h (Succ dx) (sib-ne mp dp ddp di (Succ dx) bi2 d1 h bl)))
        lin nron le
        (congr-sib2 mp dp ddp h d1 bl di (Succ dx) bi2 ys hi d2 subl w ys' st)))
    ((HTwo _ _ _ _ ddx d2 dd2 d3 dd3 x y z nx ny nz rin le1 le2 subl subr)
      (let ((erased d2x) (erased dd2x)) (double (Succ dx)))
      (let ((erased ib2)) (values (BLeft i dx ddx d2x dd2x (Succ dx) (BHere (Succ dx) d2x dd2x))))
      (let ((erased bi2)) (below-trans (Succ dp) di i bi dx (Succ dx) ib2))
      (let ((erased d3x) (erased dd3x)) (double (Succ (Succ dx))))
      (let ((erased ib3)) (values (BRight i dx ddx d3x dd3x (Succ (Succ dx)) (BHere (Succ (Succ dx)) d3x dd3x))))
      (let ((erased bi3)) (below-trans (Succ dp) di i bi dx (Succ (Succ dx)) ib3))
      (HTwo ys' hi i dx ddx d2 dd2 d3 dd3 x y z
        (setnth-nth-diff (Nat) ys h w ys' st i x nx (ne-flip h i (sib-ne mp dp ddp di i bi d1 h bl)))
        (setnth-nth-diff (Nat) ys h w ys' st (Succ dx) y ny (ne-flip h (Succ dx) (sib-ne mp dp ddp di (Succ dx) bi2 d1 h bl)))
        (setnth-nth-diff (Nat) ys h w ys' st (Succ (Succ dx)) z nz (ne-flip h (Succ (Succ dx)) (sib-ne mp dp ddp di (Succ (Succ dx)) bi3 d1 h bl)))
        rin le1 le2
        (congr-sib2 mp dp ddp h d1 bl di (Succ dx) bi2 ys hi d2 subl w ys' st)
        (congr-sib2 mp dp ddp h d1 bl di (Succ (Succ dx)) bi3 ys hi d3 subr w ys' st)))))

; ---- congr-cross: the write position is in a disjoint subtree ----

; bl says m is in subtree(i0); bi says u is in subtree(i), and cross-ne's
; certificate (i0 < i <= 2*i0) makes the two subtrees disjoint: every node of
; subtree(i) differs from m, so each Nth travels across the write unchanged.
; The certificate (lt1, le2) is about the SUBTREE ROOT i and is passed down the
; walk unchanged; bu is rebuilt per node.
(def-fns _ $ (erased congr-cross :
    (erased (Nat) i0) (erased (Nat) d0) (erased (Double i0 d0) dd0)
    (erased (Nat) i) (erased (Nat) di) (erased (Lt i0 i) lt1) (erased (NatLe i d0) le2)
    (erased (Nat) dm) (erased (Nat) m) (erased (Below i0 d0 m) bm)
    (erased (Nat) u) (erased (Below i di u) bu)
    (erased (List (Nat)) ys) (erased (Nat) hi) (erased (Nat) dx)
    (subterm erased (HeapOn ys hi u dx) H)
    (erased (Nat) w) (erased (List (Nat)) ys') (erased (SetNth (Nat) ys m w ys') st)
    -> (erased (HeapOn ys' hi u dx) out))
  (match erased H _
    ((HLeaf _ _ _ _ ddx nl) (HLeaf ys' hi u dx ddx nl))
    ((HOne _ _ _ _ ddx d2 dd2 x y nx ny lin nron le subl)
      (let ((erased d2x) (erased dd2x)) (double (Succ dx)))
      (let ((erased ub2)) (values (BLeft u dx ddx d2x dd2x (Succ dx) (BHere (Succ dx) d2x dd2x))))
      (let ((erased bu2)) (below-trans i di u bu dx (Succ dx) ub2))
      (HOne ys' hi u dx ddx d2 dd2 x y
        (setnth-nth-diff (Nat) ys m w ys' st u x nx (ne-flip m u (cross-ne i0 d0 dd0 i lt1 le2 dm m bm di u bu)))
        (setnth-nth-diff (Nat) ys m w ys' st (Succ dx) y ny (ne-flip m (Succ dx) (cross-ne i0 d0 dd0 i lt1 le2 dm m bm di (Succ dx) bu2)))
        lin nron le
        (congr-cross i0 d0 dd0 i di lt1 le2 dm m bm (Succ dx) bu2 ys hi d2 subl w ys' st)))
    ((HTwo _ _ _ _ ddx d2 dd2 d3 dd3 x y z nx ny nz rin le1 le2h subl subr)
      (let ((erased d2x) (erased dd2x)) (double (Succ dx)))
      (let ((erased ub2)) (values (BLeft u dx ddx d2x dd2x (Succ dx) (BHere (Succ dx) d2x dd2x))))
      (let ((erased bu2)) (below-trans i di u bu dx (Succ dx) ub2))
      (let ((erased d3x) (erased dd3x)) (double (Succ (Succ dx))))
      (let ((erased ub3)) (values (BRight u dx ddx d3x dd3x (Succ (Succ dx)) (BHere (Succ (Succ dx)) d3x dd3x))))
      (let ((erased bu3)) (below-trans i di u bu dx (Succ (Succ dx)) ub3))
      (HTwo ys' hi u dx ddx d2 dd2 d3 dd3 x y z
        (setnth-nth-diff (Nat) ys m w ys' st u x nx (ne-flip m u (cross-ne i0 d0 dd0 i lt1 le2 dm m bm di u bu)))
        (setnth-nth-diff (Nat) ys m w ys' st (Succ dx) y ny (ne-flip m (Succ dx) (cross-ne i0 d0 dd0 i lt1 le2 dm m bm di (Succ dx) bu2)))
        (setnth-nth-diff (Nat) ys m w ys' st (Succ (Succ dx)) z nz (ne-flip m (Succ (Succ dx)) (cross-ne i0 d0 dd0 i lt1 le2 dm m bm di (Succ (Succ dx)) bu3)))
        rin le1 le2h
        (congr-cross i0 d0 dd0 i di lt1 le2 dm m bm (Succ dx) bu2 ys hi d2 subl w ys' st)
        (congr-cross i0 d0 dd0 i di lt1 le2 dm m bm (Succ (Succ dx)) bu3 ys hi d3 subr w ys' st)))))

; ---- heap-here: replacing the root's value when the new one fits ----

; Fits ys hi h dh w: w fits at node h within [0, hi): w is >= the values at h's
; children that are in range. The Nth's are on the pre-write list ys; the
; children differ from h, so ys' holds the same values there.
(def-adts
  ((Fits : ((List (Nat)) ys) ((Nat) hi) ((Nat) h) ((Nat) dh) ((Nat) w) -> Type)
    enum
    (many FitLeaf : (erased (List (Nat)) ys) (erased (Nat) hi) (erased (Nat) h) (erased (Nat) dh)
        (erased (Nat) w) (erased (Double h dh) dd) (erased (Lt hi (Succ (Succ dh))) nl)
        -> (Fits ys hi h dh w))
    (many FitOne : (erased (List (Nat)) ys) (erased (Nat) hi) (erased (Nat) h) (erased (Nat) dh)
        (erased (Nat) w) (erased (Double h dh) dd) (erased (Nat) d2) (erased (Double (Succ dh) d2) dd2)
        (erased (Nat) z) (erased (Nth (Nat) ys (Succ dh) z) nz)
        (erased (Lt (Succ dh) hi) lin) (erased (Lt hi (Succ (Succ (Succ dh)))) nron)
        (erased (NatLe z w) le) -> (Fits ys hi h dh w))
    (many FitTwo : (erased (List (Nat)) ys) (erased (Nat) hi) (erased (Nat) h) (erased (Nat) dh)
        (erased (Nat) w) (erased (Double h dh) dd) (erased (Nat) d2) (erased (Double (Succ dh) d2) dd2)
        (erased (Nat) d3) (erased (Double (Succ (Succ dh)) d3) dd3)
        (erased (Nat) z1) (erased (Nat) z2)
        (erased (Nth (Nat) ys (Succ dh) z1) nz1) (erased (Nth (Nat) ys (Succ (Succ dh)) z2) nz2)
        (erased (Lt (Succ (Succ dh)) hi) rin)
        (erased (NatLe z1 w) le1) (erased (NatLe z2 w) le2) -> (Fits ys hi h dh w))))

; The Double witness a Fits carries.
(def-fns _ $ (erased fit-dd : (erased (List (Nat)) ys) (erased (Nat) hi) (erased (Nat) h) (erased (Nat) dh)
    (erased (Nat) w) (subterm erased (Fits ys hi h dh w) f) -> (erased (Double h dh) dd))
  (match erased f _
    ((FitLeaf _ _ _ _ _ dd _) dd)
    ((FitOne _ _ _ _ _ dd _ _ _ _ _ _ _) dd)
    ((FitTwo _ _ _ _ _ dd _ _ _ _ _ _ _ _ _ _ _) dd)))

; heap-here: subtree(h) is a max-heap on ys; the write replaces ys[h] = v with w,
; where w <= v and w fits at h. Then subtree(h) is a max-heap on ys'. This is
; the base case heap-replace walks down to (and the sift loop's exit step).
(def-fns _ $ (erased heap-here :
    (erased (List (Nat)) ys) (erased (Nat) hi) (erased (Nat) h) (erased (Nat) d)
    (subterm erased (HeapOn ys hi h d) H)
    (erased (Nat) v) (erased (Nth (Nat) ys h v) nv)
    (erased (Nat) w) (erased (List (Nat)) ys') (erased (SetNth (Nat) ys h w ys') st)
    (erased (NatLe w v) lew) (erased (Fits ys hi h d w) fit)
    -> (erased (HeapOn ys' hi h d) out))
  (match erased H _
    ((HLeaf _ _ _ _ dd nl)
      (let-match erased fit (FitLeaf fys fhi fh fdh fw fdd fnl)
        (absurd (FitOne ays ahi ah adh aw afdd ad2 add2 z nz linh nronh lez) (lt-asym (Succ d) hi linh nl))
        (absurd (FitTwo ays ahi ah adh aw afdd ad2 add2 ad3 add3 z1 z2 nz1 nz2 rinh le1h le2h) (lt-asym (Succ (Succ d)) hi rinh (lt-weaken hi (Succ (Succ d)) nl))))
      (HLeaf ys' hi h d dd nl))
    ((HOne _ _ _ _ dd d2 dd2 x y nx ny lin nron le subl)
      (let-match erased fit (FitOne fys fhi fh fdh fw fdd fd2 fdd2 z nz linh nronh lez)
        (absurd (FitLeaf ays ahi ah adh aw afdd nlh) (lt-asym (Succ d) hi lin nlh))
        (absurd (FitTwo ays ahi ah adh aw afdd ad2 add2 ad3 add3 z1 z2 nz1 nz2 rinh le1h le2h) (lt-asym (Succ (Succ d)) hi rinh nron)))
      (let-match erased (nth-fn (Nat) ys (Succ d) y z ny nz) (Refl _ _))
      (HOne ys' hi h d dd d2 dd2 w y
        (setnth-nth (Nat) ys h w ys' st)
        (setnth-nth-diff (Nat) ys h w ys' st (Succ d) y ny (NeGT (Succ d) h (double-lt h d dd)))
        lin nron lez
        (congr-top h (Succ d) d2 (double-lt h d dd) ys hi subl w ys' st)))
    ((HTwo _ _ _ _ dd d2 dd2 d3 dd3 x y z nx ny nz rin le1 le2 subl subr)
      (let-match erased fit (FitTwo fys fhi fh fdh fw fdd fd2 fdd2 fd3 fdd3 z1 z2 nz1 nz2 rinh le1h le2h)
        (absurd (FitLeaf ays ahi ah adh aw afdd nlh) (lt-asym (Succ (Succ d)) hi rin (lt-weaken hi (Succ (Succ d)) nlh)))
        (absurd (FitOne ays ahi ah adh aw afdd ad2 add2 z0 nz0 linh nronh lez0) (lt-asym (Succ (Succ d)) hi rin nronh)))
      (let-match erased (nth-fn (Nat) ys (Succ d) y z1 ny nz1) (Refl _ _))
      (let-match erased (nth-fn (Nat) ys (Succ (Succ d)) z z2 nz nz2) (Refl _ _))
      (HTwo ys' hi h d dd d2 dd2 d3 dd3 w y z
        (setnth-nth (Nat) ys h w ys' st)
        (setnth-nth-diff (Nat) ys h w ys' st (Succ d) y ny (NeGT (Succ d) h (double-lt h d dd)))
        (setnth-nth-diff (Nat) ys h w ys' st (Succ (Succ d)) z nz (NeGT (Succ (Succ d)) h (lt-weaken h (Succ d) (double-lt h d dd))))
        rin le1h le2h
        (congr-top h (Succ d) d2 (double-lt h d dd) ys hi subl w ys' st)
        (congr-top h (Succ (Succ d)) d3 (lt-weaken h (Succ d) (double-lt h d dd)) ys hi subr w ys' st)))))

; ---- heap-replace: changing one node's value keeps the subtree a heap ----

; heap-replace: subtree(i) is a max-heap on ys; h is at or below i (Lt h hi);
; the write replaces ys[h] = v with w, where w <= v and w fits at h. Then
; subtree(i) is a max-heap on ys', and the new value at i is <= the old one
; (returned so each caller can re-establish its parent edge).
(def-fns _ $ (erased heap-replace :
    (erased (List (Nat)) ys) (erased (Nat) hi) (erased (Nat) i) (erased (Nat) d)
    (subterm erased (HeapOn ys hi i d) H)
    (erased (Nat) dh) (erased (Nat) h) (erased (Below i d h) b) (erased (Lt h hi) hlt)
    (erased (Nat) v) (erased (Nth (Nat) ys h v) nv)
    (erased (Nat) w) (erased (List (Nat)) ys') (erased (SetNth (Nat) ys h w ys') st)
    (erased (NatLe w v) lew) (erased (Fits ys hi h dh w) fit)
    ->
    (erased (HeapOn ys' hi i d) out) (erased (Nat) w2) (erased (Nth (Nat) ys' i w2) nw2)
    (erased (Nat) v2) (erased (Nth (Nat) ys i v2) nv2) (erased (NatLe w2 v2) le2))
  (let-match erased b (BLeft _ _ ddx d2b dd2b _ bel)
    ((BRight _ _ ddx d3b dd3b _ bel)
      (let-match erased H (HTwo _ _ _ _ _ d2 dd2 d3 dd3 x y z nx ny nz rin le1 le2 subl subr)
        (absurd (HLeaf _ _ _ _ _ nl) (let-match erased (below-ge (Succ (Succ d)) d3b h bel) (MkNatLe _ _ gl)) (lt-asym h (Succ (Succ d)) (lt-weaken h (Succ d) (lt-le-trans h hi (Succ d) hlt nl)) gl))
        (absurd (HOne _ _ _ _ _ _ _ x y nx ny lin nron le subl) (let-match erased (below-ge (Succ (Succ d)) d3b h bel) (MkNatLe _ _ gl)) (lt-asym h (Succ (Succ d)) (lt-le-trans h hi (Succ (Succ d)) hlt nron) gl)))
      (let-match erased (double-fn (Succ (Succ d)) d3 d3b dd3 dd3b) (Refl _ _))
      (let ((erased ih) (erased w2) (erased nw2) (erased v2) (erased nv2) (erased lei))
        (heap-replace ys hi (Succ (Succ d)) d3 subr dh h bel hlt v nv w ys' st lew fit))
      (let-match erased (nth-fn (Nat) ys (Succ (Succ d)) z v2 nz nv2) (Refl _ _))
      (let-match erased (below-ge (Succ (Succ d)) d3b h bel) (MkNatLe _ _ glr))
      (let ((erased nxl)) (setnth-nth-diff (Nat) ys h w ys' st i x nx (NeLO i h (lt-le-trans i (Succ (Succ d)) h (lt-weaken i (Succ d) (double-lt i d ddx)) glr))))
      (let ((erased nyl)) (setnth-nth-diff (Nat) ys h w ys' st (Succ d) y ny (NeLO (Succ d) h (lt-le-trans (Succ d) (Succ (Succ d)) h (lt-succ (Succ d)) glr))))
      (let ((erased bil)) (BHere (Succ d) d2 dd2))
      (values (HTwo ys' hi i d ddx d2 dd2 d3 dd3 x y w2 nxl nyl nw2 rin le1 (le-trans w2 z x lei le2) (congr-sib2 i d ddx h d3b bel d2 (Succ d) bil ys hi d2 subl w ys' st) ih) x nxl x nx (le-refl x)))
    ((BHere _ _ ddb)
      (let-match erased (double-fn h d dh ddb (fit-dd ys hi h dh w fit)) (Refl _ _))
      (values (heap-here ys hi h d H v nv w ys' st lew fit) w (setnth-nth (Nat) ys h w ys' st) v nv lew)))
  (let-match erased H (HOne _ _ _ _ _ d2 dd2 x y nx ny lin nron le subl)
    ((HTwo _ _ _ _ _ d2h dd2h d3 dd3 x y z nx ny nz rin le1 le2 subl subr)
      (let-match erased (double-fn (Succ d) d2h d2b dd2h dd2b) (Refl _ _))
      (let ((erased ih) (erased w2) (erased nw2) (erased v2) (erased nv2) (erased lei))
        (heap-replace ys hi (Succ d) d2h subl dh h bel hlt v nv w ys' st lew fit))
      (let-match erased (nth-fn (Nat) ys (Succ d) y v2 ny nv2) (Refl _ _))
      (let-match erased (below-ge (Succ d) d2b h bel) (MkNatLe _ _ gll))
      (let ((erased nxl)) (setnth-nth-diff (Nat) ys h w ys' st i x nx (NeLO i h (lt-le-trans i (Succ d) h (double-lt i d ddx) gll))))
      (let ((erased bil)) (BHere (Succ (Succ d)) d3 dd3))
      (let ((erased nzl)) (setnth-nth-diff (Nat) ys h w ys' st (Succ (Succ d)) z nz (sib-ne i d ddx d2b h bel d3 (Succ (Succ d)) (BHere (Succ (Succ d)) d3 dd3))))
      (values (HTwo ys' hi i d ddx d2h dd2h d3 dd3 x w2 z nxl nw2 nzl rin (le-trans w2 y x lei le1) le2 ih (congr-sib i d ddx h d2b bel d3 (Succ (Succ d)) bil ys hi d3 subr w ys' st)) x nxl x nx (le-refl x)))
    (absurd (HLeaf _ _ _ _ _ nl) (let-match erased (below-ge (Succ d) d2b h bel) (MkNatLe _ _ gl)) (lt-asym h (Succ d) (lt-le-trans h hi (Succ d) hlt nl) gl)))
  (let-match erased (double-fn (Succ d) d2 d2b dd2 dd2b) (Refl _ _))
  (let ((erased ih) (erased w2) (erased nw2) (erased v2) (erased nv2) (erased lei))
    (heap-replace ys hi (Succ d) d2 subl dh h bel hlt v nv w ys' st lew fit))
  (let-match erased (nth-fn (Nat) ys (Succ d) y v2 ny nv2) (Refl _ _))
  (let-match erased (below-ge (Succ d) d2b h bel) (MkNatLe _ _ gll))
  (let ((erased nxl)) (setnth-nth-diff (Nat) ys h w ys' st i x nx (NeLO i h (lt-le-trans i (Succ d) h (double-lt i d ddx) gll))))
  (values (HOne ys' hi i d ddx d2 dd2 x w2 nxl nw2 lin nron (le-trans w2 y x lei le) ih) x nxl x nx (le-refl x)))
