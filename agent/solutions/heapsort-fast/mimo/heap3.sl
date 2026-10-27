; work/heap3.sl: extraction plumbing (milestone 3). All erased; nothing here
; runs. It sits after work/heap2.sl and before work/loops.sl.
;
; Contents:
;   - le-of-ge / split-nth-below / split-write / rangele-write: transporting a
;     Split and a RangeLe across one in-range write (the sift keeps the sorted
;     suffix untouched; only the prefix is rewritten).
;   - ext-plumb-tail / ext-plumb: the extraction swap's prefix bookkeeping
;     (swap positions 0 and k of a heap region [0, k+1)).
;   - asc-head: the growing sorted suffix (Cons x ss) from the range fact.
;   - kids-after-swap: the sift's entry Kids, from the pre-swap heap.
;   - split-full / rangele-nil: the empty-suffix initial state.
;   - shift-one-lt: the shift bound for one `u62-shr ... 1`.

; ---- small conversions ----

; A GE reads as a NatLe in the other direction.
(def-fns _ $ (erased le-of-ge : (erased (Nat) a) (erased (Nat) b) (subterm erased (GE a b) g) -> (erased (NatLe b a) out))
  (let-match erased g (MkGE _ _ p))
  (MkNatLe b a p))

; ---- Split / RangeLe across a write ----

; A read below the split position is a read of the prefix.
(def-fns _ $ (erased split-nth-below : (erased (List (Nat)) ys) (erased (Nat) i) (erased (List (Nat)) ps)
    (erased (List (Nat)) ss) (subterm erased (Split ys i ps ss) spl) (erased (Nat) j) (erased (Nat) w)
    (erased (Nth (Nat) ys j w) nt) (erased (Lt j i) jlt) -> (erased (Nth (Nat) ps j w) out))
  (let-match erased spl (SpCons x rest j0 ps1 ss1 spl1)
    ((SpNil _) (match erased jlt _)))
  (let-match erased nt (NthThere _ _ _ j1 _ nt1)
    ((NthHere _ _ _) (NthHere (Nat) x ps1)))
  (let-match erased jlt (LtS _ _ jlt1))
  (NthThere (Nat) x ps1 j1 w (split-nth-below rest j0 ps1 ss1 spl1 j1 w nt1 jlt1)))

; A write below the split position rewrites the prefix and leaves the suffix.
(def-fns _ $ (erased split-write : (erased (List (Nat)) ys) (erased (Nat) i) (erased (List (Nat)) ps)
    (erased (List (Nat)) ss) (subterm erased (Split ys i ps ss) spl) (erased (Nat) h) (erased (Nat) w)
    (erased (List (Nat)) ys2) (erased (SetNth (Nat) ys h w ys2) st) (erased (Lt h i) hlt)
    ->
    (erased (List (Nat)) ps2) (erased (SetNth (Nat) ps h w ps2) sp) (erased (Split ys2 i ps2 ss) out))
  (let-match erased spl (SpCons x rest j ps1 ss1 spl1)
    ((SpNil _) (match erased hlt _)))
  (let-match erased st (SetThere _ hd restx h1 _ ysx st1)
    ((SetHere _ x0 w0 resth)
      (values (Cons (Nat) w ps1) (SetHere (Nat) x0 w ps1) (SpCons w rest j ps1 ss1 spl1))))
  (let-match erased hlt (LtS _ _ hlt1))
  (let ((erased psx) (erased spx) (erased outx)) (split-write rest j ps1 ss1 spl1 h1 w ysx st1 hlt1))
  (values (Cons (Nat) hd psx) (SetThere (Nat) hd ps1 h1 w psx spx) (SpCons hd ysx j psx ss1 outx)))

; A write whose value is below the whole suffix keeps the range fact.
(def-fns _ $ (erased rangele-write : (erased (List (Nat)) ps) (erased (List (Nat)) ss)
    (erased (RangeLe ps ss) rl) (erased (Nat) h) (erased (Nat) w) (erased (List (Nat)) ps2)
    (subterm erased (SetNth (Nat) ps h w ps2) st) (erased (AllTo (Nat) GE ss w) gw)
    -> (erased (RangeLe ps2 ss) out))
  (let-match erased st (SetThere _ hd rest h1 _ psx st1)
    ((SetHere _ x0 w0 resth)
      (let-match erased rl (RLCons _ _ _ hd0 rest0))
      (RLCons w resth ss gw rest0)))
  (let-match erased rl (RLCons _ _ _ hd1 rest1))
  (RLCons hd psx ss hd1 (rangele-write rest ss rest1 h1 w psx st1 gw)))

; ---- the extraction swap's prefix bookkeeping ----

; The tail of the swap: writing x at the LAST prefix position k peels the
; prefix by one (its old last value w) and grows the suffix by one (x).
(def-fns _ $ (erased ext-plumb-tail : (erased (List (Nat)) ys) (erased (Nat) k) (erased (Nat) x) (erased (Nat) w)
    (erased (Nth (Nat) ys k w) nw) (erased (List (Nat)) ws2) (subterm erased (SetNth (Nat) ys k x ws2) s2)
    (erased (List (Nat)) ps) (erased (List (Nat)) ss) (erased (Split ys (Succ k) ps ss) spl)
    ->
    (erased (List (Nat)) psn) (erased (Snoc psn w ps) sns) (erased (Split ws2 k psn (Cons (Nat) x ss)) out))
  (let-match erased s2 (SetThere _ hd tail1 k1 xv ws2t s2p)
    ((SetHere _ a xv0 rest0)
      (let-match erased nw (NthHere _ _ _) (absurd NthThere))
      (let-match erased spl (SpCons _ _ _ _ _ sp1) (absurd SpNil))
      (let-match erased sp1 (SpNil _))
      (values (Nil (Nat)) (SnNil w) (SpNil (Cons (Nat) x rest0)))))
  (let-match erased nw (NthThere _ _ _ _ _ nwp) (absurd NthHere))
  (let-match erased spl (SpCons _ _ _ psx ssx sp1) (absurd SpNil))
  (let ((erased psn1) (erased sns1) (erased out1)) (ext-plumb-tail tail1 k1 x w nwp ws2t s2p psx ssx sp1))
  (values (Cons (Nat) hd psn1) (SnCons hd psn1 w psx sns1) (SpCons hd ws2t k1 psn1 (Cons (Nat) x ssx) out1)))

; The extraction swap: ys[0] = x and ys[k] = w are exchanged (k >= 1); the
; prefix loses x and gains w at the front, the suffix grows by x at the front.
(def-fns _ $ (erased ext-plumb : (erased (List (Nat)) ys) (erased (Nat) x) (erased (Nth (Nat) ys (Zero) x) nx)
    (erased (Nat) k1) (erased (Nat) w) (erased (Nth (Nat) ys (Succ k1) w) nw)
    (erased (List (Nat)) ws1) (erased (SetNth (Nat) ys (Zero) w ws1) s1)
    (erased (List (Nat)) ws2) (erased (SetNth (Nat) ws1 (Succ k1) x ws2) s2)
    (erased (List (Nat)) ps) (erased (List (Nat)) ss) (erased (Split ys (Succ (Succ k1)) ps ss) spl)
    ->
    (erased (List (Nat)) psp) (erased (List (Nat)) ps2) (erased (Snoc psp w ps) sns)
    (erased (SetNth (Nat) psp (Zero) w ps2) st) (erased (Split ws2 (Succ k1) ps2 (Cons (Nat) x ss)) out))
  (let-match erased s1 (SetHere _ y0 w0 tail2) (absurd SetThere))
  (let-match erased s2 (SetThere _ hd tail1 kk xv ws2t s2p) (absurd SetHere))
  (let-match erased nw (NthThere _ _ _ _ _ nwp) (absurd NthHere))
  (let-match erased spl (SpCons _ _ _ psx ssx sp1) (absurd SpNil))
  (let ((erased psn1) (erased sns1) (erased out1)) (ext-plumb-tail tail1 kk x w nwp ws2t s2p psx ssx sp1))
  (values (Cons (Nat) y0 psn1) (Cons (Nat) hd psn1) (SnCons y0 psn1 w psx sns1)
    (SetHere (Nat) y0 hd psn1) (SpCons hd ws2t kk psn1 (Cons (Nat) x ssx) out1)))

; ---- the growing sorted suffix ----

; The head x of the new suffix is above the old suffix's head (the range fact
; at the prefix's head), so Cons x ss is ascending whenever ss is.
(def-fns _ $ (erased asc-head : (erased (Nat) x) (erased (List (Nat)) ps) (erased (List (Nat)) ss)
    (erased (RangeLe (Cons (Nat) x ps) ss) rl) (subterm erased (Ascending (Nat) NatLe ss) asc)
    -> (erased (Ascending (Nat) NatLe (Cons (Nat) x ss)) out))
  (let-match erased asc (AscCons _ _ s0 s1 rest2 le12 asc1)
    ((AscNil _ _) (AscOne (Nat) NatLe x))
    ((AscOne _ _ s0b)
      (let-match erased rl (RLCons _ _ _ hd0 _))
      (let-match erased hd0 (AllToCons _ _ _ _ _ g0 _))
      (AscCons (Nat) NatLe x s0b (Nil (Nat)) (le-of-ge s0b x g0) asc)))
  (let-match erased rl (RLCons _ _ _ hd restl))
  (let-match erased hd (AllToCons _ _ _ _ _ g0 _))
  (AscCons (Nat) NatLe x s0 (Cons (Nat) s1 rest2) (le-of-ge s0 x g0) asc))

; ---- the sift's entry Kids after the root swap ----

; The pre-swap heap on [0, k+1), shrunk to [0, k), transported across the swap's
; two writes (at 0 and at k = the bound), is the Kids record sift-entry wants.
(def-fns _ $ (erased kids-after-swap : (erased (List (Nat)) ys) (erased (Nat) k)
    (erased (HeapOn ys (Succ k) (Zero) (Zero)) heap)
    (erased (Nat) w) (erased (List (Nat)) ws1) (erased (SetNth (Nat) ys (Zero) w ws1) s1)
    (erased (Nat) x) (erased (List (Nat)) ws2) (erased (SetNth (Nat) ws1 k x ws2) s2)
    -> (erased (Kids ws2 k (Zero) (Zero)) out))
  (let ((erased shrunk))
    (heap-shrink k (Succ k) (MkNatLe k (Succ k) (lt-weaken k (Succ k) (lt-succ k))) ys (Zero) (Zero) heap))
  (let-match erased shrunk (HTwo _ _ _ _ dd d2 dd2 d3 dd3 x0 y0 z0 nx0 ny0 nz0 rin le1 le2 subl subr)
    ((HLeaf _ _ _ _ ddh nlh) (KLeaf ws2 k (Zero) (Zero) ddh nlh))
    ((HOne _ _ _ _ ddh d2h dd2h xh yh nxh nyh linh nronh leh sublh)
      (let ((erased ny1))
        (setnth-nth-diff (Nat) ys (Zero) w ws1 s1 (Succ (Zero)) yh nyh (NeGT (Succ (Zero)) (Zero) (LtZ (Zero)))))
      (let ((erased ny2)) (setnth-nth-diff (Nat) ws1 k x ws2 s2 (Succ (Zero)) yh ny1 (NeLO (Succ (Zero)) k linh)))
      (let ((erased subl1)) (congr-top (Zero) (Succ (Zero)) d2h (LtZ (Zero)) ys k sublh w ws1 s1))
      (let ((erased subl2)) (congr-out k k (MkNatLe k k (lt-succ k)) ws1 (Succ (Zero)) d2h subl1 x ws2 s2))
      (KOne ws2 k (Zero) (Zero) ddh d2h dd2h yh ny2 linh nronh subl2)))
  (let ((erased ny1))
    (setnth-nth-diff (Nat) ys (Zero) w ws1 s1 (Succ (Zero)) y0 ny0 (NeGT (Succ (Zero)) (Zero) (LtZ (Zero)))))
  (let ((erased nz1))
    (setnth-nth-diff (Nat) ys (Zero) w ws1 s1 (Succ (Succ (Zero))) z0 nz0 (NeGT (Succ (Succ (Zero))) (Zero) (LtZ (Succ (Zero))))))
  (let ((erased one-lt)) (lt-trans (Succ (Zero)) (Succ (Succ (Zero))) k (lt-succ (Succ (Zero))) rin))
  (let ((erased ny2)) (setnth-nth-diff (Nat) ws1 k x ws2 s2 (Succ (Zero)) y0 ny1 (NeLO (Succ (Zero)) k one-lt)))
  (let ((erased nz2)) (setnth-nth-diff (Nat) ws1 k x ws2 s2 (Succ (Succ (Zero))) z0 nz1 (NeLO (Succ (Succ (Zero))) k rin)))
  (let ((erased subl1)) (congr-top (Zero) (Succ (Zero)) d2 (LtZ (Zero)) ys k subl w ws1 s1))
  (let ((erased subl2)) (congr-out k k (MkNatLe k k (lt-succ k)) ws1 (Succ (Zero)) d2 subl1 x ws2 s2))
  (let ((erased subr1)) (congr-top (Zero) (Succ (Succ (Zero))) d3 (LtZ (Succ (Zero))) ys k subr w ws1 s1))
  (let ((erased subr2)) (congr-out k k (MkNatLe k k (lt-succ k)) ws1 (Succ (Succ (Zero))) d3 subr1 x ws2 s2))
  (KTwo ws2 k (Zero) (Zero) dd d2 dd2 d3 dd3 y0 z0 ny2 nz2 rin subl2 subr2))

; ---- the empty-suffix initial state ----

; The whole list is the prefix at its own length.
(def-fns _ $ (erased split-full : (erased (List (Nat)) ys) (erased (Nat) n) (subterm erased (Length (Nat) ys n) ly)
    -> (erased (Split ys n ys (Nil (Nat))) out))
  (let-match erased ly (LengthCons _ y rest n1 ly1)
    ((LengthNil _) (SpNil (Nil (Nat)))))
  (SpCons y rest n1 rest (Nil (Nat)) (split-full rest n1 ly1)))

; Everything is below the empty suffix.
(def-fns _ $ (erased rangele-nil : (subterm erased (List (Nat)) ps) -> (erased (RangeLe ps (Nil (Nat))) out))
  (match erased ps _
    ((Nil _) (RLNil (Nil (Nat))))
    ((Cons _ hd tl) (RLCons hd tl (Nil (Nat)) (AllToNil (Nat) GE hd) (rangele-nil tl)))))

; ---- the shift bound for one `u62-shr` by 1 ----

; sixty-two is opaque to the checker; add-2 pins it to (Succ (Succ sixty)) so
; the one-step bound is a constructor chain. `unary 1` makes the numeral 1
; usable where a `Succ` shape is wanted.
(unary 1)
(def-fns _ $ (erased shift-one-lt : -> (erased (Lt (Succ (Zero)) (Succ sixty-two)) q))
  (let-match erased (add-2 sixty sixty-two sixty-two-add) (Refl _ _))
  (LtS (Zero) (Succ (Succ sixty)) (LtZ (Succ sixty))))
