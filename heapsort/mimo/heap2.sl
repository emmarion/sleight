; work/heap2.sl: ghost utilities for the heapsort loops (milestone 3). All erased;
; nothing here runs. It sits after work/heap.sl and before work/loops.sl.
;
; Contents:
;   - SetNth plumbing: setnth-of-nth / setnth-back / setnth-overwrite / setnth-nth-inv.
;   - order and Double helpers: le-lt-trans / max2 / double-add.
;   - the `h < hi/2` child-range arithmetic from one `u62-shr hi 1` call: pow2-1 /
;     add-2 / mul2-double / double-le / add-small / add-swap-lt, Hf + hf-of,
;     half-in / half-out.
;   - heap utilities: heap-dd / hleaf-below / heap-below / heap-shrink / congr-out /
;     heap-le-root.
;   - extraction plumbing: below-zero / split-head / split-snoc / heap-max /
;     allto-snoc / rangele-snoc / rangele-at / rangele-ext.

; ---- SetNth utilities ----

; Writing v at the position of a read: the result list and the set proof.
(def-fns _ $ (erased setnth-of-nth : (erased Type A) (erased (List A) xs) (erased (Nat) i) (erased A x)
    (subterm erased (Nth A xs i x) nt) (erased A v)
    -> (erased (List A) ys) (erased (SetNth A xs i v ys) st))
  (let-match erased nt (NthThere _ hd rest i1 x1 nt1)
    ((NthHere _ xh rh) (values (Cons A v rh) (SetHere A xh v rh))))
  (let ((erased ys1) (erased st1)) (setnth-of-nth A rest i1 x1 nt1 v))
  (values (Cons A hd ys1) (SetThere A hd rest i1 v ys1 st1)))

; Undoing a write with the value that was read there first.
(def-fns _ $ (erased setnth-back : (erased Type A) (erased (List A) xs) (erased (Nat) i) (erased A v)
    (erased (List A) ys) (subterm erased (SetNth A xs i v ys) st) (erased A x) (erased (Nth A xs i x) nt)
    -> (erased (SetNth A ys i x xs) out))
  (let-match erased st (SetThere _ hd rest i1 v1 rest2 st1)
    ((SetHere _ x0 v0 resth)
      (let-match erased nt (NthHere _ _ _) (absurd NthThere))
      (SetHere A v0 x resth)))
  (let-match erased nt (NthThere _ _ _ j1 _ nt1) (absurd NthHere))
  (SetThere A hd rest2 i1 x rest (setnth-back A rest i1 v rest2 st1 x nt1)))

; Two writes at one position: the first is undone by the second.
(def-fns _ $ (erased setnth-overwrite : (erased Type A) (erased (List A) xs) (erased (Nat) i)
    (erased A a) (erased (List A) ys) (subterm erased (SetNth A xs i a ys) st1)
    (erased A b) (erased (List A) zs) (erased (SetNth A ys i b zs) st2)
    -> (erased (SetNth A xs i b zs) out))
  (let-match erased st1 (SetThere _ hd rest i1 a1 rest2 st1x)
    ((SetHere _ x0 a0 resth)
      (let-match erased st2 (SetHere _ _ _ _) (absurd SetThere))
      (SetHere A x0 b resth)))
  (let-match erased st2 (SetThere _ hd2 rest2x i2 b2 zs2 st2x) (absurd SetHere))
  (SetThere A hd rest i1 b zs2 (setnth-overwrite A rest i1 a rest2 st1x b zs2 st2x)))

; Reading back across a write at a different position.
(def-fns _ $ (erased setnth-nth-inv : (erased Type A) (erased (List A) xs) (erased (Nat) i) (erased A y)
    (erased (List A) ys) (subterm erased (SetNth A xs i y ys) st) (erased (Nat) j) (erased A x)
    (erased (Nth A ys j x) nt) (erased (Ne j i) ne) -> (erased (Nth A xs j x) out))
  (let-match erased st (SetThere _ hd rest i1 y1 rest2 st1)
    ((SetHere _ x0 y0 resth)
      (let-match erased nt (NthThere _ _ _ j1 _ nt1)
        (absurd (NthHere _ _ _)
          (match erased ne _
            (absurd (NeLO _ _ p) (match erased p _))
            (absurd (NeGT _ _ q2) (match erased q2 _)))))
      (NthThere A x0 resth j1 x nt1)))
  (let-match erased nt (NthThere _ _ _ j1 _ nt1)
    ((NthHere _ _ _) (NthHere A hd rest)))
  (let ((erased ne1)) (ne-pred j1 i1 ne))
  (NthThere A hd rest j1 x (setnth-nth-inv A rest i1 y rest2 st1 j1 x nt1 ne1)))

; ---- order and Double helpers ----

(def-fns _ $ (erased le-lt-trans : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c)
    (subterm erased (Le a b) le) (erased (Lt b c) q) -> (erased (Lt a c) r))
  (let-match erased le (MkLe _ _ lp))
  (lt-le-trans a (Succ b) c lp (LtS b c q)))

(def-fns _ $ (erased max2 : (erased (Nat) a) (erased (Nat) b) ->
    (erased (Nat) c) (erased (Le a c) la) (erased (Le b c) lb))
  (let ((erased t)) (tri a b))
  (let-match erased t (TriE _ _ e)
    ((TriL _ _ p) (values b (le-of-lt a b p) (le-refl b)))
    ((TriG _ _ q) (values a (le-refl a) (le-of-lt b a q))))
  (let-match erased e (Refl _ _))
  (values a (le-refl a) (le-refl a)))

(def-fns _ $ (erased double-add : (erased (Nat) a) (erased (Nat) b) (subterm erased (Double a b) dd)
    -> (erased (Add a a b) p))
  (match erased dd _
    ((D0) (AddZero (Zero)))
    ((DS a1 b1 d1) (AddSucc a1 (Succ a1) (Succ b1) (add-succ-right a1 a1 b1 (double-add a1 b1 d1))))))

; ---- the `h < hi/2` child-range arithmetic ----

(def-fns _ $ (erased pow2-1 : (erased (Nat) v) (subterm erased (Pow2 (Succ (Zero)) v) p)
    -> (erased (Eq (Nat) v (Succ (Succ (Zero)))) e))
  (let-match erased p (PS k1 v1 w p1 d)
    (absurd P0))
  (let-match erased p1 (P0))
  (let-match erased d (DS _ _ d1))
  (let-match erased d1 (D0))
  (Refl (Nat) v))

(def-fns _ $ (erased add-2 : (erased (Nat) a) (erased (Nat) b) (subterm erased (Add a (Succ (Succ (Zero))) b) p)
    -> (erased (Eq (Nat) b (Succ (Succ a))) e))
  (let-match erased p (AddSucc a1 two b1 q)
    ((AddZero _)
      (Refl (Nat) (Succ (Succ (Zero))))))
  (let ((erased e1)) (add-2 a1 b1 q))
  (let-match erased e1 (Refl _ _))
  (Refl (Nat) b))

(def-fns _ $ (erased mul2-double : (erased (Nat) a) (erased (Nat) b)
    (subterm erased (Mul a (Succ (Succ (Zero))) b) mm) -> (erased (Double a b) dd))
  (let-match erased mm (MulSucc a1 two c1 d1 mm1 pp)
    ((MulZero _) (D0)))
  (let-match erased (add-2 c1 d1 pp) (Refl _ _))
  (DS a1 c1 (mul2-double a1 c1 mm1)))

(def-fns _ $ (erased double-le : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Nat) d)
    (subterm erased (Le a b) le) (erased (Double a c) pac) (erased (Double b d) pbd) -> (erased (Le c d) out))
  (let-match erased le (MkLe _ _ lp))
  (let ((erased t)) (tri a b))
  (let-match erased t (TriE _ _ e)
    ((TriL _ _ p) (MkLe c d (lt-weaken c d (double-mono a b c d p pac pbd))))
    (absurd (TriG _ _ q) (lt-asym b a q lp)))
  (let-match erased e (Refl _ _))
  (let-match erased (double-fn a c d pac pbd) (Refl _ _))
  (MkLe c d (lt-succ c)))

(def-fns _ $ (erased add-small : (erased (Nat) m) (erased (Nat) r) (erased (Nat) hi)
    (subterm erased (Add m r hi) ad) (erased (Lt r (Succ (Succ (Zero)))) rl)
    -> (erased (Lt hi (Succ (Succ m))) out))
  (let-match erased ad (AddSucc m1 r1 hi1 q)
    ((AddZero _) rl))
  (LtS hi1 (Succ (Succ m1)) (add-small m1 r hi1 q rl)))

(def-fns _ $ (erased add-swap-lt : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c)
    (erased (Nat) a2) (erased (Nat) b2) (subterm erased (Add a b c) p) (erased (Add a2 b2 c) q)
    (erased (Lt a a2) t) -> (erased (Lt b2 b) out))
  (let-match erased p (AddSucc a1 b1 c1 p1)
    ((AddZero _) (add-pos-lt b2 a2 b (add-comm a2 b2 b q) t)))
  (let-match erased q (AddSucc a21 b21 c21 q1)
    (absurd (AddZero _) (match erased t _)))
  (let-match erased t (LtS _ _ t1))
  (add-swap-lt a1 b c1 a21 b21 p1 q1 t1))

; Hf hi q: the ghost of one `u62-shr hi 1` call: hi = 2q + r with r < 2.
(def-adts
  ((Hf : ((Nat) hi) ((Nat) q) -> Type)
    enum
    (many MkHf : (erased (Nat) hi) (erased (Nat) q) (erased (Nat) m) (erased (Mul q (Succ (Succ (Zero))) m) mm)
        (erased (Nat) r) (erased (Add m r hi) ad) (erased (Lt r (Succ (Succ (Zero)))) rl)
        (erased (Lt q u62-modulus) pq) -> (Hf hi q))))

(def-fns _ $ (erased hf-of : (erased (Nat) hi) (erased (Nat) v) (subterm erased (Pow2 (Succ (Zero)) v) pv)
    (erased (Nat) q) (erased (Nat) m) (erased (Mul q v m) mm) (erased (Nat) r) (erased (Add m r hi) ad)
    (erased (Lt r v) rl) (erased (Lt q u62-modulus) pq) -> (erased (Hf hi q) out))
  (let-match erased (pow2-1 v pv) (Refl _ _))
  (MkHf hi q m mm r ad rl pq))

; h < hi/2 implies the left child 2h+1 is in range.
(def-fns _ $ (erased half-in : (erased (Nat) hi) (erased (Nat) q) (subterm erased (Hf hi q) hf)
    (erased (Nat) h) (erased (Nat) dh) (erased (Double h dh) ddh) (erased (Lt h q) hh)
    -> (erased (Lt (Succ dh) hi) out))
  (let-match erased hf (MkHf _ _ m mm r ad rl pq))
  (let ((erased mq)) (mul2-double q m mm))
  (let ((erased lem)) (double-le (Succ h) q (Succ (Succ dh)) m (MkLe (Succ h) q (LtS h q hh)) (DS h dh ddh) mq))
  (let ((erased big)) (le-trans (Succ (Succ dh)) m hi lem (MkLe m hi (add-le-left m r hi ad))))
  (let-match erased big (MkLe _ _ bigp))
  (let-match erased bigp (LtS _ _ big1))
  big1)

; h >= hi/2 implies no child is in range.
(def-fns _ $ (erased half-out : (erased (Nat) hi) (erased (Nat) q) (subterm erased (Hf hi q) hf)
    (erased (Nat) h) (erased (Nat) dh) (erased (Double h dh) ddh) (erased (Lt q (Succ h)) qh)
    -> (erased (Lt hi (Succ (Succ dh))) out))
  (let-match erased hf (MkHf _ _ m mm r ad rl pq))
  (let ((erased mq)) (mul2-double q m mm))
  (let ((erased lem)) (double-le q h m dh (MkLe q h qh) mq ddh))
  (let ((erased sm)) (add-small m r hi ad rl))
  (let-match erased lem (MkLe _ _ lp))
  (lt-le-trans hi (Succ (Succ m)) (Succ (Succ dh)) sm
    (LtS (Succ m) (Succ (Succ dh)) (LtS m (Succ dh) lp))))

; ---- heap utilities ----

; The Double witness a HeapOn carries.
(def-fns _ $ (erased heap-dd : (erased (List (Nat)) ys) (erased (Nat) hi) (erased (Nat) i) (erased (Nat) d)
    (subterm erased (HeapOn ys hi i d) H) -> (erased (Double i d) dd))
  (match erased H _
    ((HLeaf _ _ _ _ dd _) dd)
    ((HOne _ _ _ _ dd _ _ _ _ _ _ _ _ _ _) dd)
    ((HTwo _ _ _ _ dd d2 dd2 d3 dd3 x y z nx ny nz rin le1 le2 subl subr) dd)))

; hi <= j: node j sits at or past the bound, so it is a leaf there.
(def-fns _ $ (erased hleaf-below : (erased (Nat) hi) (erased (Nat) j) (erased (Nat) dj)
    (erased (Double j dj) ddj) (subterm erased (Le hi j) le) -> (erased (Lt hi (Succ (Succ dj))) out))
  (let-match erased (le-trans hi j (Succ dj) le (MkLe j (Succ dj) (lt-weaken j (Succ dj) (double-lt j dj ddj)))) (MkLe _ _ outl))
  outl)

(def-fns _ $ (erased le-of-nl : (erased (Nat) hi) (erased (Nat) i) (erased (Nat) d)
    (erased (Lt hi (Succ (Succ d))) nl) (erased (Nat) d2) (erased (Nat) j) (erased (Le (Succ d) j) gl)
    -> (erased (Le hi j) out))
  (le-trans hi (Succ d) j (MkLe hi (Succ d) nl) gl))

(def-fns _ $ (erased le-of-nl2 : (erased (Nat) hi) (erased (Nat) i) (erased (Nat) d)
    (erased (Lt hi (Succ (Succ d))) nl) (erased (Nat) d3) (erased (Nat) j) (erased (Le (Succ (Succ d)) j) gl)
    -> (erased (Le hi j) out))
  (let-match erased gl (MkLe _ _ glp))
  (MkLe hi j (lt-weaken hi j (lt-le-trans hi (Succ (Succ d)) j nl glp))))

; hi <= 2i+2 and 2i+2 <= j: hi <= j.
(def-fns _ $ (erased le-of-nron : (erased (Nat) hi) (erased (Nat) i) (erased (Nat) d)
    (erased (Lt hi (Succ (Succ (Succ d)))) nron) (erased (Nat) d3) (erased (Nat) j)
    (erased (Le (Succ (Succ d)) j) gl) -> (erased (Le hi j) out))
  (le-trans hi (Succ (Succ d)) j (MkLe hi (Succ (Succ d)) nron) gl))

; Every node of the subtree is <= the root's value (a max-heap's root is its
; maximum). The path must stay in range.
(def-fns _ $ (erased heap-le-root : (erased (List (Nat)) ys) (erased (Nat) hi) (erased (Nat) i) (erased (Nat) d)
    (erased (HeapOn ys hi i d) H) (erased (Nat) j) (subterm erased (Below i d j) b)
    (erased (Lt j hi) jlt) (erased (Nat) x) (erased (Nth (Nat) ys i x) nx)
    (erased (Nat) v) (erased (Nth (Nat) ys j v) nv) -> (erased (Le v x) out))
  (let-match erased b (BLeft _ _ ddx d2b dd2b _ bel)
    ((BRight _ _ ddx d3b dd3b _ bel)
      (let-match erased H (HTwo _ _ _ _ ddh d2 dd2 d3 dd3 x0 y0 z0 nx0 ny0 nz0 rin le1 le2 subl subr)
        (absurd (HLeaf _ _ _ _ ddh nl)
          (let-match erased (below-ge (Succ (Succ d)) d3b j bel) (MkLe _ _ gl))
          (lt-asym j (Succ (Succ d)) (lt-weaken j (Succ d) (lt-le-trans j hi (Succ d) jlt nl)) gl))
        (absurd (HOne _ _ _ _ ddh d2 dd2 x0 y0 nx0 ny0 lin nron le subl)
          (let-match erased (below-ge (Succ (Succ d)) d3b j bel) (MkLe _ _ gl))
          (lt-asym j (Succ (Succ d)) (lt-le-trans j hi (Succ (Succ d)) jlt nron) gl)))
      (let-match erased (double-fn (Succ (Succ d)) d3 d3b dd3 dd3b) (Refl _ _))
      (let ((erased ih)) (heap-le-root ys hi (Succ (Succ d)) d3 subr j bel jlt z0 nz0 v nv))
      (let-match erased (nth-fn (Nat) ys i x x0 nx nx0) (Refl _ _))
      (le-trans v z0 x ih le2))
    ((BHere _ _ _)
      (let-match erased (nth-fn (Nat) ys i x v nx nv) (Refl _ _))
      (le-refl x)))
  (let-match erased H (HOne _ _ _ _ ddh d2 dd2 x0 y0 nx0 ny0 lin nron le subl)
    ((HTwo _ _ _ _ ddh d2h dd2h d3 dd3 x0 y0 z0 nx0 ny0 nz0 rin le1 le2 subl subr)
      (let-match erased (double-fn (Succ d) d2h d2b dd2h dd2b) (Refl _ _))
      (let ((erased ih)) (heap-le-root ys hi (Succ d) d2h subl j bel jlt y0 ny0 v nv))
      (let-match erased (nth-fn (Nat) ys i x x0 nx nx0) (Refl _ _))
      (le-trans v y0 x ih le1))
    (absurd (HLeaf _ _ _ _ ddh nl)
      (let-match erased (below-ge (Succ d) d2b j bel) (MkLe _ _ gl))
      (lt-asym j (Succ d) (lt-le-trans j hi (Succ d) jlt nl) gl)))
  (let-match erased (double-fn (Succ d) d2 d2b dd2 dd2b) (Refl _ _))
  (let ((erased ih)) (heap-le-root ys hi (Succ d) d2 subl j bel jlt y0 ny0 v nv))
  (let-match erased (nth-fn (Nat) ys i x x0 nx nx0) (Refl _ _))
  (le-trans v y0 x ih le))

; Walking a Below path through a heap: every node of the path has its heap there
; (with its own double), or, when the path leaves the bound, a leaf heap.
(def-fns _ $ (erased heap-below : (erased (List (Nat)) ys) (erased (Nat) hi) (erased (Nat) i) (erased (Nat) d)
    (erased (Nat) j) (subterm erased (Below i d j) b) (erased (HeapOn ys hi i d) H)
    -> (erased (Nat) dj) (erased (HeapOn ys hi j dj) out))
  (let-match erased b (BLeft _ _ dd d2b dd2b _ bel)
    ((BRight _ _ dd d3b dd3b _ bel)
      (let-match erased H (HTwo _ _ _ _ ddh d2 dd2 d3 dd3 x y z nx ny nz rin le1 le2 subl subr)
        ((HLeaf _ _ _ _ ddh nl)
          (let ((erased dj) (erased ddj)) (double j))
          (values dj (HLeaf ys hi j dj ddj (hleaf-below hi j dj ddj (le-of-nl2 hi i d nl d3b j (below-ge (Succ (Succ d)) d3b j bel))))))
        ((HOne _ _ _ _ ddh d2 dd2 x y nx ny lin nron le subl)
          (let ((erased dj) (erased ddj)) (double j))
          (values dj (HLeaf ys hi j dj ddj (hleaf-below hi j dj ddj (le-of-nron hi i d nron d3b j (below-ge (Succ (Succ d)) d3b j bel)))))))
      (let-match erased (double-fn (Succ (Succ d)) d3 d3b dd3 dd3b) (Refl _ _))
      (heap-below ys hi (Succ (Succ d)) d3 j bel subr))
    ((BHere _ _ ddh) (values d H)))
  (let-match erased H (HOne _ _ _ _ ddh d2 dd2 x y nx ny lin nron le subl)
    ((HTwo _ _ _ _ ddh d2h dd2h d3 dd3 x y z nx ny nz rin le1 le2 subl subr)
      (let-match erased (double-fn (Succ d) d2h d2b dd2h dd2b) (Refl _ _))
      (heap-below ys hi (Succ d) d2h j bel subl))
    ((HLeaf _ _ _ _ ddh nl)
      (let ((erased dj) (erased ddj)) (double j))
      (values dj (HLeaf ys hi j dj ddj (hleaf-below hi j dj ddj (le-of-nl hi i d nl d2b j (below-ge (Succ d) d2b j bel)))))))
  (let-match erased (double-fn (Succ d) d2 d2b dd2 dd2b) (Refl _ _))
  (heap-below ys hi (Succ d) d2 j bel subl))

; A heap on a larger bound stays a heap on a smaller one (nodes at the new
; boundary drop out).
(def-fns _ $ (erased heap-shrink : (erased (Nat) hi2) (erased (Nat) hi1) (erased (Le hi2 hi1) le)
    (erased (List (Nat)) ys) (erased (Nat) i) (erased (Nat) d)
    (subterm erased (HeapOn ys hi1 i d) H) -> (erased (HeapOn ys hi2 i d) out))
  (let-match erased le (MkLe _ _ lpl))
  (match erased H _
    ((HLeaf _ _ _ _ dd nl)
      (HLeaf ys hi2 i d dd (lt-le-trans hi2 (Succ hi1) (Succ (Succ d)) lpl (LtS hi1 (Succ (Succ d)) nl))))
    ((HOne _ _ _ _ dd d2 dd2 x y nx ny lin nron le1 subl)
      (let ((erased t)) (tri hi2 (Succ d)))
      (let-match erased t (TriE _ _ e)
        ((TriG _ _ gt)
          (HOne ys hi2 i d dd d2 dd2 x y nx ny gt (le-lt-trans hi2 hi1 (Succ (Succ (Succ d))) le nron) le1
            (heap-shrink hi2 hi1 le ys (Succ d) d2 subl)))
        ((TriL _ _ lt1) (HLeaf ys hi2 i d dd (lt-trans hi2 (Succ d) (Succ (Succ d)) lt1 (lt-succ (Succ d))))))
      (let-match erased e (Refl _ _))
      (HLeaf ys hi2 i d dd (lt-succ (Succ d))))
    ((HTwo _ _ _ _ dd d2 dd2 d3 dd3 x y z nx ny nz rin le1 le2 subl subr)
      (let ((erased t)) (tri hi2 (Succ (Succ d))))
      (let-match erased t (TriE _ _ e)
        ((TriG _ _ gt)
          (HTwo ys hi2 i d dd d2 dd2 d3 dd3 x y z nx ny nz gt le1 le2
            (heap-shrink hi2 hi1 le ys (Succ d) d2 subl)
            (heap-shrink hi2 hi1 le ys (Succ (Succ d)) d3 subr)))
        ((TriL _ _ lt1) (HLeaf ys hi2 i d dd lt1)))
      (let-match erased e (Refl _ _))
      (HOne ys hi2 i d dd d2 dd2 x y nx ny (lt-succ (Succ d)) (lt-succ (Succ (Succ d))) le1
        (heap-shrink hi2 hi1 le ys (Succ d) d2 subl)))))

; A write at or past the bound leaves the heap alone (every node is below it).
(def-fns _ $ (erased congr-out : (erased (Nat) hi) (erased (Nat) h) (erased (Le hi h) le)
    (erased (List (Nat)) ys) (erased (Nat) i) (erased (Nat) d)
    (subterm erased (HeapOn ys hi i d) H) (erased (Nat) w) (erased (List (Nat)) ys')
    (erased (SetNth (Nat) ys h w ys') st) -> (erased (HeapOn ys' hi i d) out))
  (let-match erased le (MkLe _ _ lph))
  (match erased H _
    ((HLeaf _ _ _ _ dd nl) (HLeaf ys' hi i d dd nl))
    ((HOne _ _ _ _ dd d2 dd2 x y nx ny lin nron le1 subl)
      (HOne ys' hi i d dd d2 dd2 x y
        (setnth-nth-diff (Nat) ys h w ys' st i x nx (NeLO i h (lt-le-trans i hi h (lt-trans i (Succ d) hi (double-lt i d dd) lin) lph)))
        (setnth-nth-diff (Nat) ys h w ys' st (Succ d) y ny (NeLO (Succ d) h (lt-le-trans (Succ d) hi h lin lph)))
        lin nron le1
        (congr-out hi h le ys (Succ d) d2 subl w ys' st)))
    ((HTwo _ _ _ _ dd d2 dd2 d3 dd3 x y z nx ny nz rin le1 le2 subl subr)
      (HTwo ys' hi i d dd d2 dd2 d3 dd3 x y z
        (setnth-nth-diff (Nat) ys h w ys' st i x nx (NeLO i h (lt-le-trans i hi h (lt-trans i (Succ d) hi (double-lt i d dd) (lt-trans (Succ d) (Succ (Succ d)) hi (lt-succ (Succ d)) rin)) lph)))
        (setnth-nth-diff (Nat) ys h w ys' st (Succ d) y ny (NeLO (Succ d) h (lt-le-trans (Succ d) hi h (lt-trans (Succ d) (Succ (Succ d)) hi (lt-succ (Succ d)) rin) lph)))
        (setnth-nth-diff (Nat) ys h w ys' st (Succ (Succ d)) z nz (NeLO (Succ (Succ d)) h (lt-le-trans (Succ (Succ d)) hi h rin lph)))
        rin le1 le2
        (congr-out hi h le ys (Succ d) d2 subl w ys' st)
        (congr-out hi h le ys (Succ (Succ d)) d3 subr w ys' st)))))

; ---- extraction plumbing ----

; Nth is functional: one position holds one value.
; Every position is below the root 0.
(def-fns _ $ (erased below-zero : (subterm erased (Nat) j) -> (erased (Below (Zero) (Zero) j) out))
  (let-match erased j (Succ j1)
    ((Zero) (BHere (Zero) (Zero) (D0))))
  (let ((erased h1)) (nat-halve j))
  (let-match erased h1 (H1 m d dd)
    (absurd HZ)
    ((H2 m d dd)
      (let ((erased dcl) (erased ddcl)) (double (Succ (Succ d))))
      (let ((erased b0)) (below-zero (subterm (lt-subterm m j (lt-weaken m (Succ d) (double-lt m d dd)))) m))
      (below-trans (Zero) (Zero) m b0 d j (BRight m d dd dcl ddcl (Succ (Succ d)) (BHere (Succ (Succ d)) dcl ddcl)))))
  (let ((erased dcl) (erased ddcl)) (double (Succ d)))
  (let ((erased b0)) (below-zero (subterm (lt-subterm m j (double-lt m d dd))) m))
  (below-trans (Zero) (Zero) m b0 d j (BLeft m d dd dcl ddcl (Succ d) (BHere (Succ d) dcl ddcl))))

; The head of the suffix is at the split position in the whole list.
(def-fns _ $ (erased split-head : (erased (List (Nat)) ys) (erased (Nat) i) (erased (List (Nat)) ps)
    (erased (List (Nat)) ss) (subterm erased (Split ys i ps ss) spl) (erased (Nat) w)
    (erased (Nth (Nat) ss (Zero) w) nt) -> (erased (Nth (Nat) ys i w) out))
  (let-match erased spl (SpCons y rest j ps1 ss1 spl1)
    ((SpNil _) nt))
  (NthThere (Nat) y rest j w (split-head rest j ps1 ss1 spl1 w nt)))

; ps2 = ps with v appended: the split grows its prefix by the suffix's head.
(def-fns _ $ (erased split-snoc : (erased (List (Nat)) ys) (erased (Nat) j) (erased (List (Nat)) ps)
    (erased (Nat) v) (erased (List (Nat)) rest) (subterm erased (Split ys j ps (Cons (Nat) v rest)) spl)
    -> (erased (List (Nat)) ps2) (erased (Snoc ps v ps2) sn) (erased (Split ys (Succ j) ps2 rest) out))
  (let-match erased spl (SpCons y0 rest0 k ps1 ss1 spl1)
    ((SpNil _)
      (values (Cons (Nat) v (Nil (Nat))) (SnNil v) (SpCons v rest (Zero) (Nil (Nat)) rest (SpNil rest)))))
  (let ((erased ps2a) (erased sna) (erased sp1)) (split-snoc rest0 k ps1 v rest spl1))
  (values (Cons (Nat) y0 ps2a) (SnCons y0 ps1 v ps2a sna) (SpCons y0 rest0 (Succ k) ps2a rest sp1)))

; Every element of the prefix is <= the root's value (the root is the maximum
; of the max-heap on [0, hi)).
(def-fns _ $ (erased heap-max-aux : (erased (List (Nat)) whole) (erased (Nat) hi) (erased (Nat) d0)
    (erased (HeapOn whole hi (Zero) d0) H) (erased (Nat) x) (erased (Nth (Nat) whole (Zero) x) nx)
    (erased (Nat) o) (erased (List (Nat)) pre) (erased (List (Nat)) cur) (erased (Split whole o pre cur) sp)
    (erased (Nat) j) (erased (List (Nat)) ps) (erased (List (Nat)) ss) (subterm erased (Split cur j ps ss) spl)
    (erased (Add o j hi) ad) -> (erased (AllTo (Nat) Le ps x) out))
  (let-match erased (double-fn (Zero) d0 (Zero) (heap-dd whole hi (Zero) d0 H) (D0)) (Refl _ _))
  (let-match erased spl (SpCons y0 rest k ps1 ss1 spl1)
    ((SpNil _) (AllToNil (Nat) Le x)))
  (let ((erased pre2) (erased sn) (erased sp2)) (split-snoc whole o pre y0 rest sp))
  (let ((erased nh)) (split-head whole o pre cur sp y0 (NthHere (Nat) y0 rest)))
  (let ((erased olt)) (add-pos-lt o (Succ k) hi ad (LtZ k)))
  (let ((erased le0)) (heap-le-root whole hi (Zero) d0 H o (below-zero o) olt x nx y0 nh))
  (let ((erased ih)) (heap-max-aux whole hi d0 H x nx (Succ o) pre2 rest sp2 k ps1 ss1 spl1 (add-move o k hi ad)))
  (AllToCons (Nat) Le y0 ps1 x le0 ih))

(def-fns _ $ (erased heap-max : (erased (List (Nat)) ys) (erased (Nat) hi) (erased (Nat) d0)
    (erased (HeapOn ys hi (Zero) d0) H) (erased (Nat) x) (erased (Nth (Nat) ys (Zero) x) nx)
    (erased (List (Nat)) ps) (erased (List (Nat)) ss) (subterm erased (Split ys hi ps ss) spl)
    -> (erased (AllTo (Nat) Le ps x) out))
  (heap-max-aux ys hi d0 H x nx (Zero) (Nil (Nat)) ys (SpNil ys) hi ps ss spl (AddZero hi)))

; The last element of ps relates to x like the rest does.
(def-fns _ $ (erased allto-snoc : (erased (List (Nat)) ps) (erased (Nat) x)
    (subterm erased (AllTo (Nat) Le ps x) al) (erased (List (Nat)) ps') (erased (Nat) w)
    (erased (Snoc ps' w ps) sns) -> (erased (Le w x) out))
  (let-match erased sns (SnCons y0 psp w0 psn s1)
    ((SnNil _) (let-match erased al (AllToCons _ _ _ _ _ lw _)) lw))
  (let-match erased al (AllToCons _ _ y0b psnb _ ly0 leqn))
  (allto-snoc psn x leqn psp w0 s1))

; The suffix dominates its own last-appended element (the range's back half).
(def-fns _ $ (erased rangele-snoc : (erased (List (Nat)) ps) (erased (List (Nat)) ss)
    (subterm erased (RangeLe ps ss) rl) (erased (List (Nat)) ps') (erased (Nat) w)
    (erased (Snoc ps' w ps) sns) -> (erased (AllTo (Nat) GE ss w) out))
  (let-match erased sns (SnCons y0 psp w0 psn s1)
    ((SnNil _) (let-match erased rl (RLCons _ _ _ hw _)) hw))
  (let-match erased rl (RLCons _ _ _ hy rln))
  (rangele-snoc psn ss rln psp w0 s1))

; Every element of ps is <= every element of ss: read one off ps.
(def-fns _ $ (erased rangele-at : (erased (List (Nat)) ps) (erased (List (Nat)) ss)
    (subterm erased (RangeLe ps ss) rl) (erased (Nat) j) (erased (Nat) v)
    (erased (Nth (Nat) ps j v) nt) -> (erased (AllTo (Nat) GE ss v) out))
  (let-match erased nt (NthThere _ _ _ j1 _ nt1)
    ((NthHere _ _ _) (let-match erased rl (RLCons _ _ _ hv _)) hv))
  (let-match erased rl (RLCons y0 psn ss1 hy rln))
  (rangele-at psn ss rln j1 v nt1))

; The suffix grows by x at the front; the prefix loses its root x and gains w
; at the front (the extraction step's shape), and stays below the new suffix.
(def-fns _ $ (erased rangele-ext-tail : (erased (List (Nat)) psp) (erased (Nat) w) (erased (List (Nat)) psn)
    (subterm erased (Snoc psp w psn) s1) (erased (Nat) x) (erased (List (Nat)) ss)
    (erased (RangeLe psn ss) rl) (erased (AllTo (Nat) Le psn x) leq)
    -> (erased (RangeLe psp (Cons (Nat) x ss)) out))
  (let-match erased s1 (SnCons y0 psp1 w1 psn1 s2)
    ((SnNil _) (RLNil (Cons (Nat) x ss))))
  (let-match erased rl (RLCons y0b psn2 ss1 hy rln))
  (let-match erased leq (AllToCons _ _ y0d psn3 xm ly0 leqn))
  (RLCons y0 psp1 (Cons (Nat) x ss) (AllToCons (Nat) GE x ss y0 (ge-of-le y0 x ly0) hy)
    (rangele-ext-tail psp1 w1 psn1 s2 x ss rln leqn)))

(def-fns _ $ (erased rangele-ext : (erased (Nat) x) (erased (List (Nat)) ss)
    (erased (List (Nat)) psp) (erased (Nat) w) (erased (List (Nat)) ps)
    (subterm erased (Snoc psp w ps) sns) (erased (List (Nat)) ps2)
    (erased (SetNth (Nat) psp (Zero) w ps2) st)
    (erased (RangeLe ps ss) rl) (erased (AllTo (Nat) Le ps x) leq)
    -> (erased (RangeLe ps2 (Cons (Nat) x ss)) out))
  (let-match erased st (SetHere _ y0 w0 psp1)
    (absurd SetThere))
  (let-match erased sns (SnCons y0b psp2 w1 psn s1)
    (absurd SnNil))
  (let-match erased rl (RLCons y0c psn2 ss1 hy rln))
  (let-match erased leq (AllToCons _ _ y0d psn3 xm ly0 leqn))
  (let ((erased wlx)) (allto-snoc ps x leq psp w sns))
  (let ((erased gw)) (rangele-snoc ps ss rl psp w sns))
  (RLCons w psp1 (Cons (Nat) x ss) (AllToCons (Nat) GE x ss w (ge-of-le w x wlx) gw)
    (rangele-ext-tail psp1 w psn s1 x ss rln leqn)))

; ---- the sift entry state ----

; Rewriting the value already read there.
(def-fns _ $ (erased setnth-id : (erased Type A) (erased (List A) xs) (erased (Nat) i) (erased A x)
    (subterm erased (Nth A xs i x) nt) -> (erased (SetNth A xs i x xs) out))
  (let-match erased nt (NthThere _ hd rest i1 x1 nt1)
    ((NthHere _ xh rh) (SetHere A xh xh rh)))
  (SetThere A hd rest i1 x rest (setnth-id A rest i1 x nt1)))

; The children of i that are in range, with their heaps.
(def-adts
  ((Kids : ((List (Nat)) ys) ((Nat) hi) ((Nat) i) ((Nat) d) -> Type)
    enum
    (many KLeaf : (erased (List (Nat)) ys) (erased (Nat) hi) (erased (Nat) i) (erased (Nat) d)
        (erased (Double i d) dd) (erased (Lt hi (Succ (Succ d))) nl) -> (Kids ys hi i d))
    (many KOne : (erased (List (Nat)) ys) (erased (Nat) hi) (erased (Nat) i) (erased (Nat) d)
        (erased (Double i d) dd) (erased (Nat) d2) (erased (Double (Succ d) d2) dd2)
        (erased (Nat) y) (erased (Nth (Nat) ys (Succ d) y) ny)
        (erased (Lt (Succ d) hi) lin) (erased (Lt hi (Succ (Succ (Succ d)))) nron)
        (erased (HeapOn ys hi (Succ d) d2) subl) -> (Kids ys hi i d))
    (many KTwo : (erased (List (Nat)) ys) (erased (Nat) hi) (erased (Nat) i) (erased (Nat) d)
        (erased (Double i d) dd) (erased (Nat) d2) (erased (Double (Succ d) d2) dd2)
        (erased (Nat) d3) (erased (Double (Succ (Succ d)) d3) dd3)
        (erased (Nat) y) (erased (Nat) z)
        (erased (Nth (Nat) ys (Succ d) y) ny) (erased (Nth (Nat) ys (Succ (Succ d)) z) nz)
        (erased (Lt (Succ (Succ d)) hi) rin)
        (erased (HeapOn ys hi (Succ d) d2) subl) (erased (HeapOn ys hi (Succ (Succ d)) d3) subr)
        -> (Kids ys hi i d))))

; The sift entry state: the hole at i holds x; H is ws with a placeholder root
; v = max(x, children) that dominates the children, so H is a heap and
; ws = H[i := x] with x <= v.
(def-fns _ $ (erased sift-entry : (erased (List (Nat)) ws) (erased (Nat) hi) (erased (Nat) i) (erased (Nat) d)
    (erased (Double i d) dd) (subterm erased (Kids ws hi i d) kd)
    (erased (Nat) x) (erased (Nth (Nat) ws i x) nx)
    ->
    (erased (List (Nat)) H) (erased (Nat) v) (erased (Nth (Nat) H i v) nh)
    (erased (SetNth (Nat) H i x ws) sh) (erased (HeapOn H hi i d) heapH) (erased (Le x v) lew))
  (let-match erased kd (KTwo _ _ _ _ ddk d2k dd2k d3k dd3k y z ny nz rin subl subr)
    ((KLeaf _ _ _ _ ddk nl)
      (values ws x nx (setnth-id (Nat) ws i x nx) (HLeaf ws hi i d ddk nl) (le-refl x)))
    ((KOne _ _ _ _ ddk d2k dd2k y ny lin nron subl)
      (let ((erased v) (erased lxv) (erased lyv)) (max2 x y))
      (let ((erased Hw) (erased sv)) (setnth-of-nth (Nat) ws i x nx v))
      (values Hw v (setnth-nth (Nat) ws i v Hw sv) (setnth-back (Nat) ws i v Hw sv x nx)
        (HOne Hw hi i d ddk d2k dd2k v y (setnth-nth (Nat) ws i v Hw sv)
          (setnth-nth-diff (Nat) ws i v Hw sv (Succ d) y ny (NeGT (Succ d) i (double-lt i d dd)))
          lin nron lyv (congr-top i (Succ d) d2k (double-lt i d dd) ws hi subl v Hw sv))
        lxv)))
  (let ((erased v1) (erased ly1) (erased lz1)) (max2 y z))
  (let ((erased v) (erased lxv) (erased lv1)) (max2 x v1))
  (let ((erased Hw) (erased sv)) (setnth-of-nth (Nat) ws i x nx v))
  (values Hw v (setnth-nth (Nat) ws i v Hw sv) (setnth-back (Nat) ws i v Hw sv x nx)
    (HTwo Hw hi i d ddk d2k dd2k d3k dd3k v y z
      (setnth-nth (Nat) ws i v Hw sv)
      (setnth-nth-diff (Nat) ws i v Hw sv (Succ d) y ny (NeGT (Succ d) i (double-lt i d dd)))
      (setnth-nth-diff (Nat) ws i v Hw sv (Succ (Succ d)) z nz (NeGT (Succ (Succ d)) i (lt-weaken i (Succ d) (double-lt i d dd))))
      rin (le-trans y v1 v ly1 lv1) (le-trans z v1 v lz1 lv1)
      (congr-top i (Succ d) d2k (double-lt i d dd) ws hi subl v Hw sv)
      (congr-top i (Succ (Succ d)) d3k (lt-weaken i (Succ d) (double-lt i d dd)) ws hi subr v Hw sv))
    lxv))
