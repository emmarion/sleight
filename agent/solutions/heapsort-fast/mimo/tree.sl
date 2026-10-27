; work/tree.sl: tree-structure arithmetic for the heap (milestone 3 groundwork).
; All erased. The heap tree over array positions has children 2i+1, 2i+2; with
; `Double i d` (d = 2i) the children are (Succ d) and (Succ (Succ d)). `Below`
; (heappf.sl) is indexed by (i, d, h) so it lines up with the heap predicates.
; This file holds the position lemmas the heap proofs need:
;
;   - `Par j p`: p is j's parent (j = 2p+1 or 2p+2), `par-fn` (unique parent).
;   - `Pars h i k`: i is h's k-th ancestor, `pars-fn` (unique k-th ancestor),
;     `pars-chain` (two ancestors of one node are comparable).
;   - `below-ge` / `below-gap` / `below-parent` / `below-trans` / `below-of-par`.
;   - `below-pars` / `pars-below`: `Below i d h` <-> i is an ancestor of h.
;   - `sib-disj` / `sib-ne`: sibling subtrees are disjoint (the key fact that
;     lets a write inside one child subtree transport the other child's heap).
;
; Everything here is mechanical once the shapes line up; the SHAPES are the
; content. Erased code may call `lt-dec` etc. freely (spec.sl's warning pragmas
; fire only on code that runs).

; ---- small order facts ----

(def-fns _ $ (erased absurd lt-irrefl : (erased (Nat) a) (subterm erased (Lt a a) p) -> (erased (False) f))
  (lt-asym a a p (lt-succ a)))

(def-fns _ $ (erased ne-flip : (erased (Nat) a) (erased (Nat) b) (subterm erased (Ne a b) n) -> (erased (Ne b a) m))
  (match erased n _
    ((NeLO _ _ p) (NeGT b a p))
    ((NeGT _ _ q) (NeLO b a q))))

; Read-your-write: the value at the written position, after the write.
; Nth is functional: one position holds one value.
; ---- Par: parent relation ----

(def-adts
  ((Par : ((Nat) j) ((Nat) p) -> Type)
    enum
    ; j = 2p+1 (left child of p), d = 2p.
    (many ParL : (erased (Nat) p) (erased (Nat) d) (erased (Double p d) dd) -> (Par (Succ d) p))
    ; j = 2p+2 (right child of p).
    (many ParR : (erased (Nat) p) (erased (Nat) d) (erased (Double p d) dd) -> (Par (Succ (Succ d)) p))))

; A node has a unique parent.
(def-fns _ $ (erased par-fn : (erased (Nat) j) (erased (Nat) p1) (erased (Nat) p2)
    (subterm erased (Par j p1) a) (erased (Par j p2) b) -> (erased (Eq (Nat) p1 p2) e))
  (let-match erased a (ParL _ d1 dd1)
    ((ParR _ d1 dd1)
      (let-match erased b (ParR _ d2 dd2)
        (absurd (ParL _ d2 dd2) (double-parity p2 p1 d1 dd2 dd1)))
      (double-inj p1 p2 d1 dd1 dd2)))
  (let-match erased b (ParL _ d2 dd2)
    (absurd (ParR _ d2 dd2) (double-parity p1 p2 d2 dd1 dd2)))
  (double-inj p1 p2 d2 dd1 dd2))

; ---- Below utilities (Below is defined in work/heappf.sl) ----

; The Double witness a Below carries.
(def-fns _ $ (erased below-dd : (erased (Nat) i) (erased (Nat) d) (erased (Nat) h)
    (subterm erased (Below i d h) b) -> (erased (Double i d) dd))
  (match erased b _
    ((BHere _ _ dd) dd)
    ((BLeft _ _ dd _ _ _ _) dd)
    ((BRight _ _ dd _ _ _ _) dd)))

; Every node of subtree(i) is at or above i.
(def-fns _ $ (erased below-ge : (erased (Nat) i) (erased (Nat) d) (erased (Nat) h)
    (subterm erased (Below i d h) b) -> (erased (Le i h) out))
  (let-match erased b (BLeft _ _ dd _ _ _ bel)
    ((BRight _ _ dd _ _ _ bel)
      (le-trans i (Succ (Succ d)) h (le-of-lt _ _ (lt-weaken i (Succ d) (double-lt i d dd)))
        (below-ge (Succ (Succ d)) _ h bel)))
    ((BHere _ _ _) (le-refl i)))
  (le-trans i (Succ d) h (le-of-lt _ _ (double-lt i d dd)) (below-ge (Succ d) _ h bel)))

; A subtree's node is either its root or at/above 2i+1.
(def-adts
  ((Gap : ((Nat) i) ((Nat) d) ((Nat) h) -> Type)
    enum
    (many GapEq : (erased (Nat) i) (erased (Nat) d) (erased (Nat) h) (erased (Eq (Nat) h i) e) -> (Gap i d h))
    (many GapGe : (erased (Nat) i) (erased (Nat) d) (erased (Nat) h) (erased (Le (Succ d) h) l) -> (Gap i d h))))

(def-fns _ $ (erased below-gap : (erased (Nat) i) (erased (Nat) d) (erased (Nat) h)
    (subterm erased (Below i d h) b) -> (erased (Gap i d h) out))
  (let-match erased b (BLeft _ _ _ d2 dd2 _ bel)
    ((BRight _ _ _ d2 dd2 _ bel)
      (let ((erased ih)) (below-gap (Succ (Succ d)) d2 h bel))
      (let-match erased ih (GapEq _ _ _ e)
        ((GapGe _ _ _ l) (GapGe i d h (le-trans (Succ d) (Succ d2) h
          (le-of-lt _ _ (lt-trans (Succ d) (Succ (Succ d)) (Succ d2) (lt-succ (Succ d))
            (double-lt (Succ (Succ d)) d2 dd2)))
          l))))
      (let-match erased e (Refl _ _))
      (GapGe i d h (le-of-lt _ _ (lt-succ (Succ d)))))
    ((BHere _ _ _) (GapEq i d h (Refl (Nat) i))))
  (let ((erased ih)) (below-gap (Succ d) d2 h bel))
  (let-match erased ih (GapEq _ _ _ e)
    ((GapGe _ _ _ l) (GapGe i d h (le-trans (Succ d) (Succ d2) h
      (le-of-lt _ _ (double-lt (Succ d) d2 dd2)) l))))
  (let-match erased e (Refl _ _))
  (GapGe i d h (le-refl (Succ d))))

; ---- below-parent: the parent of a subtree node is in the subtree (or is the root) ----

(def-adts
  ((BPar : ((Nat) x) ((Nat) dx) ((Nat) j) ((Nat) p) -> Type)
    enum
    (many BPBelow : (erased (Nat) x) (erased (Nat) dx) (erased (Nat) j) (erased (Nat) p)
        (erased (Below x dx p) b) -> (BPar x dx j p))
    (many BPEq : (erased (Nat) x) (erased (Nat) dx) (erased (Nat) j) (erased (Nat) p)
        (erased (Eq (Nat) j x) e) -> (BPar x dx j p))))

(def-fns _ $ (erased below-parent : (erased (Nat) x) (erased (Nat) dx) (erased (Nat) j)
    (subterm erased (Below x dx j) b) (erased (Nat) p) (erased (Par j p) pr) -> (erased (BPar x dx j p) out))
  (let-match erased b (BLeft _ _ ddx d2 dd2 _ bel)
    ((BRight _ _ ddx d2 dd2 _ bel)
      (let ((erased ih)) (below-parent (Succ (Succ dx)) d2 j bel p pr))
      (let-match erased ih (BPBelow _ _ _ _ ib)
        ((BPEq _ _ _ _ e)
          (let-match erased e (Refl _ _))
          (let-match erased (par-fn j p x pr (ParR x dx ddx)) (Refl _ _))
          (BPBelow x dx j p (BHere x dx ddx))))
      (BPBelow x dx j p (BRight x dx ddx d2 dd2 p ib)))
    ((BHere _ _ _) (BPEq x dx j p (Refl (Nat) j))))
  (let ((erased ih)) (below-parent (Succ dx) d2 j bel p pr))
  (let-match erased ih (BPBelow _ _ _ _ ib)
    ((BPEq _ _ _ _ e)
      (let-match erased e (Refl _ _))
      (let-match erased (par-fn j p x pr (ParL x dx ddx)) (Refl _ _))
      (BPBelow x dx j p (BHere x dx ddx))))
  (BPBelow x dx j p (BLeft x dx ddx d2 dd2 p ib)))

; ---- below-of-par and below-trans ----

(def-fns _ $ (erased below-of-par : (erased (Nat) p) (erased (Nat) i) (subterm erased (Par p i) pr)
    -> (erased (Nat) dp) (erased (Below i dp p) out))
  (let-match erased pr (ParL _ d dd)
    ((ParR _ d dd)
      (let ((erased d2) (erased dd2)) (double (Succ (Succ d))))
      (values d (BRight i d dd d2 dd2 (Succ (Succ d)) (BHere (Succ (Succ d)) d2 dd2)))))
  (let ((erased d2) (erased dd2)) (double (Succ d)))
  (values d (BLeft i d dd d2 dd2 (Succ d) (BHere (Succ d) d2 dd2))))

(def-fns _ $ (erased below-trans : (erased (Nat) x) (erased (Nat) dx) (erased (Nat) y)
    (subterm erased (Below x dx y) b) (erased (Nat) dy) (erased (Nat) j) (erased (Below y dy j) c)
    -> (erased (Below x dx j) out))
  (let-match erased b (BLeft _ _ ddx d2 dd2 _ bel)
    ((BRight _ _ ddx d2 dd2 _ bel)
      (BRight x dx ddx d2 dd2 j (below-trans (Succ (Succ dx)) d2 y bel dy j c)))
    ((BHere _ _ ddx)
      (let-match erased (double-fn x dx dy ddx (below-dd y dy j c)) (Refl _ _))
      c))
  (BLeft x dx ddx d2 dd2 j (below-trans (Succ dx) d2 y bel dy j c)))

; ---- le-antisym and trichotomy ----

(def-fns _ $ (erased le-antisym : (erased (Nat) a) (erased (Nat) b)
    (subterm erased (Lt b (Succ a)) p) (erased (Lt a (Succ b)) q) -> (erased (Eq (Nat) a b) e))
  (let-match erased p (LtS x y pp)
    ((LtZ _)
      (let-match erased q (LtZ _)
        (absurd (LtS _ _ qq) (match erased qq _)))
      (Refl (Nat) (Zero))))
  (let-match erased q (LtS y2 _ qq)
    (absurd (LtZ _) (match erased pp _)))
  (let-match erased (le-antisym y2 x pp qq) (Refl _ _))
  (Refl (Nat) a))

(def-adts
  ((Tri : ((Nat) a) ((Nat) b) -> Type)
    enum
    (many TriL : (erased (Nat) a) (erased (Nat) b) (erased (Lt a b) p) -> (Tri a b))
    (many TriE : (erased (Nat) a) (erased (Nat) b) (erased (Eq (Nat) a b) e) -> (Tri a b))
    (many TriG : (erased (Nat) a) (erased (Nat) b) (erased (Lt b a) q) -> (Tri a b))))

(def-fns _ $ (erased tri : (erased (Nat) a) (erased (Nat) b) -> (erased (Tri a b) t))
  (let-match erased (lt-dec a b) (Yes _ _ _ _ p)
    ((No _ _ _ _ le-r) (let ((erased r)) (lt-eq-succ _ _ le-r))
      (let-match erased (lt-dec b a) (Yes _ _ _ _ q)
        ((No _ _ _ _ le-s) (let ((erased s)) (lt-eq-succ _ _ le-s)) (TriE a b (le-antisym a b r s))))
      (TriG a b q)))
  (TriL a b p))

; ---- Pars: the ancestor walk ----

; Pars h i k: i is h's k-th ancestor (walking parents up); k steps from h reach i.
(def-adts
  ((Pars : ((Nat) h) ((Nat) i) ((Nat) k) -> Type)
    enum
    (many PZ : (erased (Nat) h) -> (Pars h h (Zero)))
    (many PSucc : (erased (Nat) h) (erased (Nat) p) (erased (Nat) i) (erased (Nat) k)
        (erased (Par p i) pr) (erased (Pars h p k) rest) -> (Pars h i (Succ k)))))

; The k-th ancestor is unique.
(def-fns _ $ (erased pars-fn : (erased (Nat) h) (erased (Nat) u) (erased (Nat) v) (erased (Nat) k)
    (subterm erased (Pars h u k) a) (erased (Pars h v k) b) -> (erased (Eq (Nat) u v) e))
  (let-match erased a (PSucc _ p1 _ _ pr1 rest1)
    ((PZ _)
      (let-match erased b (PZ _))
      (Refl (Nat) h)))
  (let-match erased b (PSucc _ p2 _ _ pr2 rest2))
  (let-match erased (pars-fn h p1 p2 _ rest1 rest2) (Refl _ _))
  (par-fn p1 u v pr1 pr2))

; An ancestor chain from below: Below i d h <-> i is an ancestor of h.
(def-fns _ $ (erased pars-below : (erased (Nat) h) (erased (Nat) i) (erased (Nat) k)
    (subterm erased (Pars h i k) w) -> (erased (Nat) dy) (erased (Below i dy h) out))
  (let-match erased w (PSucc _ p _ _ pr rest)
    ((PZ _)
      (let ((erased dy) (erased ddy)) (double i))
      (values dy (BHere i dy ddy))))
  (let ((erased dy2) (erased bp)) (pars-below h p _ rest))
  (let ((erased dp) (erased ib)) (below-of-par p i pr))
  (values dp (below-trans i dp p ib dy2 h bp)))

(def-fns _ $ (erased below-pars : (erased (Nat) i) (erased (Nat) d) (erased (Nat) h)
    (subterm erased (Below i d h) b) -> (erased (Nat) k) (erased (Pars h i k) out))
  (let-match erased b (BLeft _ _ dd d2 dd2 _ bel)
    ((BRight _ _ dd d2 dd2 _ bel)
      (let ((erased k1) (erased w1)) (below-pars (Succ (Succ d)) d2 h bel))
      (values (Succ k1) (PSucc h (Succ (Succ d)) i k1 (ParR i d dd) w1)))
    ((BHere _ _ _) (values (Zero) (PZ h))))
  (let ((erased k1) (erased w1)) (below-pars (Succ d) d2 h bel))
  (values (Succ k1) (PSucc h (Succ d) i k1 (ParL i d dd) w1)))

; Two ancestors of one node are comparable: equal, or one below the other.
(def-adts
  ((AncOrd : ((Nat) u) ((Nat) v) -> Type)
    enum
    (many AOE : (erased (Nat) u) (erased (Nat) v) (erased (Eq (Nat) u v) e) -> (AncOrd u v))
    (many AOUV : (erased (Nat) u) (erased (Nat) v) (erased (Nat) du) (erased (Below u du v) b) -> (AncOrd u v))
    (many AOVU : (erased (Nat) u) (erased (Nat) v) (erased (Nat) dv) (erased (Below v dv u) b) -> (AncOrd u v))))

(def-fns _ $ (erased pars-chain : (erased (Nat) h) (erased (Nat) u) (erased (Nat) k)
    (subterm erased (Pars h u k) a) (erased (Nat) v) (erased (Nat) l) (erased (Pars h v l) b)
    -> (erased (AncOrd u v) out))
  (let-match erased a (PSucc _ p1 _ _ pr1 rest1)
    ((PZ _)
      (let-match erased b (PSucc _ _ _ _ _ _)
        ((PZ _) (AOE u v (Refl (Nat) h))))
      (let ((erased dv) (erased bv)) (pars-below h v l b))
      (AOVU u v dv bv)))
  (let-match erased b (PSucc _ p2 _ _ pr2 rest2)
    ((PZ _)
      (let ((erased du) (erased bu)) (pars-below h u k a))
      (AOUV u v du bu)))
  (let ((erased ord)) (pars-chain h p1 _ rest1 p2 _ rest2))
  (match erased ord _
    ((AOE _ _ e)
      (let-match erased e (Refl _ _))
      (let-match erased (par-fn p1 u v pr1 pr2) (Refl _ _))
      (AOE u v (Refl (Nat) u)))
    ((AOUV _ _ dp bp)
      (let ((erased lifted)) (below-parent p1 dp p2 bp v pr2))
      (let-match erased lifted (BPBelow _ _ _ _ ib)
        ((BPEq _ _ _ _ e2)
          (let-match erased e2 (Refl _ _))
          (let-match erased (par-fn p1 u v pr1 pr2) (Refl _ _))
          (AOE u v (Refl (Nat) u))))
      (let ((erased du) (erased ip)) (below-of-par p1 u pr1))
      (AOUV u v du (below-trans u du p1 ip dp v ib)))
    ((AOVU _ _ dp bp)
      (let ((erased lifted)) (below-parent p2 dp p1 bp u pr1))
      (let-match erased lifted (BPBelow _ _ _ _ ib)
        ((BPEq _ _ _ _ e2)
          (let-match erased e2 (Refl _ _))
          (let-match erased (par-fn p1 u v pr1 pr2) (Refl _ _))
          (AOE u v (Refl (Nat) u))))
      (let ((erased dv) (erased ip)) (below-of-par p2 v pr2))
      (AOVU u v dv (below-trans v dv p2 ip dp u ib)))))

; ---- sibling subtrees are disjoint ----

; If h is in subtree(2m+1), it is not in subtree(2m+2): the two children of a
; node hold disjoint subtrees. This is the fact that lets heap-replace leave the
; sibling subtree's heap proof alone while rewriting the path subtree.
(def-fns _ $ (erased absurd sib-disj : (erased (Nat) m) (erased (Nat) d) (erased (Double m d) dd)
    (erased (Nat) d1) (erased (Nat) h) (erased (Below (Succ d) d1 h) bl)
    (erased (Nat) d2) (erased (Below (Succ (Succ d)) d2 h) br) -> (erased (False) f))
  (let ((erased k1) (erased wl)) (below-pars (Succ d) d1 h bl))
  (let ((erased k2) (erased wr)) (below-pars (Succ (Succ d)) d2 h br))
  (let ((erased ord)) (pars-chain h (Succ d) k1 wl (Succ (Succ d)) k2 wr))
  (match erased ord _
    (absurd (AOE _ _ e) (match erased e _))
    (absurd (AOUV _ _ du b1)
      (let ((erased g)) (below-gap (Succ d) du (Succ (Succ d)) b1))
      (match erased g _
        (absurd (GapEq _ _ _ e2) (match erased e2 _))
        (absurd (GapGe _ _ _ l)
          (let-match erased l (MkLe _ _ q))
          (let-match erased q (LtS _ _ q1))
          (let ((erased dbl)) (below-dd (Succ d) du (Succ (Succ d)) b1))
          (let-match erased dbl (DS _ b2 dbl2))
          (lt-asym (Succ d) du (LtS d (Succ b2) (double-lt d b2 dbl2)) q1))))
    (absurd (AOVU _ _ dv b1)
      (let ((erased g)) (below-gap (Succ (Succ d)) dv (Succ d) b1))
      (match erased g _
        (absurd (GapEq _ _ _ e2) (match erased e2 _))
        (absurd (GapGe _ _ _ l)
          (let-match erased l (MkLe _ _ q))
          (let-match erased q (LtS _ _ q1))
          (let ((erased dbl)) (below-dd (Succ (Succ d)) dv (Succ d) b1))
          (let-match erased dbl (DS _ b2 dbl2))
          (lt-asym (Succ (Succ d)) dv
            (LtS (Succ d) (Succ b2) (double-lt (Succ d) b2 dbl2))
            (lt-weaken dv (Succ (Succ d)) (lt-weaken dv (Succ d) q1))))))))

; ---- crossing subtrees are disjoint ----

; cross-ne: i0 < i <= 2*i0 means subtree(i) and subtree(i0) are disjoint (i sits
; strictly between i0 and i0's left child 2*i0+1, so neither node is an ancestor
; of the other and a tree's subtrees of incomparable nodes are disjoint): any
; node m of subtree(i0) differs from any node h of subtree(i). This is the fact
; that lets the build loop's sift at j leave the heaps at [j+1, 2j] alone.
(def-fns _ $ (erased cross-ne : (erased (Nat) i0) (erased (Nat) d0) (erased (Double i0 d0) dd0)
    (erased (Nat) i) (erased (Lt i0 i) lt1) (erased (Le i d0) le2)
    (erased (Nat) dm) (erased (Nat) m) (erased (Below i0 d0 m) bm)
    (erased (Nat) dh) (erased (Nat) h) (erased (Below i dh h) bh) -> (erased (Ne m h) out))
  (let ((erased t)) (tri m h))
  (let-match erased t (TriE _ _ e)
    ((TriL _ _ p) (NeLO m h p))
    ((TriG _ _ q) (NeGT m h q)))
  (let-match erased e (Refl _ _))
  (let ((erased k1) (erased w1)) (below-pars i0 d0 m bm))
  (let ((erased k2) (erased w2)) (below-pars i dh h bh))
  (let ((erased ord)) (pars-chain m i0 k1 w1 i k2 w2))
  (match erased ord _
    (absurd (AOE _ _ e2)
      (let-match erased e2 (Refl _ _))
      (lt-irrefl i0 lt1))
    (absurd (AOUV _ _ du b1)
      (let-match erased (double-fn i0 du d0 (below-dd i0 du i b1) dd0) (Refl _ _))
      (let ((erased g)) (below-gap i0 d0 i b1))
      (match erased g _
        (absurd (GapEq _ _ _ e2)
          (let-match erased e2 (Refl _ _))
          (lt-irrefl i0 lt1))
        (absurd (GapGe _ _ _ l)
          (let-match erased le2 (MkLe _ _ le2p))
          (let-match erased l (MkLe _ _ q1))
          (lt-asym i (Succ d0) le2p q1))))
    (absurd (AOVU _ _ dv b1)
      (let-match erased (double-fn i dv dh (below-dd i dv i0 b1) (below-dd i dh h bh)) (Refl _ _))
      (let ((erased g)) (below-gap i dh i0 b1))
      (match erased g _
        (absurd (GapEq _ _ _ e2)
          (let-match erased e2 (Refl _ _))
          (lt-irrefl i0 lt1))
        (absurd (GapGe _ _ _ l)
          (let-match erased l (MkLe _ _ q1))
          (lt-asym (Succ dh) i
            (lt-le-trans (Succ dh) (Succ i0) i q1 (LtS i0 i lt1))
            (lt-weaken i (Succ dh) (double-lt i dh (below-dd i dh h bh)))))))))

; A node in the right subtree differs from a node in the left subtree.
(def-fns _ $ (erased sib-ne : (erased (Nat) m) (erased (Nat) d) (erased (Double m d) dd)
    (erased (Nat) d1) (erased (Nat) h) (erased (Below (Succ d) d1 h) bl)
    (erased (Nat) d2) (erased (Nat) j) (erased (Below (Succ (Succ d)) d2 j) br)
    -> (erased (Ne j h) out))
  (let ((erased t)) (tri j h))
  (match erased t _
    ((TriL _ _ p) (NeLO j h p))
    ((TriG _ _ q) (NeGT j h q))
    (absurd (TriE _ _ e)
      (let-match erased e (Refl _ _))
      (sib-disj m d dd d1 j bl d2 br))))
