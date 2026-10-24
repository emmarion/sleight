; work/heappf.sl: heapsort (milestone 3) invariant scaffolding. In files.txt so
; the invariant TYPES stay live and checked. The invariant TYPES are here; the
; preservation lemmas (work/heap.sl, work/heap2.sl), the window plumbing
; (work/heap3.sl, work/heap4.sl) and the loops (work/loops.sl) follow. See
; HANDOFF.md for the full design. The committed sort is the certified heapsort
; (work/sort.sl).
;
; Array layout: the content list ys is a max-heap on [0, hi): every node i has
; its value >= its children's, where the children of i are 2i+1 and 2i+2. With
; `Double i d` (d = 2i), the left child is (Succ d) and the right (Succ (Succ d)).
;
; The sift-down ghost (the key invariant). Sift-down moves a stray value x down
; from a hole h, swapping it with its larger child until it fits. `SinkInv ws H
; hi i0 h x` says: H is a max-heap on the subtree rooted at i0; ws is H with the
; hole h holding x instead of H's value v there (so `SetNth H h x ws`); and
; `Le x v` (the displaced value v is >= x). It is INDUCTIVE: swapping the hole h
; with the larger child c maps H to H' = H[h := H[c]] (still a heap -- because
; H[parent of h] >= H[h] >= H[c] = H'[h] and H[c] >= H[c's children] and H[c] >= H[c+1]
; as c is the larger child), and ws to ws' = H'[c := x], with the new hole at c
; and H'[c] = H[c] >= x. At the end (x fits, or h is a leaf) `SetNth H h x ws`
; with `Le x v` and H a heap forces ws itself to be a heap.

(def-adts
  ((HeapOn : ((List (Nat)) ys) ((Nat) hi) ((Nat) i) ((Nat) d) -> Type)
    enum
    ; no left child: hi <= 2i+1, i.e. hi < (Succ (Succ d)) with d = 2i.
    (many HLeaf : (erased (List (Nat)) ys) (erased (Nat) hi) (erased (Nat) i) (erased (Nat) d)
        (erased (Double i d) dd) (erased (Lt hi (Succ (Succ d))) nl)
        -> (HeapOn ys hi i d))
    ; left child (Succ d) in, right child (Succ (Succ d)) out: 2i+1 < hi <= 2i+2.
    ; Max-heap: child <= parent, i.e. (Le y x) with x at the parent, y at the child.
    (many HOne : (erased (List (Nat)) ys) (erased (Nat) hi) (erased (Nat) i) (erased (Nat) d)
        (erased (Double i d) dd) (erased (Nat) d2) (erased (Double (Succ d) d2) dd2)
        (erased (Nat) x) (erased (Nat) y)
        (erased (Nth (Nat) ys i x) nx) (erased (Nth (Nat) ys (Succ d) y) ny)
        (erased (Lt (Succ d) hi) lin) (erased (Lt hi (Succ (Succ (Succ d)))) nron)
        (erased (Le y x) le) (erased (HeapOn ys hi (Succ d) d2) subl)
        -> (HeapOn ys hi i d))
    ; both children in: 2i+2 < hi.
    (many HTwo : (erased (List (Nat)) ys) (erased (Nat) hi) (erased (Nat) i) (erased (Nat) d)
        (erased (Double i d) dd) (erased (Nat) d2) (erased (Double (Succ d) d2) dd2)
        (erased (Nat) d3) (erased (Double (Succ (Succ d)) d3) dd3)
        (erased (Nat) x) (erased (Nat) y) (erased (Nat) z)
        (erased (Nth (Nat) ys i x) nx) (erased (Nth (Nat) ys (Succ d) y) ny) (erased (Nth (Nat) ys (Succ (Succ d)) z) nz)
        (erased (Lt (Succ (Succ d)) hi) rin)
        (erased (Le y x) le1) (erased (Le z x) le2)
        (erased (HeapOn ys hi (Succ d) d2) subl) (erased (HeapOn ys hi (Succ (Succ d)) d3) subr)
        -> (HeapOn ys hi i d))))

(def-adts
  ((SinkInv : ((List (Nat)) ws) ((List (Nat)) H) ((Nat) hi) ((Nat) i0) ((Nat) h) ((Nat) x) -> Type)
    enum
    (many MkSink : (erased (List (Nat)) ws) (erased (List (Nat)) H) (erased (Nat) hi) (erased (Nat) i0)
        (erased (Nat) d0) (erased (Nat) h) (erased (Nat) x) (erased (Nat) v)
        (erased (Nth (Nat) H h v) nh) (erased (SetNth (Nat) H h x ws) sh)
        (erased (HeapOn H hi i0 d0) heap) (erased (Le x v) le)
        -> (SinkInv ws H hi i0 h x))))

; `Below i d h`: h is at or below i in the heap tree (h = i, or h in i's left/right
; subtree), with d = 2i carried as an INDEX (each constructor holds the Double
; witness). This is the PATH that heap-replace walks: to change node h's value
; and keep subtree(i) a heap, recurse from i down along Below to h. Indexing by
; d lets Below line up with HeapOn (also indexed by d) without unifying two
; Double witnesses per level; each step names the child's own double d2.
(def-adts
  ((Below : ((Nat) i) ((Nat) d) ((Nat) h) -> Type)
    enum
    (many BHere : (erased (Nat) i) (erased (Nat) d) (erased (Double i d) dd) -> (Below i d i))
    (many BLeft : (erased (Nat) i) (erased (Nat) d) (erased (Double i d) dd)
        (erased (Nat) d2) (erased (Double (Succ d) d2) dd2) (erased (Nat) h)
        (erased (Below (Succ d) d2 h) bel) -> (Below i d h))
    (many BRight : (erased (Nat) i) (erased (Nat) d) (erased (Double i d) dd)
        (erased (Nat) d2) (erased (Double (Succ (Succ d)) d2) dd2) (erased (Nat) h)
        (erased (Below (Succ (Succ d)) d2 h) bel) -> (Below i d h))))

; heap-replace (THE crux lemma, to be written). Changing node h's value from v to
; w inside subtree(i) keeps subtree(i) a max-heap, provided (a) w <= v (so every
; ancestor edge is preserved by the chain ancestor >= ... >= v >= w) and (b) w
; fits at h (w >= h's children, so h's own child edges hold). Recurse on `Below`,
; matching `HeapOn` alongside; return also the NEW value at i and its `Le` to the
; old, so each caller can re-establish the parent edge (the chain the plain "all
; edges but the hole" formulation loses):
;
;   heap-replace : HeapOn ys hi i -> Below i h -> Nth ys h v -> SetNth ys h w ys'
;                  -> Le w v -> (w >= ys'[h's children])
;                  -> (HeapOn ys' hi i, Nth ys' i w', Le w' v_i)   with Nth ys i v_i
;
; The sift swap instantiates w := H[c] (c = larger child): w <= v because c is a
; child in the heap, and w fits because c is the larger child. Then
; H' = H[h := H[c]] is a heap and the SinkInv step goes through.

; ---- Nth-preservation utilities that heap-replace needs ----

; Ne a b: a != b, as a < b or b < a. Used to exclude the write position when
; transporting an Nth read across a SetNth write.
(def-adts
  ((Ne : ((Nat) a) ((Nat) b) -> Type)
    enum
    (many NeLO : (erased (Nat) a) (erased (Nat) b) (erased (Lt a b) p) -> (Ne a b))
    (many NeGT : (erased (Nat) a) (erased (Nat) b) (erased (Lt b a) q) -> (Ne a b))))

(def-fns _ $ (erased ne-pred : (erased (Nat) a) (erased (Nat) b) (subterm erased (Ne (Succ a) (Succ b)) n) -> (erased (Ne a b) m))
  (let-match erased n (NeLO _ _ p) ((NeGT _ _ q) (let-match erased q (LtS _ _ q1)) (NeGT a b q1)))
  (let-match erased p (LtS _ _ p1))
  (NeLO a b p1))

; setnth-nth-diff: a read at j is preserved across a write at h != j.
(def-fns _ $ (erased setnth-nth-diff : (erased Type A) (erased (List A) xs) (erased (Nat) h) (erased A w)
    (erased (List A) ys) (subterm erased (SetNth A xs h w ys) st) (erased (Nat) j) (erased A x)
    (erased (Nth A xs j x) nt) (erased (Ne j h) ne) -> (erased (Nth A ys j x) out))
  (let-match erased st (SetThere _ x0 rest h1 _ ys1 st1)
    ((SetHere _ x0 _ rest)
      (let-match erased ne (NeGT _ _ q) ((NeLO _ _ z) (match erased z _)))
      (let-match erased q (LtZ j1))
      (let-match erased nt (NthThere _ _ _ _ _ nt1))
      (NthThere A w rest j1 x nt1)))
  (let-match erased nt (NthThere _ _ _ j1 _ nt1)
    ((NthHere _ _ _) (NthHere A x0 ys1)))
  (let ((erased ne1)) (ne-pred j1 h1 ne))
  (NthThere A x0 ys1 j1 x (setnth-nth-diff A rest h1 w ys1 st1 j1 x nt1 ne1)))

; Far hi i h (the per-node Ne walk) and far-ne are gone: work/heap.sl transports
; an unchanged subtree across a write with `congr-top` (write above the subtree)
; and `congr-sib` (write in a sibling subtree), which build the Ne's from tree.sl
; bounds and `sib-ne` instead.

; heap-on-congr / heap-replace live in work/heap.sl (they need tree.sl's
; sib-ne, so they come after it in files.txt).
