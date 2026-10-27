; work/heap4.sl: build-loop plumbing (milestone 3). All erased; nothing here
; runs. It sits after work/heap3.sl and before work/loops.sl.
;
; Frames ys n i0 d0 lo hi: heap proofs on ys at every node in [lo, hi), each
; node strictly above i0 and at or below 2*i0 (the two per-node facts cross-ne
; wants), so every node's subtree is disjoint from subtree(i0). The build
; loop's sift at j rewrites only positions of subtree(j), leaving these heaps
; alone (frames-congr). The frame window is the SAFE part [j+1, 2j] of the
; build invariant: the children 2j+1, 2j+2 are NOT disjoint from subtree(j)
; and are carried outside the frame (see BInv).
;
; BInv ys n j dj: the build loop's invariant -- the whole window [j+1, 2j+2]
; holds heaps on ys: the two child heaps (2j+1, 2j+2) for the next sift's Kids,
; plus the safe frame [j+1, 2j]. `binv-leaves` fills the initial one (every
; node at or above the half mark is a leaf); `binv-kids` reads the Kids record
; off it; `binv-down` steps it to j-1 after sifting node j.
;
; Contents: le-step / leaf-of-half (kept), q-le-n, Frames + frames-congr /
; frames-leaves / frames-recert, Peel2 + frames-peel2, BInv + binv-leaves /
; binv-kids / binv-down.

; ---- small helpers ----

; NatLe q j implies NatLe q (Succ j).
(def-fns _ $ (erased le-step : (erased (Nat) q) (erased (Nat) j) (subterm erased (NatLe q j) qj)
    -> (erased (NatLe q (Succ j)) out))
  (let-match erased qj (MkNatLe _ _ lp))
  (MkNatLe q (Succ j) (lt-weaken q (Succ j) lp)))

; A node at or above the half mark has its children past the bound: the HLeaf
; shape. From Hf n q (n = 2q + r, r < 2), Double q m, Double j dj, NatLe q j.
(def-fns _ $ (erased leaf-of-half : (erased (Nat) n) (erased (Nat) q) (subterm erased (Hf n q) hf)
    (erased (Nat) j) (erased (Nat) dj) (erased (Double j dj) ddj) (erased (NatLe q j) qj)
    -> (erased (Lt n (Succ (Succ dj))) out))
  (let-match erased hf (MkHf _ _ m mm r ad rl pq))
  (let ((erased mq)) (mul2-double q m mm))
  (let ((erased mdj)) (double-le q j m dj qj mq ddj))
  (let ((erased sm)) (add-small m r n ad rl))
  (let-match erased mdj (MkNatLe _ _ mp))
  (lt-le-trans n (Succ (Succ m)) (Succ (Succ dj)) sm
    (LtS (Succ m) (Succ (Succ dj)) (LtS m (Succ dj) mp))))

; The half mark is at or below the length: q <= n.
(def-fns _ $ (erased q-le-n : (erased (Nat) n) (erased (Nat) q) (subterm erased (Hf n q) hf)
    -> (erased (NatLe q n) out))
  (let-match erased hf (MkHf _ _ m mm r ad rl pq))
  (let ((erased qm)) (MkNatLe q m (mul-le q (Succ (Succ (Zero))) m mm (LtZ (Succ (Zero))))))
  (le-trans q m n qm (MkNatLe m n (add-le-left m r n ad))))

; ---- Frames: the disjoint window's heaps ----

(def-adts
  ((Frames : ((List (Nat)) ys) ((Nat) n) ((Nat) i0) ((Nat) d0) ((Nat) lo) ((Nat) hi) -> Type)
    enum
    (many FrNil : (erased (List (Nat)) ys) (erased (Nat) n) (erased (Nat) i0) (erased (Nat) d0) (erased (Nat) lo)
        -> (Frames ys n i0 d0 lo lo))
    (many FrCons : (erased (List (Nat)) ys) (erased (Nat) n) (erased (Nat) i0) (erased (Nat) d0)
        (erased (Nat) lo) (erased (Nat) hi)
        (erased (Nat) di) (erased (Double lo di) ddl) (erased (Lt i0 lo) ltl) (erased (NatLe lo d0) lel)
        (erased (HeapOn ys n lo di) heap) (erased (Frames ys n i0 d0 (Succ lo) hi) rest)
        -> (Frames ys n i0 d0 lo hi))))

; A window's range is inhabited only left-to-right: lo <= hi (a nonempty
; window with hi < lo is impossible -- used to refute impossible peels).
(def-fns _ $ (erased frames-le : (erased (List (Nat)) ys) (erased (Nat) n) (erased (Nat) i0) (erased (Nat) d0)
    (erased (Nat) lo) (erased (Nat) hi) (subterm erased (Frames ys n i0 d0 lo hi) fr) -> (erased (NatLe lo hi) out))
  (let-match erased fr (FrCons _ _ _ _ _ _ di ddl ltl lel heap rest)
    ((FrNil _ _ _ _ _) (le-refl lo)))
  (let-match erased (frames-le ys n i0 d0 (Succ lo) hi rest) (MkNatLe _ _ lp))
  (let-match erased lp (LtS _ _ lp1))
  (MkNatLe lo hi (lt-weaken lo hi lp1)))

; A write inside subtree(i0) leaves a disjoint window's heaps alone.
(def-fns _ $ (erased frames-congr : (erased (List (Nat)) ys) (erased (Nat) n) (erased (Nat) i0) (erased (Nat) d0)
    (erased (Double i0 d0) dd0) (erased (Nat) lo) (erased (Nat) hi)
    (subterm erased (Frames ys n i0 d0 lo hi) fr)
    (erased (Nat) dm) (erased (Nat) m) (erased (Below i0 d0 m) bm)
    (erased (Nat) w) (erased (List (Nat)) ys') (erased (SetNth (Nat) ys m w ys') st)
    -> (erased (Frames ys' n i0 d0 lo hi) out))
  (let-match erased fr (FrCons _ _ _ _ _ _ di ddl ltl lel heap rest)
    ((FrNil _ _ _ _ _) (FrNil ys' n i0 d0 lo)))
  (let ((erased rest2)) (frames-congr ys n i0 d0 dd0 (Succ lo) hi rest dm m bm w ys' st))
  (let ((erased heap2))
    (congr-cross i0 d0 dd0 lo di ltl lel dm m bm lo (BHere lo di ddl) ys n di heap w ys' st))
  (FrCons ys' n i0 d0 lo hi di ddl ltl lel heap2 rest2))

; A window of leaf heaps: every node in [lo, (Succ d0)) is at or above the half
; mark. The per-node bounds come from the `Add lo c (Succ d0)` counter (lo < hi
; while c > 0).
(def-fns _ $ (erased frames-leaves : (erased (List (Nat)) ys) (erased (Nat) n) (erased (Nat) q)
    (erased (Hf n q) hf) (erased (Nat) i0) (erased (Nat) d0)
    (erased (Nat) lo) (subterm erased (Nat) c) (erased (Add lo c (Succ d0)) ac)
    (erased (Lt i0 lo) ltl) (erased (NatLe q lo) qlo)
    -> (erased (Frames ys n i0 d0 lo (Succ d0)) out))
  (let-match erased c (Succ c1)
    ((Zero)
      (let-match erased (add-eq-zero lo (Succ d0) ac) (Refl _ _))
      (FrNil ys n i0 d0 lo)))
  (let ((erased di) (erased ddl)) (double lo))
  (let ((erased gl)) (leaf-of-half n q hf lo di ddl qlo))
  (let ((erased rest))
    (frames-leaves ys n q hf i0 d0 (Succ lo) c1 (add-move lo c1 (Succ d0) ac) (lt-weaken i0 lo ltl) (le-step q lo qlo)))
  (FrCons ys n i0 d0 lo (Succ d0) di ddl ltl (MkNatLe lo d0 (add-pos-lt lo (Succ c1) (Succ d0) ac (LtZ c1)))
    (HLeaf ys n lo di ddl gl) rest))

; Moving a window to a lower root: the per-node facts about i0 relax (the new
; root is below the old), the per-node bounds come from the counter again.
(def-fns _ $ (erased frames-recert : (erased (List (Nat)) ys) (erased (Nat) n) (erased (Nat) i0) (erased (Nat) d0)
    (erased (Nat) lo) (erased (Nat) d2) (subterm erased (Nat) k) (erased (Add lo k (Succ d2)) ac)
    (subterm erased (Frames ys n i0 d0 lo (Succ d2)) fr)
    (erased (Nat) i2) (erased (Lt i2 lo) ltl) -> (erased (Frames ys n i2 d2 lo (Succ d2)) out))
  (let-match erased k (Succ k1)
    ((Zero)
      (let-match erased (add-eq-zero lo (Succ d2) ac) (Refl _ _))
      (FrNil ys n i2 d2 lo)))
  (let-match erased fr (FrCons _ _ _ _ _ _ di ddl ltl0 lel0 heap rest)
    (absurd (FrNil _ _ _ _ _)
      (let ((erased bad)) (add-pos-lt lo (Succ k1) (Succ d2) ac (LtZ k1)))
      (lt-irrefl lo bad)))
  (FrCons ys n i2 d2 lo (Succ d2) di ddl ltl (MkNatLe lo d2 (add-pos-lt lo (Succ k1) (Succ d2) ac (LtZ k1)))
    heap
    (frames-recert ys n i0 d0 (Succ lo) d2 k1 (add-move lo k1 (Succ d2) ac) rest i2 (lt-weaken i2 lo ltl))))

; ---- Peel2: the top of a window, zero, one or two entries ----

(def-adts
  ((Peel2 : ((List (Nat)) ys) ((Nat) n) ((Nat) i0) ((Nat) d0) ((Nat) lo) ((Nat) hi) -> Type)
    enum
    (many P2Zero : (erased (List (Nat)) ys) (erased (Nat) n) (erased (Nat) i0) (erased (Nat) d0) (erased (Nat) lo)
        -> (Peel2 ys n i0 d0 lo lo))
    (many P2One : (erased (List (Nat)) ys) (erased (Nat) n) (erased (Nat) i0) (erased (Nat) d0) (erased (Nat) lo)
        (erased (Nat) di) (erased (Double lo di) ddl) (erased (HeapOn ys n lo di) heap)
        -> (Peel2 ys n i0 d0 lo (Succ lo)))
    (many P2Two : (erased (List (Nat)) ys) (erased (Nat) n) (erased (Nat) i0) (erased (Nat) d0) (erased (Nat) lo)
        (erased (Nat) m1)
        (erased (Nat) dm1) (erased (Double m1 dm1) ddm1)
        (erased (Nat) dm2) (erased (Double (Succ m1) dm2) ddm2)
        (erased (HeapOn ys n m1 dm1) h1) (erased (HeapOn ys n (Succ m1) dm2) h2)
        (erased (Frames ys n i0 d0 lo m1) front)
        -> (Peel2 ys n i0 d0 lo (Succ (Succ m1))))))

; The last two entries of a window (positions hi-2, hi-1) and the front below
; them. A window of 0 or 1 entries comes back as P2Zero / P2One.
(def-fns _ $ (erased frames-peel2 : (erased (List (Nat)) ys) (erased (Nat) n) (erased (Nat) i0) (erased (Nat) d0)
    (erased (Nat) lo) (erased (Nat) hi) (subterm erased (Frames ys n i0 d0 lo hi) fr)
    -> (erased (Peel2 ys n i0 d0 lo hi) out))
  (let-match erased fr (FrCons _ _ _ _ _ _ di ddl ltl lel heap rest)
    ((FrNil _ _ _ _ _) (P2Zero ys n i0 d0 lo)))
  (let ((erased peel)) (frames-peel2 ys n i0 d0 (Succ lo) hi rest))
  (let-match erased peel (P2Two _ _ _ _ _ m1 dm1 ddm1 dm2 ddm2 h1 h2 front)
    ((P2Zero _ _ _ _ _)
      (P2One ys n i0 d0 lo di ddl heap))
    ((P2One _ _ _ _ _ di2 ddl2 heap2)
      (P2Two ys n i0 d0 lo lo di ddl di2 ddl2 heap heap2 (FrNil ys n i0 d0 lo))))
  (P2Two ys n i0 d0 lo m1 dm1 ddm1 dm2 ddm2 h1 h2 (FrCons ys n i0 d0 lo m1 di ddl ltl lel heap front)))

; ---- BInv: the build loop's window ----

(def-adts
  ((BInv : ((List (Nat)) ys) ((Nat) n) ((Nat) j) ((Nat) dj) -> Type)
    enum
    (many MkBInv : (erased (List (Nat)) ys) (erased (Nat) n) (erased (Nat) j) (erased (Nat) dj)
        (erased (Nat) d2) (erased (Double (Succ dj) d2) dd2) (erased (HeapOn ys n (Succ dj) d2) heapl)
        (erased (Nat) d3) (erased (Double (Succ (Succ dj)) d3) dd3) (erased (HeapOn ys n (Succ (Succ dj)) d3) heapr)
        (erased (Frames ys n j dj (Succ j) (Succ dj)) fr)
        -> (BInv ys n j dj))))

; The initial window at the half mark: every node in [j+1, 2j+2] is a leaf.
(def-fns _ $ (erased binv-leaves : (erased (List (Nat)) ys) (erased (Nat) n) (erased (Nat) q) (erased (Hf n q) hf)
    (erased (Nat) j) (erased (Nat) dj) (erased (Double j dj) ddj) (erased (NatLe q (Succ j)) qj)
    -> (erased (BInv ys n j dj) out))
  (let ((erased d2) (erased dd2)) (double (Succ dj)))
  (let ((erased d3) (erased dd3)) (double (Succ (Succ dj))))
  (let ((erased qk)) (le-trans q (Succ j) (Succ dj) qj (MkNatLe (Succ j) (Succ dj) (LtS j (Succ dj) (double-lt j dj ddj)))))
  (let ((erased gl)) (leaf-of-half n q hf (Succ dj) d2 dd2 qk))
  (let ((erased gr)) (leaf-of-half n q hf (Succ (Succ dj)) d3 dd3 (le-step q (Succ dj) qk)))
  (let ((erased fr))
    (frames-leaves ys n q hf j dj (Succ j) j (AddSucc j j dj (double-add j dj ddj)) (lt-succ j) qj))
  (MkBInv ys n j dj d2 dd2 (HLeaf ys n (Succ dj) d2 dd2 gl) d3 dd3 (HLeaf ys n (Succ (Succ dj)) d3 dd3 gr) fr))

; The Kids record for sifting node j: its two child heaps and one erased
; boundary test (the children may straddle the bound).
(def-fns _ $ (erased binv-kids : (erased (List (Nat)) ys) (erased (List (Copy (Nat))) ds)
    (erased (Copies (Nat) ys ds) rel) (erased (Nat) n) (erased (Length (Nat) ys n) ly)
    (erased (Nat) j) (erased (Nat) dj) (erased (Double j dj) ddj)
    (subterm erased (BInv ys n j dj) binv) -> (erased (Kids ys n j dj) out))
  (let-match erased binv (MkBInv _ _ _ _ d2 dd2 heapl d3 dd3 heapr fr))
  (let ((erased t)) (tri (Succ (Succ dj)) n))
  (let-match erased t (TriE _ _ e)
    ((TriL _ _ rin)
      (let ((erased y) (erased ny) (erased _))
        (nth-pair ys ds rel n ly (Succ dj) (lt-trans (Succ dj) (Succ (Succ dj)) n (lt-succ (Succ dj)) rin)))
      (let ((erased z) (erased nz) (erased _)) (nth-pair ys ds rel n ly (Succ (Succ dj)) rin))
      (KTwo ys n j dj ddj d2 dd2 d3 dd3 y z ny nz rin heapl heapr))
    ((TriG _ _ nl) (KLeaf ys n j dj ddj nl)))
  (let-match erased e (Refl _ _))
  (let ((erased y) (erased ny) (erased _)) (nth-pair ys ds rel n ly (Succ dj) (lt-succ (Succ dj))))
  (KOne ys n j dj ddj d2 dd2 y ny (lt-succ (Succ dj)) (lt-succ (Succ (Succ dj))) heapl))

; The window for j-1 after sifting node j = Succ j1: the sift's output heap at
; j and the transported safe frame give BInv at j1. The frame's top two
; (2j-1, 2j) become j1's child heaps; @j joins the frame at the front (unless
; j = 1, where @j IS the left child and the frame is empty).
(def-fns _ $ (erased binv-down : (erased (List (Nat)) ys) (erased (Nat) n)
    (erased (Nat) j1) (erased (Nat) dj1) (erased (Double j1 dj1) ddj1)
    (erased (HeapOn ys n (Succ j1) (Succ (Succ dj1))) newh)
    (erased (Frames ys n (Succ j1) (Succ (Succ dj1)) (Succ (Succ j1)) (Succ (Succ (Succ dj1)))) fr)
    -> (erased (BInv ys n j1 dj1) out))
  (let ((erased peel))
    (frames-peel2 ys n (Succ j1) (Succ (Succ dj1)) (Succ (Succ j1)) (Succ (Succ (Succ dj1))) fr))
  (let-match erased peel (P2Two _ _ _ _ _ m1 dm1 ddm1 dm2 ddm2 h1 h2 front)
    (absurd (P2Zero _ _ _ _ _)
      (lt-irrefl j1 (double-lt j1 dj1 ddj1)))
    ((P2One _ _ _ _ _ di ddl heap)
      (MkBInv ys n j1 dj1 (Succ (Succ dj1)) (DS j1 dj1 ddj1) newh di ddl heap (FrNil ys n j1 dj1 (Succ j1)))))
  (let-match erased ddj1 (DS j0 dj0 ddj0)
    (absurd (D0)
      (let-match erased (frames-le ys n (Succ j1) (Succ (Succ dj1)) (Succ (Succ j1)) (Succ dj1) front) (MkNatLe _ _ bad))
      (lt-irrefl (Succ (Succ j1)) bad)))
  (MkBInv ys n j1 dj1 dm1 ddm1 h1 dm2 ddm2 h2
    (FrCons ys n j1 dj1 (Succ j1) (Succ dj1) (Succ (Succ dj1)) (DS j1 dj1 ddj1) (lt-succ j1)
      (MkNatLe (Succ j1) dj1 (LtS (Succ j0) (Succ (Succ dj0)) (LtS j0 (Succ dj0) (double-lt j0 dj0 ddj0))))
      newh
      (frames-recert ys n (Succ j1) (Succ (Succ dj1)) (Succ (Succ j1)) dj1 j0
        (AddSucc (Succ (Succ j0)) j0 (Succ (Succ dj0))
          (AddSucc (Succ j0) j0 (Succ dj0) (AddSucc j0 j0 dj0 (double-add j0 dj0 ddj0))))
        front j1 (lt-weaken j1 (Succ j1) (lt-succ j1))))))
