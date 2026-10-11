(def-adts
  ((LenU : ((ULst) xs) ((Nat) n) -> Type)
    enum
    (many LNil : -> (LenU (UNil) (Zero)))
    (many LCons : (erased (U62) x) (erased (ULst) xs) (erased (Nat) n) (erased (LenU xs n) p)
       -> (LenU (UCons x xs) (Succ n)))))

(def-adts
  ((CatU : ((ULst) a) ((ULst) b) ((ULst) c) -> Type)
    enum
    (many CatNil : (erased (ULst) b) -> (CatU (UNil) b b))
    (many CatCons : (erased (U62) x) (erased (ULst) a) (erased (ULst) b) (erased (ULst) c) (erased (CatU a b c) p)
       -> (CatU (UCons x a) b (UCons x c)))))

(def-adts
  ((MergeU : ((ULst) a) ((ULst) b) ((ULst) m) -> Type)
    enum
    (many MNilL : (erased (ULst) b) -> (MergeU (UNil) b b))
    (many MNilR : (erased (ULst) a) -> (MergeU a (UNil) a))
    (many MLeft : (erased (U62) x) (erased (ULst) xt) (erased (U62) y) (erased (ULst) yt) (erased (ULst) m)
       (erased (LeU x y) l) (erased (MergeU xt (UCons y yt) m) p)
       -> (MergeU (UCons x xt) (UCons y yt) (UCons x m)))
    (many MRight : (erased (U62) x) (erased (ULst) xt) (erased (U62) y) (erased (ULst) yt) (erased (ULst) m)
       (erased (LeU y x) l) (erased (MergeU (UCons x xt) yt m) p)
       -> (MergeU (UCons x xt) (UCons y yt) (UCons y m)))))

(def-fns _ $ (erased perm-refl : (subterm erased (ULst) a) -> (erased (PermU a a) p))
  (match erased a _
    ((UNil) (PNil))
    ((UCons x t) (PSkip x t t (perm-refl t)))))

(def-fns _ $ (erased cat-exists : (subterm erased (ULst) a) (erased (ULst) b) -> (erased (ULst) c) (erased (CatU a b c) p))
  (let-match erased a (UCons x t) ((UNil) (values b (CatNil b))))
  (let ((erased c1) (erased p1)) (cat-exists t b))
  (values (UCons x c1) (CatCons x t b c1 p1)))

(def-fns _ $ (erased cat-nil-right : (subterm erased (ULst) a) -> (erased (CatU a (UNil) a) p))
  (match erased a _
    ((UNil) (CatNil (UNil)))
    ((UCons x t) (CatCons x t (UNil) t (cat-nil-right t)))))

(def-fns _ $ (erased cat-fn : (erased (ULst) a) (erased (ULst) b) (erased (ULst) c1) (erased (ULst) c2)
    (subterm erased (CatU a b c1) p) (erased (CatU a b c2) q) -> (erased (Eq (ULst) c1 c2) e))
  (match erased p _
    ((CatNil _) (let-match erased q (CatNil _)) (Refl (ULst) c1))
    ((CatCons x t _ d1 p1)
      (let-match erased q (CatCons _ _ _ d2 q1))
      (match erased (cat-fn t b d1 d2 p1 q1) _ ((Refl _ _) (Refl (ULst) c1))))))

(def-fns _ $ (erased perm-middle : (erased (U62) y) (erased (ULst) yt) (erased (ULst) a) (erased (ULst) c) (erased (ULst) d)
    (subterm erased (CatU a (UCons y yt) c) p) (erased (CatU a yt d) q) -> (erased (PermU c (UCons y d)) r))
  (match erased p _
    ((CatNil _) (let-match erased q (CatNil _)) (perm-refl c))
    ((CatCons z a1 _ c1 p1)
      (let-match erased q (CatCons _ _ _ d1 q1))
      (PTrans _ _ _ (PSkip z c1 (UCons y d1) (perm-middle y yt a1 c1 d1 p1 q1)) (PSwap z y d1)))))

(def-fns _ $ (erased perm-cat-right : (erased (ULst) a) (erased (ULst) b) (erased (ULst) b2) (erased (ULst) c) (erased (ULst) c2)
    (erased (PermU b b2) pb) (subterm erased (CatU a b c) p) (erased (CatU a b2 c2) q) -> (erased (PermU c c2) r))
  (match erased p _
    ((CatNil _) (let-match erased q (CatNil _)) pb)
    ((CatCons x a1 _ c1 p1)
      (let-match erased q (CatCons _ _ _ d1 q1))
      (PSkip x c1 d1 (perm-cat-right a1 b b2 c1 d1 pb p1 q1)))))

(def-fns _ $ (erased perm-cat-left : (erased (ULst) a) (erased (ULst) a2) (erased (ULst) b) (erased (ULst) c) (erased (ULst) c2)
    (subterm erased (PermU a a2) pa) (erased (CatU a b c) p) (erased (CatU a2 b c2) q) -> (erased (PermU c c2) r))
  (match erased pa _
    ((PNil) (let-match erased p (CatNil _)) (let-match erased q (CatNil _)) (perm-refl c))
    ((PSkip x t t2 pt)
      (let-match erased p (CatCons _ _ _ c1 p1))
      (let-match erased q (CatCons _ _ _ d1 q1))
      (PSkip x c1 d1 (perm-cat-left t t2 b c1 d1 pt p1 q1)))
    ((PSwap x y t)
      (let-match erased p (CatCons _ _ _ c1 p1))
      (let-match erased p1 (CatCons _ _ _ c3 p3))
      (let-match erased q (CatCons _ _ _ d1 q1))
      (let-match erased q1 (CatCons _ _ _ d3 q3))
      (let-match erased (cat-fn t b c3 d3 p3 q3) (Refl _ _))
      (PSwap x y c3))
    ((PTrans _ m _ pam pma2)
      (let ((erased cm) (erased pm)) (cat-exists m b))
      (PTrans _ _ _ (perm-cat-left a m b c cm pam p pm) (perm-cat-left m a2 b cm c2 pma2 pm q)))))

(def-fns _ $ (erased merge-perm : (erased (ULst) a) (erased (ULst) b) (erased (ULst) m) (erased (ULst) c)
    (subterm erased (MergeU a b m) pm) (erased (CatU a b c) p) -> (erased (PermU c m) r))
  (match erased pm _
    ((MNilL _) (let-match erased p (CatNil _)) (perm-refl c))
    ((MNilR _)
      (let-match erased (cat-fn a (UNil) c a p (cat-nil-right a)) (Refl _ _))
      (perm-refl c))
    ((MLeft x xt y yt m2 l q)
      (let-match erased p (CatCons _ _ _ c1 p1))
      (PSkip x c1 m2 (merge-perm xt b m2 c1 q p1)))
    ((MRight x xt y yt m2 l q)
      (let ((erased d) (erased pd)) (cat-exists a yt))
      (PTrans _ _ _ (perm-middle y yt a c d p pd) (PSkip y d m2 (merge-perm a yt m2 d q pd))))))

(def-fns _ $ (erased merge-lehead : (erased (U62) z) (erased (ULst) a) (erased (ULst) b) (erased (ULst) m)
    (erased (LeHead z a) ha) (erased (LeHead z b) hb) (erased (MergeU a b m) pm) -> (erased (LeHead z m) h))
  (match erased pm _
    ((MNilL _) hb)
    ((MNilR _) ha)
    ((MLeft x xt y yt m2 l q) (let-match erased ha (LHCons _ _ _ lz)) (LHCons z x m2 lz))
    ((MRight x xt y yt m2 l q) (let-match erased hb (LHCons _ _ _ lz)) (LHCons z y m2 lz))))

(def-fns _ $ (erased merge-sorted : (erased (ULst) a) (erased (ULst) b) (erased (ULst) m)
    (erased (SortedU a) sa) (erased (SortedU b) sb) (subterm erased (MergeU a b m) pm) -> (erased (SortedU m) s))
  (match erased pm _
    ((MNilL _) sb)
    ((MNilR _) sa)
    ((MLeft x xt y yt m2 l q)
      (let-match erased sa (SortCons _ _ hx sxt))
      (SortCons x m2 (merge-lehead x xt b m2 hx (LHCons x y yt l) q) (merge-sorted xt b m2 sxt sb q)))
    ((MRight x xt y yt m2 l q)
      (let-match erased sb (SortCons _ _ hy syt))
      (SortCons y m2 (merge-lehead y a yt m2 (LHCons y x xt l) hy q) (merge-sorted a yt m2 sa syt q)))))

(def-fns _ $ (erased double-add : (erased (Nat) m) (erased (Nat) d) (subterm erased (Double m d) dd) -> (erased (Add m m d) p))
  (match erased dd _
    ((D0) (AddZero (Zero)))
    ((DS a b d1) (AddSucc a (Succ a) (Succ b) (add-succ-right a a b (double-add a b d1))))))

(def-fns _ $ (erased add-shift : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Add a (Succ b) c) p) ->
    (erased (Add (Succ a) b c) q))
  (let ((erased c1) (erased e) (erased q)) (add-succ-right-inv a b c p))
  (match erased e _ ((Refl _ _) (AddSucc a b c1 q))))
