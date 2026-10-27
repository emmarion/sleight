(def-adts $ (Ver : -> Type)
  enum
  (many V0 : -> (Ver))
  (many V1 : (many (Ver) a) -> (Ver))
  (many V2 : (many (Ver) a) (many (Ver) b) -> (Ver)))

(def-adts
  ((Where : ((Nat) k) ((Nat) m) ((Nat) k2) -> Type)
    enum
    (many Hi : (erased (Nat) k m) (erased (NatLe m k) p) -> (Where k m k))
    (many Lo : (erased (Nat) k m k2) (erased (Lt k m) p) (erased (Lt k2 m) q) -> (Where k m k2))))

(def-adts
  ((KidOk : ((List (Nat)) xs) ((Nat) m) ((Nat) c) ((Nat) u) -> Type)
    enum
    (many KOut : (erased (List (Nat)) xs) (erased (Nat) m c u) (erased (NatLe m c) p) -> (KidOk xs m c u))
    (many KIn : (erased (List (Nat)) xs) (erased (Nat) m c u v) (erased (Nth (Nat) xs c v) n) (erased (NatLe v u) p)
       -> (KidOk xs m c u))))

(def-fns _ $ (erased where-of : (erased (Nat) k m) -> (erased (Where k m k) r))
  (match erased (nat-cmp k m) _
    ((CLt _ _ _ _ p) (Lo k m k p p))
    ((CEq _ _ _) (Hi k k (le-refl k)))
    ((CGt _ _ _ _ p) (Hi k m (lt-le m k p)))))

(def-fns _ $ (erased kid-le : (erased (List (Nat)) xs) (erased (Nat) m j u x) (erased (KidOk xs m j u) k) (erased (Lt j m) jm)
    (erased (Nth (Nat) xs j x) nx) -> (erased (NatLe x u) r))
  (let-match erased k (KIn _ _ _ _ v nv le) (absurd (KOut _ _ _ _ p) (lt-not-le j m jm p)))
  (let-match erased (nth-fn _ _ _ _ _ nx nv) (Refl _ _))
  le)

(def-fns _ $ (erased where-lo : (erased (Nat) a m k2 b) (erased (Where a m k2) wh) (erased (Lt a m) am) (erased (Lt b m) bm)
    -> (erased (Where b m k2) r))
  (let-match erased wh (Lo _ _ _ _ q) (absurd (Hi _ _ p) (lt-not-le a m am p)))
  (Lo b m k2 bm q))

(def-fns _ $ (erased absurd ne-irrefl : (erased (Nat) a) (erased (Ne a a) ne) -> (erased (False) f))
  (match erased ne _ (absurd (NeLt _ _ p) (lt-irrefl a p)) (absurd (NeGt _ _ p) (lt-irrefl a p))))

(def-lvl Inv)

; Each package holds an `Inv`-level proof function and its version v; a function may call
; only functions whose versions are strict subterms of its own (§17, §19).
(def-adts
  ((HeapExc : ((List (Nat)) xs) ((Nat) k) ((Nat) i) ((Nat) m) -> Type)
    enum
    (many MkHeapExc : (erased (List (Nat)) xs) (erased (Nat) k i m) (erased (Ver) v)
       (erased (Fn Inv (subterm erased v is w) (erased (Nat) p j x y) (erased (NatLe k p) kp) (erased (Ne p i) pi)
          (erased (Child p j) c) (erased (Lt j m) jm) (erased (Nth (Nat) xs j x) nx) (erased (Nth (Nat) xs p y) ny)
          -> (erased (NatLe x y) r)) f)
       -> (HeapExc xs k i m))))

(def-adts
  ((Grand : ((List (Nat)) xs) ((Nat) k) ((Nat) i) ((Nat) m) -> Type)
    enum
    (many MkGrand : (erased (List (Nat)) xs) (erased (Nat) k i m) (erased (Ver) v)
       (erased (Fn Inv (subterm erased v is w) (erased (Nat) q j x y) (erased (NatLe k q) kq) (erased (Child q i) cq)
          (erased (Child i j) c) (erased (Lt j m) jm) (erased (Nth (Nat) xs j x) nx) (erased (Nth (Nat) xs q y) ny)
          -> (erased (NatLe x y) r)) f)
       -> (Grand xs k i m))))

(def-adts
  ((Suffix : ((List (Nat)) xs) ((Nat) m) -> Type)
    enum
    (many MkSuffix : (erased (List (Nat)) xs) (erased (Nat) m) (erased (Ver) v)
       (erased (Fn Inv (subterm erased v is w) (erased (Nat) i j x y) (erased (Lt i j) ij) (erased (NatLe m j) mj)
          (erased (Nth (Nat) xs i x) nx) (erased (Nth (Nat) xs j y) ny) -> (erased (NatLe x y) r)) f)
       -> (Suffix xs m))))

(def-adts
  ((Stays : ((List (Nat)) xs) ((List (Nat)) ys) ((Nat) m) -> Type)
    enum
    (many MkStays : (erased (List (Nat)) xs ys) (erased (Nat) m) (erased (Ver) v)
       (erased (Fn Inv (subterm erased v is w) (erased (Nat) k z) (erased (Nth (Nat) ys k z) n) ->
          (erased (Nat) k2) (erased (Nth (Nat) xs k2 z) n2) (erased (Where k m k2) wh)) f)
       -> (Stays xs ys m))))

(def-adts
  ((CMax : ((List (Nat)) xs) ((Nat) i) ((Nat) m) ((Nat) u) -> Type)
    enum
    (many MkCMax : (erased (List (Nat)) xs) (erased (Nat) i m u) (erased (Ver) v)
       (erased (Fn Inv (subterm erased v is w) (erased (Nat) j x) (erased (Child i j) c) (erased (Lt j m) jm)
          (erased (Nth (Nat) xs j x) nx) -> (erased (NatLe x u) r)) f)
       -> (CMax xs i m u))))

(def-adts
  ((Max : ((List (Nat)) xs) ((Nat) m) ((Nat) r) -> Type)
    enum
    (many MkMax : (erased (List (Nat)) xs) (erased (Nat) m r) (erased (Ver) v)
       (erased (Fn Inv (subterm erased v is w) (subterm erased (Nat) a) (erased (Nat) x) (erased (Lt a m) am)
          (erased (Nth (Nat) xs a x) nx) -> (erased (NatLe x r) le)) f)
       -> (Max xs m r))))


(def-fns _ $ (erased heap-top : (erased (List (Nat)) xs) (erased (Nat) n q) (erased (Half2 n q) h) -> (erased (HeapExc xs q n n) r))
  (def-fns Inv $ (erased absurd f : (subterm erased (V0) is w) (erased (Nat) p j x y) (erased (NatLe q p) kp) (erased (Ne p n) pi)
      (erased (Child p j) c) (erased (Lt j n) jm) (erased (Nth (Nat) xs j x) nx) (erased (Nth (Nat) xs p y) ny) -> (erased (NatLe x y) r))
    (lt-not-le j n jm (kids-out n q p j h kp c)))
  (MkHeapExc xs q n n (V0) f))

(def-fns _ $ (erased heap-down : (erased (List (Nat)) xs) (erased (Nat) i n) (erased (HeapExc xs (Succ i) n n) h)
    -> (erased (HeapExc xs i i n) r))
  (let-match erased h (MkHeapExc _ _ _ _ v g))
  (def-fns Inv $ (erased f : (subterm erased (V1 v) is w) (erased (Nat) p j x y) (erased (NatLe i p) kp) (erased (Ne p i) pi)
      (erased (Child p j) c) (erased (Lt j n) jm) (erased (Nth (Nat) xs j x) nx) (erased (Nth (Nat) xs p y) ny) -> (erased (NatLe x y) r))
    (g v p j x y (MkNatLe _ _ (LtS _ _ (le-ne-lt i p kp pi))) (ne-top p j n c jm) c jm nx ny))
  (MkHeapExc xs i i n (V1 v) f))

(def-fns _ $ (erased grand-none : (erased (List (Nat)) xs) (erased (Nat) k m) -> (erased (Grand xs k k m) r))
  (def-fns Inv $ (erased absurd f : (subterm erased (V0) is w) (erased (Nat) q j x y) (erased (NatLe k q) kq) (erased (Child q k) cq)
      (erased (Child k j) c) (erased (Lt j m) jm) (erased (Nth (Nat) xs j x) nx) (erased (Nth (Nat) xs q y) ny) -> (erased (NatLe x y) r))
    (lt-not-le q k (child-lt q k cq) kq))
  (MkGrand xs k k m (V0) f))

(def-fns _ $ (erased stays-id : (erased (List (Nat)) xs) (erased (Nat) m) -> (erased (Stays xs xs m) r))
  (def-fns Inv $ (erased f : (subterm erased (V0) is w) (erased (Nat) k z) (erased (Nth (Nat) xs k z) n) ->
      (erased (Nat) k2) (erased (Nth (Nat) xs k2 z) n2) (erased (Where k m k2) wh))
    (values k n (where-of k m)))
  (MkStays xs xs m (V0) f))

(def-fns _ $ (erased cmax : (erased (List (Nat)) xs) (erased (Nat) i e m u) (erased (Double i e) de)
    (erased (KidOk xs m (Succ e) u) k1) (erased (KidOk xs m (Succ (Succ e)) u) k2) -> (erased (CMax xs i m u) r))
  (def-fns Inv $ (erased f : (subterm erased (V0) is w) (erased (Nat) j x) (erased (Child i j) c) (erased (Lt j m) jm)
      (erased (Nth (Nat) xs j x) nx) -> (erased (NatLe x u) r))
    (match erased c _
      ((ChL _ d dd) (let-match erased (double-fn i d e dd de) (Refl _ _)) (kid-le _ _ _ _ _ k1 jm nx))
      ((ChR _ d dd) (let-match erased (double-fn i d e dd de) (Refl _ _)) (kid-le _ _ _ _ _ k2 jm nx))))
  (MkCMax xs i m u (V0) f))

(def-fns _ $ (erased sift-done : (erased (List (Nat)) xs) (erased (Nat) k i m vi u) (erased (HeapExc xs k i m) h)
    (erased (CMax xs i m u) cm) (erased (Nth (Nat) xs i vi) ni) (erased (NatLe u vi) uv) -> (erased (HeapExc xs k m m) r))
  (let-match erased h (MkHeapExc _ _ _ _ vh g))
  (let-match erased cm (MkCMax _ _ _ _ vc gc))
  (def-fns Inv $ (erased f : (subterm erased (V2 vh vc) is w) (erased (Nat) p j x y) (erased (NatLe k p) kp) (erased (Ne p m) pm)
      (erased (Child p j) c) (erased (Lt j m) jm) (erased (Nth (Nat) xs j x) nx) (erased (Nth (Nat) xs p y) ny) -> (erased (NatLe x y) r))
    (let-match erased (eq-ne p i) (Diff _ _ pi)
      ((Same _)
        (let-match erased (nth-fn _ _ _ _ _ ny ni) (Refl _ _))
        (le-le x u y (gc vc j x c jm nx) uv)))
    (g vh p j x y kp pi c jm nx ny))
  (MkHeapExc xs k m m (V2 vh vc) f))

(def-fns _ $ (erased sift-swap : (erased (List (Nat)) xs0 xs ys) (erased (Nat) k i c m vi vc) (erased (Swap xs i c ys) sw)
    (erased (Child i c) ic) (erased (Lt c m) cm) (erased (NatLe k i) ki) (erased (Nth (Nat) xs i vi) ni) (erased (Nth (Nat) xs c vc) nc)
    (erased (Lt vi vc) lt) (erased (HeapExc xs k i m) h) (erased (Grand xs k i m) gr) (erased (CMax xs i m vc) cmx)
    (erased (Stays xs0 xs m) st) -> (erased (HeapExc ys k c m) h2) (erased (Grand ys k c m) gr2) (erased (Stays xs0 ys m) st2))
  (let-match erased h (MkHeapExc _ _ _ _ vh fh))
  (let-match erased gr (MkGrand _ _ _ _ vg fg))
  (let-match erased cmx (MkCMax _ _ _ _ vm fm))
  (let-match erased st (MkStays _ _ _ vs fs))
  (let ((erased ltic)) (child-lt i c ic))
  (let ((erased im)) (lt-trans i c m ltic cm))
  (def-fns Inv $ (erased fh2 : (subterm erased (V2 vh (V2 vg vm)) is w) (erased (Nat) p j x y) (erased (NatLe k p) kp) (erased (Ne p c) pc)
      (erased (Child p j) cj) (erased (Lt j m) jm) (erased (Nth (Nat) ys j x) nx) (erased (Nth (Nat) ys p y) ny) -> (erased (NatLe x y) r))
    (let-match erased (eq-ne p i) (Diff _ _ pi)
      ((Same _)
        (let-match erased (nth-fn _ _ _ _ _ (swap-at-i _ _ _ _ _ sw ltic ny) nc) (Refl _ _))
        (let-match erased (eq-ne j c) (Diff _ _ jc)
          ((Same _)
            (let-match erased (nth-fn _ _ _ _ _ (swap-at-j _ _ _ _ _ sw nx) ni) (Refl _ _))
            (lt-le _ _ lt)))
        (fm vm j x cj jm (swap-at _ _ _ _ _ _ sw (NeGt j i (child-lt i j cj)) jc nx))))
    (let ((erased ny2)) (swap-at _ _ _ _ _ _ sw pi pc ny))
    (let-match erased (eq-ne j i) (Diff _ _ ji)
      ((Same _) (fg vg p c x y kp cj ic cm (swap-at-i _ _ _ _ _ sw ltic nx) ny2)))
    (let-match erased (eq-ne j c) (Diff _ _ jc)
      (absurd (Same _) (let-match erased (child-fn p i c cj ic) (Refl _ _)) (ne-irrefl p pi)))
    (fh vh p j x y kp pi cj jm (swap-at _ _ _ _ _ _ sw ji jc nx) ny2))
  (def-fns Inv $ (erased fg2 : (subterm erased (V1 vh) is w) (erased (Nat) q j x y) (erased (NatLe k q) kq) (erased (Child q c) cq)
      (erased (Child c j) cj) (erased (Lt j m) jm) (erased (Nth (Nat) ys j x) nx) (erased (Nth (Nat) ys q y) ny) -> (erased (NatLe x y) r))
    (let-match erased (child-fn q i c cq ic) (Refl _ _))
    (let ((erased cjl)) (child-lt c j cj))
    (fh vh c j x y (le-le k i c ki (lt-le i c ltic)) (NeGt c i ltic) cj jm
      (swap-at _ _ _ _ _ _ sw (NeGt j i (lt-trans i c j ltic cjl)) (NeGt j c cjl) nx) (swap-at-i _ _ _ _ _ sw ltic ny)))
  (def-fns Inv $ (erased fs2 : (subterm erased (V1 vs) is w) (erased (Nat) kk z) (erased (Nth (Nat) ys kk z) n) ->
      (erased (Nat) k2) (erased (Nth (Nat) xs0 k2 z) n2) (erased (Where kk m k2) wh))
    (let-match erased (eq-ne kk i) (Diff _ _ kki)
      ((Same _)
        (let ((erased k2) (erased n2) (erased wh)) (fs vs c z (swap-at-i _ _ _ _ _ sw ltic n)))
        (values k2 n2 (where-lo c m k2 kk wh cm im))))
    (let-match erased (eq-ne kk c) (Diff _ _ kkc)
      ((Same _)
        (let ((erased k2) (erased n2) (erased wh)) (fs vs i z (swap-at-j _ _ _ _ _ sw n)))
        (values k2 n2 (where-lo i m k2 kk wh im cm))))
    (fs vs kk z (swap-at _ _ _ _ _ _ sw kki kkc n)))
  (values (MkHeapExc ys k c m (V2 vh (V2 vg vm)) fh2) (MkGrand ys k c m (V1 vh) fg2) (MkStays xs0 ys m (V1 vs) fs2)))

(def-fns _ $ (erased down-heap : (erased (List (Nat)) xs ys) (erased (Nat) m1) (erased (Swap xs (Zero) m1 ys) sw)
    (erased (HeapExc xs (Zero) (Succ m1) (Succ m1)) h) -> (erased (HeapExc ys (Zero) (Zero) m1) r))
  (let-match erased h (MkHeapExc _ _ _ _ v g))
  (def-fns Inv $ (erased f : (subterm erased (V1 v) is w) (erased (Nat) p j x y) (erased (NatLe (Zero) p) kp) (erased (Ne p (Zero)) pz)
      (erased (Child p j) c) (erased (Lt j m1) jm) (erased (Nth (Nat) ys j x) nx) (erased (Nth (Nat) ys p y) ny) -> (erased (NatLe x y) r))
    (let ((erased pj)) (child-lt p j c))
    (let ((erased pm)) (lt-trans p j m1 pj jm))
    (g v p j x y kp (NeLt p (Succ m1) (lt-weaken p m1 pm)) c (lt-weaken j m1 jm)
      (swap-at _ _ _ _ _ _ sw (NeGt j (Zero) (le-lt-lt (Zero) p j kp pj)) (NeLt j m1 jm) nx)
      (swap-at _ _ _ _ _ _ sw pz (NeLt p m1 pm) ny)))
  (MkHeapExc ys (Zero) (Zero) m1 (V1 v) f))

(def-fns _ $ (erased rootmax : (erased (List (Nat)) xs) (erased (Nat) n m r) (erased (Length (Nat) xs n) len) (erased (NatLe m n) mn)
    (erased (HeapExc xs (Zero) m m) h) (erased (Nth (Nat) xs (Zero) r) nr) -> (erased (Max xs m r) mx))
  (let-match erased h (MkHeapExc _ _ _ _ v g))
  (def-fns Inv $ (erased f : (subterm erased (V1 v) is w) (subterm erased (Nat) a) (erased (Nat) x) (erased (Lt a m) am)
      (erased (Nth (Nat) xs a x) nx) -> (erased (NatLe x r) le))
    (let-match erased a (Succ a1)
      ((Zero) (let-match erased (nth-fn _ _ _ _ _ nx nr) (Refl _ _)) (le-refl x)))
    (let ((erased p) (erased c)) (parent a (LtZ a1)))
    (let ((erased pa)) (child-lt p a c))
    (let ((erased pm)) (lt-trans p a m pa am))
    (let ((erased y) (erased ny)) (nth-exists _ _ _ _ len (lt-le-lt p m n pm mn)))
    (le-le x y r (g v p a x y (MkNatLe _ _ (LtZ p)) (ne-top p a m c am) c am nx ny)
      (f w (subterm (lt-subterm p a pa)) p y pm ny)))
  (MkMax xs m r (V1 v) f))

(def-fns _ $ (erased down-suffix : (erased (List (Nat)) xs ys zs) (erased (Nat) n m1 r) (erased (Length (Nat) xs n) len)
    (erased (NatLe (Succ m1) n) mn) (erased (HeapExc xs (Zero) (Succ m1) (Succ m1)) h) (erased (Nth (Nat) xs (Zero) r) nr)
    (erased (Suffix xs (Succ m1)) sf) (erased (Swap xs (Zero) m1 ys) sw) (erased (Lt (Zero) m1) zm) (erased (Stays ys zs m1) st)
    -> (erased (Suffix zs m1) r2))
  (let-match erased (rootmax _ _ _ _ len mn h nr) (MkMax _ _ _ vx fx))
  (let-match erased sf (MkSuffix _ _ vs fs))
  (let-match erased st (MkStays _ _ _ vt ft))
  (def-fns Inv $ (erased f : (subterm erased (V2 vx (V2 vs vt)) is w) (erased (Nat) i j x y) (erased (Lt i j) ij) (erased (NatLe m1 j) mj)
      (erased (Nth (Nat) zs i x) nx) (erased (Nth (Nat) zs j y) ny) -> (erased (NatLe x y) le))
    (let ((erased j2) (erased ny2) (erased wj)) (ft vt j y ny))
    (let-match erased wj (Hi _ _ _) (absurd (Lo _ _ _ p _) (lt-not-le j m1 p mj)))
    (let ((erased i2) (erased nx2) (erased wi)) (ft vt i x nx))
    (let ((erased i2j)) (match erased wi (((Lt i2 j) l)) ((Hi _ _ _) ij) ((Lo _ _ _ _ q) (lt-le-lt i2 m1 j q mj))))
    (let-match erased (eq-ne j m1) (Diff _ _ jm)
      ((Same _)
        (let-match erased (nth-fn _ _ _ _ _ (swap-at-j _ _ _ _ _ sw ny2) nr) (Refl _ _))
        (let ((erased a) (erased na) (erased ab)) (swap-pos _ _ _ _ _ _ _ sw zm (lt-succ m1) (lt-weaken i2 m1 i2j) nx2))
        (fx vx a x ab na)))
    (let ((erased mj2)) (le-ne-lt m1 j mj jm))
    (let ((erased a) (erased na) (erased ab)) (swap-pos _ _ _ _ _ _ _ sw zm mj2 i2j nx2))
    (fs vs a j x y ab (MkNatLe _ _ (LtS _ _ mj2)) na (swap-at _ _ _ _ _ _ sw (NeGt j (Zero) (lt-trans _ _ _ zm mj2)) jm ny2)))
  (MkSuffix zs m1 (V2 vx (V2 vs vt)) f))

(def-fns _ $ (erased suffix-none : (erased (List (Nat)) xs) (erased (Nat) n) (erased (Length (Nat) xs n) len) -> (erased (Suffix xs n) r))
  (def-fns Inv $ (erased absurd f : (subterm erased (V0) is w) (erased (Nat) i j x y) (erased (Lt i j) ij) (erased (NatLe n j) mj)
      (erased (Nth (Nat) xs i x) nx) (erased (Nth (Nat) xs j y) ny) -> (erased (NatLe x y) le))
    (lt-not-le j n (nth-lt-length _ _ _ _ _ ny len) mj))
  (MkSuffix xs n (V0) f))

(def-fns _ $ (erased sorted-of-suffix : (erased (List (Nat)) xs) (erased (Nat) n m) (subterm erased (Length (Nat) xs n) len)
    (erased (Suffix xs m) sf) (erased (NatLe m 1) m1) -> (erased (Ascending (Nat) NatLe xs) r))
  (let-match erased len (LengthCons _ x rest n1 len1) ((LengthNil _) (AscNil _ _)))
  (let-match erased len1 (LengthCons _ y rest2 n2 len2) ((LengthNil _) (AscOne _ _ x)))
  (let-match erased sf (MkSuffix _ _ v g))
  (def-fns Inv $ (erased f : (subterm erased (V1 v) is w) (erased (Nat) i j a b) (erased (Lt i j) ij) (erased (NatLe 1 j) mj)
      (erased (Nth (Nat) rest i a) na) (erased (Nth (Nat) rest j b) nb) -> (erased (NatLe a b) le))
    (g v (Succ i) (Succ j) a b (LtS i j ij) (le-le m 1 (Succ j) m1 (MkNatLe _ _ (LtS _ _ (LtZ j))))
      (NthThere _ _ _ _ _ na) (NthThere _ _ _ _ _ nb)))
  (AscCons _ _ x y rest2 (g v (Zero) 1 x y (LtZ (Zero)) m1 (NthHere _ _ _) (NthThere _ _ _ _ _ (NthHere _ _ _)))
    (sorted-of-suffix rest n1 1 len1 (MkSuffix rest 1 (V1 v) f) (le-refl 1))))
