(def-adts
  ((EqNe : ((Nat) a) ((Nat) b) -> Type)
    enum
    (many Same : (erased (Nat) a) -> (EqNe a a))
    (many Diff : (erased (Nat) a) (erased (Nat) b) (erased (Ne a b) ne) -> (EqNe a b))))

(def-fns _ $ (erased eq-ne : (erased (Nat) a b) -> (erased (EqNe a b) r))
  (match erased (nat-cmp a b) _
    ((CLt _ _ _ _ p) (Diff a b (NeLt a b p)))
    ((CEq _ _ _) (Same a))
    ((CGt _ _ _ _ p) (Diff a b (NeGt a b p)))))

(lt-lemma (erased lt-le : (erased (Nat) a b) (erased (Lt a b) p) -> (erased (NatLe a b) r)))
(lt-lemma (erased le-lt-lt : (erased (Nat) a b c) (erased (NatLe a b) p) (erased (Lt b c) q) -> (erased (Lt a c) r)))
(lt-lemma (erased lt-le-lt : (erased (Nat) a b c) (erased (Lt a b) p) (erased (NatLe b c) q) -> (erased (Lt a c) r)))
(lt-lemma (erased le-le : (erased (Nat) a b c) (erased (NatLe a b) p) (erased (NatLe b c) q) -> (erased (NatLe a c) r)))
(lt-lemma (erased le-refl : (erased (Nat) a) -> (erased (NatLe a a) r)))
(lt-lemma (erased le-up : (erased (Nat) a b) (erased (NatLe a b) p) -> (erased (NatLe (Succ a) (Succ (Succ b))) r)))

(def-fns _ $ (erased le-ne-lt : (erased (Nat) a b) (erased (NatLe a b) p) (erased (Ne b a) ne) -> (erased (Lt a b) r))
  (let-match erased ne (NeGt _ _ q) (absurd (NeLt _ _ q) (lt-asym b a q (le-lt a b p))))
  q)

; d is 2p, so the children of p are d+1 and d+2.
(def-adts
  ((Child : ((Nat) p) ((Nat) j) -> Type)
    enum
    (many ChL : (erased (Nat) p) (erased (Nat) d) (erased (Double p d) dd) -> (Child p (Succ d)))
    (many ChR : (erased (Nat) p) (erased (Nat) d) (erased (Double p d) dd) -> (Child p (Succ (Succ d))))))

(def-fns _ $ (erased child-lt : (erased (Nat) p j) (erased (Child p j) c) -> (erased (Lt p j) r))
  (match erased c _
    ((ChL _ d dd) (double-le p d dd))
    ((ChR _ d dd) (lt-weaken p (Succ d) (double-le p d dd)))))

(def-fns _ $ (erased child-fn : (erased (Nat) p q j) (erased (Child p j) a) (erased (Child q j) b) -> (erased (Eq (Nat) p q) e))
  (match erased a _
    ((ChL _ d da) (match erased b _
      ((ChL _ _ db) (double-inj p q d da db))
      (absurd (ChR _ d2 db) (double-parity p q d2 da db))))
    ((ChR _ d da) (match erased b _
      (absurd (ChL _ d2 db) (double-parity q p d db da))
      ((ChR _ _ db) (double-inj p q d da db))))))

(def-fns _ $ (erased parent : (subterm erased (Nat) a) (erased (Lt (Zero) a) pos) -> (erased (Nat) p) (erased (Child p a) c))
  (let-match erased a (Succ a1) (absurd (Zero) pos))
  (let-match erased a1 (Succ a2) ((Zero) (values (Zero) (ChL (Zero) (Zero) (D0)))))
  (let-match erased a2 (Succ a3) ((Zero) (values (Zero) (ChR (Zero) (Zero) (D0)))))
  (let ((erased p1) (erased c1)) (parent a2 (LtZ a3)))
  (match erased c1 _
    ((ChL _ d dd) (values (Succ p1) (ChL (Succ p1) (Succ (Succ d)) (DS p1 d dd))))
    ((ChR _ d dd) (values (Succ p1) (ChR (Succ p1) (Succ (Succ d)) (DS p1 d dd))))))

(lt-lemma (erased le-pred : (erased (Nat) a b) (erased (NatLe (Succ a) (Succ b)) p) -> (erased (NatLe a b) r)))
(lt-lemma (erased le-ss : (erased (Nat) a b) (erased (NatLe a b) p) -> (erased (NatLe (Succ (Succ a)) (Succ (Succ b))) r)))

(def-fns _ $ (erased double-le-mono : (erased (Nat) q i d e) (subterm erased (Double q d) dq) (erased (Double i e) di)
    (erased (NatLe q i) le) -> (erased (NatLe d e) r))
  (let-match erased dq (DS q1 d1 dq1) ((D0) (MkNatLe _ _ (LtZ e))))
  (let-match erased di (DS i1 e1 di1)
    (absurd (D0) (let-match erased le (MkNatLe _ _ l)) (let-match erased l (LtS _ _ l1)) l1))
  (le-ss d1 e1 (double-le-mono q1 i1 d1 e1 dq1 di1 (le-pred q1 i1 le))))

(def-fns _ $ (erased double-gap : (erased (Nat) i q e d) (subterm erased (Lt i q) l) (erased (Double i e) di)
    (erased (Double q d) dq) -> (erased (Lt (Succ e) d) r))
  (let-match erased dq (DS q1 d1 dq1) (absurd (D0) l))
  (match erased l _
    ((LtZ _) (let-match erased di (D0)) (LtS (Zero) (Succ d1) (LtZ d1)))
    ((LtS i1 _ l1)
      (let-match erased di (DS _ e1 di1))
      (LtS (Succ (Succ e1)) (Succ d1) (LtS (Succ e1) d1 (double-gap i1 q1 e1 d1 l1 di1 dq1))))))

(unary 1)

(def-fns _ $ (erased shr-one-ok : -> (erased (Lt 1 (Succ sixty-two)) q))
  (let-match erased (add-fn sixty _ _ _ sixty-two-add (add-succ-right _ _ _ (add-succ-right _ _ _ (add-zero-right sixty))))
    (Refl _ _))
  (LtS (Zero) (Succ (Succ sixty)) (LtZ (Succ sixty))))

(def-fns _ $ (erased mul2-double : (erased (Nat) q m) (subterm erased (Mul q (Succ (Succ (Zero))) m) mm) -> (erased (Double q m) d))
  (let-match erased mm (MulSucc q1 _ c _ mm1 p) ((MulZero _) (D0)))
  (let-match erased (add-fn c _ m _ p (add-succ-right _ _ _ (add-succ-right _ _ _ (add-zero-right c)))) (Refl _ _))
  (DS q1 c (mul2-double q1 c mm1)))

; d is 2q: q is m halved, rounding down.
(def-adts
  ((Half2 : ((Nat) m) ((Nat) q) -> Type)
    enum
    (many MkHalf2 : (erased (Nat) m q d) (erased (Double q d) dq) (erased (NatLe d m) lo) (erased (Lt m (Succ (Succ d))) hi)
       -> (Half2 m q))))

(def-fns _ $ (erased half-of : (erased (Nat) m q v k r) (erased (Pow2 1 v) pv) (erased (Mul q v k) mm) (erased (Add k r m) a)
    (erased (Lt r v) rl) -> (erased (Half2 m q) h))
  (let-match erased pv (PS _ _ _ p0 dv))
  (let-match erased p0 (P0))
  (let-match erased dv (DS _ _ d0))
  (let-match erased d0 (D0))
  (let ((erased lo)) (MkNatLe _ _ (add-le-left k r m a)))
  (let ((erased dq)) (mul2-double q k mm))
  (match erased rl _
    ((LtZ _) (let-match erased (add-comm _ _ _ a) (AddZero _)) (MkHalf2 m q k dq lo (lt-weaken _ _ (lt-succ k))))
    ((LtS _ _ l1)
      (let-match erased l1 (LtZ _) (absurd (LtS _ _ l2) l2))
      (let-match erased (add-comm _ _ _ a) (AddSucc _ _ _ a1))
      (let-match erased a1 (AddZero _))
      (MkHalf2 m q k dq lo (lt-succ (Succ k))))))

(lt-lemma (erased out-bound : (erased (Nat) m d e) (erased (Lt m (Succ (Succ d))) p) (erased (NatLe d e) q) -> (erased (NatLe m (Succ e)) r)))
(lt-lemma (erased le-succ-r : (erased (Nat) a b) (erased (NatLe a b) p) -> (erased (NatLe a (Succ b)) r)))

(def-fns _ $ (erased kids-out : (erased (Nat) m q i j) (erased (Half2 m q) h) (erased (NatLe q i) qi) (erased (Child i j) c)
    -> (erased (NatLe m j) r))
  (let-match erased h (MkHalf2 _ _ d dq lo hi))
  (match erased c _
    ((ChL _ e de) (out-bound m d e hi (double-le-mono q i d e dq de qi)))
    ((ChR _ e de) (le-succ-r _ _ (out-bound m d e hi (double-le-mono q i d e dq de qi))))))

(def-fns _ $ (erased kids-in : (erased (Nat) m q i e) (erased (Half2 m q) h) (erased (Lt i q) iq) (erased (Double i e) de)
    -> (erased (NatLe (Succ (Succ e)) m) r))
  (let-match erased h (MkHalf2 _ _ d dq lo hi))
  (le-le _ _ _ (MkNatLe _ _ (LtS _ _ (double-gap i q e d iq de dq))) lo))

(lt-lemma (erased lt-not-le : (erased (Nat) a b) (erased (Lt a b) p) (erased (NatLe b a) q) -> (erased (False) f)))

(def-fns _ $ (erased ne-top : (erased (Nat) p j m) (erased (Child p j) c) (erased (Lt j m) jm) -> (erased (Ne p m) r))
  (NeLt p m (lt-trans p j m (child-lt p j c) jm)))

(def-fns _ $ (erased double-add : (erased (Nat) a b) (subterm erased (Double a b) d) -> (erased (Add a a b) r))
  (let-match erased d (DS a1 b1 d1) ((D0) (AddZero (Zero))))
  (AddSucc a1 (Succ a1) (Succ b1) (add-succ-right a1 a1 b1 (double-add a1 b1 d1))))

(lt-lemma (erased double-le-le : (erased (Nat) q d m) (erased (Double q d) dq) (erased (NatLe d m) lo) -> (erased (NatLe q m) r)))

(def-fns _ $ (erased half-le : (erased (Nat) m q) (erased (Half2 m q) h) -> (erased (NatLe q m) r))
  (let-match erased h (MkHalf2 _ _ d dq lo hi))
  (double-le-le q d m dq lo))

(def-fns _ $ (erased add-dec : (erased (Nat) i a c b m) (subterm erased (Add i a m) p) (erased (Add c b m) q) (erased (Lt i c) ic)
    -> (erased (Lt b a) r))
  (let-match erased p (AddSucc i1 _ m1 p1) ((AddZero _) (add-pos-lt b c m (add-comm c b m q) ic)))
  (let-match erased ic (LtS _ c1 ic1))
  (let-match erased q (AddSucc _ _ _ q1))
  (add-dec i1 a c1 b m1 p1 q1 ic1))

(def-fns _ $ (erased cnt-step : (erased (Nat) i c m cnt) (erased (Add i cnt m) p) (erased (Lt i c) ic) (erased (Lt c m) cm)
    -> (erased (Nat) cnt2) (erased (Add c cnt2 m) q) (erased (Lt cnt2 cnt) r))
  (let ((erased cnt2) (erased q)) (sub m c (lt-weaken c m cm)))
  (values cnt2 q (add-dec i cnt c cnt2 m p q ic)))

(lt-lemma (erased kid-bound2 : (erased (Nat) e m b) (erased (NatLe (Succ (Succ e)) m) p) (erased (Lt m b) q) -> (erased (Lt (Succ (Succ e)) b) r)))
(lt-lemma (erased kid-bound1 : (erased (Nat) e m b) (erased (NatLe (Succ (Succ e)) m) p) (erased (Lt m b) q) -> (erased (Lt (Succ e) b) r)))
(lt-lemma (erased kid-bound0 : (erased (Nat) e m b) (erased (NatLe (Succ (Succ e)) m) p) (erased (Lt m b) q) -> (erased (Lt e b) r)))
(lt-lemma (erased kid-in1 : (erased (Nat) e m) (erased (NatLe (Succ (Succ e)) m) p) -> (erased (Lt (Succ e) m) r)))

(let ((erased (Lt 1 u62-modulus) one-fits)) (prove-literal-lt 1 4611686018427387904))
