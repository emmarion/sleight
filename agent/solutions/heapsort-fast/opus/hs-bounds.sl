; Index bounds and small lemmas for the runtime part.

; 2 * max-array-length + 2, spelled so that its halving is max-array-length.
(let ((erased hs-top-fits)) (prove-literal-lt 36028797018963970 4611686018427387904))
(let-match erased (numeral-of 36028797018963970) (N2 hs-top-b hs-top-m hs-top-d hs-top-v hs-top-dd))
(let-match erased (numeral-fn hs-top-b hs-top-m max-array-length hs-top-v (numeral-of 18014398509481984)) (Refl _ _))

(unary 1)
(let ((erased hs-one-fits)) (prove-literal-lt 1 4611686018427387904))

; A shift by 1 is allowed: sixty-two is a successor.
(let-match erased (add-comm sixty (Succ (Succ (Zero))) sixty-two sixty-two-add) (AddSucc _ _ hs-s61 hs-s61-add))
(let ((erased hs-shift-one)) (LtS (Zero) (Succ hs-s61) (LtZ hs-s61)))

(def-fns _ $ (erased mul2-double : (erased (Nat) q) (erased (Nat) m) (subterm erased (Mul q (Succ (Succ (Zero))) m) mm)
    -> (erased (Double q m) dd))
  (let-match erased mm (MulSucc q1 _ c _ mm1 ad) ((MulZero _) (D0)))
  (let-match erased (add-comm c (Succ (Succ (Zero))) m ad) (AddSucc _ _ m1 ad1))
  (let-match erased ad1 (AddSucc _ _ m2 ad2))
  (let-match erased ad2 (AddZero _))
  (DS q1 c (mul2-double q1 c mm1)))

; n = m + r with r < 2 gives n <= m + 1.
(def-fns _ $ (erased add-small : (erased (Nat) m) (erased (Nat) r) (erased (Nat) n) (erased (Add m r n) ad)
    (erased (Lt r (Succ (Succ (Zero)))) rl) -> (erased (Lt n (Succ (Succ m))) q))
  (let-match erased (add-comm m r n ad) (AddSucc r1 _ n1 ad1) ((AddZero _) (lt-weaken m (Succ m) (lt-succ m))))
  (let-match erased rl (LtS _ _ rl1))
  (let-match erased rl1 (LtZ _) (absurd (LtS _ _ z) z))
  (let-match erased ad1 (AddZero _))
  (lt-succ (Succ m)))

(def-fns _ $ (erased double-lt-mono : (erased (Nat) k) (erased (Nat) m) (subterm erased (Lt k m) lt)
    (erased (Nat) dk) (erased (Double k dk) ddk) (erased (Nat) dm) (erased (Double m dm) ddm) -> (erased (Lt (Succ dk) dm) r))
  (match erased lt _
    ((LtZ b)
      (let-match erased ddk (D0))
      (let-match erased ddm (DS _ db _))
      (LtS (Zero) (Succ db) (LtZ db)))
    ((LtS k1 m1 lt1)
      (let-match erased ddk (DS _ dk1 ddk1))
      (let-match erased ddm (DS _ dm1 ddm1))
      (LtS (Succ (Succ dk1)) (Succ dm1) (LtS (Succ dk1) dm1 (double-lt-mono k1 m1 lt1 dk1 ddk1 dm1 ddm1))))))

(def-fns _ $ (erased le-lt-trans : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Lt a (Succ b)) ab) (erased (Lt b c) bc)
    -> (erased (Lt a c) r))
  (lt-le-trans a (Succ b) c ab (LtS b c bc)))

; Positions up to 2k+2 fit in a u62 when k < max-array-length.
(def-fns _ $ (erased idx-bound : (erased (Nat) k) (erased (Lt k max-array-length) km) (erased (Nat) d) (erased (Double k d) dd)
    -> (erased (Lt (Succ (Succ d)) u62-modulus) r))
  (let ((erased q)) (double-lt-mono k max-array-length km d dd hs-top-d hs-top-dd))
  (lt-trans (Succ (Succ d)) (Succ (Succ hs-top-d)) u62-modulus
    (LtS (Succ d) (Succ hs-top-d) (lt-trans (Succ d) hs-top-d (Succ hs-top-d) q (lt-succ hs-top-d))) hs-top-fits))

(def-fns _ $ (erased fuel-step : (erased (Nat) k) (erased (Nat) f) (erased (Nat) n) (subterm erased (Add k f n) kf)
    (erased (Nat) m) (erased (Nat) g) (erased (Add m g n) mg) (erased (Lt k m) km) -> (erased (Lt g f) r))
  (let-match erased kf (AddSucc k1 _ n1 kf1) ((AddZero _) (add-pos-lt g m n (add-comm m g n mg) km)))
  (let-match erased km (LtS _ m1 km1))
  (let-match erased mg (AddSucc _ _ _ mg1))
  (fuel-step k1 f n1 kf1 m1 g mg1 km1))

(def-fns _ $ (erased double-add : (erased (Nat) k) (erased (Nat) d) (subterm erased (Double k d) dd) -> (erased (Add k k d) r))
  (let-match erased dd (DS a b dd1) ((D0) (AddZero (Zero))))
  (AddSucc a (Succ a) (Succ b) (add-succ-right a a b (double-add a b dd1))))

(def-fns _ $ (erased ule-of-le : (erased (Nat) x) (erased (Lt x u62-modulus) px) (erased (Nat) y) (erased (Lt y u62-modulus) py)
    (erased (Lt x (Succ y)) le) -> (erased (ULe (MkCopy (U62) (MkU62 x px)) (MkCopy (U62) (MkU62 y py))) r))
  (MkULe x px y py (MkLe x y le)))

(def-fns _ $ (erased allbelow-shrink : (erased (List Elt) xs) (erased (Nat) n) (erased Elt s)
    (erased (AllBelow xs (Succ n) s) ab) -> (erased (AllBelow xs n s) r))
  (let-match erased ab (ABS _ _ _ x nx le rest))
  rest)

(def-fns _ $ (erased asc-push : (erased (List Elt) xs) (erased (Nat) n) (erased (List Elt) s)
    (erased (Ascending Elt ULe s) asc) (erased (Bound xs n s) bd) (erased Elt r) (erased (Nth Elt xs (Zero) r) nr)
    (erased (Lt (Zero) n) pos) -> (erased (Ascending Elt ULe (Cons Elt r s)) asc2))
  (let-match erased bd (BdCons _ _ e rest ab) ((BdNil _ _) (AscOne Elt ULe r)))
  (AscCons Elt ULe r e rest (allbelow-lookup xs n e ab (Zero) r nr pos) asc))

(def-fns _ $ (erased wr-length : (erased (List (Nat)) xs) (erased (List Elt) es) (subterm erased (Wr xs es) w)
    (erased (Nat) k) (erased (Length Elt es k) lp) -> (erased (Length (Nat) xs k) r))
  (let-match erased w (WrCons x px xs1 es1 w1) ((WrNil) (let-match erased lp (LengthNil _)) (LengthNil (Nat))))
  (let-match erased lp (LengthCons _ _ _ k1 lp1))
  (LengthCons (Nat) x xs1 k1 (wr-length xs1 es1 w1 k1 lp1)))
