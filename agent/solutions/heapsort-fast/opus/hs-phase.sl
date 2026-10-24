; Lemmas for the build and extraction phases.

; s is no less than every position below n.
(def-adts
  ((AllBelow : ((List Elt) xs) ((Nat) n) (Elt s) -> Type)
    enum
    (many ABZ : (erased (List Elt) xs) (erased Elt s) -> (AllBelow xs (Zero) s))
    (many ABS : (erased (List Elt) xs) (erased (Nat) n) (erased Elt s) (erased Elt x) (erased (Nth Elt xs n x) nx)
        (erased (ULe x s) le) (erased (AllBelow xs n s) rest) -> (AllBelow xs (Succ n) s))))

; Dropping n elements of xs leaves s.
(def-adts
  ((DropN : ((List Elt) xs) ((Nat) n) ((List Elt) s) -> Type)
    enum
    (many DZ : (erased (List Elt) xs) -> (DropN xs (Zero) xs))
    (many DS1 : (erased Elt x) (erased (List Elt) xs) (erased (Nat) n) (erased (List Elt) s) (erased (DropN xs n s) d)
        -> (DropN (Cons Elt x xs) (Succ n) s))))

; The sorted suffix s is no less than everything before it.
(def-adts
  ((Bound : ((List Elt) xs) ((Nat) n) ((List Elt) s) -> Type)
    enum
    (many BdNil : (erased (List Elt) xs) (erased (Nat) n) -> (Bound xs n (Nil Elt)))
    (many BdCons : (erased (List Elt) xs) (erased (Nat) n) (erased Elt s) (erased (List Elt) rest)
        (erased (AllBelow xs n s) ab) -> (Bound xs n (Cons Elt s rest)))))

; A sequence of swaps below n.
(def-adts
  ((Shuf : ((List Elt) xs) ((Nat) n) ((List Elt) ys) -> Type)
    enum
    (many ShNil : (erased (List Elt) xs) (erased (Nat) n) -> (Shuf xs n xs))
    (many ShCons : (erased (List Elt) xs) (erased (Nat) n) (erased (Nat) i) (erased (Nat) j) (erased (List Elt) ys)
        (erased (List Elt) zs) (erased (Swap xs i j ys) sw) (erased (Lt j n) jn) (erased (Shuf ys n zs) rest)
        -> (Shuf xs n zs))))

(def-fns _ $ (erased allbelow-lookup : (erased (List Elt) xs) (erased (Nat) n) (erased Elt s)
    (subterm erased (AllBelow xs n s) ab) (erased (Nat) i) (erased Elt x) (erased (Nth Elt xs i x) ni) (erased (Lt i n) lt)
    -> (erased (ULe x s) r))
  (let-match erased ab (ABS _ n1 _ y ny le rest) (absurd (ABZ _ _) lt))
  (let-match erased (le-case i n1 lt) (LeEq _) ((LeLt _ _ q) (allbelow-lookup xs n1 s rest i x ni q)))
  (let-match erased (nth-fn Elt xs i y x ny ni) (Refl _ _))
  le)

(def-fns _ $ (erased allbelow-swap-walk : (erased (List Elt) xs) (erased (Nat) n) (erased Elt s)
    (erased (AllBelow xs n s) full) (erased (Nat) i) (erased (Nat) j) (erased (List Elt) ys) (erased (Swap xs i j ys) sw)
    (erased (Lt j n) jn) (erased (Nat) t) (subterm erased (AllBelow xs t s) ab) -> (erased (AllBelow ys t s) r))
  (let-match erased ab (ABS _ t1 _ x nx le rest) ((ABZ _ _) (ABZ ys s)))
  (let ((erased tl)) (allbelow-swap-walk xs n s full i j ys sw jn t1 rest))
  (let-match erased sw (MkSwap _ _ _ xi xj zs _ ni nj ij s1 s2))
  (let ((erased in)) (lt-trans i j n ij jn))
  (let-match erased (eq-or-ne t1 i) (IsNe _ _ ti)
    ((IsEq _)
      (ABS ys t1 s xj (swap-at-i xs i j ys sw xj nj) (allbelow-lookup xs n s full j xj nj jn) tl)))
  (let-match erased (eq-or-ne t1 j) (IsNe _ _ tj)
    ((IsEq _)
      (ABS ys t1 s xi (swap-at-j xs i j ys sw xi ni) (allbelow-lookup xs n s full i xi ni in) tl)))
  (ABS ys t1 s x (swap-other xs i j ys sw t1 x nx ti tj) le tl))

(def-fns _ $ (erased allbelow-swap : (erased (List Elt) xs) (erased (Nat) n) (erased Elt s)
    (erased (AllBelow xs n s) ab) (erased (Nat) i) (erased (Nat) j) (erased (List Elt) ys) (erased (Swap xs i j ys) sw)
    (erased (Lt j n) jn) -> (erased (AllBelow ys n s) r))
  (allbelow-swap-walk xs n s ab i j ys sw jn n ab))

(def-fns _ $ (erased dropn-set : (erased (List Elt) xs) (erased (Nat) m) (erased (List Elt) s)
    (subterm erased (DropN xs m s) dr) (erased (Nat) i) (erased Elt y) (erased (List Elt) ys)
    (erased (SetNth Elt xs i y ys) st) (erased (Lt i m) im) -> (erased (DropN ys m s) r))
  (let-match erased dr (DS1 x rest m1 _ dr1) (absurd (DZ _) im))
  (let-match erased st (SetThere _ _ _ i1 _ rest2 st1) ((SetHere _ _ _ _) (DS1 y rest m1 s dr1)))
  (let-match erased im (LtS _ _ im1))
  (DS1 x rest2 m1 s (dropn-set rest m1 s dr1 i1 y rest2 st1 im1)))

(def-fns _ $ (erased dropn-swap : (erased (List Elt) xs) (erased (Nat) m) (erased (List Elt) s)
    (erased (DropN xs m s) dr) (erased (Nat) i) (erased (Nat) j) (erased (List Elt) ys) (erased (Swap xs i j ys) sw)
    (erased (Lt j m) jm) -> (erased (DropN ys m s) r))
  (let-match erased sw (MkSwap _ _ _ xi xj zs _ ni nj ij s1 s2))
  (dropn-set zs m s (dropn-set xs m s dr i xj zs s1 (lt-trans i j m ij jm)) j xi ys s2 jm))

(def-fns _ $ (erased dropn-step : (erased (List Elt) xs) (erased (Nat) n) (erased (List Elt) s)
    (subterm erased (DropN xs (Succ n) s) dr) (erased Elt x) (erased (Nth Elt xs n x) nx) -> (erased (DropN xs n (Cons Elt x s)) r))
  (let-match erased dr (DS1 y rest _ _ dr1))
  (let-match erased nx (NthHere _ _ _)
    ((NthThere _ _ _ n1 _ nx1) (DS1 y rest n1 (Cons Elt x s) (dropn-step rest n1 s dr1 x nx1))))
  (let-match erased dr1 (DZ _))
  (DZ (Cons Elt x s)))

(def-fns _ $ (erased dropn-full : (erased (List Elt) xs) (erased (Nat) n) (subterm erased (Length Elt xs n) len)
    -> (erased (DropN xs n (Nil Elt)) r))
  (match erased len _
    ((LengthNil _) (DZ (Nil Elt)))
    ((LengthCons _ x rest n1 len1) (DS1 x rest n1 (Nil Elt) (dropn-full rest n1 len1)))))

(def-fns _ $ (erased shuf-perm : (erased (List Elt) xs) (erased (Nat) n) (erased (List Elt) zs)
    (subterm erased (Shuf xs n zs) sh) -> (erased (Permutation Elt xs zs) pm))
  (match erased sh _
    ((ShNil _ _) (perm-refl xs))
    ((ShCons _ _ i j ys _ sw jn rest) (PTrans Elt xs ys zs (swap-perm xs i j ys sw) (shuf-perm ys n zs rest)))))

(def-fns _ $ (erased shuf-length : (erased (List Elt) xs) (erased (Nat) n) (erased (List Elt) zs)
    (subterm erased (Shuf xs n zs) sh) (erased (Nat) len) (erased (Length Elt xs len) lp) -> (erased (Length Elt zs len) r))
  (match erased sh _
    ((ShNil _ _) lp)
    ((ShCons _ _ i j ys _ sw jn rest) (shuf-length ys n zs rest len (swap-length xs i j ys sw len lp)))))

(def-fns _ $ (erased shuf-dropn : (erased (List Elt) xs) (erased (Nat) n) (erased (List Elt) zs)
    (subterm erased (Shuf xs n zs) sh) (erased (Nat) m) (erased (Lt n (Succ m)) nm) (erased (List Elt) s)
    (erased (DropN xs m s) dr) -> (erased (DropN zs m s) r))
  (match erased sh _
    ((ShNil _ _) dr)
    ((ShCons _ _ i j ys _ sw jn rest)
      (shuf-dropn ys n zs rest m nm s (dropn-swap xs m s dr i j ys sw (lt-le-trans j n m jn nm))))))

(def-fns _ $ (erased shuf-bound : (erased (List Elt) xs) (erased (Nat) n) (erased (List Elt) zs)
    (subterm erased (Shuf xs n zs) sh) (erased (List Elt) s) (erased (Bound xs n s) bd) -> (erased (Bound zs n s) r))
  (let-match erased sh (ShCons _ _ i j ys _ sw jn rest) ((ShNil _ _) bd))
  (let ((erased bd1)) (match erased bd (((Bound ys n s) b))
    ((BdNil _ _) (BdNil ys n))
    ((BdCons _ _ e r ab) (BdCons ys n e r (allbelow-swap xs n e ab i j ys sw jn)))))
  (shuf-bound ys n zs rest s bd1))

; In a full heap (Covers xs n n 1), the root is no less than any position below n.
(def-fns _ $ (erased rootmax-at : (erased (List Elt) xs) (erased (Nat) n) (erased (Covers xs n n (Succ (Zero))) cv)
    (erased (Nat) len) (erased (Length Elt xs len) lp) (erased (Lt n (Succ len)) nl) (erased Elt r) (erased (Nth Elt xs (Zero) r) nr)
    (subterm erased (Nat) fuel) (erased (Nat) i) (erased (Lt i fuel) lf) (erased (Lt i n) lt) (erased Elt x) (erased (Nth Elt xs i x) ni)
    -> (erased (ULe x r) le))
  (let-match erased i (Succ i1) ((Zero) (let-match erased (nth-fn Elt xs (Zero) r x nr ni) (Refl _ _)) (ule-refl r)))
  (let ((erased p) (erased pp)) (parent-exists i (LtZ i1)))
  (let ((erased pi)) (parent-lt p i pp))
  (let ((erased pn)) (lt-trans p i n pi lt))
  (let ((erased y) (erased np)) (nth-exists Elt xs len p lp (lt-le-trans p n len pn nl)))
  (let ((erased xy)) (covers-lookup xs n n (Succ (Zero)) cv i (LtS (Zero) i (LtZ i1)) lt p pp (NeL p n pn) x y ni np))
  (let ((erased yr)) (rootmax-at xs n cv len lp nl r nr (subterm (lt-subterm i fuel lf)) i p pi pn y np))
  (ule-trans x y r xy yr))

(def-fns _ $ (erased rootmax-walk : (erased (List Elt) xs) (erased (Nat) n) (erased (Covers xs n n (Succ (Zero))) cv)
    (erased (Nat) len) (erased (Length Elt xs len) lp) (erased (Lt n (Succ len)) nl) (erased Elt r) (erased (Nth Elt xs (Zero) r) nr)
    (subterm erased (Nat) t) (erased (Lt t (Succ n)) tn) -> (erased (AllBelow xs t r) ab))
  (let-match erased t (Succ t1) ((Zero) (ABZ xs r)))
  (let ((erased t1n)) (lt-le-trans t1 (Succ t1) n (lt-succ t1) tn))
  (let ((erased x) (erased nx)) (nth-exists Elt xs len t1 lp (lt-le-trans t1 n len t1n nl)))
  (ABS xs t1 r x nx (rootmax-at xs n cv len lp nl r nr n t1 t1n t1n x nx)
    (rootmax-walk xs n cv len lp nl r nr t1 (lt-weaken t1 n t1n))))

(def-fns _ $ (erased root-max : (erased (List Elt) xs) (erased (Nat) n) (erased (Covers xs n n (Succ (Zero))) cv)
    (erased (Nat) len) (erased (Length Elt xs len) lp) (erased (Lt n (Succ len)) nl) (erased Elt r) (erased (Nth Elt xs (Zero) r) nr)
    -> (erased (AllBelow xs n r) ab))
  (rootmax-walk xs n cv len lp nl r nr n (lt-succ n)))

; Swapping the root of a full heap of n+1 with position n, the first n positions are a heap except at the root.
(def-fns _ $ (erased covers-root-shrink : (erased (List Elt) xs) (erased (Nat) n) (erased (Nat) a)
    (subterm erased (Covers xs (Succ n) (Succ n) a) cv) (erased (Lt (Zero) a) pos)
    (erased (List Elt) ys) (erased (Swap xs (Zero) n ys) sw) -> (erased (Covers ys n (Zero) a) r))
  (let-match erased cv (COk _ _ _ _ p x y pa an na np le rest)
    ((CEnd _ _ _ _ out) (let-match erased out (LtS _ _ out1)) (CEnd ys n (Zero) a (lt-weaken n a out1)))
    (absurd (CSkip _ _ _ _ pk an rest) (lt-asym (Succ n) a (parent-lt (Succ n) a pk) (lt-weaken a (Succ n) an))))
  (let-match erased (le-case a n an) (LeLt _ _ cn)
    ((LeEq _) (CEnd ys n (Zero) n (lt-succ n))))
  (let ((erased tl)) (covers-root-shrink xs n (Succ a) rest (LtZ a) ys sw))
  (let-match erased (eq-or-ne p (Zero)) (IsNe _ _ p0)
    ((IsEq _) (CSkip ys n (Zero) a pa cn tl)))
  (let ((erased pn)) (lt-trans p a n (parent-lt p a pa) cn))
  (COk ys n (Zero) a p x y pa cn (swap-other xs (Zero) n ys sw a x na (NeG a (Zero) pos) (NeL a n cn))
    (swap-other xs (Zero) n ys sw p y np p0 (NeL p n pn)) le tl))

(def-fns _ $ (erased covers-prepend : (erased (List Elt) xs) (erased (Nat) n) (erased (Nat) k) (erased (Nat) c)
    (erased (Covers xs n k (Succ c)) cv) (erased (ParentOf k c) pk) -> (erased (Covers xs n k c) r))
  (let-match erased (lt-dec c n) (Yes _ _ cn) ((No _ _ q) (CEnd xs n k c q)))
  (CSkip xs n k c pk cn cv))

; Moving the build phase down to position i, whose children are 2i+1 and 2i+2.
(def-fns _ $ (erased build-step : (erased (List Elt) xs) (erased (Nat) n) (erased (Nat) i) (erased (Nat) d) (erased (Double i d) dd)
    (erased (Covers xs n n (Succ (Succ (Succ d)))) cv) -> (erased (Covers xs n i (Succ d)) r))
  (let ((erased dn) (erased ddn)) (double n))
  (let ((erased b1)) (lt-weaken n (Succ dn) (double-lt n dn ddn)))
  (let ((erased cv1)) (covers-fill xs n n (Succ (Succ (Succ d))) cv dn ddn
    (BOut xs n (Succ dn) n b1) (BOut xs n (Succ (Succ dn)) n (lt-weaken n (Succ (Succ dn)) b1)) i))
  (covers-prepend xs n i (Succ d) (covers-prepend xs n i (Succ (Succ d)) cv1 (PoR i d dd)) (PoL i d dd)))
