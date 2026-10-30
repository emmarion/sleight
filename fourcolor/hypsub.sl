; Lists of darts as sets, and the classes of a graph counted among the darts of a list. Load after colalias.sl.

; ys lists the darts of xs in t, and zs those not in t.
(def-adts $ (Split : ((List (Nat)) t xs ys zs) -> Type)
  enum
  (many SpNil : (erased (List (Nat)) t) -> (Split t (Nil (Nat)) (Nil (Nat)) (Nil (Nat))))
  (many SpIn : (erased (List (Nat)) t xs ys zs) (erased (Nat) x) (erased (In x t) p) (erased (Split t xs ys zs) rest)
      -> (Split t (Cons (Nat) x xs) (Cons (Nat) x ys) zs))
  (many SpOut : (erased (List (Nat)) t xs ys zs) (erased (Nat) x) (erased (NotIn x t) p) (erased (Split t xs ys zs) rest)
      -> (Split t (Cons (Nat) x xs) ys (Cons (Nat) x zs))))

(def-fns _ $ (erased split-exists : (erased (List (Nat)) t) (subterm erased (List (Nat)) xs) -> (erased (List (Nat)) ys zs) (erased (Split t xs ys zs) r))
  (let-match erased xs (Cons _ x xs1) ((Nil _) (values (Nil _) (Nil _) (SpNil t))))
  (let ((erased ys1) (erased zs1) (erased r1)) (split-exists t xs1))
  (match erased (in-dec x t) _
    ((OrL _ _ p) (values (Cons _ x ys1) zs1 (SpIn t xs1 ys1 zs1 x p r1)))
    ((OrR _ _ p) (values ys1 (Cons _ x zs1) (SpOut t xs1 ys1 zs1 x p r1)))))

(def-fns _ $ (erased split-length : (erased (List (Nat)) t xs ys zs) (erased (Nat) n) (subterm erased (Split t xs ys zs) sp) (erased (Length (Nat) xs n) ln)
    -> (erased (Nat) a b) (erased (Length (Nat) ys a) la) (erased (Length (Nat) zs b) lb) (erased (Add a b n) ab))
  (match erased sp _
    ((SpNil _) (let-match erased ln (LengthNil _)) (values (Zero) (Zero) (LengthNil _) (LengthNil _) (AddZero (Zero))))
    ((SpIn _ xs1 ys1 zs1 x p sp1)
      (let-match erased ln (LengthCons _ _ _ n1 ln1))
      (let ((erased a) (erased b) (erased la) (erased lb) (erased ab)) (split-length t xs1 ys1 zs1 n1 sp1 ln1))
      (values (Succ a) b (LengthCons _ x ys1 a la) lb (AddSucc a b n1 ab)))
    ((SpOut _ xs1 ys1 zs1 x p sp1)
      (let-match erased ln (LengthCons _ _ _ n1 ln1))
      (let ((erased a) (erased b) (erased la) (erased lb) (erased ab)) (split-length t xs1 ys1 zs1 n1 sp1 ln1))
      (values a (Succ b) la (LengthCons _ x zs1 b lb) (add-succ-right a b n1 ab)))))

(def-fns _ $ (erased split-sub : (erased (List (Nat)) t xs ys zs) (subterm erased (Split t xs ys zs) sp) -> (erased (Sub ys xs) a) (erased (Sub zs xs) b))
  (match erased sp _
    ((SpNil _) (values (SubNil _) (SubNil _)))
    ((SpIn _ xs1 ys1 zs1 x p sp1)
      (let ((erased a) (erased b)) (split-sub t xs1 ys1 zs1 sp1))
      (values (SubCons x ys1 _ (InHere x xs1) (sub-cons x ys1 xs1 a)) (sub-cons x zs1 xs1 b)))
    ((SpOut _ xs1 ys1 zs1 x p sp1)
      (let ((erased a) (erased b)) (split-sub t xs1 ys1 zs1 sp1))
      (values (sub-cons x ys1 xs1 a) (SubCons x zs1 _ (InHere x xs1) (sub-cons x zs1 xs1 b))))))

(def-fns _ $ (erased split-in : (erased (List (Nat)) t xs ys zs) (erased (Nat) y) (subterm erased (Split t xs ys zs) sp) (erased (In y ys) iy)
    -> (erased (In y t) r))
  (match erased sp _
    (absurd (SpNil _) iy)
    ((SpIn _ xs1 ys1 zs1 x p sp1) (match erased iy _ ((InHere _ _) p) ((InThere _ _ _ iy1) (split-in t xs1 ys1 zs1 y sp1 iy1))))
    ((SpOut _ xs1 ys1 zs1 x p sp1) (split-in t xs1 ys1 zs1 y sp1 iy))))

(def-fns _ $ (erased split-out : (erased (List (Nat)) t xs ys zs) (erased (Nat) y) (subterm erased (Split t xs ys zs) sp) (erased (In y zs) iy)
    -> (erased (NotIn y t) r))
  (match erased sp _
    (absurd (SpNil _) iy)
    ((SpIn _ xs1 ys1 zs1 x p sp1) (split-out t xs1 ys1 zs1 y sp1 iy))
    ((SpOut _ xs1 ys1 zs1 x p sp1) (match erased iy _ ((InHere _ _) p) ((InThere _ _ _ iy1) (split-out t xs1 ys1 zs1 y sp1 iy1))))))

(def-fns _ $ (erased split-cover : (erased (List (Nat)) t xs ys zs) (erased (Nat) y) (subterm erased (Split t xs ys zs) sp) (erased (In y xs) iy)
    -> (erased (Or (In y ys) (In y zs)) r))
  (match erased sp _
    (absurd (SpNil _) iy)
    ((SpIn _ xs1 ys1 zs1 x p sp1)
      (match erased iy _
        ((InHere _ _) (OrL _ _ (InHere y ys1)))
        ((InThere _ _ _ iy1) (match erased (split-cover t xs1 ys1 zs1 y sp1 iy1) _
          ((OrL _ _ i) (OrL _ _ (InThere y x ys1 i))) ((OrR _ _ i) (OrR _ _ i))))))
    ((SpOut _ xs1 ys1 zs1 x p sp1)
      (match erased iy _
        ((InHere _ _) (OrR _ _ (InHere y zs1)))
        ((InThere _ _ _ iy1) (match erased (split-cover t xs1 ys1 zs1 y sp1 iy1) _
          ((OrL _ _ i) (OrL _ _ i)) ((OrR _ _ i) (OrR _ _ (InThere y x zs1 i)))))))))

(def-fns _ $ (erased split-distinct : (erased (List (Nat)) t xs ys zs) (subterm erased (Split t xs ys zs) sp) (erased (Distinct xs) dx)
    -> (erased (Distinct ys) a) (erased (Distinct zs) b))
  (match erased sp _
    ((SpNil _) (values (DistNil) (DistNil)))
    ((SpIn _ xs1 ys1 zs1 x p sp1)
      (let-match erased dx (DistCons _ _ out dx1))
      (let ((erased a) (erased b)) (split-distinct t xs1 ys1 zs1 sp1 dx1))
      (let ((erased s1) (erased s2)) (split-sub t xs1 ys1 zs1 sp1))
      (values (DistCons x ys1 (notin-sub x ys1 xs1 s1 out) a) b))
    ((SpOut _ xs1 ys1 zs1 x p sp1)
      (let-match erased dx (DistCons _ _ out dx1))
      (let ((erased a) (erased b)) (split-distinct t xs1 ys1 zs1 sp1 dx1))
      (let ((erased s1) (erased s2)) (split-sub t xs1 ys1 zs1 sp1))
      (values a (DistCons x zs1 (notin-sub x zs1 xs1 s2 out) b)))))

(def-fns _ $ (erased sub-in : (erased (List (Nat)) m s) (erased (Nat) x) (subterm erased (Sub m s) sb) (erased (In x m) ix) -> (erased (In x s) r))
  (let-match erased sb (SubCons y m1 _ p sb1) (absurd (SubNil _) ix))
  (match erased ix _ ((InHere _ _) p) ((InThere _ _ _ ix1) (sub-in m1 s x sb1 ix1))))

(def-fns _ $ (erased sub-trans : (erased (List (Nat)) a b c) (subterm erased (Sub a b) p) (erased (Sub b c) q) -> (erased (Sub a c) r))
  (let-match erased p (SubCons x a1 _ ix p1) ((SubNil _) (SubNil c)))
  (SubCons x a1 c (sub-in b c x q ix) (sub-trans a1 b c p1 q)))

(def-fns _ $ (erased app-sub : (erased (List (Nat)) xs ys zs s) (subterm erased (AppN xs ys zs) ap) (erased (Sub xs s) sx) (erased (Sub ys s) sy)
    -> (erased (Sub zs s) r))
  (let-match erased ap (AppCons xs1 _ zs1 x ap1) ((AppNil _) sy))
  (let-match erased sx (SubCons _ _ _ ix sx1))
  (SubCons x zs1 s ix (app-sub xs1 ys zs1 s ap1 sx1 sy)))

(def-fns _ $ (erased split-disj : (erased (List (Nat)) t xs ys zs) (subterm erased (Split t xs ys zs) sp) -> (erased (Disj zs t) r))
  (match erased sp _
    ((SpNil _) (DisjNil t))
    ((SpIn _ xs1 ys1 zs1 x p sp1) (split-disj t xs1 ys1 zs1 sp1))
    ((SpOut _ xs1 ys1 zs1 x p sp1) (DisjCons x zs1 t p (split-disj t xs1 ys1 zs1 sp1)))))

(def-fns _ $ (erased notin-of-disj : (erased (Nat) x) (erased (List (Nat)) s m) (subterm erased (Disj s m) dj) (erased (In x m) ix) -> (erased (NotIn x s) r))
  (let-match erased dj (DisjCons y s1 _ oy dj1) ((DisjNil _) (NotInNil x)))
  (NotInCons x y s1 (apart-sym y x (notin-in y x m oy ix)) (notin-of-disj x s1 m dj1 ix)))

(def-fns _ $ (erased disj-sym : (erased (List (Nat)) s m) (erased (Disj s m) dj) (subterm erased (List (Nat)) m2) (erased (Sub m2 m) sb) -> (erased (Disj m2 s) r))
  (let-match erased m2 (Cons _ x m3) ((Nil _) (DisjNil s)))
  (let-match erased sb (SubCons _ _ _ ix sb1))
  (DisjCons x m3 s (notin-of-disj x s m dj ix) (disj-sym s m dj m3 sb1)))

; Two duplicate-free lists with the same darts have the same length.
(def-fns _ $ (erased same-size : (erased (List (Nat)) xs ys) (erased (Nat) a b) (erased (Distinct xs) dx) (erased (Distinct ys) dy)
    (erased (Sub xs ys) sxy) (erased (Sub ys xs) syx) (erased (Length (Nat) xs a) la) (erased (Length (Nat) ys b) lb) -> (erased (Eq (Nat) a b) e))
  (le-antisym a b (pigeonhole xs ys a b dx sxy la lb) (pigeonhole ys xs b a dy syx lb la)))

; A duplicate-free list is injective.
(def-fns _ $ (erased distinct-nth : (erased (List (Nat)) h) (erased (Nat) i j x) (subterm erased (Distinct h) dh) (erased (Nth (Nat) h i x) pi)
    (erased (Nth (Nat) h j x) pj) -> (erased (Eq (Nat) i j) e))
  (let-match erased dh (DistCons y h1 out dh1) (absurd (DistNil) pi))
  (match erased pi _
    ((NthHere _ _ _)
      (match erased pj _
        ((NthHere _ _ _) (Refl _ i))
        (absurd (NthThere _ _ _ j1 _ pj1) (apart-irrefl x (notin-in x x h1 out (nth-in h1 j1 x pj1))))))
    ((NthThere _ _ _ i1 _ pi1)
      (match erased pj _
        (absurd (NthHere _ _ _) (apart-irrefl x (notin-in x x h1 out (nth-in h1 i1 x pi1))))
        ((NthThere _ _ _ j1 _ pj1) (eq-cong-succ i1 j1 (distinct-nth h1 i1 j1 x dh1 pi1 pj1)))))))

(def-fns _ $ (erased notin-respects : (erased (List (Nat)) h xs ys) (erased (Nat) x y) (erased (Distinct h) dh) (subterm erased (NotIn x xs) out)
    (erased (Nth (Nat) h x y) px) (erased (Respects h xs ys) rp) -> (erased (NotIn y ys) r))
  (let-match erased rp (RespCons _ xs1 ys1 j l pj rp1) ((RespNil _) (NotInNil y)))
  (let-match erased out (NotInCons _ _ _ ne out1))
  (NotInCons y l ys1
    (match erased (nat-cmp y l) _
      ((CLt _ _ _ _ q) (ApLt _ _ y l q))
      (absurd (CEq _ _ _) (let-match erased (distinct-nth h x j y dh px pj) (Refl _ _)) (apart-irrefl x ne))
      ((CGt _ _ _ _ q) (ApGt _ _ y l q)))
    (notin-respects h xs1 ys1 x y dh out1 px rp1)))

; The image of a duplicate-free list under an injective one.
(def-fns _ $ (erased respects-distinct : (erased (List (Nat)) h xs ys) (erased (Distinct h) dh) (subterm erased (Distinct xs) dx) (erased (Respects h xs ys) rp)
    -> (erased (Distinct ys) r))
  (let-match erased rp (RespCons _ xs1 ys1 j l pj rp1) ((RespNil _) (DistNil)))
  (let-match erased dx (DistCons _ _ out dx1))
  (DistCons l ys1 (notin-respects h xs1 ys1 j l dh out pj rp1) (respects-distinct h xs1 ys1 dh dx1 rp1)))

(def-fns _ $ (erased notin-respects-back : (erased (List (Nat)) lab xs ls) (erased (Nat) x l) (subterm erased (NotIn l ls) out) (erased (Nth (Nat) lab x l) px)
    (erased (Respects lab xs ls) rp) -> (erased (NotIn x xs) r))
  (let-match erased rp (RespCons _ xs1 ls1 j l2 pj rp1) ((RespNil _) (NotInNil x)))
  (let-match erased out (NotInCons _ _ _ ne out1))
  (NotInCons x j xs1
    (match erased (nat-cmp x j) _
      ((CLt _ _ _ _ q) (ApLt _ _ x j q))
      (absurd (CEq _ _ _) (let-match erased (nth-fn _ lab x l l2 px pj) (Refl _ _)) (apart-irrefl l ne))
      ((CGt _ _ _ _ q) (ApGt _ _ x j q)))
    (notin-respects-back lab xs1 ls1 x l out1 px rp1)))

; Darts with distinct labels are distinct.
(def-fns _ $ (erased distinct-back : (erased (List (Nat)) lab xs ls) (subterm erased (Distinct ls) dl) (erased (Respects lab xs ls) rp) -> (erased (Distinct xs) r))
  (let-match erased rp (RespCons _ xs1 ls1 j l pj rp1) ((RespNil _) (DistNil)))
  (let-match erased dl (DistCons _ _ out dl1))
  (DistCons j xs1 (notin-respects-back lab xs1 ls1 j l out pj rp1) (distinct-back lab xs1 ls1 dl1 rp1)))

; An entry of ls = lab . xs is the label of a dart of xs.
(def-fns _ $ (erased respects-in : (erased (List (Nat)) lab xs ls) (erased (Nat) l) (subterm erased (Respects lab xs ls) rp) (erased (In l ls) il)
    -> (erased (Nat) j) (erased (In j xs) ij) (erased (Nth (Nat) lab j l) pj))
  (let-match erased rp (RespCons _ xs1 ls1 j0 l0 p0 rp1) (absurd (RespNil _) il))
  (match erased il _
    ((InHere _ _) (values j0 (InHere j0 xs1) p0))
    ((InThere _ _ _ il1)
      (let ((erased j) (erased ij) (erased pj)) (respects-in lab xs1 ls1 l rp1 il1))
      (values j (InThere j j0 xs1 ij) pj))))

