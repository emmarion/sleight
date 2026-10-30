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


(def-fns _ $ (erased split-sub-t : (erased (List (Nat)) t xs ys zs) (subterm erased (Split t xs ys zs) sp) -> (erased (Sub ys t) r))
  (match erased sp _
    ((SpNil _) (SubNil t))
    ((SpIn _ xs1 ys1 zs1 x p sp1) (SubCons x ys1 t p (split-sub-t t xs1 ys1 zs1 sp1)))
    ((SpOut _ xs1 ys1 zs1 x p sp1) (split-sub-t t xs1 ys1 zs1 sp1))))

; Names that red/ctree.sl defines again, kept for the files loaded after it.
(let ((erased HSubNil)) SubNil)
(let ((erased HSubCons)) SubCons)

(def-fns _ $ (erased app-sub-l : (erased (List (Nat)) xs ys zs m) (erased (AppN xs ys zs) ap) (subterm erased (Sub m xs) sb) -> (erased (Sub m zs) r))
  (let-match erased sb (SubCons x m1 _ ix sb1) ((SubNil _) (SubNil zs)))
  (SubCons x m1 zs (app-in-l xs ys zs x ap ix) (app-sub-l xs ys zs m1 ap sb1)))

(def-fns _ $ (erased app-sub-r : (erased (List (Nat)) xs ys zs m) (erased (AppN xs ys zs) ap) (subterm erased (Sub m ys) sb) -> (erased (Sub m zs) r))
  (let-match erased sb (SubCons x m1 _ ix sb1) ((SubNil _) (SubNil zs)))
  (SubCons x m1 zs (app-in-r xs ys zs x ap ix) (app-sub-r xs ys zs m1 ap sb1)))

; Every dart of xs is joined in g to a dart of rs.
(def-adts $ (Covers : ((List (Bond)) g) ((List (Nat)) rs xs) -> Type)
  enum
  (many CovNil : (erased (List (Bond)) g) (erased (List (Nat)) rs) -> (Covers g rs (Nil (Nat))))
  (many CovCons : (erased (List (Bond)) g) (erased (List (Nat)) rs xs) (erased (Nat) x r) (erased (In r rs) pin) (erased (Conn g r x) c)
      (erased (Covers g rs xs) rest) -> (Covers g rs (Cons (Nat) x xs))))

; g tells x apart from every dart of rs.
(def-adts $ (SepAll : ((List (Bond)) g) ((Nat) x) ((List (Nat)) rs) -> Type)
  enum
  (many SANil : (erased (List (Bond)) g) (erased (Nat) x) -> (SepAll g x (Nil (Nat))))
  (many SACons : (erased (List (Bond)) g) (erased (Nat) x y) (erased (List (Nat)) rs) (erased (Sep g x y) s) (erased (SepAll g x rs) rest)
      -> (SepAll g x (Cons (Nat) y rs))))

; g tells any two darts of rs apart.
(def-adts $ (PairSep : ((List (Bond)) g) ((List (Nat)) rs) -> Type)
  enum
  (many PSNil : (erased (List (Bond)) g) -> (PairSep g (Nil (Nat))))
  (many PSCons : (erased (List (Bond)) g) (erased (Nat) r) (erased (List (Nat)) rs) (erased (SepAll g r rs) s) (erased (PairSep g rs) rest)
      -> (PairSep g (Cons (Nat) r rs))))

; The darts of xs lie in k classes of g: rs lists k darts of xs, one of each class.
(def-adts $ (ClassesOn : ((List (Bond)) g) ((List (Nat)) xs) ((Nat) k) -> Type)
  enum
  (many MkClassesOn : (erased (List (Bond)) g) (erased (List (Nat)) xs rs) (erased (Nat) k) (erased (Length (Nat) rs k) lr) (erased (Sub rs xs) sr)
      (erased (PairSep g rs) ps) (erased (Covers g rs xs) cv) -> (ClassesOn g xs k)))

(def-fns _ $ (erased covers-at : (erased (List (Bond)) g) (erased (List (Nat)) rs xs) (erased (Nat) x) (subterm erased (Covers g rs xs) cv) (erased (In x xs) ix)
    -> (erased (Nat) r) (erased (In r rs) pin) (erased (Conn g r x) c))
  (let-match erased cv (CovCons _ _ xs1 y r pin c cv1) (absurd (CovNil _ _) ix))
  (match erased ix _ ((InHere _ _) (values r pin c)) ((InThere _ _ _ ix1) (covers-at g rs xs1 x cv1 ix1))))

; ys pairs each dart of xs with a dart joined to it in g.
(def-adts $ (Joined : ((List (Bond)) g) ((List (Nat)) xs ys) -> Type)
  enum
  (many JNil : (erased (List (Bond)) g) -> (Joined g (Nil (Nat)) (Nil (Nat))))
  (many JCons : (erased (List (Bond)) g) (erased (List (Nat)) xs ys) (erased (Nat) x y) (erased (Conn g x y) c) (erased (Joined g xs ys) rest)
      -> (Joined g (Cons (Nat) x xs) (Cons (Nat) y ys))))

(def-fns _ $ (erased covers-image : (erased (List (Bond)) g) (erased (List (Nat)) rs xs m) (erased (Covers g rs xs) cv) (subterm erased (Sub m xs) sb)
    -> (erased (List (Nat)) ims) (erased (Sub ims rs) si) (erased (Joined g m ims) jn))
  (let-match erased sb (SubCons x m1 _ ix sb1) ((SubNil _) (values (Nil _) (SubNil rs) (JNil g))))
  (let ((erased r) (erased pin) (erased c)) (covers-at g rs xs x cv ix))
  (let ((erased ims1) (erased si1) (erased jn1)) (covers-image g rs xs m1 cv sb1))
  (values (Cons _ r ims1) (SubCons r ims1 rs pin si1) (JCons g m1 ims1 x r (conn-sym g r x c) jn1)))

(def-fns _ $ (erased joined-notin : (erased (List (Bond)) g) (erased (List (Nat)) m ims) (erased (Nat) r i) (subterm erased (SepAll g r m) sa)
    (erased (Joined g m ims) jn) (erased (Conn g r i) c) -> (erased (NotIn i ims) res))
  (let-match erased sa (SACons _ _ y m1 s sa1) ((SANil _ _) (let-match erased jn (JNil _)) (NotInNil i)))
  (let-match erased jn (JCons _ _ ims1 _ j cj jn1))
  (NotInCons i j ims1 (roots-apart g r y i j s (conn-sym g r i c) (conn-sym g y j cj)) (joined-notin g m1 ims1 r i sa1 jn1 c)))

(def-fns _ $ (erased joined-distinct : (erased (List (Bond)) g) (erased (List (Nat)) m ims) (subterm erased (PairSep g m) ps) (erased (Joined g m ims) jn)
    -> (erased (Distinct ims) r))
  (let-match erased ps (PSCons _ r m1 sa ps1) ((PSNil _) (let-match erased jn (JNil _)) (DistNil)))
  (let-match erased jn (JCons _ _ ims1 _ i c jn1))
  (DistCons i ims1 (joined-notin g m1 ims1 r i sa jn1 c) (joined-distinct g m1 ims1 ps1 jn1)))

(def-fns _ $ (erased joined-length : (erased (List (Bond)) g) (erased (List (Nat)) m ims) (erased (Nat) k) (subterm erased (Joined g m ims) jn)
    (erased (Length (Nat) m k) l) -> (erased (Length (Nat) ims k) r))
  (let-match erased jn (JCons _ m1 ims1 x i c jn1) ((JNil _) l))
  (let-match erased l (LengthCons _ _ _ k1 l1))
  (LengthCons _ i ims1 k1 (joined-length g m1 ims1 k1 jn1 l1)))

(def-fns _ $ (erased co-le : (erased (List (Bond)) g) (erased (List (Nat)) xs) (erased (Nat) k1 k2) (erased (ClassesOn g xs k1) c1) (erased (ClassesOn g xs k2) c2)
    -> (erased (Lt k1 (Succ k2)) r))
  (let-match erased c1 (MkClassesOn _ _ rs1 _ lr1 sr1 ps1 cv1))
  (let-match erased c2 (MkClassesOn _ _ rs2 _ lr2 sr2 ps2 cv2))
  (let ((erased ims) (erased si) (erased jn)) (covers-image g rs2 xs rs1 cv2 sr1))
  (pigeonhole ims rs2 k1 k2 (joined-distinct g rs1 ims ps1 jn) si (joined-length g rs1 ims k1 jn lr1) lr2))

; The count of classes among the darts of xs is determined.
(def-fns _ $ (erased co-unique : (erased (List (Bond)) g) (erased (List (Nat)) xs) (erased (Nat) k1 k2) (erased (ClassesOn g xs k1) c1)
    (erased (ClassesOn g xs k2) c2) -> (erased (Eq (Nat) k1 k2) e))
  (le-antisym k1 k2 (co-le g xs k1 k2 c1 c2) (co-le g xs k2 k1 c2 c1)))

(def-fns _ $ (erased rooted-covers : (erased (List (Bond)) g) (erased (List (Nat)) rs xs ls) (subterm erased (Rooted g rs xs ls) ro) -> (erased (Covers g rs xs) r))
  (let-match erased ro (RootedCons _ _ xs1 ls1 x r pin c ro1) ((RootedNil _ _) (CovNil g rs)))
  (CovCons g rs xs1 x r pin c (rooted-covers g rs xs1 ls1 ro1)))

(def-fns _ $ (erased fixed-sepall : (erased (List (Bond)) g) (erased (List (Nat)) lab rs m) (erased (Nat) x) (erased (Const lab g) cl) (erased (Respects lab rs rs) fix)
    (erased (In x rs) ix) (subterm erased (Sub m rs) sb) (erased (NotIn x m) out) -> (erased (SepAll g x m) r))
  (let-match erased sb (SubCons y m1 _ iy sb1) ((SubNil _) (SANil g x)))
  (let-match erased out (NotInCons _ _ _ ne out1))
  (SACons g x y m1 (MkSep g x y lab x y cl (fixed-in lab rs x fix ix) (fixed-in lab rs y fix iy) ne) (fixed-sepall g lab rs m1 x cl fix ix sb1 out1)))

; Distinct darts fixed by a labelling constant along g are told apart by g.
(def-fns _ $ (erased fixed-pairsep : (erased (List (Bond)) g) (erased (List (Nat)) lab rs m) (erased (Const lab g) cl) (erased (Respects lab rs rs) fix)
    (subterm erased (Sub m rs) sb) (erased (Distinct m) dm) -> (erased (PairSep g m) r))
  (let-match erased sb (SubCons x m1 _ ix sb1) ((SubNil _) (PSNil g)))
  (let-match erased dm (DistCons _ _ out dm1))
  (PSCons g x m1 (fixed-sepall g lab rs m1 x cl fix ix sb1 out) (fixed-pairsep g lab rs m1 cl fix sb1 dm1)))

(def-fns _ $ (erased co-of-classes : (erased (List (Bond)) g) (erased (Nat) d k) (erased (List (Nat)) ids) (erased (Classes g d k) cs) (erased (Iota d ids) io)
    -> (erased (ClassesOn g ids k) r))
  (let-match erased cs (MkClasses _ _ _ ids2 lab rs io2 ll lr dr fix cl ro))
  (let-match erased (iota-fn d ids ids2 io io2) (Refl _ _))
  (MkClassesOn g ids rs k lr (under-sub d rs ids (respects-under lab rs rs d fix ll) io) (fixed-pairsep g lab rs rs cl fix (sub-refl rs) dr)
    (rooted-covers g rs ids lab ro)))

(def-fns _ $ (erased classes-of-co : (erased (List (Bond)) g) (erased (Nat) d k) (erased (List (Nat)) ids) (erased (ClassesOn g ids k) co) (erased (Iota d ids) io)
    (erased (Below g d) bg) -> (erased (Classes g d k) r))
  (let ((erased k2) (erased cs)) (classes-exists g d bg))
  (let-match erased (co-unique g ids k k2 co (co-of-classes g d k2 ids cs io)) (Refl _ _))
  cs)

; A set g never leaves holds every dart joined to one of its darts.
(def-fns _ $ (erased shut-conn : (erased (Nat) d x y) (erased (List (Nat)) s) (erased (List (Bond)) g) (erased (Shut s g) sh) (erased (Below g d) bg)
    (erased (Conn g x y) c) (erased (In x s) ix) (erased (Lt x d) lx) (erased (Lt y d) ly) -> (erased (In y s) r))
  (match erased (in-dec y s) _
    ((OrL _ _ iy) iy)
    (absurd (OrR _ _ oy) (sep-conn g y x (shut-sep d y x s g sh bg oy ix ly lx) (conn-sym g x y c)))))

(def-fns _ $ (erased co-cover : (erased (List (Bond)) g) (erased (Nat) d) (erased (List (Nat)) s ids lab rs ys zs m) (erased (Iota d ids) io)
    (erased (Length (Nat) lab d) ll) (erased (Respects lab rs rs) fix) (erased (Rooted g rs ids lab) ro) (erased (Shut s g) sh) (erased (Below g d) bg)
    (erased (Split s rs ys zs) sp) (erased (Under s d) us) (subterm erased (Sub m s) sb) -> (erased (Covers g ys m) r))
  (let-match erased sb (SubCons x m1 _ ix sb1) ((SubNil _) (CovNil g ys)))
  (let ((erased lx)) (under-in s x d us ix))
  (let ((erased r) (erased pr)) (nth-exists _ lab d x ll lx))
  (let ((erased pin) (erased c)) (classes-root g d ids lab rs x r io ro pr lx))
  (let ((erased ir)) (shut-conn d x r s g sh bg (conn-sym g r x c) ix lx (under-in rs r d (respects-under lab rs rs d fix ll) pin)))
  (CovCons g ys m1 x r
    (match erased (split-cover s rs ys zs r sp pin) _
      ((OrL _ _ i) i)
      (absurd (OrR _ _ i) (apart-irrefl r (notin-in r r s (split-out s rs ys zs r sp i) ir))))
    c (co-cover g d s ids lab rs ys zs m1 io ll fix ro sh bg sp us sb1)))

; A set of darts that g never leaves lies in some number of classes.
(def-fns _ $ (erased co-exists : (erased (List (Bond)) g) (erased (Nat) d k) (erased (List (Nat)) s) (erased (Classes g d k) cs) (erased (Shut s g) sh)
    (erased (Under s d) us) -> (erased (Nat) k1) (erased (ClassesOn g s k1) r))
  (let ((erased bg)) (classes-below g d k cs))
  (let-match erased cs (MkClasses _ _ _ ids lab rs io ll lr dr fix cl ro))
  (let ((erased ys) (erased zs) (erased sp)) (split-exists s rs))
  (let ((erased k1) (erased l1)) (length-exists _ ys))
  (let ((erased dy) (erased dz)) (split-distinct s rs ys zs sp dr))
  (let ((erased sy) (erased sz)) (split-sub s rs ys zs sp))
  (values k1 (MkClassesOn g s ys k1 l1 (split-sub-t s rs ys zs sp) (fixed-pairsep g lab rs ys cl fix sy dy)
    (co-cover g d s ids lab rs ys zs s io ll fix ro sh bg sp us (sub-refl s)))))

(def-fns _ $ (erased sepall-app : (erased (List (Bond)) g) (erased (Nat) x) (erased (List (Nat)) xs ys zs) (subterm erased (AppN xs ys zs) ap)
    (erased (SepAll g x xs) a) (erased (SepAll g x ys) b) -> (erased (SepAll g x zs) r))
  (let-match erased ap (AppCons xs1 _ zs1 y ap1) ((AppNil _) b))
  (let-match erased a (SACons _ _ _ _ s a1))
  (SACons g x y zs1 s (sepall-app g x xs1 ys zs1 ap1 a1 b)))

(def-fns _ $ (erased shut-sepall : (erased (Nat) d x) (erased (List (Nat)) s t m) (erased (List (Bond)) g) (erased (Shut s g) sh) (erased (Below g d) bg)
    (erased (In x s) ix) (erased (Lt x d) lx) (erased (Disj t s) dj) (erased (Under t d) ut) (subterm erased (Sub m t) sb) -> (erased (SepAll g x m) r))
  (let-match erased sb (SubCons y m1 _ iy sb1) ((SubNil _) (SANil g x)))
  (SACons g x y m1 (sep-sym g y x (shut-sep d y x s g sh bg (disj-notin y t s dj iy) ix (under-in t y d ut iy) lx))
    (shut-sepall d x s t m1 g sh bg ix lx dj ut sb1)))

(def-fns _ $ (erased pairsep-union : (erased (Nat) d) (erased (List (Nat)) s t xs ys zs) (erased (List (Bond)) g) (subterm erased (AppN xs ys zs) ap)
    (erased (PairSep g xs) a) (erased (PairSep g ys) b) (erased (Sub xs s) sx) (erased (Sub ys t) sy) (erased (Shut s g) sh) (erased (Below g d) bg)
    (erased (Disj t s) dj) (erased (Under s d) us) (erased (Under t d) ut) -> (erased (PairSep g zs) r))
  (let-match erased ap (AppCons xs1 _ zs1 x ap1) ((AppNil _) b))
  (let-match erased a (PSCons _ _ _ sa a1))
  (let-match erased sx (SubCons _ _ _ ix sx1))
  (PSCons g x zs1 (sepall-app g x xs1 ys zs1 ap1 sa (shut-sepall d x s t ys g sh bg ix (under-in s x d us ix) dj ut sy))
    (pairsep-union d s t xs1 ys zs1 g ap1 a1 b sx1 sy sh bg dj us ut)))

(def-fns _ $ (erased covers-union : (erased (List (Bond)) g) (erased (List (Nat)) s t st rs1 rs2 rs u) (erased (Covers g rs1 s) c1) (erased (Covers g rs2 t) c2)
    (erased (AppN rs1 rs2 rs) ar) (erased (AppN s t st) ap) (subterm erased (Sub u st) sb) -> (erased (Covers g rs u) r))
  (let-match erased sb (SubCons x u1 _ ix sb1) ((SubNil _) (CovNil g rs)))
  (let ((erased rest)) (covers-union g s t st rs1 rs2 rs u1 c1 c2 ar ap sb1))
  (match erased (app-in-inv s t st x ap ix) _
    ((OrL _ _ i) (let ((erased r) (erased pin) (erased c)) (covers-at g rs1 s x c1 i)) (CovCons g rs u1 x r (app-in-l rs1 rs2 rs r ar pin) c rest))
    ((OrR _ _ i) (let ((erased r) (erased pin) (erased c)) (covers-at g rs2 t x c2 i)) (CovCons g rs u1 x r (app-in-r rs1 rs2 rs r ar pin) c rest))))

; The classes of two disjoint sets of darts, the first one never left by g, add up.
(def-fns _ $ (erased co-union : (erased (List (Bond)) g) (erased (Nat) d k1 k2 k) (erased (List (Nat)) s t st u) (erased (ClassesOn g s k1) c1)
    (erased (ClassesOn g t k2) c2) (erased (AppN s t st) ap) (erased (Sub u st) su) (erased (Sub st u) us) (erased (Shut s g) sh) (erased (Below g d) bg)
    (erased (Disj t s) dj) (erased (Under s d) uds) (erased (Under t d) udt) (erased (Add k1 k2 k) a) -> (erased (ClassesOn g u k) r))
  (let-match erased c1 (MkClassesOn _ _ rs1 _ lr1 sr1 ps1 cv1))
  (let-match erased c2 (MkClassesOn _ _ rs2 _ lr2 sr2 ps2 cv2))
  (let ((erased rs) (erased aprs)) (app-exists rs1 rs2))
  (MkClassesOn g u rs k (app-length rs1 rs2 rs k1 k2 k aprs lr1 lr2 a)
    (sub-trans rs st u (app-sub rs1 rs2 rs st aprs (app-sub-l s t st rs1 ap sr1) (app-sub-r s t st rs2 ap sr2)) us)
    (pairsep-union d s t rs1 rs2 rs g aprs ps1 ps2 sr1 sr2 sh bg dj uds udt)
    (covers-union g s t st rs1 rs2 rs u cv1 cv2 aprs ap su)))

; Each dart x of xs goes by f1 to a dart y of t, which f2 sends to a dart joined to x in g.
(def-adts $ (Lift : ((List (Bond)) g) ((List (Nat)) f1 f2 t xs) -> Type)
  enum
  (many LiftNil : (erased (List (Bond)) g) (erased (List (Nat)) f1 f2 t) -> (Lift g f1 f2 t (Nil (Nat))))
  (many LiftCons : (erased (List (Bond)) g) (erased (List (Nat)) f1 f2 t xs) (erased (Nat) x y z) (erased (Nth (Nat) f1 x y) p1) (erased (In y t) iy)
      (erased (Nth (Nat) f2 y z) p2) (erased (Conn g x z) c) (erased (Lift g f1 f2 t xs) rest) -> (Lift g f1 f2 t (Cons (Nat) x xs))))

; Each bond of g has both ends off xs, or both on xs and sent by f to darts joined in g2.
(def-adts $ (Moves : ((List (Bond)) g) ((List (Nat)) xs f) ((List (Bond)) g2) -> Type)
  enum
  (many MvNil : (erased (List (Nat)) xs f) (erased (List (Bond)) g2) -> (Moves (Nil (Bond)) xs f g2))
  (many MvIn : (erased (List (Bond)) g g2) (erased (List (Nat)) xs f) (erased (Nat) x y x2 y2) (erased (In x xs) ix) (erased (In y xs) iy)
      (erased (Nth (Nat) f x x2) px) (erased (Nth (Nat) f y y2) py) (erased (Conn g2 x2 y2) c) (erased (Moves g xs f g2) rest)
      -> (Moves (Cons (Bond) (MkBond x y) g) xs f g2))
  (many MvOut : (erased (List (Bond)) g g2) (erased (List (Nat)) xs f) (erased (Nat) x y) (erased (NotIn x xs) ox) (erased (NotIn y xs) oy)
      (erased (Moves g xs f g2) rest) -> (Moves (Cons (Bond) (MkBond x y) g) xs f g2)))

(def-fns _ $ (erased lift-at : (erased (List (Bond)) g) (erased (List (Nat)) f1 f2 t xs) (erased (Nat) x) (subterm erased (Lift g f1 f2 t xs) lf) (erased (In x xs) ix)
    -> (erased (Nat) y z) (erased (Nth (Nat) f1 x y) p1) (erased (In y t) iy) (erased (Nth (Nat) f2 y z) p2) (erased (Conn g x z) c))
  (let-match erased lf (LiftCons _ _ _ _ xs1 x0 y z p1 iy p2 c lf1) (absurd (LiftNil _ _ _ _) ix))
  (match erased ix _ ((InHere _ _) (values y z p1 iy p2 c)) ((InThere _ _ _ ix1) (lift-at g f1 f2 t xs1 x lf1 ix1))))

(def-fns _ $ (erased moves-tail : (erased (List (Bond)) g g2) (erased (Bond) b) (erased (List (Nat)) xs f) (erased (Moves (Cons (Bond) b g) xs f g2) mv)
    -> (erased (Moves g xs f g2) r))
  (match erased mv _
    ((MvIn _ _ _ _ x y x2 y2 ix iy px py c rest) rest)
    ((MvOut _ _ _ _ x y ox oy rest) rest)))

(def-fns _ $ (erased adj-move : (erased (List (Bond)) g g2) (erased (List (Nat)) xs f) (erased (Nat) x y x2) (subterm erased (Adj g x y) a) (erased (Moves g xs f g2) mv)
    (erased (In x xs) ix) (erased (Nth (Nat) f x x2) px) -> (erased (Nat) y2) (erased (Nth (Nat) f y y2) py) (erased (Conn g2 x2 y2) c) (erased (In y xs) iy))
  (match erased a _
    ((AdjFwd g1 _ _)
      (match erased mv _
        ((MvIn _ _ _ _ _ _ x3 y3 _ iy px3 py3 c3 _) (let-match erased (nth-fn _ f x x3 x2 px3 px) (Refl _ _)) (values y3 py3 c3 iy))
        (absurd (MvOut _ _ _ _ _ _ ox _ _) (apart-irrefl x (notin-in x x xs ox ix)))))
    ((AdjBwd g1 _ _)
      (match erased mv _
        ((MvIn _ _ _ _ _ _ x3 y3 iy _ px3 py3 c3 _) (let-match erased (nth-fn _ f x y3 x2 py3 px) (Refl _ _)) (values x3 px3 (conn-sym g2 x3 y3 c3) iy))
        (absurd (MvOut _ _ _ _ _ _ _ oy _) (apart-irrefl x (notin-in x x xs oy ix)))))
    ((AdjThere g1 b _ _ a1) (adj-move g1 g2 xs f x y x2 a1 (moves-tail g1 g2 b xs f mv) ix px))))

(def-fns _ $ (erased conn-move : (erased (List (Bond)) g g2) (erased (List (Nat)) xs f) (erased (Nat) x y x2) (subterm erased (Conn g x y) cn) (erased (Moves g xs f g2) mv)
    (erased (In x xs) ix) (erased (Nth (Nat) f x x2) px) -> (erased (Nat) y2) (erased (Nth (Nat) f y y2) py) (erased (Conn g2 x2 y2) c) (erased (In y xs) iy))
  (let-match erased cn (ConnStep _ _ w _ a cn1) ((ConnHere _ _) (values x2 px (ConnHere g2 x2) ix)))
  (let ((erased w2) (erased pw) (erased cw) (erased iw)) (adj-move g g2 xs f x w x2 a mv ix px))
  (let ((erased y2) (erased py) (erased cy) (erased iy)) (conn-move g g2 xs f w y w2 cn1 mv iw pw))
  (values y2 py (conn-cat g2 x2 w2 y2 cw cy) iy))

(def-fns _ $ (erased lift-image : (erased (List (Bond)) g) (erased (List (Nat)) f1 f2 t xs m) (erased (Lift g f1 f2 t xs) lf) (subterm erased (Sub m xs) sb)
    -> (erased (List (Nat)) ims) (erased (Respects f1 m ims) rp) (erased (Sub ims t) si))
  (let-match erased sb (SubCons x m1 _ ix sb1) ((SubNil _) (values (Nil _) (RespNil f1) (SubNil t))))
  (let ((erased y) (erased z) (erased p1) (erased iy) (erased p2) (erased c)) (lift-at g f1 f2 t xs x lf ix))
  (let ((erased ims1) (erased rp1) (erased si1)) (lift-image g f1 f2 t xs m1 lf sb1))
  (values (Cons _ y ims1) (RespCons f1 m1 ims1 x y p1 rp1) (SubCons y ims1 t iy si1)))

; Darts told apart in g1 have images told apart in g2.
(def-fns _ $ (erased sep-map : (erased (List (Bond)) g1 g2) (erased (List (Nat)) s1 s2 h l) (erased (Nat) d k2 a b a2 b2) (erased (Sep g1 a b) sp)
    (erased (In a s1) ia) (erased (In b s1) ib) (erased (Nth (Nat) h a a2) pa) (erased (Nth (Nat) h b b2) pb) (erased (Lift g1 h l s2 s1) lf)
    (erased (Moves g2 s2 l g1) mv) (erased (Classes g2 d k2) cs) (erased (Under s2 d) us) -> (erased (Sep g2 a2 b2) r))
  (let ((erased a3) (erased a4) (erased qa) (erased ja) (erased la) (erased ca)) (lift-at g1 h l s2 s1 a lf ia))
  (let ((erased b3) (erased b4) (erased qb) (erased jb) (erased lb) (erased cb)) (lift-at g1 h l s2 s1 b lf ib))
  (let-match erased (nth-fn _ h a a3 a2 qa pa) (Refl _ _))
  (let-match erased (nth-fn _ h b b3 b2 qb pb) (Refl _ _))
  (match erased (classes-dec g2 d k2 a2 b2 cs (under-in s2 a2 d us ja) (under-in s2 b2 d us jb)) _
    (absurd (OrL _ _ c)
      (let ((erased b5) (erased q5) (erased c5) (erased i5)) (conn-move g2 g1 s2 l a2 b2 a4 c mv ja la))
      (let-match erased (nth-fn _ l b2 b5 b4 q5 lb) (Refl _ _))
      (sep-conn g1 a b sp (conn-cat g1 a a4 b ca (conn-cat g1 a4 b4 b c5 (conn-sym g1 b b4 cb)))))
    ((OrR _ _ s) s)))

(def-fns _ $ (erased sepall-map : (erased (List (Bond)) g1 g2) (erased (List (Nat)) s1 s2 h l m ims) (erased (Nat) d k2 a a2) (subterm erased (SepAll g1 a m) sa)
    (erased (In a s1) ia) (erased (Sub m s1) sb) (erased (Nth (Nat) h a a2) pa) (erased (Respects h m ims) rp) (erased (Lift g1 h l s2 s1) lf)
    (erased (Moves g2 s2 l g1) mv) (erased (Classes g2 d k2) cs) (erased (Under s2 d) us) -> (erased (SepAll g2 a2 ims) r))
  (let-match erased sa (SACons _ _ b m1 sp sa1) ((SANil _ _) (let-match erased rp (RespNil _)) (SANil g2 a2)))
  (let-match erased rp (RespCons _ _ ims1 _ b2 pb rp1))
  (let-match erased sb (SubCons _ _ _ ib sb1))
  (SACons g2 a2 b2 ims1 (sep-map g1 g2 s1 s2 h l d k2 a b a2 b2 sp ia ib pa pb lf mv cs us)
    (sepall-map g1 g2 s1 s2 h l m1 ims1 d k2 a a2 sa1 ia sb1 pa rp1 lf mv cs us)))

(def-fns _ $ (erased pairsep-map : (erased (List (Bond)) g1 g2) (erased (List (Nat)) s1 s2 h l m ims) (erased (Nat) d k2) (subterm erased (PairSep g1 m) ps)
    (erased (Sub m s1) sb) (erased (Respects h m ims) rp) (erased (Lift g1 h l s2 s1) lf) (erased (Moves g2 s2 l g1) mv) (erased (Classes g2 d k2) cs)
    (erased (Under s2 d) us) -> (erased (PairSep g2 ims) r))
  (let-match erased ps (PSCons _ a m1 sa ps1) ((PSNil _) (let-match erased rp (RespNil _)) (PSNil g2)))
  (let-match erased rp (RespCons _ _ ims1 _ a2 pa rp1))
  (let-match erased sb (SubCons _ _ _ ia sb1))
  (PSCons g2 a2 ims1 (sepall-map g1 g2 s1 s2 h l m1 ims1 d k2 a a2 sa ia sb1 pa rp1 lf mv cs us)
    (pairsep-map g1 g2 s1 s2 h l m1 ims1 d k2 ps1 sb1 rp1 lf mv cs us)))

(def-fns _ $ (erased covers-map : (erased (List (Bond)) g1 g2) (erased (List (Nat)) s1 s2 h l rs ims m) (erased (Covers g1 rs s1) cv) (erased (Sub rs s1) sr)
    (erased (Respects h rs ims) rp) (erased (Lift g1 h l s2 s1) lf1) (erased (Lift g2 l h s1 s2) lf2) (erased (Moves g1 s1 h g2) mv)
    (subterm erased (Sub m s2) sb) -> (erased (Covers g2 ims m) r))
  (let-match erased sb (SubCons x m1 _ ix sb1) ((SubNil _) (CovNil g2 ims)))
  (let ((erased y) (erased z) (erased p1) (erased iy) (erased p2) (erased cxz)) (lift-at g2 l h s1 s2 x lf2 ix))
  (let ((erased r) (erased pin) (erased cry)) (covers-at g1 rs s1 y cv iy))
  (let ((erased ir)) (sub-in rs s1 r sr pin))
  (let ((erased r2) (erased z2) (erased q1) (erased ir2) (erased q2) (erased crz)) (lift-at g1 h l s2 s1 r lf1 ir))
  (let ((erased z3) (erased q3) (erased c3) (erased i3)) (conn-move g1 g2 s1 h r y r2 cry mv ir q1))
  (let-match erased (nth-fn _ h y z3 z q3 p2) (Refl _ _))
  (CovCons g2 ims m1 x r2 (in-map h rs ims r r2 pin rp q1) (conn-cat g2 r2 z x c3 (conn-sym g2 x z cxz))
    (covers-map g1 g2 s1 s2 h l rs ims m1 cv sr rp lf1 lf2 mv sb1)))

; The classes of g1 on s1 and of g2 on s2 correspond through h and l, which send darts of one to darts of the other joined to
; them (Gonthier's adjunction_n_comp).
(def-fns _ $ (erased co-map : (erased (List (Bond)) g1 g2) (erased (List (Nat)) s1 s2 h l) (erased (Nat) k d k2) (erased (ClassesOn g1 s1 k) co)
    (erased (Lift g1 h l s2 s1) lf1) (erased (Lift g2 l h s1 s2) lf2) (erased (Moves g1 s1 h g2) mv1) (erased (Moves g2 s2 l g1) mv2)
    (erased (Classes g2 d k2) cs) (erased (Under s2 d) us) -> (erased (ClassesOn g2 s2 k) r))
  (let-match erased co (MkClassesOn _ _ rs _ lr sr ps cv))
  (let ((erased ims) (erased rp) (erased si)) (lift-image g1 h l s2 s1 rs lf1 sr))
  (MkClassesOn g2 s2 ims k (respects-length h rs ims k rp lr) si (pairsep-map g1 g2 s1 s2 h l rs ims d k2 ps sr rp lf1 mv2 cs us)
    (covers-map g1 g2 s1 s2 h l rs ims s2 cv sr rp lf1 lf2 mv1 (sub-refl s2))))

(def-fns _ $ (erased sub-under : (erased (List (Nat)) m s) (erased (Nat) k) (subterm erased (Sub m s) sb) (erased (Under s k) u) -> (erased (Under m k) r))
  (let-match erased sb (SubCons x m1 _ ix sb1) ((SubNil _) (UnderNil k)))
  (UnderCons m1 x k (under-in s x k u ix) (sub-under m1 s k sb1 u)))

(def-fns _ $ (erased respects-under-vals : (erased (List (Nat)) h xs ys) (erased (Nat) d) (subterm erased (Respects h xs ys) rp) (erased (Under h d) u)
    -> (erased (Under ys d) r))
  (let-match erased rp (RespCons _ xs1 ys1 j y p rp1) ((RespNil _) (UnderNil d)))
  (UnderCons ys1 y d (under-nth h j y d u p) (respects-under-vals h xs1 ys1 d rp1 u)))

; ls sends each dart of xs in h to its position in h, and every other dart to 0.
(def-adts $ (InvL : ((List (Nat)) h xs ls) -> Type)
  enum
  (many IvNil : (erased (List (Nat)) h) -> (InvL h (Nil (Nat)) (Nil (Nat))))
  (many IvIn : (erased (List (Nat)) h xs ls) (erased (Nat) x j) (erased (Nth (Nat) h j x) p) (erased (InvL h xs ls) rest)
      -> (InvL h (Cons (Nat) x xs) (Cons (Nat) j ls)))
  (many IvOut : (erased (List (Nat)) h xs ls) (erased (Nat) x) (erased (NotIn x h) p) (erased (InvL h xs ls) rest)
      -> (InvL h (Cons (Nat) x xs) (Cons (Nat) (Zero) ls))))

(def-fns _ $ (erased inv-exists : (erased (List (Nat)) h) (subterm erased (List (Nat)) xs) -> (erased (List (Nat)) ls) (erased (InvL h xs ls) r))
  (let-match erased xs (Cons _ x xs1) ((Nil _) (values (Nil _) (IvNil h))))
  (let ((erased ls1) (erased r1)) (inv-exists h xs1))
  (match erased (in-dec x h) _
    ((OrL _ _ ix) (let ((erased j) (erased p)) (in-nth x h ix)) (values (Cons _ j ls1) (IvIn h xs1 ls1 x j p r1)))
    ((OrR _ _ o) (values (Cons _ (Zero) ls1) (IvOut h xs1 ls1 x o r1)))))

(def-fns _ $ (erased inv-nth : (erased (List (Nat)) h xs ls) (erased (Nat) i x j) (subterm erased (InvL h xs ls) iv) (erased (Distinct h) dh)
    (erased (Nth (Nat) xs i x) px) (erased (Nth (Nat) h j x) pj) -> (erased (Nth (Nat) ls i j) r))
  (match erased iv _
    (absurd (IvNil _) px)
    ((IvIn _ xs1 ls1 y j2 p iv1)
      (match erased px _
        ((NthHere _ _ _) (let-match erased (distinct-nth h j2 j x dh p pj) (Refl _ _)) (NthHere _ j2 ls1))
        ((NthThere _ _ _ i1 _ px1) (NthThere _ j2 ls1 i1 j (inv-nth h xs1 ls1 i1 x j iv1 dh px1 pj)))))
    ((IvOut _ xs1 ls1 y o iv1)
      (match erased px _
        (absurd (NthHere _ _ _) (apart-irrefl x (notin-in x x h o (nth-in h j x pj))))
        ((NthThere _ _ _ i1 _ px1) (NthThere _ (Zero) ls1 i1 j (inv-nth h xs1 ls1 i1 x j iv1 dh px1 pj)))))))
