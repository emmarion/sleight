(def-adts
  ((Agr : (Type A) ((List A) xs ys) ((Nat) q) -> Type)
    enum
    (many AgZ : (erased Type A) (erased (List A) xs ys) -> (Agr A xs ys (Zero)))
    (many AgR : (erased Type A) (erased (List A) xs) (erased (Nat) q) -> (Agr A xs xs q))
    (many AgS : (erased Type A) (erased A a) (erased (List A) xs ys) (erased (Nat) q) (erased (Agr A xs ys q) g) -> (Agr A (Cons A a xs) (Cons A a ys) (Succ q)))))

(def-fns _ $ (erased agr-nth : (erased Type A) (erased (List A) xs ys) (erased (Nat) q i) (erased A x) (subterm erased (Agr A xs ys q) g) (erased (Nth A xs i x) nt) (erased (Lt i q) lt)
    -> (erased (Nth A ys i x) r))
  (let-match erased g (AgS _ a xs1 ys1 q1 g1) (absurd (AgZ _ _ _) lt) ((AgR _ _ _) nt))
  (let-match erased nt (NthThere _ _ _ i1 _ nt1) ((NthHere _ _ _) (NthHere _ a ys1)))
  (let-match erased lt (LtS _ _ lt1))
  (NthThere _ a ys1 i1 x (agr-nth A xs1 ys1 q1 i1 x g1 nt1 lt1)))

(def-fns _ $ (erased setnth-agr : (erased Type A) (erased (List A) xs ys) (erased (Nat) q i) (erased A y) (subterm erased (SetNth A xs i y ys) st) (erased (Lt q (Succ i)) le)
    -> (erased (Agr A xs ys q) g))
  (let-match erased q (Succ q1) ((Zero) (AgZ A xs ys)))
  (let-match erased st (SetThere _ a rest i1 _ rest2 st1) (absurd (SetHere _ _ _ _) (let-match erased le (LtS _ _ l1)) l1))
  (let-match erased le (LtS _ _ l1))
  (AgS A a rest rest2 q1 (setnth-agr A rest rest2 q1 i1 y st1 l1)))

(def-fns _ $ (erased agr-trans : (erased Type A) (erased (List A) xs ys zs) (erased (Nat) q) (subterm erased (Agr A xs ys q) g1) (erased (Agr A ys zs q) g2)
    -> (erased (Agr A xs zs q) g))
  (let-match erased g1 (AgS _ a xs1 ys1 q1 h1) ((AgZ _ _ _) (AgZ A xs zs)) ((AgR _ _ _) g2))
  (let-match erased g2 (AgS _ _ _ zs1 _ h2) ((AgR _ _ _) g1))
  (AgS A a xs1 zs1 q1 (agr-trans A xs1 ys1 zs1 q1 h1 h2)))

(def-fns _ $ (erased agr-mono : (erased Type A) (erased (List A) xs ys) (erased (Nat) q q2) (subterm erased (Agr A xs ys q) g) (erased (Lt q2 (Succ q)) le)
    -> (erased (Agr A xs ys q2) g2))
  (let-match erased q2 (Succ q3) ((Zero) (AgZ A xs ys)))
  (match erased g _
    (absurd (AgZ _ _ _) (let-match erased le (LtS _ _ l1)) l1)
    ((AgR _ _ _) (AgR A xs q2))
    ((AgS _ a xs1 ys1 q1 h) (let-match erased le (LtS _ _ l1)) (AgS A a xs1 ys1 q3 (agr-mono A xs1 ys1 q1 q3 h l1)))))

(def-fns _ $ (erased splice-agr : (erased Type A) (erased (List A) xs qs ys zs) (erased (Nat) n)
    (subterm erased (Splice A xs (Zero) n ys xs) p) (erased (Splice A qs (Zero) n ys zs) q) -> (erased (Agr A xs zs n) g))
  (let-match erased p (SpliceHere _ x _ xs1 n1 ys1 _ p1) ((SpliceNil _ _) (AgZ A xs zs)))
  (let-match erased q (SpliceHere _ _ _ qs1 _ _ zs1 q1))
  (AgS A x xs1 zs1 n1 (splice-agr A xs1 qs1 ys1 zs1 n1 p1 q1)))

(def-fns _ $ (erased splice-length : (erased Type A) (erased (List A) xs ys zs) (erased (Nat) i n m)
    (subterm erased (Splice A xs i n ys zs) p) (erased (Length A xs m) l) -> (erased (Length A zs m) r))
  (match erased p _
    ((SpliceNil _ _) l)
    ((SpliceHere _ _ y xs1 n1 ys1 zs1 p1) (let-match erased l (LengthCons _ _ _ m1 l1)) (LengthCons _ y zs1 m1 (splice-length _ xs1 ys1 zs1 (Zero) n1 m1 p1 l1)))
    ((SpliceThere _ x xs1 i1 _ _ zs1 p1) (let-match erased l (LengthCons _ _ _ m1 l1)) (LengthCons _ x zs1 m1 (splice-length _ xs1 ys zs1 i1 n m1 p1 l1)))))

; Lay A xs ps n: logical element i of xs (0 the top) is at physical index n-1-i of ps.
(def-adts
  ((Lay : (Type A) ((List A) xs) ((List (Copy A)) ps) ((Nat) n) -> Type)
    enum
    (many LayN : (erased Type A) (erased (List (Copy A)) ps) -> (Lay A (Nil A) ps (Zero)))
    (many LayC : (erased Type A) (erased A x) (erased (List A) xs) (erased (List (Copy A)) ps) (erased (Nat) n)
       (erased (Lay A xs ps n) ly) (erased (Nth (Copy A) ps n (MkCopy A x)) nt) -> (Lay A (Cons A x xs) ps (Succ n)))))

(def-fns _ $ (erased lay-length : (erased Type A) (erased (List A) xs) (erased (List (Copy A)) ps) (erased (Nat) n)
    (subterm erased (Lay A xs ps n) ly) -> (erased (Length A xs n) l))
  (let-match erased ly (LayC _ x xs1 _ n1 ly1 _) ((LayN _ _) (LengthNil _)))
  (LengthCons _ x xs1 n1 (lay-length _ xs1 ps n1 ly1)))

(def-fns _ $ (erased lay-le : (erased Type A) (erased (List A) xs) (erased (List (Copy A)) ps) (erased (Nat) n len)
    (erased (Lay A xs ps n) ly) (erased (Length (Copy A) ps len) l) -> (erased (Lt n (Succ len)) le))
  (let-match erased ly (LayC _ _ _ _ n1 _ nt) ((LayN _ _) (LtZ len)))
  (LtS n1 len (nth-lt-length _ ps n1 len _ nt l)))

(def-fns _ $ (erased lay-nth : (erased Type A) (erased (List A) xs) (erased (List (Copy A)) ps) (erased (Nat) n i j) (erased A x)
    (subterm erased (Lay A xs ps n) ly) (erased (Nth A xs i x) nt) (erased (Add (Succ i) j n) ad) -> (erased (Nth (Copy A) ps j (MkCopy A x)) r))
  (let-match erased ly (LayC _ _ xs1 _ n1 ly1 nt1) (absurd (LayN _ _) nt))
  (let-match erased ad (AddSucc _ _ _ ad1))
  (let-match erased nt (NthThere _ _ _ i1 _ nt2) ((NthHere _ _ _) (let-match erased ad1 (AddZero _)) nt1))
  (lay-nth _ xs1 ps n1 i1 j x ly1 nt2 ad1))

(def-fns _ $ (erased lay-agr : (erased Type A) (erased (List A) xs) (erased (List (Copy A)) ps qs) (erased (Nat) n q)
    (subterm erased (Lay A xs ps n) ly) (erased (Agr (Copy A) ps qs q) g) (erased (Lt n (Succ q)) le) -> (erased (Lay A xs qs n) r))
  (let-match erased ly (LayC _ x xs1 _ n1 ly1 nt) ((LayN _ _) (LayN A qs)))
  (let-match erased le (LtS _ _ lt))
  (LayC A x xs1 qs n1 (lay-agr A xs1 ps qs n1 q ly1 g (lt-weaken n1 q lt)) (agr-nth _ ps qs q n1 (MkCopy A x) g nt lt)))

(def-fns _ $ (erased lay-drop-le : (erased Type A) (erased (List A) p ys xs) (erased (List (Copy A)) ps) (erased (Nat) n k)
    (subterm erased (Cat A p ys xs) c) (erased (Lay A xs ps n) ly) (erased (Length A p k) lk) -> (erased (Lt k (Succ n)) le))
  (let-match erased c (CatC _ _ p1 _ xs1 c1) ((CatN _ _) (let-match erased lk (LengthNil _)) (LtZ n)))
  (let-match erased lk (LengthCons _ _ _ k1 lk1))
  (let-match erased ly (LayC _ _ _ _ n1 ly1 _))
  (LtS k1 n (lay-drop-le A p1 ys xs1 ps n1 k1 c1 ly1 lk1)))

(def-fns _ $ (erased lay-drop : (erased Type A) (erased (List A) p ys xs) (erased (List (Copy A)) ps) (erased (Nat) n k m)
    (subterm erased (Cat A p ys xs) c) (erased (Lay A xs ps n) ly) (erased (Length A p k) lk) (erased (Add k m n) ad) -> (erased (Lay A ys ps m) r))
  (let-match erased c (CatC _ _ p1 _ xs1 c1) ((CatN _ _) (let-match erased lk (LengthNil _)) (let-match erased ad (AddZero _)) ly))
  (let-match erased lk (LengthCons _ _ _ k1 lk1))
  (let-match erased ly (LayC _ _ _ _ n1 ly1 _))
  (let-match erased ad (AddSucc _ _ _ ad1))
  (lay-drop A p1 ys xs1 ps n1 k1 m c1 ly1 lk1 ad1))

(def-adts $ (Av : (Type A) ((List A) xs) -> Type)
  enum
  (many MkAv : (erased Type A) (erased (List A) xs) (erased (List (Copy A)) ps) (many (Nat) n) (erased (Lay A xs ps n) ly)
     (unique (Array (Copy A) ps) a) (many A d) -> (Av A xs)))

(def-fns _ $ (many av-new : (erased Type A) (many A x0) (many (Nat) cap) -> (unique (Av A (Nil A)) v))
  (let ((erased ps) (unique a) (erased _)) (array-make A cap x0))
  (MkAv A (Nil A) ps (Zero) (LayN A ps) a x0))

(def-fns _ $ (many av-len : (erased Type A) (erased (List A) xs) (unique (Av A xs) v) ->
    (many (Nat) n) (erased (Length A xs n) p) (unique v is v2 at v))
  (let-match unique v (MkAv _ _ ps n ly a d u))
  (values n (lay-length _ xs ps n ly) (at unique (u A xs ps n ly a d))))

(def-fns _ $ (many av-get : (erased Type A) (erased (List A) xs) (unique (Av A xs) v) (many (Nat) i) (erased A x) (erased (Nth A xs i x) nt) ->
    (many x is y) (unique v is v2 at v))
  (let-match unique v (MkAv _ _ ps n ly a d u))
  (let ((many j) (erased ad)) (sub n (Succ i) (LtS i n (nth-lt-length _ xs i n x nt (lay-length _ xs ps n ly)))))
  (let ((many y) (unique a2)) (array-get _ _ a j x (lay-nth _ xs ps n i j x ly nt ad)))
  (values y (at unique (u A xs ps n ly a2 d))))

(def-fns _ $ (many av-place : (erased Type A) (erased (List A) xs) (erased (List (Copy A)) ps) (many (Nat) n) (erased (Lay A xs ps n) ly)
    (erased (Copy A) w) (erased (Nth (Copy A) ps n w) nt) (unique (Array (Copy A) ps) a) (many A x) ->
    (erased (List (Copy A)) qs) (erased (Lay A (Cons A x xs) qs (Succ n)) ly2) (unique (Array (Copy A) qs) a2 at a))
  (let ((erased qs) (unique a2) (erased st)) (array-place _ _ a n (MkCopy _ x) w nt))
  (values qs (LayC A x xs qs n (lay-agr A xs ps qs n n ly (setnth-agr _ ps qs n n _ st (lt-succ n)) (lt-succ n)) (setnth-nth _ ps n _ qs st)) a2))

(def-fns _ $ (many av-push : (erased Type A) (erased (List A) xs) (unique (Av A xs) v) (many A x) -> (unique (Av A (Cons A x xs)) v2 at v))
  (let-match unique v (MkAv _ _ ps n ly a d u))
  (let ((many len) (erased lc) (unique a1)) (array-length _ _ a))
  (let-match many (lt-dec n len) (Yes _ _ _ _ lt)
    ((No _ _ _ _ _)
      (let ((many c) (erased ad)) (add n n))
      (let ((erased qs) (unique b) (erased rp)) (array-make A (Succ c) d))
      (let ((erased le)) (add-le-left n n c ad))
      (let ((erased ys) (erased fr)) (splice-range _ ps len lc (Zero) n n (AddZero n) (lay-le _ xs ps n len ly lc)))
      (let ((erased old) (erased to)) (splice-range _ qs (Succ c) (repeat-length _ _ _ _ rp) (Zero) n n (AddZero n) (lt-weaken n (Succ c) le)))
      (let ((erased zs) (unique b2) (erased sp)) (array-blit _ _ (share a1) (Zero) _ b (Zero) n ys fr old to))
      (let ((erased w) (erased nt)) (nth-exists _ zs (Succ c) n (splice-length _ qs ys zs (Zero) n (Succ c) sp (repeat-length _ _ _ _ rp)) le))
      (let ((erased zs2) (erased ly2) (unique b3))
        (av-place A xs zs n (lay-agr A xs ps zs n n ly (splice-agr _ ps qs ys zs n fr sp) (lt-succ n)) w nt b2 x))
      (u A (Cons A x xs) zs2 (Succ n) ly2 b3 (at) d)))
  (let ((erased w) (erased nt)) (nth-exists _ ps len n lc lt))
  (let ((erased ps2) (erased ly2) (unique a2)) (av-place A xs ps n ly w nt a1 x))
  (u A (Cons A x xs) ps2 (Succ n) ly2 (at) a2 (at) d))

(def-fns _ $ (many av-pop : (erased Type A) (erased A x) (erased (List A) xs) (unique (Av A (Cons A x xs)) v) ->
    (many x is y) (unique (Av A xs) v2 at v))
  (let-match unique v (MkAv _ _ ps n ly a d u))
  (let-match erased ly (LayC _ _ _ _ _ ly1 nt))
  (let-match many n (Succ m))
  (let ((many y) (unique a2)) (array-get _ _ a m x nt))
  (let ((unique v2)) (u A xs ps m ly1 (at) a2 (at) d))
  (values y v2))

(def-fns _ $ (many av-set-top : (erased Type A) (erased A x) (erased (List A) xs) (unique (Av A (Cons A x xs)) v) (many A y) ->
    (unique (Av A (Cons A y xs)) v2 at v))
  (let-match unique v (MkAv _ _ ps n ly a d u))
  (let-match erased ly (LayC _ _ _ _ _ ly1 nt))
  (let-match many n (Succ m))
  (let ((erased qs) (erased ly2) (unique a2)) (av-place A xs ps m ly1 _ nt a y))
  (at unique (u A (Cons A y xs) qs n ly2 a2 d)))

(def-fns _ $ (many av-drop : (erased Type A) (erased (List A) p ys xs) (unique (Av A xs) v) (many (Nat) k)
    (erased (Cat A p ys xs) c) (erased (Length A p k) lk) -> (unique (Av A ys) v2 at v))
  (let-match unique v (MkAv _ _ ps n ly a d u))
  (let ((many m) (erased ad)) (sub n k (lay-drop-le A p ys xs ps n k c ly lk)))
  (u A ys ps m (lay-drop A p ys xs ps n k m c ly lk ad) (at) a (at) d))

; Lyb xs ps n: logical element i of xs (0 the top) is at physical index n-1-i of ps.
(def-adts
  ((Lyb : ((List (U8)) xs) ((List (U8)) ps) ((Nat) n) -> Type)
    enum
    (many LybN : (erased (List (U8)) ps) -> (Lyb (Nil (U8)) ps (Zero)))
    (many LybC : (erased (U8) x) (erased (List (U8)) xs) (erased (List (U8)) ps) (erased (Nat) n)
       (erased (Lyb xs ps n) ly) (erased (Nth (U8) ps n x) nt) -> (Lyb (Cons (U8) x xs) ps (Succ n)))))

(def-fns _ $ (erased lyb-length : (erased (List (U8)) xs) (erased (List (U8)) ps) (erased (Nat) n)
    (subterm erased (Lyb xs ps n) ly) -> (erased (Length (U8) xs n) l))
  (let-match erased ly (LybC x xs1 _ n1 ly1 _) ((LybN _) (LengthNil _)))
  (LengthCons _ x xs1 n1 (lyb-length xs1 ps n1 ly1)))

(def-fns _ $ (erased lyb-le : (erased (List (U8)) xs) (erased (List (U8)) ps) (erased (Nat) n len)
    (erased (Lyb xs ps n) ly) (erased (Length (U8) ps len) l) -> (erased (Lt n (Succ len)) le))
  (let-match erased ly (LybC _ _ _ n1 _ nt) ((LybN _) (LtZ len)))
  (LtS n1 len (nth-lt-length _ ps n1 len _ nt l)))

(def-fns _ $ (erased lyb-nth : (erased (List (U8)) xs) (erased (List (U8)) ps) (erased (Nat) n i j) (erased (U8) x)
    (subterm erased (Lyb xs ps n) ly) (erased (Nth (U8) xs i x) nt) (erased (Add (Succ i) j n) ad) -> (erased (Nth (U8) ps j x) r))
  (let-match erased ly (LybC _ xs1 _ n1 ly1 nt1) (absurd (LybN _) nt))
  (let-match erased ad (AddSucc _ _ _ ad1))
  (let-match erased nt (NthThere _ _ _ i1 _ nt2) ((NthHere _ _ _) (let-match erased ad1 (AddZero _)) nt1))
  (lyb-nth xs1 ps n1 i1 j x ly1 nt2 ad1))

(def-fns _ $ (erased lyb-agr : (erased (List (U8)) xs) (erased (List (U8)) ps qs) (erased (Nat) n q)
    (subterm erased (Lyb xs ps n) ly) (erased (Agr (U8) ps qs q) g) (erased (Lt n (Succ q)) le) -> (erased (Lyb xs qs n) r))
  (let-match erased ly (LybC x xs1 _ n1 ly1 nt) ((LybN _) (LybN qs)))
  (let-match erased le (LtS _ _ lt))
  (LybC x xs1 qs n1 (lyb-agr xs1 ps qs n1 q ly1 g (lt-weaken n1 q lt)) (agr-nth _ ps qs q n1 x g nt lt)))

(def-fns _ $ (erased lyb-drop-le : (erased (List (U8)) p ys xs) (erased (List (U8)) ps) (erased (Nat) n k)
    (subterm erased (Cat (U8) p ys xs) c) (erased (Lyb xs ps n) ly) (erased (Length (U8) p k) lk) -> (erased (Lt k (Succ n)) le))
  (let-match erased c (CatC _ _ p1 _ xs1 c1) ((CatN _ _) (let-match erased lk (LengthNil _)) (LtZ n)))
  (let-match erased lk (LengthCons _ _ _ k1 lk1))
  (let-match erased ly (LybC _ _ _ n1 ly1 _))
  (LtS k1 n (lyb-drop-le p1 ys xs1 ps n1 k1 c1 ly1 lk1)))

(def-fns _ $ (erased lyb-drop : (erased (List (U8)) p ys xs) (erased (List (U8)) ps) (erased (Nat) n k m)
    (subterm erased (Cat (U8) p ys xs) c) (erased (Lyb xs ps n) ly) (erased (Length (U8) p k) lk) (erased (Add k m n) ad) -> (erased (Lyb ys ps m) r))
  (let-match erased c (CatC _ _ p1 _ xs1 c1) ((CatN _ _) (let-match erased lk (LengthNil _)) (let-match erased ad (AddZero _)) ly))
  (let-match erased lk (LengthCons _ _ _ k1 lk1))
  (let-match erased ly (LybC _ _ _ n1 ly1 _))
  (let-match erased ad (AddSucc _ _ _ ad1))
  (lyb-drop p1 ys xs1 ps n1 k1 m c1 ly1 lk1 ad1))

(def-adts $ (Bv : ((List (U8)) xs) -> Type)
  enum
  (many MkBv : (erased (List (U8)) xs) (erased (List (U8)) ps) (many (Nat) n) (erased (Lyb xs ps n) ly)
     (unique (Bytes ps) a) (many (U8) d) -> (Bv xs)))

(def-fns _ $ (many bv-new : (many (U8) x0) (many (Nat) cap) -> (unique (Bv (Nil (U8))) v))
  (let ((erased ps) (unique a) (erased _)) (bytes-make cap x0))
  (MkBv (Nil (U8)) ps (Zero) (LybN ps) a x0))

(def-fns _ $ (many bv-len : (erased (List (U8)) xs) (unique (Bv xs) v) ->
    (many (Nat) n) (erased (Length (U8) xs n) p) (unique v is v2 at v))
  (let-match unique v (MkBv _ ps n ly a d u))
  (values n (lyb-length xs ps n ly) (at unique (u xs ps n ly a d))))

(def-fns _ $ (many bv-get : (erased (List (U8)) xs) (unique (Bv xs) v) (many (Nat) i) (erased (U8) x) (erased (Nth (U8) xs i x) nt) ->
    (many x is y) (unique v is v2 at v))
  (let-match unique v (MkBv _ ps n ly a d u))
  (let ((many j) (erased ad)) (sub n (Succ i) (LtS i n (nth-lt-length _ xs i n x nt (lyb-length xs ps n ly)))))
  (let ((many y) (unique a2)) (bytes-get _ a j x (lyb-nth xs ps n i j x ly nt ad)))
  (values y (at unique (u xs ps n ly a2 d))))

(def-fns _ $ (many bv-place : (erased (List (U8)) xs) (erased (List (U8)) ps) (many (Nat) n) (erased (Lyb xs ps n) ly)
    (erased (U8) w) (erased (Nth (U8) ps n w) nt) (unique (Bytes ps) a) (many (U8) x) ->
    (erased (List (U8)) qs) (erased (Lyb (Cons (U8) x xs) qs (Succ n)) ly2) (unique (Bytes qs) a2 at a))
  (let ((erased qs) (unique a2) (erased st)) (bytes-set _ a n x w nt))
  (values qs (LybC x xs qs n (lyb-agr xs ps qs n n ly (setnth-agr _ ps qs n n _ st (lt-succ n)) (lt-succ n)) (setnth-nth _ ps n _ qs st)) a2))

(def-fns _ $ (many bv-push : (erased (List (U8)) xs) (unique (Bv xs) v) (many (U8) x) -> (unique (Bv (Cons (U8) x xs)) v2 at v))
  (let-match unique v (MkBv _ ps n ly a d u))
  (let ((many len) (erased lc) (unique a1)) (bytes-length _ a))
  (let-match many (lt-dec n len) (Yes _ _ _ _ lt)
    ((No _ _ _ _ _)
      (let ((many c) (erased ad)) (add n n))
      (let ((erased qs) (unique b) (erased rp)) (bytes-make (Succ c) d))
      (let ((erased le)) (add-le-left n n c ad))
      (let ((erased ys) (erased fr)) (splice-range _ ps len lc (Zero) n n (AddZero n) (lyb-le xs ps n len ly lc)))
      (let ((erased old) (erased to)) (splice-range _ qs (Succ c) (repeat-length _ _ _ _ rp) (Zero) n n (AddZero n) (lt-weaken n (Succ c) le)))
      (let ((erased zs) (unique b2) (erased sp)) (bytes-blit _ (share a1) (Zero) _ b (Zero) n ys fr old to))
      (let ((erased w) (erased nt)) (nth-exists _ zs (Succ c) n (splice-length _ qs ys zs (Zero) n (Succ c) sp (repeat-length _ _ _ _ rp)) le))
      (let ((erased zs2) (erased ly2) (unique b3))
        (bv-place xs zs n (lyb-agr xs ps zs n n ly (splice-agr _ ps qs ys zs n fr sp) (lt-succ n)) w nt b2 x))
      (u (Cons (U8) x xs) zs2 (Succ n) ly2 b3 (at) d)))
  (let ((erased w) (erased nt)) (nth-exists _ ps len n lc lt))
  (let ((erased ps2) (erased ly2) (unique a2)) (bv-place xs ps n ly w nt a1 x))
  (u (Cons (U8) x xs) ps2 (Succ n) ly2 (at) a2 (at) d))

(def-fns _ $ (many bv-pop : (erased (U8) x) (erased (List (U8)) xs) (unique (Bv (Cons (U8) x xs)) v) ->
    (many x is y) (unique (Bv xs) v2 at v))
  (let-match unique v (MkBv _ ps n ly a d u))
  (let-match erased ly (LybC _ _ _ _ ly1 nt))
  (let-match many n (Succ m))
  (let ((many y) (unique a2)) (bytes-get _ a m x nt))
  (let ((unique v2)) (u xs ps m ly1 (at) a2 (at) d))
  (values y v2))

(def-fns _ $ (many bv-set-top : (erased (U8) x) (erased (List (U8)) xs) (unique (Bv (Cons (U8) x xs)) v) (many (U8) y) ->
    (unique (Bv (Cons (U8) y xs)) v2 at v))
  (let-match unique v (MkBv _ ps n ly a d u))
  (let-match erased ly (LybC _ _ _ _ ly1 nt))
  (let-match many n (Succ m))
  (let ((erased qs) (erased ly2) (unique a2)) (bv-place xs ps m ly1 _ nt a y))
  (at unique (u (Cons (U8) y xs) qs n ly2 a2 d)))

(def-fns _ $ (many bv-drop : (erased (List (U8)) p ys xs) (unique (Bv xs) v) (many (Nat) k)
    (erased (Cat (U8) p ys xs) c) (erased (Length (U8) p k) lk) -> (unique (Bv ys) v2 at v))
  (let-match unique v (MkBv _ ps n ly a d u))
  (let ((many m) (erased ad)) (sub n k (lyb-drop-le p ys xs ps n k c ly lk)))
  (u ys ps m (lyb-drop p ys xs ps n k m c ly lk ad) (at) a (at) d))
