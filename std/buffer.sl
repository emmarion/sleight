(def-adts $ (Concat : (Type A) ((List A) xs) ((List A) ys) ((List A) zs) -> Type)
  enum
  (many ConcatNil : (erased Type A) (erased (List A) ys) -> (Concat A (Nil A) ys ys))
  (many ConcatCons : (erased Type A) (erased A x) (erased (List A) xs ys zs) (erased (Concat A xs ys zs) p)
     -> (Concat A (Cons A x xs) ys (Cons A x zs))))

(def-fns _ $ (erased concat-exists : (erased Type A) (subterm erased (List A) xs) (erased (List A) ys) ->
    (erased (List A) zs) (erased (Concat A xs ys zs) p))
  (let-match erased xs (Cons _ x rest) ((Nil _) (values ys (ConcatNil _ ys))))
  (let ((erased zs1) (erased p1)) (concat-exists _ rest ys))
  (values (Cons _ x zs1) (ConcatCons _ x rest ys zs1 p1)))

(def-fns _ $ (erased concat-fn : (erased Type A) (erased (List A) xs ys zs ws)
    (subterm erased (Concat A xs ys zs) p) (erased (Concat A xs ys ws) q) -> (erased (Eq (List A) zs ws) e))
  (let-match erased p (ConcatCons _ _ rest _ zs1 p1) ((ConcatNil _ _) (let-match erased q (ConcatNil _ _)) (Refl _ zs)))
  (let-match erased q (ConcatCons _ _ _ _ ws1 q1))
  (let-match erased (concat-fn _ rest ys zs1 ws1 p1 q1) (Refl _ _))
  (Refl _ zs))

(def-fns _ $ (erased concat-nil-right : (erased Type A) (subterm erased (List A) xs) -> (erased (Concat A xs (Nil A) xs) p))
  (let-match erased xs (Cons _ x rest) ((Nil _) (ConcatNil _ (Nil _))))
  (ConcatCons _ x rest (Nil _) rest (concat-nil-right _ rest)))

(def-fns _ $ (erased concat-assoc : (erased Type A) (erased (List A) a b c ab bc)
    (subterm erased (Concat A a b ab) p) (erased (Concat A b c bc) q) ->
    (erased (List A) abc) (erased (Concat A ab c abc) r) (erased (Concat A a bc abc) s))
  (let-match erased p (ConcatCons _ x a1 _ ab1 p1) ((ConcatNil _ _) (values bc q (ConcatNil _ bc))))
  (let ((erased abc1) (erased r1) (erased s1)) (concat-assoc _ a1 b c ab1 bc p1 q))
  (values (Cons _ x abc1) (ConcatCons _ x ab1 c abc1 r1) (ConcatCons _ x a1 bc abc1 s1)))

(def-fns _ $ (erased concat-length : (erased Type A) (erased (List A) xs ys zs) (erased (Nat) a b c)
    (subterm erased (Concat A xs ys zs) p) (erased (Length A xs a) la) (erased (Length A ys b) lb) (erased (Add a b c) ad) ->
    (erased (Length A zs c) l))
  (let-match erased p (ConcatCons _ x xs1 _ zs1 p1)
    ((ConcatNil _ _) (let-match erased la (LengthNil _)) (let-match erased ad (AddZero _)) lb))
  (let-match erased la (LengthCons _ _ _ a1 la1))
  (let-match erased ad (AddSucc _ _ c1 ad1))
  (LengthCons _ x zs1 c1 (concat-length _ xs1 ys zs1 a1 b c1 p1 la1 lb ad1)))

(def-fns _ $ (erased concat-nth-left : (erased Type A) (erased (List A) xs ys zs) (erased (Nat) i) (erased A e)
    (subterm erased (Concat A xs ys zs) p) (erased (Nth A xs i e) q) -> (erased (Nth A zs i e) r))
  (let-match erased p (ConcatCons _ x xs1 _ zs1 p1) (absurd (ConcatNil _ _) q))
  (let-match erased q (NthThere _ _ _ i1 _ q1) ((NthHere _ _ _) (NthHere _ x zs1)))
  (NthThere _ x zs1 i1 e (concat-nth-left _ xs1 ys zs1 i1 e p1 q1)))

(def-fns _ $ (erased concat-nth-right : (erased Type A) (erased (List A) xs ys zs) (erased (Nat) l j k) (erased A e)
    (subterm erased (Concat A xs ys zs) p) (erased (Length A xs l) lx) (erased (Nth A ys j e) q) (erased (Add l j k) ad) ->
    (erased (Nth A zs k e) r))
  (let-match erased p (ConcatCons _ x xs1 _ zs1 p1)
    ((ConcatNil _ _) (let-match erased lx (LengthNil _)) (let-match erased ad (AddZero _)) q))
  (let-match erased lx (LengthCons _ _ _ l1 lx1))
  (let-match erased ad (AddSucc _ _ k1 ad1))
  (NthThere _ x zs1 k1 e (concat-nth-right _ xs1 ys zs1 l1 j k1 e p1 lx1 q ad1)))

(def-fns _ $ (erased concat-nth-left-inv : (erased Type A) (erased (List A) xs ys zs) (erased (Nat) l i) (erased A e)
    (subterm erased (Concat A xs ys zs) p) (erased (Length A xs l) lx) (erased (Lt i l) lt) (erased (Nth A zs i e) q) ->
    (erased (Nth A xs i e) r))
  (let-match erased p (ConcatCons _ x xs1 _ zs1 p1)
    (absurd (ConcatNil _ _) (let-match erased lx (LengthNil _)) lt))
  (let-match erased q (NthThere _ _ _ i1 _ q1) ((NthHere _ _ _) (NthHere _ x xs1)))
  (let-match erased lx (LengthCons _ _ _ l1 lx1))
  (let-match erased lt (LtS _ _ lt1))
  (NthThere _ x xs1 i1 e (concat-nth-left-inv _ xs1 ys zs1 l1 i1 e p1 lx1 lt1 q1)))

(def-fns _ $ (erased concat-nth-right-inv : (erased Type A) (erased (List A) xs ys zs) (erased (Nat) l j k) (erased A e)
    (subterm erased (Concat A xs ys zs) p) (erased (Length A xs l) lx) (erased (Add l j k) ad) (erased (Nth A zs k e) q) ->
    (erased (Nth A ys j e) r))
  (let-match erased p (ConcatCons _ _ xs1 _ zs1 p1)
    ((ConcatNil _ _) (let-match erased lx (LengthNil _)) (let-match erased ad (AddZero _)) q))
  (let-match erased lx (LengthCons _ _ _ l1 lx1))
  (let-match erased ad (AddSucc _ _ k1 ad1))
  (let-match erased q (NthThere _ _ _ _ _ q1))
  (concat-nth-right-inv _ xs1 ys zs1 l1 j k1 e p1 lx1 ad1 q1))

(def-fns _ $ (erased concat-set-left : (erased Type A) (erased (List A) xs ys zs xs2) (erased (Nat) i) (erased A y)
    (subterm erased (Concat A xs ys zs) p) (erased (SetNth A xs i y xs2) s) ->
    (erased (List A) zs2) (erased (SetNth A zs i y zs2) t) (erased (Concat A xs2 ys zs2) c))
  (let-match erased p (ConcatCons _ x xs1 _ zs1 p1) (absurd (ConcatNil _ _) s))
  (let-match erased s (SetThere _ _ _ i1 _ xs21 s1)
    ((SetHere _ _ _ _) (values (Cons _ y zs1) (SetHere _ x y zs1) (ConcatCons _ y xs1 ys zs1 p1))))
  (let ((erased zs21) (erased t1) (erased c1)) (concat-set-left _ xs1 ys zs1 xs21 i1 y p1 s1))
  (values (Cons _ x zs21) (SetThere _ x zs1 i1 y zs21 t1) (ConcatCons _ x xs21 ys zs21 c1)))

(def-fns _ $ (erased concat-set-right : (erased Type A) (erased (List A) xs ys zs ys2) (erased (Nat) l j k) (erased A y)
    (subterm erased (Concat A xs ys zs) p) (erased (Length A xs l) lx) (erased (SetNth A ys j y ys2) s) (erased (Add l j k) ad) ->
    (erased (List A) zs2) (erased (SetNth A zs k y zs2) t) (erased (Concat A xs ys2 zs2) c))
  (let-match erased p (ConcatCons _ x xs1 _ zs1 p1)
    ((ConcatNil _ _) (let-match erased lx (LengthNil _)) (let-match erased ad (AddZero _)) (values ys2 s (ConcatNil _ ys2))))
  (let-match erased lx (LengthCons _ _ _ l1 lx1))
  (let-match erased ad (AddSucc _ _ k1 ad1))
  (let ((erased zs21) (erased t1) (erased c1)) (concat-set-right _ xs1 ys zs1 ys2 l1 j k1 y p1 lx1 s ad1))
  (values (Cons _ x zs21) (SetThere _ x zs1 k1 y zs21 t1) (ConcatCons _ x xs1 ys2 zs21 c1)))

(def-fns _ $ (erased nth-setnth : (erased Type A) (erased (List A) xs) (erased (Nat) i) (erased A m y)
    (subterm erased (Nth A xs i m) q) -> (erased (List A) ys) (erased (SetNth A xs i y ys) s))
  (let-match erased q (NthThere _ a rest i1 _ q1) ((NthHere _ _ rest) (values (Cons _ y rest) (SetHere _ m y rest))))
  (let ((erased ys1) (erased s1)) (nth-setnth _ rest i1 m y q1))
  (values (Cons _ a ys1) (SetThere _ a rest i1 y ys1 s1)))

(def-fns _ $ (erased splice-self : (erased Type A) (erased (List A) xs ys zs) (erased (Nat) i n)
    (subterm erased (Splice A xs i n ys zs) p) -> (erased (Splice A zs i n ys zs) q))
  (match erased p _
    ((SpliceNil _ _) (SpliceNil _ zs))
    ((SpliceHere _ _ y xs1 n1 ys1 zs1 p1) (SpliceHere _ y y zs1 n1 ys1 zs1 (splice-self _ xs1 ys1 zs1 (Zero) n1 p1)))
    ((SpliceThere _ x xs1 i1 _ _ zs1 p1) (SpliceThere _ x zs1 i1 n ys zs1 (splice-self _ xs1 ys zs1 i1 n p1)))))

(def-fns _ $ (erased splice-length : (erased Type A) (erased (List A) xs ys zs) (erased (Nat) i n l)
    (subterm erased (Splice A xs i n ys zs) p) (erased (Length A xs l) lx) -> (erased (Length A zs l) lz))
  (match erased p _
    ((SpliceNil _ _) lx)
    ((SpliceHere _ _ y xs1 n1 ys1 zs1 p1)
      (let-match erased lx (LengthCons _ _ _ l1 lx1))
      (LengthCons _ y zs1 l1 (splice-length _ xs1 ys1 zs1 (Zero) n1 l1 p1 lx1)))
    ((SpliceThere _ x xs1 i1 _ _ zs1 p1)
      (let-match erased lx (LengthCons _ _ _ l1 lx1))
      (LengthCons _ x zs1 l1 (splice-length _ xs1 ys zs1 i1 n l1 p1 lx1)))))

(def-fns _ $ (erased splice-count : (erased Type A) (erased (List A) xs ys zs) (erased (Nat) i n)
    (subterm erased (Splice A xs i n ys zs) p) -> (erased (Length A ys n) l))
  (match erased p _
    ((SpliceNil _ _) (LengthNil _))
    ((SpliceHere _ _ y xs1 n1 ys1 zs1 p1) (LengthCons _ y ys1 n1 (splice-count _ xs1 ys1 zs1 (Zero) n1 p1)))
    ((SpliceThere _ _ xs1 i1 _ _ zs1 p1) (splice-count _ xs1 ys zs1 i1 n p1))))

(def-fns _ $ (erased splice-whole : (erased Type A) (erased (List A) xs) (erased (Nat) n)
    (subterm erased (Length A xs n) l) -> (erased (Splice A xs (Zero) n xs xs) p))
  (let-match erased l (LengthCons _ x rest k l1) ((LengthNil _) (SpliceNil _ (Nil _))))
  (SpliceHere _ x x rest k rest rest (splice-whole _ rest k l1)))

(def-fns _ $ (erased concat-splice-left : (erased Type A) (erased (List A) pre post bs) (erased (Nat) h)
    (subterm erased (Concat A pre post bs) p) (erased (Length A pre h) lp) -> (erased (Splice A bs (Zero) h pre bs) s))
  (let-match erased p (ConcatCons _ x pre1 _ bs1 p1) ((ConcatNil _ _) (let-match erased lp (LengthNil _)) (SpliceNil _ bs)))
  (let-match erased lp (LengthCons _ _ _ h1 lp1))
  (SpliceHere _ x x bs1 h1 pre1 bs1 (concat-splice-left _ pre1 post bs1 h1 p1 lp1)))

(def-fns _ $ (erased concat-splice-right : (erased Type A) (erased (List A) pre post bs) (erased (Nat) h r)
    (subterm erased (Concat A pre post bs) p) (erased (Length A pre h) lp) (erased (Length A post r) lq) ->
    (erased (Splice A bs h r post bs) s))
  (let-match erased p (ConcatCons _ x pre1 _ bs1 p1)
    ((ConcatNil _ _) (let-match erased lp (LengthNil _)) (splice-whole _ post r lq)))
  (let-match erased lp (LengthCons _ _ _ h1 lp1))
  (SpliceThere _ x bs1 h1 r post bs1 (concat-splice-right _ pre1 post bs1 h1 r p1 lp1 lq)))

(def-fns _ $ (erased prefix-nth : (erased Type A) (erased (List A) bs xs) (erased (Nat) n i) (erased A e)
    (subterm erased (Splice A bs (Zero) n xs bs) p) (erased (Nth A xs i e) q) -> (erased (Nth A bs i e) r))
  (let-match erased p (SpliceHere _ x _ bs1 n1 xs1 _ p1) (absurd (SpliceNil _ _) q))
  (let-match erased q (NthThere _ _ _ i1 _ q1) ((NthHere _ _ _) (NthHere _ x bs1)))
  (NthThere _ x bs1 i1 e (prefix-nth _ bs1 xs1 n1 i1 e p1 q1)))

(def-fns _ $ (erased prefix-setnth : (erased Type A) (erased (List A) bs xs bs2) (erased (Nat) n i) (erased A m y)
    (subterm erased (Splice A bs (Zero) n xs bs) p) (erased (Nth A xs i m) q) (erased (SetNth A bs i y bs2) s) ->
    (erased (List A) xs2) (erased (SetNth A xs i y xs2) t) (erased (Splice A bs2 (Zero) n xs2 bs2) u))
  (let-match erased p (SpliceHere _ x _ bs1 n1 xs1 _ p1) (absurd (SpliceNil _ _) q))
  (let-match erased s (SetThere _ _ _ i1 _ bs21 s1)
    ((SetHere _ _ _ _) (values (Cons _ y xs1) (SetHere _ x y xs1) (SpliceHere _ y y bs1 n1 xs1 bs1 p1))))
  (let-match erased q (NthThere _ _ _ _ _ q1))
  (let ((erased xs21) (erased t1) (erased u1)) (prefix-setnth _ bs1 xs1 bs21 n1 i1 m y p1 q1 s1))
  (values (Cons _ x xs21) (SetThere _ x xs1 i1 y xs21 t1) (SpliceHere _ x x bs21 n1 xs21 bs21 u1)))

(def-fns _ $ (erased prefix-push : (erased Type A) (erased (List A) bs xs bs2) (erased (Nat) n) (erased A y)
    (subterm erased (Splice A bs (Zero) n xs bs) p) (erased (SetNth A bs n y bs2) s) ->
    (erased (List A) xs2) (erased (Concat A xs (Cons A y (Nil A)) xs2) c) (erased (Splice A bs2 (Zero) (Succ n) xs2 bs2) u))
  (match erased p _
    ((SpliceNil _ _)
      (let-match erased s (SetHere _ _ _ rest))
      (values (Cons _ y (Nil _)) (ConcatNil _ _) (SpliceHere _ y y rest (Zero) (Nil _) rest (SpliceNil _ rest))))
    ((SpliceHere _ x _ bs1 n1 xs1 _ p1)
      (let-match erased s (SetThere _ _ _ _ _ bs21 s1))
      (let ((erased xs21) (erased c1) (erased u1)) (prefix-push _ bs1 xs1 bs21 n1 y p1 s1))
      (values (Cons _ x xs21) (ConcatCons _ x xs1 _ xs21 c1) (SpliceHere _ x x bs21 (Succ n1) xs21 bs21 u1)))))

(def-fns _ $ (erased prefix-pop : (erased Type A) (erased (List A) bs xs) (erased (Nat) m)
    (subterm erased (Splice A bs (Zero) (Succ m) xs bs) p) ->
    (erased (List A) ys) (erased A e) (erased (Concat A ys (Cons A e (Nil A)) xs) c) (erased (Nth A bs m e) q)
    (erased (Splice A bs (Zero) m ys bs) u))
  (let-match erased p (SpliceHere _ x _ bs1 _ xs1 _ p1))
  (let-match erased p1 (SpliceHere _ _ _ _ m1 _ _ _)
    ((SpliceNil _ _) (values (Nil _) x (ConcatNil _ _) (NthHere _ x bs1) (SpliceNil _ bs))))
  (let ((erased ys1) (erased e) (erased c1) (erased q1) (erased u1)) (prefix-pop _ bs1 xs1 m1 p1))
  (values (Cons _ x ys1) e (ConcatCons _ x ys1 _ xs1 c1) (NthThere _ x bs1 m1 e q1) (SpliceHere _ x x bs1 m1 ys1 bs1 u1)))

(def-fns _ $ (erased prefix-trans : (erased Type A) (erased (List A) z cs xs) (erased (Nat) c n)
    (subterm erased (Splice A cs (Zero) n xs cs) q) (erased (Splice A z (Zero) c cs z) p) -> (erased (Splice A z (Zero) n xs z) r))
  (let-match erased q (SpliceHere _ x _ cs1 n1 xs1 _ q1) ((SpliceNil _ _) (SpliceNil _ z)))
  (let-match erased p (SpliceHere _ _ _ z1 c1 _ _ p1))
  (SpliceHere _ x x z1 n1 xs1 z1 (prefix-trans _ z1 cs1 xs1 c1 n1 q1 p1)))

(def-fns _ $ (erased prefix-le : (erased Type A) (erased (List A) ys zs) (erased (Nat) n c)
    (subterm erased (Splice A ys (Zero) n zs ys) p) (erased (Length A ys c) l) -> (erased (Lt n (Succ c)) lt))
  (let-match erased p (SpliceHere _ _ _ ys1 n1 zs1 _ p1) ((SpliceNil _ _) (LtZ c)))
  (let-match erased l (LengthCons _ _ _ c1 l1))
  (LtS n1 (Succ c1) (prefix-le _ ys1 zs1 n1 c1 p1 l1)))

(def-fns _ $ (erased prefix-cat : (erased Type A) (erased (List A) y z ys1 ys2 cs) (erased (Nat) a b c)
    (subterm erased (Splice A y (Zero) a ys1 y) p) (erased (Splice A y a b ys2 z) q) (erased (Concat A ys1 ys2 cs) k)
    (erased (Add a b c) ad) -> (erased (Splice A z (Zero) c cs z) r))
  (match erased p _
    ((SpliceNil _ _)
      (let-match erased k (ConcatNil _ _))
      (let-match erased ad (AddZero _))
      (splice-self _ y ys2 z (Zero) b q))
    ((SpliceHere _ x _ y1 a1 ys11 _ p1)
      (let-match erased q (SpliceThere _ _ _ _ _ _ z1 q1))
      (let-match erased k (ConcatCons _ _ _ _ cs1 k1))
      (let-match erased ad (AddSucc _ _ c1 ad1))
      (SpliceHere _ x x z1 c1 cs1 z1 (prefix-cat _ y1 z1 ys11 ys2 cs1 a1 b c1 p1 q1 k1 ad1)))))

(def-fns _ $ (erased prefix-extend : (erased Type A) (erased (List A) bs ws bs2 xs) (erased (Nat) n)
    (subterm erased (Splice A bs (Zero) n xs bs) p) (erased (Concat A bs ws bs2) c) -> (erased (Splice A bs2 (Zero) n xs bs2) q))
  (let-match erased p (SpliceHere _ x _ bs1 n1 xs1 _ p1) ((SpliceNil _ _) (SpliceNil _ bs2)))
  (let-match erased c (ConcatCons _ _ _ _ bs21 c1))
  (SpliceHere _ x x bs21 n1 xs1 bs21 (prefix-extend _ bs1 ws bs21 xs1 n1 p1 c1)))

(def-adts $ (Rot : (Type A) ((List A) bs) ((Nat) h) ((Nat) r) ((List A) cs) -> Type)
  enum
  (many MkRot : (erased Type A) (erased (List A) pre post bs cs) (erased (Nat) h r)
     (erased (Concat A pre post bs) pb) (erased (Length A pre h) lh) (erased (Length A post r) lr) (erased (Concat A post pre cs) pc)
     -> (Rot A bs h r cs)))

(def-adts $ (Phys : ((Nat) h) ((Nat) r) ((Nat) i) ((Nat) p) -> Type)
  enum
  (many PhysPost : (erased (Nat) h r i p) (erased (Lt i r) lt) (erased (Add h i p) a) -> (Phys h r i p))
  (many PhysPre : (erased (Nat) h r i p) (erased (Add r p i) a) -> (Phys h r i p)))

(def-adts $ (Front : (Type A) ((List A) xs) ((List A) ys) -> Type)
  enum
  (many FrontNone : (erased Type A) -> (Front A (Nil A) (Nil A)))
  (many FrontSome : (erased Type A) (many A x) (erased (List A) ys) -> (Front A (Cons A x ys) ys)))

(def-adts $ (Back : (Type A) ((List A) xs) ((List A) ys) -> Type)
  enum
  (many BackNone : (erased Type A) -> (Back A (Nil A) (Nil A)))
  (many BackSome : (erased Type A) (erased (List A) xs ys) (many A x) (erased (Concat A ys (Cons A x (Nil A)) xs) c) -> (Back A xs ys)))

(def-fns _ $ (many phys : (many (Nat) h r i) -> (many (Nat) p) (erased (Phys h r i p) w))
  (match many (lt-dec i r) _
    ((Yes _ _ _ _ lt) (let ((many p) (erased a)) (add h i)) (values p (PhysPost h r i p lt a)))
    ((No _ _ _ _ ge) (let ((many p) (erased a)) (sub i r (le-lt-succ r i ge))) (values p (PhysPre h r i p a)))))

(def-fns _ $ (erased rot-fresh : (erased Type A) (erased (List A) bs) (erased (Nat) c) (erased (Length A bs c) l) ->
    (erased (Rot A bs (Zero) c bs) rot))
  (MkRot _ (Nil _) bs bs bs (Zero) c (ConcatNil _ bs) (LengthNil _) l (concat-nil-right _ bs)))

(def-fns _ $ (erased rot-length : (erased Type A) (erased (List A) bs cs) (erased (Nat) h r c)
    (erased (Rot A bs h r cs) rot) (erased (Add r h c) ad) -> (erased (Length A cs c) l))
  (let-match erased rot (MkRot _ pre post _ _ _ _ _ lh lr pc))
  (concat-length _ post pre cs r h c pc lr lh ad))

(def-fns _ $ (erased rot-segments : (erased Type A) (erased (List A) bs cs) (erased (Nat) h r) (erased (Rot A bs h r cs) rot) ->
    (erased (List A) post pre) (erased (Splice A bs h r post bs) sr) (erased (Splice A bs (Zero) h pre bs) sl)
    (erased (Concat A post pre cs) pc))
  (let-match erased rot (MkRot _ pre1 post1 _ _ _ _ pb lh lr pc1))
  (values post1 pre1 (concat-splice-right _ pre1 post1 bs h r pb lh lr) (concat-splice-left _ pre1 post1 bs h pb lh) pc1))

(def-fns _ $ (erased rot-nth : (erased Type A) (erased (List A) bs cs) (erased (Nat) h r i p) (erased A e)
    (erased (Rot A bs h r cs) rot) (erased (Phys h r i p) w) (erased (Nth A cs i e) q) -> (erased (Nth A bs p e) s))
  (let-match erased rot (MkRot _ pre post _ _ _ _ pb lh lr pc))
  (match erased w _
    ((PhysPost _ _ _ _ lt a) (concat-nth-right _ pre post bs h i p e pb lh (concat-nth-left-inv _ post pre cs r i e pc lr lt q) a))
    ((PhysPre _ _ _ _ a) (concat-nth-left _ pre post bs p e pb (concat-nth-right-inv _ post pre cs r p i e pc lr a q)))))

(def-fns _ $ (erased rot-set : (erased Type A) (erased (List A) bs cs) (erased (Nat) h r i p) (erased A m y)
    (erased (Rot A bs h r cs) rot) (erased (Phys h r i p) w) (erased (Nth A cs i m) q) ->
    (erased (List A) bs2 cs2) (erased (SetNth A bs p y bs2) sb) (erased (SetNth A cs i y cs2) sc) (erased (Rot A bs2 h r cs2) rot2))
  (let-match erased rot (MkRot _ pre post _ _ _ _ pb lh lr pc))
  (match erased w _
    ((PhysPost _ _ _ _ lt a)
      (let ((erased post2) (erased s)) (nth-setnth _ post i m y (concat-nth-left-inv _ post pre cs r i m pc lr lt q)))
      (let ((erased cs3) (erased sc3) (erased pc2)) (concat-set-left _ post pre cs post2 i y pc s))
      (let ((erased bs3) (erased sb3) (erased pb2)) (concat-set-right _ pre post bs post2 h i p y pb lh s a))
      (values bs3 cs3 sb3 sc3 (MkRot _ pre post2 bs3 cs3 h r pb2 lh (setnth-length _ post i r y post2 s lr) pc2)))
    ((PhysPre _ _ _ _ a)
      (let ((erased pre2) (erased s)) (nth-setnth _ pre p m y (concat-nth-right-inv _ post pre cs r p i m pc lr a q)))
      (let ((erased bs3) (erased sb3) (erased pb2)) (concat-set-left _ pre post bs pre2 p y pb s))
      (let ((erased cs3) (erased sc3) (erased pc2)) (concat-set-right _ post pre cs pre2 r p i y pc lr s a))
      (values bs3 cs3 sb3 sc3 (MkRot _ pre2 post bs3 cs3 h r pb2 (setnth-length _ pre p h y pre2 s lh) lr pc2)))))

(def-fns _ $ (erased rot-pop : (erased Type A) (erased (List A) bs cs1) (erased (Nat) h r1) (erased A x)
    (erased (Rot A bs h (Succ r1) (Cons A x cs1)) rot) ->
    (erased (List A) cs2) (erased (Concat A cs1 (Cons A x (Nil A)) cs2) c) (erased (Rot A bs (Succ h) r1 cs2) rot2)
    (erased (Nth A bs h x) q))
  (let-match erased rot (MkRot _ pre post _ _ _ _ pb lh lr pc))
  (let-match erased lr (LengthCons _ _ post1 _ lr1))
  (let-match erased pc (ConcatCons _ _ _ _ _ pc1))
  (let ((erased one)) (Cons _ x (Nil _)))
  (let ((erased pre2) (erased k)) (concat-exists _ pre one))
  (let ((erased bs2) (erased k1) (erased k2)) (concat-assoc _ pre one post1 pre2 post k (ConcatCons _ x (Nil _) post1 post1 (ConcatNil _ post1))))
  (let-match erased (concat-fn _ pre post bs2 bs k2 pb) (Refl _ _))
  (let ((erased cs2) (erased k3) (erased k4)) (concat-assoc _ post1 pre one cs1 pre2 pc1 k))
  (let ((erased lh2)) (concat-length _ pre one pre2 h (Succ (Zero)) (Succ h) k lh (LengthCons _ x (Nil _) (Zero) (LengthNil _))
                        (add-succ-right h (Zero) h (add-zero-right h))))
  (values cs2 k3 (MkRot _ pre2 post1 bs cs2 (Succ h) r1 k1 lh2 lr1 k4)
    (concat-nth-right _ pre post bs h (Zero) h x pb lh (NthHere _ x post1) (add-zero-right h))))

(def-fns _ $ (many rot-norm : (erased Type A) (erased (List A) bs cs1) (erased A x) (many (Nat) h r c)
    (erased (Rot A bs h r (Cons A x cs1)) rot) (erased (Length A bs c) l) ->
    (many (Nat) h2 r1) (erased (Rot A bs h2 (Succ r1) (Cons A x cs1)) rot2))
  (let-match many r (Succ r1)
    ((Zero)
      (let-match erased rot (MkRot _ pre _ _ _ _ _ pb _ lr pc))
      (let-match erased lr (LengthNil _))
      (let-match erased pc (ConcatNil _ _))
      (let-match erased (concat-fn _ pre (Nil _) bs pre pb (concat-nil-right _ pre)) (Refl _ _))
      (let-match many c (Succ c1) (absurd (Zero) l))
      (values (Zero) c1 (rot-fresh _ bs c l))))
  (values h r1 rot))

(def-fns _ $ (many copy-array-empty : (erased Type A) -> (unique (Array (Copy A) (Nil (Copy A))) a))
  (list-to-array _ (Nil _)))

(def-fns _ $ (many copy-array-make : (erased Type A) (many (Nat) n) (many (Copy A) x) ->
    (erased (List (Copy A)) xs) (unique (Array (Copy A) xs) a) (erased (Repeat (Copy A) n x xs) p))
  (let-match many x (MkCopy _ v))
  (array-make _ n v))

(def-fns _ $ (many copy-array-get : (erased Type A) (erased (List (Copy A)) xs) (unique (Array (Copy A) xs) a) (many (Nat) i)
    (erased (Copy A) e) (erased (Nth (Copy A) xs i e) nth) -> (many e is v) (unique a is r at a))
  (let-match erased e (MkCopy _ x))
  (let ((many v) (unique r)) (array-get _ _ a i x nth))
  (values (MkCopy _ v) r))

(def-fns _ $ (many copy-array-set : (erased Type A) (erased (List (Copy A)) xs) (unique (Array (Copy A) xs) a) (many (Nat) i)
    (many (Copy A) x) (erased (Copy A) m) (erased (Nth (Copy A) xs i m) nth) ->
    (erased (List (Copy A)) ys) (unique (Array (Copy A) ys) r at a) (erased (SetNth (Copy A) xs i x ys) p))
  (let-match many x (MkCopy _ v))
  (array-place _ _ a i (MkCopy _ v) m nth))

(def-fns _ $ (many bytes-empty : -> (unique (Bytes (Nil (U8))) b))
  (let-match many #\x00 (MkChar z))
  (let ((erased _) (unique b) (erased p)) (bytes-make (Zero) z))
  (let-match erased p (RepeatNil _ _))
  b)

(def-fns _ $ (many subst-sym : (subterm many (List $ Raw) env) (many (Raw) t) -> (many (List $ Raw) out))
  (let-match many env (Cons _ e rest) ((Nil _) (Cons _ t $ Nil _)))
  (let-match many e (RawList _ kv) (else (tail $ subst-sym rest t)))
  (let-match many kv (Cons _ k v) ((Nil _) (tail $ subst-sym rest t)))
  (match many (same-sym k t) _ ((BTrue) v) ((BFalse) (tail $ subst-sym rest t))))

(def-fns _
  ((many subst-raw : (many (List $ Raw) env) (subterm many (Raw) t) -> (many (List $ Raw) out))
    (match many t _
      ((RawList p items) (Cons _ (RawList p $ notail $ subst-raws env items) $ Nil _))
      ((RawSymbol _ _) (subst-sym env t))
      (else (Cons _ t $ Nil _))))
  ((many subst-raws : (many (List $ Raw) env) (subterm many (List $ Raw) ts) -> (many (List $ Raw) out))
    (let-match many ts (Cons _ t rest) ((Nil _) (Nil _)))
    (raws-append (notail $ subst-raw env t) (notail $ subst-raws env rest))))

(def-fns _ $ (many instances-of : (subterm many (List $ Raw) sets) (many (List $ Raw) body) -> (many (List $ Raw) out))
  (let-match many sets (Cons _ s rest) ((Nil _) (Nil _)))
  (let-match many s (RawList _ env) (else (qq (compile-error "an `instances` substitution is a list of `(name item ...)` entries"))))
  (raws-append (subst-raws env body) (notail $ instances-of rest body)))

(def-fns _ $ (many instances-usage : -> (many (List $ Raw) out))
  (qq (compile-error "`instances` takes a list of substitutions, then the forms they instantiate")))

(def-macro (instances args)
  (let-match many args (Cons _ sets body) ((Nil _) (instances-usage)))
  (let-match many sets (RawList _ ss) (else (instances-usage)))
  (instances-of ss body))

(instances
  (((%TK (Type A)) (%TP (erased Type A)) (%TA _) (%TY A) (%E (Copy A)) (%BUF Array (Copy A))
    (%empty copy-array-empty) (%make copy-array-make) (%get copy-array-get) (%set copy-array-set) (%len array-length) (%blit array-blit))
   ((%TK) (%TP) (%TA) (%TY) (%E (U8)) (%BUF Bytes)
    (%empty bytes-empty) (%make bytes-make) (%get bytes-get) (%set bytes-set) (%len bytes-length) (%blit bytes-blit)
    (Vec BytesVec) (MkVec MkBytesVec) (vec-new bytes-vec-new) (vec-length bytes-vec-length) (vec-get bytes-vec-get)
    (vec-set bytes-vec-set) (vec-room bytes-vec-room) (vec-push bytes-vec-push) (vec-pop bytes-vec-pop)
    (Ring BytesRing) (MkRing MkBytesRing) (ring-new bytes-ring-new) (ring-length bytes-ring-length) (ring-get bytes-ring-get)
    (ring-set bytes-ring-set) (ring-room bytes-ring-room) (ring-push-back bytes-ring-push-back) (ring-pop-front bytes-ring-pop-front)))

  (def-adts $ (Vec : %TK ((List %E) xs) -> Type)
    enum
    (many MkVec : %TP (erased (List %E) xs bs) (unique (%BUF bs) buf) (many (Nat) n) (erased (Splice %E bs (Zero) n xs bs) p)
       -> (Vec %TY xs)))

  (def-fns _ $ (many vec-new : %TP -> (unique (Vec %TY (Nil %E)) v))
    (MkVec %TA _ _ (%empty %TA) (Zero) (SpliceNil _ (Nil _))))

  (def-fns _ $ (many vec-length : %TP (erased (List %E) xs) (unique (Vec %TY xs) v) ->
      (many (Nat) n) (erased (Length %E xs n) l) (unique v is w at v))
    (let-match unique v (MkVec %TA _ bs buf n p u))
    (values n (splice-count _ bs xs bs (Zero) n p) (at unique (u %TA _ _ buf n p))))

  (def-fns _ $ (many vec-get : %TP (erased (List %E) xs) (unique (Vec %TY xs) v) (many (Nat) i)
      (erased %E e) (erased (Nth %E xs i e) q) -> (many e is x) (unique v is w at v))
    (let-match unique v (MkVec %TA _ bs buf n p u))
    (let ((many x) (unique buf2)) (%get %TA _ buf i e (prefix-nth _ bs xs n i e p q)))
    (values x (at unique (u %TA _ _ buf2 n p))))

  (def-fns _ $ (many vec-set : %TP (erased (List %E) xs) (unique (Vec %TY xs) v) (many (Nat) i) (many %E y)
      (erased %E m) (erased (Nth %E xs i m) q) ->
      (erased (List %E) ys) (unique (Vec %TY ys) w at v) (erased (SetNth %E xs i y ys) s))
    (let-match unique v (MkVec %TA _ bs buf n p u))
    (let ((erased bs2) (unique buf2) (erased sb)) (%set %TA _ buf i y m (prefix-nth _ bs xs n i m p q)))
    (let ((erased ys) (erased s) (erased p2)) (prefix-setnth _ bs xs bs2 n i m y p q sb))
    (values ys (at unique (u %TA _ _ buf2 n p2)) s))

  (def-fns _ $ (many vec-room : %TP (erased (List %E) xs bs) (unique (%BUF bs) buf) (many (Nat) n cap) (many %E y)
      (erased (Splice %E bs (Zero) n xs bs) p) (erased (Length %E bs cap) lb) ->
      (erased (List %E) bs2) (unique (%BUF bs2) buf2) (erased (Nat) cap2) (erased (Length %E bs2 cap2) lb2) (erased (Lt n cap2) lt2)
      (erased (Splice %E bs2 (Zero) n xs bs2) p2))
    (let-match many (lt-dec n cap) (No _ _ _ _ _) ((Yes _ _ _ _ lt) (values bs buf cap lb lt p)))
    (let ((many d) (erased ad)) (add n n))
    (let ((erased nb) (unique nbuf) (erased rep)) (%make %TA (Succ d) y))
    (let ((erased ln)) (repeat-length _ (Succ d) y nb rep))
    (let ((erased lt)) (add-le-left n n d ad))
    (let ((erased _) (erased to)) (splice-range _ nb (Succ d) ln (Zero) n n (AddZero n) (lt-weaken n (Succ d) lt)))
    (let ((erased z) (unique buf2) (erased q) (unique _)) (%blit %TA _ buf (Zero) _ nbuf (Zero) n _ p _ to))
    (values z buf2 (Succ d) (splice-length _ nb xs z (Zero) n (Succ d) q ln) lt (splice-self _ nb xs z (Zero) n q)))

  (def-fns _ $ (many vec-push : %TP (erased (List %E) xs) (unique (Vec %TY xs) v) (many %E y) ->
      (erased (List %E) ys) (unique (Vec %TY ys) w at v) (erased (Concat %E xs (Cons %E y (Nil %E)) ys) c))
    (let-match unique v (MkVec %TA _ _ buf n p u))
    (let ((many cap) (erased lb) (unique buf1)) (%len %TA _ buf))
    (let ((erased bs2) (unique buf2) (erased cap2) (erased lb2) (erased lt2) (erased p2)) (vec-room %TA _ _ buf1 n cap y p lb))
    (let ((erased m) (erased nth)) (nth-exists _ bs2 cap2 n lb2 lt2))
    (let ((erased bs3) (unique buf3) (erased sb)) (%set %TA _ buf2 n y m nth))
    (let ((erased ys) (erased c) (erased p3)) (prefix-push _ bs2 xs bs3 n y p2 sb))
    (values ys (u %TA _ _ buf3 (Succ n) p3) c))

  (def-fns _ $ (many vec-pop : %TP (erased (List %E) xs) (unique (Vec %TY xs) v) ->
      (erased (List %E) ys) (unique (Vec %TY ys) w at v) (many (Back %E xs ys) b))
    (let-match unique v (MkVec %TA _ bs buf n p u))
    (let-match many n (Succ m)
      ((Zero) (let-match erased p (SpliceNil _ _)) (values (Nil _) (at unique (u %TA _ _ buf n p)) (BackNone _))))
    (let ((erased ys) (erased e) (erased c) (erased q) (erased p2)) (prefix-pop _ bs xs m p))
    (let ((many x) (unique buf2)) (%get %TA _ buf m e q))
    (values ys (u %TA _ _ (at) buf2 m p2) (BackSome _ xs ys x c)))

  (def-adts $ (Ring : %TK ((List %E) xs) -> Type)
    enum
    (many MkRing : %TP (erased (List %E) xs bs cs) (unique (%BUF bs) buf) (many (Nat) h r n)
       (erased (Rot %E bs h r cs) rot) (erased (Splice %E cs (Zero) n xs cs) p) -> (Ring %TY xs)))

  (def-fns _ $ (many ring-new : %TP -> (unique (Ring %TY (Nil %E)) v))
    (MkRing %TA _ _ _ (%empty %TA) (Zero) (Zero) (Zero) (rot-fresh _ (Nil _) (Zero) (LengthNil _)) (SpliceNil _ (Nil _))))

  (def-fns _ $ (many ring-length : %TP (erased (List %E) xs) (unique (Ring %TY xs) v) ->
      (many (Nat) n) (erased (Length %E xs n) l) (unique v is w at v))
    (let-match unique v (MkRing %TA _ _ cs buf h r n rot p u))
    (values n (splice-count _ cs xs cs (Zero) n p) (at unique (u %TA _ _ _ buf h r n rot p))))

  (def-fns _ $ (many ring-get : %TP (erased (List %E) xs) (unique (Ring %TY xs) v) (many (Nat) i)
      (erased %E e) (erased (Nth %E xs i e) q) -> (many e is x) (unique v is w at v))
    (let-match unique v (MkRing %TA _ bs cs buf h r n rot p u))
    (let ((many k) (erased ph)) (phys h r i))
    (let ((many x) (unique buf2)) (%get %TA _ buf k e (rot-nth _ bs cs h r i k e rot ph (prefix-nth _ cs xs n i e p q))))
    (values x (at unique (u %TA _ _ _ buf2 h r n rot p))))

  (def-fns _ $ (many ring-set : %TP (erased (List %E) xs) (unique (Ring %TY xs) v) (many (Nat) i) (many %E y)
      (erased %E m) (erased (Nth %E xs i m) q) ->
      (erased (List %E) ys) (unique (Ring %TY ys) w at v) (erased (SetNth %E xs i y ys) s))
    (let-match unique v (MkRing %TA _ bs cs buf h r n rot p u))
    (let ((many k) (erased ph)) (phys h r i))
    (let ((erased nth)) (prefix-nth _ cs xs n i m p q))
    (let ((erased bs2) (unique buf2) (erased sb)) (%set %TA _ buf k y m (rot-nth _ bs cs h r i k m rot ph nth)))
    (let ((erased bs3) (erased cs2) (erased sb3) (erased sc) (erased rot2)) (rot-set _ bs cs h r i k m y rot ph nth))
    (let-match erased (setnth-fn _ bs k y bs2 bs3 sb sb3) (Refl _ _))
    (let ((erased ys) (erased s) (erased p2)) (prefix-setnth _ cs xs cs2 n i m y p q sc))
    (values ys (at unique (u %TA _ _ _ buf2 h r n rot2 p2)) s))

  (def-fns _ $ (many ring-room : %TP (erased (List %E) xs bs cs) (unique (%BUF bs) buf) (many (Nat) h r n) (many %E y)
      (erased (Rot %E bs h r cs) rot) (erased (Splice %E cs (Zero) n xs cs) p) ->
      (erased (List %E) bs2 cs2) (unique (%BUF bs2) buf2) (many (Nat) h2 r2) (erased (Rot %E bs2 h2 r2 cs2) rot2)
      (erased (Nat) cap) (erased (Length %E cs2 cap) lc2) (erased (Lt n cap) lt2) (erased (Splice %E cs2 (Zero) n xs cs2) p2))
    (let ((many c) (erased ad)) (add r h))
    (let ((erased lc)) (rot-length _ bs cs h r c rot ad))
    (let-match many (lt-dec n c) (No _ _ _ _ _) ((Yes _ _ _ _ lt) (values bs cs buf h r rot c lc lt p)))
    (let ((many d) (erased dd)) (add c c))
    (let ((erased nb) (unique nbuf) (erased rep)) (%make %TA (Succ d) y))
    (let ((erased ln)) (repeat-length _ (Succ d) y nb rep))
    (let ((erased lcd)) (add-le-left c c d dd))
    (let ((erased lrd)) (lt-trans r (Succ c) (Succ (Succ d)) (add-le-left r h c ad) (LtS c (Succ d) lcd)))
    (let ((erased post) (erased pre) (erased sr) (erased sl) (erased pc)) (rot-segments _ bs cs h r rot))
    (let ((erased _) (erased to1)) (splice-range _ nb (Succ d) ln (Zero) r r (AddZero r) lrd))
    (let ((erased z1) (unique buf1) (erased q1) (unique src)) (%blit %TA _ buf h _ nbuf (Zero) r _ sr _ to1))
    (let ((erased l1)) (splice-length _ nb post z1 (Zero) r (Succ d) q1 ln))
    (let ((erased _) (erased to2)) (splice-range _ z1 (Succ d) l1 r h c ad (lt-weaken c (Succ d) lcd)))
    (let ((erased z2) (unique buf2) (erased q2) (unique _)) (%blit %TA _ src (Zero) _ buf1 r h _ sl _ to2))
    (let ((erased l2)) (splice-length _ z1 pre z2 r h (Succ d) q2 l1))
    (let ((erased full)) (prefix-cat _ z1 z2 post pre cs r h c (splice-self _ nb post z1 (Zero) r q1) q2 pc ad))
    (values z2 z2 buf2 (Zero) (Succ d) (rot-fresh _ z2 (Succ d) l2) (Succ d) l2
      (lt-le-trans n (Succ c) (Succ d) (prefix-le _ cs xs n c p lc) (LtS c (Succ d) lcd))
      (prefix-trans _ z2 cs xs c n p full)))

  (def-fns _ $ (many ring-push-back : %TP (erased (List %E) xs) (unique (Ring %TY xs) v) (many %E y) ->
      (erased (List %E) ys) (unique (Ring %TY ys) w at v) (erased (Concat %E xs (Cons %E y (Nil %E)) ys) c))
    (let-match unique v (MkRing %TA _ _ _ buf h r n rot p u))
    (let ((erased bs2) (erased cs2) (unique buf2) (many h2) (many r2) (erased rot2) (erased cap) (erased lc) (erased lt) (erased p2))
      (ring-room %TA _ _ _ buf h r n y rot p))
    (let ((many k) (erased ph)) (phys h2 r2 n))
    (let ((erased m) (erased nth)) (nth-exists _ cs2 cap n lc lt))
    (let ((erased bs3) (unique buf3) (erased sb)) (%set %TA _ buf2 k y m (rot-nth _ bs2 cs2 h2 r2 n k m rot2 ph nth)))
    (let ((erased bs4) (erased cs3) (erased sb4) (erased sc) (erased rot3)) (rot-set _ bs2 cs2 h2 r2 n k m y rot2 ph nth))
    (let-match erased (setnth-fn _ bs2 k y bs3 bs4 sb sb4) (Refl _ _))
    (let ((erased ys) (erased c) (erased p3)) (prefix-push _ cs2 xs cs3 n y p2 sc))
    (values ys (u %TA _ _ _ buf3 h2 r2 (Succ n) rot3 p3) c))

  (def-fns _ $ (many ring-pop-front : %TP (erased (List %E) xs) (unique (Ring %TY xs) v) ->
      (erased (List %E) ys) (unique (Ring %TY ys) w at v) (many (Front %E xs ys) f))
    (let-match unique v (MkRing %TA _ bs _ buf h r n rot p u))
    (let-match many n (Succ m)
      ((Zero) (let-match erased p (SpliceNil _ _)) (values (Nil _) (at unique (u %TA _ _ _ buf h r n rot p)) (FrontNone _))))
    (let-match erased p (SpliceHere _ x _ cs1 _ ys _ p1))
    (let ((many cap) (erased lb) (unique buf1)) (%len %TA _ buf))
    (let ((many h1) (many r1) (erased rot1)) (rot-norm _ bs cs1 x h r cap rot lb))
    (let ((erased cs2) (erased k) (erased rot2) (erased q)) (rot-pop _ bs cs1 h1 r1 x rot1))
    (let ((many e) (unique buf2)) (%get %TA _ buf1 h1 x q))
    (values ys (u %TA _ _ _ (at) buf2 (Succ h1) r1 m rot2 (prefix-extend _ cs1 _ cs2 ys m p1 k)) (FrontSome _ e ys))))
