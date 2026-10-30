; Undirected graphs on darts, as lists of bonds, and the count of their connected classes.

(def-adts $ (Bond : -> Type)
  enum
  (many MkBond : (many (Nat) x y) -> (Bond)))

; A bond of g joins x and y, read either way.
(def-adts $ (Adj : ((List (Bond)) g) ((Nat) x) ((Nat) y) -> Type)
  enum
  (many AdjFwd : (erased (List (Bond)) g) (erased (Nat) x y) -> (Adj (Cons (Bond) (MkBond x y) g) x y))
  (many AdjBwd : (erased (List (Bond)) g) (erased (Nat) x y) -> (Adj (Cons (Bond) (MkBond x y) g) y x))
  (many AdjThere : (erased (List (Bond)) g) (erased (Bond) b) (erased (Nat) x y) (erased (Adj g x y) p)
      -> (Adj (Cons (Bond) b g) x y)))

(def-adts $ (Conn : ((List (Bond)) g) ((Nat) x) ((Nat) y) -> Type)
  enum
  (many ConnHere : (erased (List (Bond)) g) (erased (Nat) x) -> (Conn g x x))
  (many ConnStep : (erased (List (Bond)) g) (erased (Nat) x y z) (erased (Adj g x y) a) (erased (Conn g y z) c)
      -> (Conn g x z)))

(def-fns _ $ (erased adj-sym : (erased (List (Bond)) g) (erased (Nat) x y) (subterm erased (Adj g x y) a) -> (erased (Adj g y x) r))
  (match erased a _
    ((AdjFwd g1 _ _) (AdjBwd g1 x y))
    ((AdjBwd g1 _ _) (AdjFwd g1 y x))
    ((AdjThere g1 b _ _ a1) (AdjThere g1 b y x (adj-sym g1 x y a1)))))

(def-fns _ $ (erased conn-adj : (erased (List (Bond)) g) (erased (Nat) x y) (erased (Adj g x y) a) -> (erased (Conn g x y) r))
  (ConnStep g x y y a (ConnHere g y)))

(def-fns _ $ (erased conn-cat : (erased (List (Bond)) g) (erased (Nat) x y z) (subterm erased (Conn g x y) c) (erased (Conn g y z) d)
    -> (erased (Conn g x z) r))
  (let-match erased c (ConnStep _ _ w _ a c1) ((ConnHere _ _) d))
  (ConnStep g x w z a (conn-cat g w y z c1 d)))

(def-fns _ $ (erased conn-sym : (erased (List (Bond)) g) (erased (Nat) x y) (subterm erased (Conn g x y) c) -> (erased (Conn g y x) r))
  (let-match erased c (ConnStep _ _ w _ a c1) ((ConnHere _ _) c))
  (conn-cat g y w x (conn-sym g w y c1) (conn-adj g w x (adj-sym g x w a))))

(def-fns _ $ (erased conn-cons : (erased (List (Bond)) g) (erased (Bond) b) (erased (Nat) x y) (subterm erased (Conn g x y) c)
    -> (erased (Conn (Cons (Bond) b g) x y) r))
  (let-match erased c (ConnStep _ _ w _ a c1) ((ConnHere _ _) (ConnHere _ x)))
  (ConnStep _ x w y (AdjThere g b x w a) (conn-cons g b w y c1)))

(def-fns _ $ (erased adj-snoc : (erased (List (Bond)) g g2) (erased (Bond) b) (erased (Nat) x y) (subterm erased (Adj g x y) a)
    (erased (Snoc (Bond) g b g2) s) -> (erased (Adj g2 x y) r))
  (let-match erased s (SnocCons _ b0 _ g1 g3 s1) (absurd (SnocNil _ _) a))
  (match erased a _
    ((AdjFwd _ _ _) (AdjFwd g3 x y))
    ((AdjBwd _ _ _) (AdjBwd g3 y x))
    ((AdjThere _ _ _ _ a1) (AdjThere g3 b0 x y (adj-snoc g1 g3 b x y a1 s1)))))

(def-fns _ $ (erased conn-snoc : (erased (List (Bond)) g g2) (erased (Bond) b) (erased (Nat) x y) (subterm erased (Conn g x y) c)
    (erased (Snoc (Bond) g b g2) s) -> (erased (Conn g2 x y) r))
  (let-match erased c (ConnStep _ _ w _ a c1) ((ConnHere _ _) (ConnHere _ x)))
  (ConnStep _ x w y (adj-snoc g g2 b x w a s) (conn-snoc g g2 b w y c1 s)))

(def-fns _ $ (erased adj-snoc-new : (erased (List (Bond)) g g2) (erased (Nat) x y) (subterm erased (Snoc (Bond) g (MkBond x y) g2) s)
    -> (erased (Adj g2 x y) r))
  (let-match erased s (SnocCons _ b0 _ g1 g3 s1) ((SnocNil _ _) (AdjFwd _ x y)))
  (AdjThere g3 b0 x y (adj-snoc-new g1 g3 x y s1)))

; h joins the two ends of every bond of g.
(def-adts $ (Spans : ((List (Bond)) h) ((List (Bond)) g) -> Type)
  enum
  (many SpansNil : (erased (List (Bond)) h) -> (Spans h (Nil (Bond))))
  (many SpansCons : (erased (List (Bond)) h g) (erased (Nat) x y) (erased (Conn h x y) c) (erased (Spans h g) rest)
      -> (Spans h (Cons (Bond) (MkBond x y) g))))

(def-fns _ $ (erased spans-adj : (erased (List (Bond)) h g) (erased (Nat) x y) (subterm erased (Adj g x y) a) (erased (Spans h g) sp)
    -> (erased (Conn h x y) r))
  (match erased a _
    ((AdjFwd _ _ _) (let-match erased sp (SpansCons _ _ _ _ c _)) c)
    ((AdjBwd _ _ _) (let-match erased sp (SpansCons _ _ _ _ c _)) (conn-sym h y x c))
    ((AdjThere g1 _ _ _ a1) (let-match erased sp (SpansCons _ _ _ _ _ sp1)) (spans-adj h g1 x y a1 sp1))))

(def-fns _ $ (erased spans-conn : (erased (List (Bond)) h g) (erased (Nat) x y) (subterm erased (Conn g x y) c) (erased (Spans h g) sp)
    -> (erased (Conn h x y) r))
  (let-match erased c (ConnStep _ _ w _ a c1) ((ConnHere _ _) (ConnHere h x)))
  (conn-cat h x w y (spans-adj h g x w a sp) (spans-conn h g w y c1 sp)))

(def-fns _ $ (erased spans-cons : (erased (List (Bond)) h g) (erased (Bond) b) (subterm erased (Spans h g) sp)
    -> (erased (Spans (Cons (Bond) b h) g) r))
  (let-match erased sp (SpansCons _ g1 x y c sp1) ((SpansNil _) (SpansNil _)))
  (SpansCons _ g1 x y (conn-cons h b x y c) (spans-cons h g1 b sp1)))

(def-fns _ $ (erased spans-snoc : (erased (List (Bond)) h h2 g) (erased (Bond) b) (subterm erased (Spans h g) sp) (erased (Snoc (Bond) h b h2) s)
    -> (erased (Spans h2 g) r))
  (let-match erased sp (SpansCons _ g1 x y c sp1) ((SpansNil _) (SpansNil _)))
  (SpansCons _ g1 x y (conn-snoc h h2 b x y c s) (spans-snoc h h2 g1 b sp1 s)))

(def-fns _ $ (erased spans-self : (subterm erased (List (Bond)) g) -> (erased (Spans g g) r))
  (let-match erased g (Cons _ b g1) ((Nil _) (SpansNil _)))
  (let-match erased b (MkBond x y))
  (SpansCons g g1 x y (conn-adj g x y (AdjFwd g1 x y)) (spans-cons g1 g1 b (spans-self g1))))

(def-fns _ $ (erased spans-trans : (erased (List (Bond)) h g f) (subterm erased (Spans g f) sp) (erased (Spans h g) sq)
    -> (erased (Spans h f) r))
  (let-match erased sp (SpansCons _ f1 x y c sp1) ((SpansNil _) (SpansNil _)))
  (SpansCons h f1 x y (spans-conn h g x y c sq) (spans-trans h g f1 sp1 sq)))

; Every bond of g has both ends below d.
(def-adts $ (Below : ((List (Bond)) g) ((Nat) d) -> Type)
  enum
  (many BelowNil : (erased (Nat) d) -> (Below (Nil (Bond)) d))
  (many BelowCons : (erased (List (Bond)) g) (erased (Nat) x y d) (erased (Lt x d) px) (erased (Lt y d) py) (erased (Below g d) rest)
      -> (Below (Cons (Bond) (MkBond x y) g) d)))

; lab gives the two ends of every bond of g one label.
(def-adts $ (Const : ((List (Nat)) lab) ((List (Bond)) g) -> Type)
  enum
  (many ConstNil : (erased (List (Nat)) lab) -> (Const lab (Nil (Bond))))
  (many ConstCons : (erased (List (Nat)) lab) (erased (List (Bond)) g) (erased (Nat) x y l)
      (erased (Nth (Nat) lab x l) px) (erased (Nth (Nat) lab y l) py) (erased (Const lab g) rest)
      -> (Const lab (Cons (Bond) (MkBond x y) g))))

; The dart listed by xs at each position, labelled at that position by ls, is joined in g to its label, which is in rs.
(def-adts $ (Rooted : ((List (Bond)) g) ((List (Nat)) rs) ((List (Nat)) xs) ((List (Nat)) ls) -> Type)
  enum
  (many RootedNil : (erased (List (Bond)) g) (erased (List (Nat)) rs) -> (Rooted g rs (Nil (Nat)) (Nil (Nat))))
  (many RootedCons : (erased (List (Bond)) g) (erased (List (Nat)) rs xs ls) (erased (Nat) x r)
      (erased (In r rs) pin) (erased (Conn g r x) c) (erased (Rooted g rs xs ls) rest)
      -> (Rooted g rs (Cons (Nat) x xs) (Cons (Nat) r ls))))

; ids lists 0..n-1.
(def-adts $ (Iota : ((Nat) n) ((List (Nat)) ids) -> Type)
  enum
  (many IotaZ : -> (Iota (Zero) (Nil (Nat))))
  (many IotaS : (erased (Nat) n) (erased (List (Nat)) ids ids2) (erased (Iota n ids) p) (erased (Snoc (Nat) ids n ids2) s)
      -> (Iota (Succ n) ids2)))

; The darts 0..d-1 fall into k classes of g: lab sends each dart to the root of its class, and rs lists the roots,
; each its own label.
(def-adts $ (Classes : ((List (Bond)) g) ((Nat) d) ((Nat) k) -> Type)
  enum
  (many MkClasses : (erased (List (Bond)) g) (erased (Nat) d k) (erased (List (Nat)) ids lab rs)
      (erased (Iota d ids) io) (erased (Length (Nat) lab d) ll) (erased (Length (Nat) rs k) lr) (erased (Distinct rs) dr)
      (erased (Respects lab rs rs) fix) (erased (Const lab g) cl) (erased (Rooted g rs ids lab) ro)
      -> (Classes g d k)))

; A labelling constant along g tells x and y apart.
(def-adts $ (Sep : ((List (Bond)) g) ((Nat) x) ((Nat) y) -> Type)
  enum
  (many MkSep : (erased (List (Bond)) g) (erased (Nat) x y) (erased (List (Nat)) lab) (erased (Nat) l1 l2)
      (erased (Const lab g) cl) (erased (Nth (Nat) lab x l1) p1) (erased (Nth (Nat) lab y l2) p2) (erased (Apart (Nat) Lt l1 l2) ne)
      -> (Sep g x y)))

(def-fns _ $ (erased iota-length : (erased (Nat) n) (erased (List (Nat)) ids) (subterm erased (Iota n ids) io) -> (erased (Length (Nat) ids n) l))
  (let-match erased io (IotaS n1 ids1 _ io1 s) ((IotaZ) (LengthNil _)))
  (snoc-length _ ids1 ids n1 n1 s (iota-length n1 ids1 io1)))

(def-fns _ $ (erased iota-nth : (erased (Nat) n i) (erased (List (Nat)) ids) (subterm erased (Iota n ids) io) (erased (Lt i n) lt)
    -> (erased (Nth (Nat) ids i i) r))
  (let-match erased io (IotaS n1 ids1 _ io1 s) (absurd (IotaZ) lt))
  (match erased (nat-cmp i n1) _
    ((CLt _ _ _ _ l) (snoc-old _ ids1 ids n1 i i s (iota-nth n1 i ids1 io1 l)))
    ((CEq _ _ _) (snoc-new _ ids1 ids n1 n1 s (iota-length n1 ids1 io1)))
    (absurd (CGt _ _ _ _ g) (lt-asym n1 i g lt))))

(def-fns _ $ (erased iota-exists : (subterm erased (Nat) n) -> (erased (List (Nat)) ids) (erased (Iota n ids) io))
  (let-match erased n (Succ n1) ((Zero) (values (Nil _) (IotaZ))))
  (let ((erased ids1) (erased io1)) (iota-exists n1))
  (let ((erased ids) (erased s)) (snoc-exists _ ids1 n1))
  (values ids (IotaS n1 ids1 ids io1 s)))

(def-fns _ $ (erased snoc-fn : (erased Type A) (erased (List A) xs ys zs) (erased A a) (subterm erased (Snoc A xs a ys) p)
    (erased (Snoc A xs a zs) q) -> (erased (Eq (List A) ys zs) e))
  (let-match erased p (SnocCons _ x _ xs1 ys1 p1) ((SnocNil _ _) (let-match erased q (SnocNil _ _)) (Refl _ ys)))
  (let-match erased q (SnocCons _ _ _ _ zs1 q1))
  (let-match erased (snoc-fn _ xs1 ys1 zs1 a p1 q1) (Refl _ _))
  (Refl _ ys))

(def-fns _ $ (erased iota-fn : (erased (Nat) n) (erased (List (Nat)) ids ids2) (subterm erased (Iota n ids) p) (erased (Iota n ids2) q)
    -> (erased (Eq (List (Nat)) ids ids2) e))
  (let-match erased p (IotaS n1 ids1 _ p1 s1) ((IotaZ) (let-match erased q (IotaZ)) (Refl _ ids)))
  (let-match erased q (IotaS _ ids3 _ q1 s3))
  (let-match erased (iota-fn n1 ids1 ids3 p1 q1) (Refl _ _))
  (snoc-fn _ ids1 ids ids2 n1 s1 s3))

(def-fns _ $ (erased adj-const : (erased (List (Nat)) lab) (erased (List (Bond)) g) (erased (Nat) x y l) (subterm erased (Adj g x y) a)
    (erased (Const lab g) cl) (erased (Nth (Nat) lab x l) p) -> (erased (Nth (Nat) lab y l) r))
  (match erased a _
    ((AdjFwd _ _ _)
      (let-match erased cl (ConstCons _ _ _ _ l1 px py _))
      (let-match erased (nth-fn _ lab x l l1 p px) (Refl _ _))
      py)
    ((AdjBwd _ _ _)
      (let-match erased cl (ConstCons _ _ _ _ l1 px py _))
      (let-match erased (nth-fn _ lab x l l1 p py) (Refl _ _))
      px)
    ((AdjThere g1 _ _ _ a1)
      (let-match erased cl (ConstCons _ _ _ _ _ _ _ cl1))
      (adj-const lab g1 x y l a1 cl1 p))))

(def-fns _ $ (erased conn-const : (erased (List (Nat)) lab) (erased (List (Bond)) g) (erased (Nat) x y l) (subterm erased (Conn g x y) c)
    (erased (Const lab g) cl) (erased (Nth (Nat) lab x l) p) -> (erased (Nth (Nat) lab y l) r))
  (let-match erased c (ConnStep _ _ w _ a c1) ((ConnHere _ _) p))
  (conn-const lab g w y l c1 cl (adj-const lab g x w l a cl p)))

(def-fns _ $ (erased absurd sep-conn : (erased (List (Bond)) g) (erased (Nat) x y) (erased (Sep g x y) s) (erased (Conn g x y) c)
    -> (erased (False) f))
  (let-match erased s (MkSep _ _ _ lab l1 l2 cl p1 p2 ne))
  (let-match erased (nth-fn _ lab y l1 l2 (conn-const lab g x y l1 c cl p1) p2) (Refl _ _))
  (apart-irrefl l1 ne))

(def-fns _ $ (erased const-snoc : (erased (List (Nat)) lab lab2) (erased (List (Bond)) g) (erased (Nat) a) (subterm erased (Const lab g) cl)
    (erased (Snoc (Nat) lab a lab2) s) -> (erased (Const lab2 g) r))
  (let-match erased cl (ConstCons _ g1 x y l px py cl1) ((ConstNil _) (ConstNil _)))
  (ConstCons lab2 g1 x y l (snoc-old _ lab lab2 a l x s px) (snoc-old _ lab lab2 a l y s py) (const-snoc lab lab2 g1 a cl1 s)))

(def-fns _ $ (erased const-below : (erased (List (Nat)) lab) (erased (List (Bond)) g) (erased (Nat) d) (subterm erased (Const lab g) cl)
    (erased (Length (Nat) lab d) ll) -> (erased (Below g d) r))
  (let-match erased cl (ConstCons _ g1 x y l px py cl1) ((ConstNil _) (BelowNil d)))
  (BelowCons g1 x y d (nth-lt-length _ lab x d l px ll) (nth-lt-length _ lab y d l py ll) (const-below lab g1 d cl1 ll)))

(def-fns _ $ (erased const-spans : (erased (List (Nat)) lab) (erased (List (Bond)) g h) (erased (Nat) d) (erased (Const lab g) cl)
    (erased (Length (Nat) lab d) ll) (subterm erased (Spans g h) sp) (erased (Below h d) bh) -> (erased (Const lab h) r))
  (let-match erased sp (SpansCons _ h1 x y c sp1) ((SpansNil _) (ConstNil _)))
  (let-match erased bh (BelowCons _ _ _ _ px _ bh1))
  (let ((erased l) (erased p)) (nth-exists _ lab d x ll px))
  (ConstCons lab h1 x y l p (conn-const lab g x y l c cl p) (const-spans lab g h1 d cl ll sp1 bh1)))

(def-fns _ $ (erased rooted-nth : (erased (List (Bond)) g) (erased (List (Nat)) rs xs ls) (erased (Nat) j x r)
    (subterm erased (Rooted g rs xs ls) ro) (erased (Nth (Nat) xs j x) px) (erased (Nth (Nat) ls j r) pr)
    -> (erased (In r rs) pin) (erased (Conn g r x) c))
  (let-match erased ro (RootedCons _ _ xs1 ls1 x0 r0 pin0 c0 ro1) (absurd (RootedNil _ _) px))
  (let-match erased px (NthThere _ _ _ j1 _ px1) ((NthHere _ _ _) (let-match erased pr (NthHere _ _ _)) (values pin0 c0)))
  (let-match erased pr (NthThere _ _ _ _ _ pr1))
  (rooted-nth g rs xs1 ls1 j1 x r ro1 px1 pr1))

; The root of dart x is joined to it.
(def-fns _ $ (erased classes-root : (erased (List (Bond)) g) (erased (Nat) d) (erased (List (Nat)) ids lab rs) (erased (Nat) x r)
    (erased (Iota d ids) io) (erased (Rooted g rs ids lab) ro) (erased (Nth (Nat) lab x r) p) (erased (Lt x d) lt)
    -> (erased (In r rs) pin) (erased (Conn g r x) c))
  (rooted-nth g rs ids lab x x r ro (iota-nth d x ids io lt) p))

(def-fns _ $ (erased rooted-snoc : (erased (List (Bond)) g) (erased (List (Nat)) rs xs xs2 ls ls2) (erased (Nat) x r)
    (subterm erased (Rooted g rs xs ls) ro) (erased (Snoc (Nat) xs x xs2) sx) (erased (Snoc (Nat) ls r ls2) sl)
    (erased (In r rs) pin) (erased (Conn g r x) c) -> (erased (Rooted g rs xs2 ls2) res))
  (match erased ro _
    ((RootedNil _ _)
      (let-match erased sx (SnocNil _ _))
      (let-match erased sl (SnocNil _ _))
      (RootedCons g rs _ _ x r pin c (RootedNil g rs)))
    ((RootedCons _ _ xs1 ls1 x0 r0 pin0 c0 ro1)
      (let-match erased sx (SnocCons _ _ _ _ xs3 sx1))
      (let-match erased sl (SnocCons _ _ _ _ ls3 sl1))
      (RootedCons g rs xs3 ls3 x0 r0 pin0 c0 (rooted-snoc g rs xs1 xs3 ls1 ls3 x r ro1 sx1 sl1 pin c)))))

(def-fns _ $ (erased rooted-cons : (erased (List (Bond)) g) (erased (List (Nat)) rs xs ls) (erased (Nat) y)
    (subterm erased (Rooted g rs xs ls) ro) -> (erased (Rooted g (Cons (Nat) y rs) xs ls) res))
  (let-match erased ro (RootedCons _ _ xs1 ls1 x r pin c ro1) ((RootedNil _ _) (RootedNil g _)))
  (RootedCons g _ xs1 ls1 x r (InThere r y rs pin) c (rooted-cons g rs xs1 ls1 y ro1)))

(def-fns _ $ (erased rooted-spans : (erased (List (Bond)) g h) (erased (List (Nat)) rs xs ls)
    (subterm erased (Rooted g rs xs ls) ro) (erased (Spans h g) sp) -> (erased (Rooted h rs xs ls) res))
  (let-match erased ro (RootedCons _ _ xs1 ls1 x r pin c ro1) ((RootedNil _ _) (RootedNil h rs)))
  (RootedCons h rs xs1 ls1 x r pin (spans-conn h g r x c sp) (rooted-spans g h rs xs1 ls1 ro1 sp)))

(def-fns _ $ (erased fixed-notin : (erased (List (Nat)) lab rs) (erased (Nat) d) (subterm erased (Respects lab rs rs) fix)
    (erased (Length (Nat) lab d) ll) -> (erased (NotIn d rs) r))
  (let-match erased fix (RespCons _ rs1 _ j _ p fix1) ((RespNil _) (NotInNil d)))
  (NotInCons d j rs1 (ApGt _ _ d j (nth-lt-length _ lab j d j p ll)) (fixed-notin lab rs1 d fix1 ll)))

(def-fns _ $ (erased fixed-in : (erased (List (Nat)) lab rs) (erased (Nat) r) (erased (Respects lab rs rs) fix)
    (subterm erased (In r rs) pin) -> (erased (Nth (Nat) lab r r) p))
  (let-match erased fix (RespCons _ rs1 _ j _ p0 fix1) (absurd (RespNil _) pin))
  (let-match erased pin (InThere _ _ _ pin1) ((InHere _ _) p0))
  (fixed-in lab rs1 r fix1 pin1))

; A new dart with no bonds is a class of its own.
(def-fns _ $ (erased classes-grow : (erased (List (Bond)) g) (erased (Nat) d k) (erased (Classes g d k) cs) -> (erased (Classes g (Succ d) (Succ k)) r))
  (let-match erased cs (MkClasses _ _ _ ids lab rs io ll lr dr fix cl ro))
  (let ((erased ids2) (erased si)) (snoc-exists _ ids d))
  (let ((erased lab2) (erased sl)) (snoc-exists _ lab d))
  (MkClasses g (Succ d) (Succ k) ids2 lab2 (Cons _ d rs) (IotaS d ids ids2 io si) (snoc-length _ lab lab2 d d sl ll)
    (LengthCons _ d rs k lr) (DistCons d rs (fixed-notin lab rs d fix ll) dr)
    (RespCons lab2 rs rs d d (snoc-new _ lab lab2 d d sl ll) (respects-lab lab lab2 rs rs d fix sl))
    (const-snoc lab lab2 g d cl sl)
    (rooted-snoc g (Cons _ d rs) ids ids2 lab lab2 d d (rooted-cons g rs ids lab d ro) si sl (InHere d rs) (ConnHere g d))))

(def-fns _ $ (erased classes-nil : (subterm erased (Nat) d) -> (erased (Classes (Nil (Bond)) d d) r))
  (let-match erased d (Succ d1)
    ((Zero) (MkClasses _ _ _ _ _ _ (IotaZ) (LengthNil _) (LengthNil _) (DistNil) (RespNil _) (ConstNil _) (RootedNil _ _))))
  (classes-grow _ d1 d1 (classes-nil d1)))

; The classes depend only on which darts g joins.
(def-fns _ $ (erased classes-equiv : (erased (List (Bond)) g h) (erased (Nat) d k) (erased (Classes g d k) cs)
    (erased (Spans h g) shg) (erased (Spans g h) sgh) (erased (Below h d) bh) -> (erased (Classes h d k) r))
  (let-match erased cs (MkClasses _ _ _ ids lab rs io ll lr dr fix cl ro))
  (MkClasses h d k ids lab rs io ll lr dr fix (const-spans lab g h d cl ll sgh bh) (rooted-spans g h rs ids lab ro shg)))

(def-fns _ $ (erased classes-below : (erased (List (Bond)) g) (erased (Nat) d k) (erased (Classes g d k) cs) -> (erased (Below g d) r))
  (let-match erased cs (MkClasses _ _ _ ids lab rs io ll lr dr fix cl ro))
  (const-below lab g d cl ll))

; Two darts are joined or told apart.
(def-fns _ $ (erased classes-dec : (erased (List (Bond)) g) (erased (Nat) d k x y) (erased (Classes g d k) cs)
    (erased (Lt x d) px) (erased (Lt y d) py) -> (erased (Or (Conn g x y) (Sep g x y)) r))
  (let-match erased cs (MkClasses _ _ _ ids lab rs io ll lr dr fix cl ro))
  (let ((erased rx) (erased qx)) (nth-exists _ lab d x ll px))
  (let ((erased ry) (erased qy)) (nth-exists _ lab d y ll py))
  (let ((erased ix) (erased cx)) (classes-root g d ids lab rs x rx io ro qx px))
  (let ((erased iy) (erased cy)) (classes-root g d ids lab rs y ry io ro qy py))
  (match erased (nat-cmp rx ry) _
    ((CLt _ _ _ _ l) (OrR _ _ (MkSep g x y lab rx ry cl qx qy (ApLt _ _ rx ry l))))
    ((CEq _ _ _) (OrL _ _ (conn-cat g x rx y (conn-sym g rx x cx) cy)))
    ((CGt _ _ _ _ l) (OrR _ _ (MkSep g x y lab rx ry cl qx qy (ApGt _ _ rx ry l))))))

(def-fns _ $ (erased classes-link-same : (erased (List (Bond)) g) (erased (Nat) d k x y) (erased (Classes g d k) cs)
    (erased (Conn g x y) c) (erased (Lt x d) px) (erased (Lt y d) py) -> (erased (Classes (Cons (Bond) (MkBond x y) g) d k) r))
  (classes-equiv g _ d k cs (spans-cons g g _ (spans-self g)) (SpansCons g g x y c (spans-self g))
    (BelowCons g x y d px py (classes-below g d k cs))))

; ls2 is ls with every a replaced by b.
(def-adts $ (Redirect : ((Nat) a b) ((List (Nat)) ls ls2) -> Type)
  enum
  (many RdNil : (erased (Nat) a b) -> (Redirect a b (Nil (Nat)) (Nil (Nat))))
  (many RdHit : (erased (Nat) a b) (erased (List (Nat)) ls ls2) (erased (Redirect a b ls ls2) p)
      -> (Redirect a b (Cons (Nat) a ls) (Cons (Nat) b ls2)))
  (many RdMiss : (erased (Nat) a b l) (erased (List (Nat)) ls ls2) (erased (Apart (Nat) Lt l a) ne) (erased (Redirect a b ls ls2) p)
      -> (Redirect a b (Cons (Nat) l ls) (Cons (Nat) l ls2))))

(def-fns _ $ (erased redirect-exists : (erased (Nat) a b) (subterm erased (List (Nat)) ls) -> (erased (List (Nat)) ls2) (erased (Redirect a b ls ls2) r))
  (let-match erased ls (Cons _ l ls1) ((Nil _) (values (Nil _) (RdNil a b))))
  (let ((erased ls3) (erased r1)) (redirect-exists a b ls1))
  (match erased (nat-cmp l a) _
    ((CLt _ _ _ _ p) (values (Cons _ l ls3) (RdMiss a b l ls1 ls3 (ApLt _ _ l a p) r1)))
    ((CEq _ _ _) (values (Cons _ b ls3) (RdHit a b ls1 ls3 r1)))
    ((CGt _ _ _ _ p) (values (Cons _ l ls3) (RdMiss a b l ls1 ls3 (ApGt _ _ l a p) r1)))))

(def-fns _ $ (erased redirect-hit : (erased (Nat) a b i) (erased (List (Nat)) ls ls2) (subterm erased (Redirect a b ls ls2) rd)
    (erased (Nth (Nat) ls i a) p) -> (erased (Nth (Nat) ls2 i b) q))
  (match erased rd _
    (absurd (RdNil _ _) p)
    ((RdHit _ _ ls1 ls3 rd1)
      (let-match erased p (NthThere _ _ _ i1 _ p1) ((NthHere _ _ _) (NthHere _ b ls3)))
      (NthThere _ b ls3 i1 b (redirect-hit a b i1 ls1 ls3 rd1 p1)))
    ((RdMiss _ _ l ls1 ls3 ne rd1)
      (let-match erased p (NthThere _ _ _ i1 _ p1) (absurd (NthHere _ _ _) (apart-irrefl a ne)))
      (NthThere _ l ls3 i1 b (redirect-hit a b i1 ls1 ls3 rd1 p1)))))

(def-fns _ $ (erased redirect-miss : (erased (Nat) a b i l) (erased (List (Nat)) ls ls2) (subterm erased (Redirect a b ls ls2) rd)
    (erased (Nth (Nat) ls i l) p) (erased (Apart (Nat) Lt l a) ne) -> (erased (Nth (Nat) ls2 i l) q))
  (match erased rd _
    (absurd (RdNil _ _) p)
    ((RdHit _ _ ls1 ls3 rd1)
      (let-match erased p (NthThere _ _ _ i1 _ p1) (absurd (NthHere _ _ _) (apart-irrefl a ne)))
      (NthThere _ b ls3 i1 l (redirect-miss a b i1 l ls1 ls3 rd1 p1 ne)))
    ((RdMiss _ _ l0 ls1 ls3 ne0 rd1)
      (let-match erased p (NthThere _ _ _ i1 _ p1) ((NthHere _ _ _) (NthHere _ l ls3)))
      (NthThere _ l0 ls3 i1 l (redirect-miss a b i1 l ls1 ls3 rd1 p1 ne)))))

(def-fns _ $ (erased redirect-length : (erased (Nat) a b n) (erased (List (Nat)) ls ls2) (subterm erased (Redirect a b ls ls2) rd)
    (erased (Length (Nat) ls n) l) -> (erased (Length (Nat) ls2 n) r))
  (match erased rd _
    ((RdNil _ _) (let-match erased l (LengthNil _)) (LengthNil _))
    ((RdHit _ _ ls1 ls3 rd1)
      (let-match erased l (LengthCons _ _ _ n1 l1))
      (LengthCons _ b ls3 n1 (redirect-length a b n1 ls1 ls3 rd1 l1)))
    ((RdMiss _ _ l0 ls1 ls3 ne rd1)
      (let-match erased l (LengthCons _ _ _ n1 l1))
      (LengthCons _ l0 ls3 n1 (redirect-length a b n1 ls1 ls3 rd1 l1)))))

(def-fns _ $ (erased const-redirect : (erased (Nat) a b) (erased (List (Nat)) lab lab2) (erased (List (Bond)) g)
    (subterm erased (Const lab g) cl) (erased (Redirect a b lab lab2) rd) -> (erased (Const lab2 g) r))
  (let-match erased cl (ConstCons _ g1 x y l px py cl1) ((ConstNil _) (ConstNil _)))
  (let ((erased rest)) (const-redirect a b lab lab2 g1 cl1 rd))
  (match erased (nat-cmp l a) _
    ((CLt _ _ _ _ p)
      (ConstCons lab2 g1 x y l (redirect-miss a b x l lab lab2 rd px (ApLt _ _ l a p)) (redirect-miss a b y l lab lab2 rd py (ApLt _ _ l a p)) rest))
    ((CEq _ _ _) (ConstCons lab2 g1 x y b (redirect-hit a b x lab lab2 rd px) (redirect-hit a b y lab lab2 rd py) rest))
    ((CGt _ _ _ _ p)
      (ConstCons lab2 g1 x y l (redirect-miss a b x l lab lab2 rd px (ApGt _ _ l a p)) (redirect-miss a b y l lab lab2 rd py (ApGt _ _ l a p)) rest))))

; ys is xs without one occurrence of x.
(def-adts $ (Remove : ((Nat) x) ((List (Nat)) xs ys) -> Type)
  enum
  (many RmHere : (erased (Nat) x) (erased (List (Nat)) xs) -> (Remove x (Cons (Nat) x xs) xs))
  (many RmThere : (erased (Nat) x y) (erased (List (Nat)) xs ys) (erased (Remove x xs ys) p) -> (Remove x (Cons (Nat) y xs) (Cons (Nat) y ys))))

(def-fns _ $ (erased remove-exists : (erased (Nat) x) (erased (List (Nat)) xs) (subterm erased (In x xs) p) -> (erased (List (Nat)) ys) (erased (Remove x xs ys) r))
  (let-match erased p (InThere _ y xs1 p1) ((InHere _ xs1) (values xs1 (RmHere x xs1))))
  (let ((erased ys1) (erased r1)) (remove-exists x xs1 p1))
  (values (Cons _ y ys1) (RmThere x y xs1 ys1 r1)))

(def-fns _ $ (erased remove-src : (erased (Nat) x) (erased (List (Nat)) xs ys) (subterm erased (Remove x xs ys) rm) -> (erased (In x xs) r))
  (let-match erased rm (RmThere _ y xs1 ys1 rm1) ((RmHere _ xs1) (InHere x xs1)))
  (InThere x y xs1 (remove-src x xs1 ys1 rm1)))

(def-fns _ $ (erased remove-keep : (erased (Nat) x z) (erased (List (Nat)) xs ys) (subterm erased (Remove x xs ys) rm) (erased (In z xs) p)
    (erased (Apart (Nat) Lt z x) ne) -> (erased (In z ys) r))
  (match erased rm _
    ((RmHere _ _) (let-match erased p (InThere _ _ _ p1) (absurd (InHere _ _) (apart-irrefl x ne))) p1)
    ((RmThere _ y xs1 ys1 rm1)
      (let-match erased p (InThere _ _ _ p1) ((InHere _ _) (InHere z ys1)))
      (InThere z y ys1 (remove-keep x z xs1 ys1 rm1 p1 ne)))))

(def-fns _ $ (erased remove-in : (erased (Nat) x z) (erased (List (Nat)) xs ys) (subterm erased (Remove x xs ys) rm) (erased (In z ys) p)
    -> (erased (In z xs) r))
  (let-match erased rm (RmThere _ y xs1 ys1 rm1) ((RmHere _ _) (InThere z x ys p)))
  (let-match erased p (InThere _ _ _ p1) ((InHere _ _) (InHere z xs1)))
  (InThere z y xs1 (remove-in x z xs1 ys1 rm1 p1)))

(def-fns _ $ (erased notin-remove : (erased (Nat) x z) (erased (List (Nat)) xs ys) (subterm erased (Remove x xs ys) rm) (erased (NotIn z xs) p)
    -> (erased (NotIn z ys) r))
  (match erased rm _
    ((RmHere _ _) (let-match erased p (NotInCons _ _ _ _ p1)) p1)
    ((RmThere _ y xs1 ys1 rm1)
      (let-match erased p (NotInCons _ _ _ ne p1))
      (NotInCons z y ys1 ne (notin-remove x z xs1 ys1 rm1 p1)))))

(def-fns _ $ (erased remove-distinct : (erased (Nat) x) (erased (List (Nat)) xs ys) (subterm erased (Remove x xs ys) rm) (erased (Distinct xs) dx)
    -> (erased (Distinct ys) r))
  (match erased rm _
    ((RmHere _ _) (let-match erased dx (DistCons _ _ _ d1)) d1)
    ((RmThere _ y xs1 ys1 rm1)
      (let-match erased dx (DistCons _ _ p d1))
      (DistCons y ys1 (notin-remove x y xs1 ys1 rm1 p) (remove-distinct x xs1 ys1 rm1 d1)))))

(def-fns _ $ (erased remove-length : (erased (Nat) x m) (erased (List (Nat)) xs ys) (subterm erased (Remove x xs ys) rm) (erased (Length (Nat) ys m) l)
    -> (erased (Length (Nat) xs (Succ m)) r))
  (let-match erased rm (RmThere _ y xs1 ys1 rm1) ((RmHere _ _) (LengthCons _ x ys m l)))
  (let-match erased l (LengthCons _ _ _ m1 l1))
  (LengthCons _ y xs1 (Succ m1) (remove-length x m1 xs1 ys1 rm1 l1)))

(def-fns _ $ (erased fixed-redirect : (erased (Nat) a b) (erased (List (Nat)) lab lab2 ys) (subterm erased (Respects lab ys ys) fix)
    (erased (NotIn a ys) out) (erased (Redirect a b lab lab2) rd) -> (erased (Respects lab2 ys ys) r))
  (let-match erased fix (RespCons _ ys1 _ y _ p fix1) ((RespNil _) (RespNil lab2)))
  (let-match erased out (NotInCons _ _ _ ne out1))
  (RespCons lab2 ys1 ys1 y y (redirect-miss a b y y lab lab2 rd p (apart-sym a y ne)) (fixed-redirect a b lab lab2 ys1 fix1 out1 rd)))

(def-fns _ $ (erased fixed-remove : (erased (Nat) a b) (erased (List (Nat)) lab lab2 rs rs2) (subterm erased (Remove a rs rs2) rm)
    (erased (Respects lab rs rs) fix) (erased (Distinct rs) dr) (erased (Redirect a b lab lab2) rd) -> (erased (Respects lab2 rs2 rs2) r))
  (match erased rm _
    ((RmHere _ _)
      (let-match erased fix (RespCons _ _ _ _ _ _ fix1))
      (let-match erased dr (DistCons _ _ out _))
      (fixed-redirect a b lab lab2 rs2 fix1 out rd))
    ((RmThere _ y rs1 rs3 rm1)
      (let-match erased fix (RespCons _ _ _ _ _ p fix1))
      (let-match erased dr (DistCons _ _ out dr1))
      (RespCons lab2 rs3 rs3 y y (redirect-miss a b y y lab lab2 rd p (notin-in y a rs1 out (remove-src a rs1 rs3 rm1)))
        (fixed-remove a b lab lab2 rs1 rs3 rm1 fix1 dr1 rd)))))

; Merging the class rooted at a into the one rooted at b, which h joins to it.
(def-fns _ $ (erased rooted-merge : (erased (List (Bond)) g h) (erased (List (Nat)) rs rs2 xs ls ls2) (erased (Nat) a b)
    (subterm erased (Rooted g rs xs ls) ro) (erased (Redirect a b ls ls2) rd) (erased (Remove a rs rs2) rm)
    (erased (In b rs2) pb) (erased (Conn h b a) cba) (erased (Spans h g) sp) -> (erased (Rooted h rs2 xs ls2) res))
  (let-match erased ro (RootedCons _ _ xs1 ls1 x r pin c ro1) ((RootedNil _ _) (let-match erased rd (RdNil _ _)) (RootedNil h rs2)))
  (match erased rd _
    ((RdHit _ _ _ ls3 rd1)
      (RootedCons h rs2 xs1 ls3 x b pb (conn-cat h b a x cba (spans-conn h g a x c sp)) (rooted-merge g h rs rs2 xs1 ls1 ls3 a b ro1 rd1 rm pb cba sp)))
    ((RdMiss _ _ _ _ ls3 ne rd1)
      (RootedCons h rs2 xs1 ls3 x r (remove-keep a r rs rs2 rm pin ne) (spans-conn h g r x c sp)
        (rooted-merge g h rs rs2 xs1 ls1 ls3 a b ro1 rd1 rm pb cba sp)))))

(def-fns _ $ (erased roots-apart : (erased (List (Bond)) g) (erased (Nat) x y rx ry) (erased (Sep g x y) s)
    (erased (Conn g rx x) cx) (erased (Conn g ry y) cy) -> (erased (Apart (Nat) Lt rx ry) ne))
  (match erased (nat-cmp rx ry) _
    ((CLt _ _ _ _ l) (ApLt _ _ rx ry l))
    (absurd (CEq _ _ _) (sep-conn g x y s (conn-cat g x rx y (conn-sym g rx x cx) cy)))
    ((CGt _ _ _ _ l) (ApGt _ _ rx ry l))))

; A bond between two classes merges them.
(def-fns _ $ (erased classes-link-merge : (erased (List (Bond)) g) (erased (Nat) d k x y) (erased (Classes g d k) cs)
    (erased (Sep g x y) s) (erased (Lt x d) px) (erased (Lt y d) py)
    -> (erased (Nat) k1) (erased (Eq (Nat) k (Succ k1)) e) (erased (Classes (Cons (Bond) (MkBond x y) g) d k1) r))
  (let-match erased cs (MkClasses _ _ _ ids lab rs io ll lr dr fix cl ro))
  (let ((erased rx) (erased qx)) (nth-exists _ lab d x ll px))
  (let ((erased ry) (erased qy)) (nth-exists _ lab d y ll py))
  (let ((erased ix) (erased cx)) (classes-root g d ids lab rs x rx io ro qx px))
  (let ((erased iy) (erased cy)) (classes-root g d ids lab rs y ry io ro qy py))
  (let ((erased ne)) (roots-apart g x y rx ry s cx cy))
  (let ((erased lab2) (erased rd)) (redirect-exists ry rx lab))
  (let ((erased rs2) (erased rm)) (remove-exists ry rs iy))
  (let ((erased k1) (erased lr2)) (length-exists _ rs2))
  (let ((erased h)) (Cons (Bond) (MkBond x y) g))
  (let ((erased sp)) (spans-cons g g (MkBond x y) (spans-self g)))
  (let ((erased cxy)) (conn-adj h x y (AdjFwd g x y)))
  (values k1 (length-fn _ rs k (Succ k1) lr (remove-length ry k1 rs rs2 rm lr2))
    (MkClasses h d k1 ids lab2 rs2 io (redirect-length ry rx d lab lab2 rd ll) lr2 (remove-distinct ry rs rs2 rm dr)
      (fixed-remove ry rx lab lab2 rs rs2 rm fix dr rd)
      (ConstCons lab2 g x y rx (redirect-miss ry rx x rx lab lab2 rd qx ne) (redirect-hit ry rx y lab lab2 rd qy) (const-redirect ry rx lab lab2 g cl rd))
      (rooted-merge g h rs rs2 ids lab lab2 ry rx ro rd rm (remove-keep ry rx rs rs2 rm ix ne)
        (conn-cat h rx x ry (spans-conn h g rx x cx sp) (conn-cat h x y ry cxy (conn-sym h ry y (spans-conn h g ry y cy sp))))
        sp))))

; Every graph has a count of classes.
(def-fns _ $ (erased classes-exists : (erased (List (Bond)) g) (erased (Nat) d) (subterm erased (Below g d) bg) -> (erased (Nat) k) (erased (Classes g d k) r))
  (let-match erased bg (BelowCons g1 x y _ px py bg1) ((BelowNil _) (values d (classes-nil d))))
  (let ((erased k1) (erased cs1)) (classes-exists g1 d bg1))
  (let-match erased (classes-dec g1 d k1 x y cs1 px py) (OrR _ _ s)
    ((OrL _ _ c) (values k1 (classes-link-same g1 d k1 x y cs1 c px py))))
  (let ((erased k2) (erased e) (erased cs2)) (classes-link-merge g1 d k1 x y cs1 s px py))
  (values k2 cs2))

(def-fns _ $ (erased sub-remove : (erased (Nat) x) (erased (List (Nat)) m ys ys1) (subterm erased (Sub m ys) sb) (erased (NotIn x m) out)
    (erased (Remove x ys ys1) rm) -> (erased (Sub m ys1) r))
  (let-match erased sb (SubCons z m1 _ p sb1) ((SubNil _) (SubNil ys1)))
  (let-match erased out (NotInCons _ _ _ ne out1))
  (SubCons z m1 ys1 (remove-keep x z ys ys1 rm p (apart-sym x z ne)) (sub-remove x m1 ys ys1 sb1 out1 rm)))

; A list of distinct darts, all in ys, is no longer than ys.
(def-fns _ $ (erased pigeonhole : (erased (List (Nat)) xs ys) (erased (Nat) a b) (subterm erased (Distinct xs) dx) (erased (Sub xs ys) sb)
    (erased (Length (Nat) xs a) la) (erased (Length (Nat) ys b) lb) -> (erased (Lt a (Succ b)) r))
  (let-match erased dx (DistCons x xs1 out dx1) ((DistNil) (let-match erased la (LengthNil _)) (LtZ b)))
  (let-match erased sb (SubCons _ _ _ p sb1))
  (let-match erased la (LengthCons _ _ _ a1 la1))
  (let ((erased ys1) (erased rm)) (remove-exists x ys p))
  (let ((erased b1) (erased lb1)) (length-exists _ ys1))
  (let-match erased (length-fn _ ys b (Succ b1) lb (remove-length x b1 ys ys1 rm lb1)) (Refl _ _))
  (LtS a1 (Succ b1) (pigeonhole xs1 ys1 a1 b1 dx1 (sub-remove x xs1 ys ys1 sb1 out rm) la1 lb1)))

(def-fns _ $ (erased respects-length : (erased (List (Nat)) lab xs ls) (erased (Nat) n) (subterm erased (Respects lab xs ls) rp)
    (erased (Length (Nat) xs n) l) -> (erased (Length (Nat) ls n) r))
  (let-match erased rp (RespCons _ xs1 ls1 j v p rp1) ((RespNil _) (let-match erased l (LengthNil _)) (LengthNil _)))
  (let-match erased l (LengthCons _ _ _ n1 l1))
  (LengthCons _ v ls1 n1 (respects-length lab xs1 ls1 n1 rp1 l1)))

; The image ims of the darts rs, each below d, under a labelling of length d.
(def-fns _ $ (erased image-exists : (erased (List (Nat)) lab lab2 rs) (erased (Nat) d) (subterm erased (Respects lab rs rs) fix)
    (erased (Length (Nat) lab d) ll) (erased (Length (Nat) lab2 d) ll2) -> (erased (List (Nat)) ims) (erased (Respects lab2 rs ims) r))
  (let-match erased fix (RespCons _ rs1 _ j _ p fix1) ((RespNil _) (values (Nil _) (RespNil lab2))))
  (let ((erased s) (erased q)) (nth-exists _ lab2 d j ll2 (nth-lt-length _ lab j d j p ll)))
  (let ((erased ims1) (erased r1)) (image-exists lab lab2 rs1 d fix1 ll ll2))
  (values (Cons _ s ims1) (RespCons lab2 rs1 ims1 j s q r1)))

(def-fns _ $ (erased image-sub : (erased (List (Bond)) g) (erased (List (Nat)) lab2 rs rs2 ims ids) (erased (Nat) d)
    (subterm erased (Respects lab2 rs ims) rp) (erased (Iota d ids) io) (erased (Rooted g rs2 ids lab2) ro) (erased (Length (Nat) lab2 d) ll)
    -> (erased (Sub ims rs2) r))
  (let-match erased rp (RespCons _ rs1 ims1 j s q rp1) ((RespNil _) (SubNil rs2)))
  (let ((erased pin) (erased c)) (classes-root g d ids lab2 rs2 j s io ro q (nth-lt-length _ lab2 j d s q ll)))
  (SubCons s ims1 rs2 pin (image-sub g lab2 rs1 rs2 ims1 ids d rp1 io ro ll)))

; Distinct roots of lab have distinct roots under lab2, for two root labellings of g.
(def-fns _ $ (erased image-notin : (erased (List (Bond)) g) (erased (List (Nat)) lab lab2 rs rs2 ims ids) (erased (Nat) d r s)
    (subterm erased (Respects lab2 rs ims) rp) (erased (Respects lab rs rs) fix) (erased (NotIn r rs) out)
    (erased (Nth (Nat) lab r r) pr) (erased (Conn g s r) cs) (erased (Const lab g) cl)
    (erased (Iota d ids) io) (erased (Rooted g rs2 ids lab2) ro) (erased (Length (Nat) lab2 d) ll) -> (erased (NotIn s ims) res))
  (let-match erased rp (RespCons _ rs1 ims1 j s1 q rp1) ((RespNil _) (NotInNil s)))
  (let-match erased fix (RespCons _ _ _ _ _ pj fix1))
  (let-match erased out (NotInCons _ _ _ ne out1))
  (let ((erased rest)) (image-notin g lab lab2 rs1 rs2 ims1 ids d r s rp1 fix1 out1 pr cs cl io ro ll))
  (let ((erased pin) (erased cj)) (classes-root g d ids lab2 rs2 j s1 io ro q (nth-lt-length _ lab2 j d s1 q ll)))
  (match erased (nat-cmp s s1) _
    ((CLt _ _ _ _ l) (NotInCons s s1 ims1 (ApLt _ _ s s1 l) rest))
    (absurd (CEq _ _ _)
      (let-match erased (nth-fn _ lab j r j (conn-const lab g r j r (conn-cat g r s j (conn-sym g s r cs) cj) cl pr) pj) (Refl _ _))
      (apart-irrefl r ne))
    ((CGt _ _ _ _ l) (NotInCons s s1 ims1 (ApGt _ _ s s1 l) rest))))

(def-fns _ $ (erased image-distinct : (erased (List (Bond)) g) (erased (List (Nat)) lab lab2 rs rs2 ims ids) (erased (Nat) d)
    (subterm erased (Respects lab2 rs ims) rp) (erased (Respects lab rs rs) fix) (erased (Distinct rs) dr) (erased (Const lab g) cl)
    (erased (Iota d ids) io) (erased (Rooted g rs2 ids lab2) ro) (erased (Length (Nat) lab2 d) ll) -> (erased (Distinct ims) res))
  (let-match erased rp (RespCons _ rs1 ims1 j s q rp1) ((RespNil _) (DistNil)))
  (let-match erased fix (RespCons _ _ _ _ _ pj fix1))
  (let-match erased dr (DistCons _ _ out dr1))
  (let ((erased pin) (erased cj)) (classes-root g d ids lab2 rs2 j s io ro q (nth-lt-length _ lab2 j d s q ll)))
  (DistCons s ims1 (image-notin g lab lab2 rs1 rs2 ims1 ids d j s rp1 fix1 out pj cj cl io ro ll)
    (image-distinct g lab lab2 rs1 rs2 ims1 ids d rp1 fix1 dr1 cl io ro ll)))

(def-fns _ $ (erased classes-le : (erased (List (Bond)) g) (erased (Nat) d k1 k2) (erased (Classes g d k1) c1) (erased (Classes g d k2) c2)
    -> (erased (Lt k1 (Succ k2)) r))
  (let-match erased c1 (MkClasses _ _ _ ids lab rs io ll lr dr fix cl ro))
  (let-match erased c2 (MkClasses _ _ _ ids2 lab2 rs2 io2 ll2 lr2 dr2 fix2 cl2 ro2))
  (let-match erased (iota-fn d ids ids2 io io2) (Refl _ _))
  (let ((erased ims) (erased rp)) (image-exists lab lab2 rs d fix ll ll2))
  (pigeonhole ims rs2 k1 k2 (image-distinct g lab lab2 rs rs2 ims ids d rp fix dr cl io ro2 ll2)
    (image-sub g lab2 rs rs2 ims ids d rp io ro2 ll2) (respects-length lab2 rs ims k1 rp lr) lr2))

; The count of classes is determined by the graph.
(def-fns _ $ (erased classes-unique : (erased (List (Bond)) g) (erased (Nat) d k1 k2) (erased (Classes g d k1) c1) (erased (Classes g d k2) c2)
    -> (erased (Eq (Nat) k1 k2) e))
  (let ((erased l12)) (classes-le g d k1 k2 c1 c2))
  (let ((erased l21)) (classes-le g d k2 k1 c2 c1))
  (match erased (nat-cmp k1 k2) _
    (absurd (CLt _ _ _ _ l) (lt-asym k1 k2 l l21))
    ((CEq _ _ _) (Refl _ k1))
    (absurd (CGt _ _ _ _ l) (lt-asym k2 k1 l l12))))
