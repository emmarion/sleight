(let ((erased Cnt)) (U8))

(let ((erased flag-w) (erased cnt-w) (erased rcd-w)) (values (Succ (Zero)) (Succ (Succ (Zero))) (Succ (Succ (Succ (Succ (Zero)))))))

; Entry i of us, the w bytes from w i, holds n, low byte first.
(def-adts $ (Elt : ((Nat) w) ((List (U8)) us) ((Nat) i) ((Nat) n) -> Type)
  enum
  (many MkElt : (erased (Nat) w) (erased (List (U8)) us) (erased (Nat) i q n) (erased (Mul i w q) m) (erased (List (U8)) ds)
      (erased (Splice (U8) us q w ds us) s) (erased (LE ds n) le) -> (Elt w us i n)))

; vs is us with entry i set to n.
(def-adts $ (Put : ((Nat) w) ((List (U8)) us) ((Nat) i) ((Nat) n) ((List (U8)) vs) -> Type)
  enum
  (many MkPut : (erased (Nat) w) (erased (List (U8)) us vs) (erased (Nat) i q n) (erased (Mul i w q) m) (erased (List (U8)) ds)
      (erased (Splice (U8) us q w ds vs) s) (erased (LE ds n) le) -> (Put w us i n vs)))

; us holds len entries of w bytes, w at least 1, in fewer than 2^62 bytes.
(def-adts $ (Sz : ((Nat) w) ((List (U8)) us) ((Nat) len) -> Type)
  enum
  (many MkSz : (erased (Nat) w) (erased (List (U8)) us) (erased (Nat) len bl) (erased (Lt (Zero) w) wp) (erased (Mul len w bl) m)
      (erased (Length (U8) us bl) l) (erased (Lt bl u62-modulus) b) -> (Sz w us len)))

; Every entry of us is v.
(def-adts $ (Fill : ((Nat) w) ((List (U8)) us) ((Nat) v) -> Type)
  enum
  (many MkFill : (erased (Nat) w) (erased (List (U8)) us) (erased (Nat) bl v) (erased (U8) x) (erased (Repeat (U8) bl x us) rp) (erased (List (U8)) ds)
      (erased (Repeat (U8) w x ds) rd) (erased (LE ds v) le) -> (Fill w us v)))

(def-fns _ $ (erased le-fn : (erased (List Cnt) ds) (erased (Nat) n m) (subterm erased (LE ds n) a) (erased (LE ds m) b) -> (erased (Eq (Nat) n m) e))
  (let-match erased a (LEByte d w k _ _ ds1 a1 ma aa) ((LEEnd) (let-match erased b (LEEnd)) (Refl _ n)))
  (let-match erased b (LEByte _ w2 k2 _ _ _ b1 mb ab))
  (let-match erased (le-fn ds1 w w2 a1 b1) (Refl _ _))
  (let-match erased (mul-fn w u8-modulus k k2 ma mb) (Refl _ _))
  (let-match erased (add-fn k d n m aa ab) (Refl _ _))
  (Refl _ n))

(def-fns _ $ (erased le-exists : (subterm erased (List Cnt) ds) -> (erased (Nat) v) (erased (LE ds v) p))
  (let-match erased ds (Cons _ x ds1) ((Nil _) (values (Zero) (LEEnd))))
  (let-match erased x (MkU8 d pd))
  (let ((erased w) (erased p1)) (le-exists ds1))
  (let ((erased k) (erased mm)) (mul w u8-modulus))
  (let ((erased v) (erased a)) (add k d))
  (values v (LEByte d w k v pd ds1 p1 mm a)))

(def-fns _ $ (erased le-one : (erased (U8) b) (erased (Nat) v) (erased (LE (Cons (U8) b (Nil (U8))) v) p) -> (erased (Lt v u8-modulus) vb) (erased (Eq (U8) b (MkU8 v vb)) e))
  (let-match erased p (LEByte d _ _ _ pd _ p1 mm a))
  (let-match erased p1 (LEEnd))
  (let-match erased mm (MulZero _))
  (let-match erased a (AddZero _))
  (values pd (Refl _ b)))

(def-fns _ $ (erased splice-fn : (erased Type A) (erased (List A) xs ys zs) (erased (Nat) i n) (subterm erased (Splice A xs i n ys xs) p)
    (erased (Splice A xs i n zs xs) q) -> (erased (Eq (List A) ys zs) e))
  (match erased p _
    ((SpliceNil _ _) (let-match erased q (SpliceNil _ _)) (Refl _ ys))
    ((SpliceHere _ _ y xs1 n1 ys1 _ p1)
      (let-match erased q (SpliceHere _ _ _ _ _ zs1 _ q1))
      (let-match erased (splice-fn A xs1 ys1 zs1 (Zero) n1 p1 q1) (Refl _ _))
      (Refl _ ys))
    ((SpliceThere _ _ xs1 k1 _ _ _ p1)
      (let-match erased q (SpliceThere _ _ _ _ _ _ _ q1))
      (splice-fn A xs1 ys zs k1 n p1 q1))))

(def-fns _ $ (erased splice-end : (erased Type A) (erased (List A) xs ys zs) (erased (Nat) i n e len) (subterm erased (Splice A xs i n ys zs) p)
    (erased (Length A xs len) l) (erased (Add i n e) a) -> (erased (Lt e (Succ len)) r))
  (match erased p _
    ((SpliceNil _ _) (let-match erased a (AddZero _)) (LtZ len))
    ((SpliceHere _ _ _ xs1 n1 _ _ p1)
      (let-match erased a (AddZero _))
      (let-match erased l (LengthCons _ _ _ len1 l1))
      (LtS _ _ (splice-end A xs1 _ _ (Zero) n1 n1 len1 p1 l1 (AddZero n1))))
    ((SpliceThere _ _ xs1 ix _ _ _ p1)
      (let-match erased a (AddSucc _ _ e1 a1))
      (let-match erased l (LengthCons _ _ _ len1 l1))
      (LtS _ _ (splice-end A xs1 ys _ ix n e1 len1 p1 l1 a1)))))

; A splice writing [i, e) leaves a read of [k, k + m) alone when e is at most k.
(def-fns _ $ (erased splice-after : (erased Type A) (erased (List A) xs ys zs ds) (erased (Nat) i n e k m) (subterm erased (Splice A xs i n ys zs) w)
    (erased (Splice A xs k m ds xs) r) (erased (Add i n e) a) (erased (Lt e (Succ k)) l) -> (erased (Splice A zs k m ds zs) q))
  (match erased w _
    ((SpliceNil _ _) r)
    ((SpliceHere _ x y xs1 n1 ys1 zs1 w1)
      (let-match erased a (AddZero _))
      (let-match erased l (LtS _ _ l1))
      (let-match erased r (SpliceThere _ _ _ k1 _ _ _ r1) (absurd (SpliceNil _ _) l1) (absurd (SpliceHere _ _ _ _ _ _ _ _) l1))
      (SpliceThere A y zs1 k1 m ds zs1 (splice-after A xs1 ys1 zs1 ds (Zero) n1 n1 k1 m w1 r1 (AddZero n1) l1)))
    ((SpliceThere _ x xs1 j1 _ _ zs1 w1)
      (let-match erased a (AddSucc _ _ e1 a1))
      (let-match erased l (LtS _ _ l1))
      (let-match erased r (SpliceThere _ _ _ k1 _ _ _ r1) (absurd (SpliceNil _ _) l1) (absurd (SpliceHere _ _ _ _ _ _ _ _) l1))
      (SpliceThere A x zs1 k1 m ds zs1 (splice-after A xs1 ys zs1 ds j1 n e1 k1 m w1 r1 a1 l1)))))

; A splice writing from i leaves a read of [k, f) alone when f is at most i.
(def-fns _ $ (erased splice-before : (erased Type A) (erased (List A) xs ys zs ds) (erased (Nat) i n k m f) (erased (Splice A xs i n ys zs) w)
    (subterm erased (Splice A xs k m ds xs) r) (erased (Add k m f) a) (erased (Lt f (Succ i)) l) -> (erased (Splice A zs k m ds zs) q))
  (match erased r _
    ((SpliceNil _ _) (SpliceNil A zs))
    ((SpliceHere _ x _ xs1 m1 ds1 _ r1)
      (let-match erased a (AddZero _))
      (let-match erased l (LtS _ _ l1))
      (let-match erased w (SpliceThere _ _ _ k1 _ _ zs1 w1) (absurd (SpliceNil _ _) l1) (absurd (SpliceHere _ _ _ _ _ _ _ _) l1))
      (SpliceHere A x x zs1 m1 ds1 zs1 (splice-before A xs1 ys zs1 ds1 k1 n (Zero) m1 m1 w1 r1 (AddZero m1) l1)))
    ((SpliceThere _ x xs1 k1 _ _ _ r1)
      (let-match erased a (AddSucc _ _ f1 a1))
      (let-match erased l (LtS _ _ l1))
      (let-match erased w (SpliceThere _ _ _ j1 _ _ zs1 w1) (absurd (SpliceNil _ _) l1) (absurd (SpliceHere _ _ _ _ _ _ _ _) l1))
      (SpliceThere A x zs1 k1 m ds zs1 (splice-before A xs1 ys zs1 ds j1 n k1 m f1 w1 r1 a1 l1)))))

(def-fns _ $ (erased splice-length : (erased Type A) (erased (List A) xs ys zs) (erased (Nat) i n L) (subterm erased (Splice A xs i n ys zs) p)
    (erased (Length A xs L) l) -> (erased (Length A zs L) r))
  (match erased p _
    ((SpliceNil _ _) l)
    ((SpliceHere _ x y xs1 n1 ys1 zs1 p1) (let-match erased l (LengthCons _ _ _ L1 l1)) (LengthCons A y zs1 L1 (splice-length A xs1 ys1 zs1 (Zero) n1 L1 p1 l1)))
    ((SpliceThere _ x xs1 k1 _ _ zs1 p1) (let-match erased l (LengthCons _ _ _ L1 l1)) (LengthCons A x zs1 L1 (splice-length A xs1 ys zs1 k1 n L1 p1 l1)))))

(def-fns _ $ (erased repeat-splice : (erased Type A) (erased (List A) xs ds) (erased (Nat) L q m) (erased A x) (erased (Repeat A L x xs) rp)
    (subterm erased (Splice A xs q m ds xs) p) -> (erased (Repeat A m x ds) r))
  (match erased p _
    ((SpliceNil _ _) (RepeatNil A x))
    ((SpliceHere _ _ _ xs1 m1 ds1 _ p1) (let-match erased rp (RepeatCons _ L1 _ _ rp1)) (RepeatCons A m1 x ds1 (repeat-splice A xs1 ds1 L1 (Zero) m1 x rp1 p1)))
    ((SpliceThere _ _ xs1 q1 _ _ _ p1) (let-match erased rp (RepeatCons _ L1 _ _ rp1)) (repeat-splice A xs1 ds L1 q1 m x rp1 p1))))

(def-fns _ $ (erased splice-nth : (erased Type A) (erased (List A) xs ys zs) (erased (Nat) i n) (erased A y) (subterm erased (Splice A xs i (Succ n) (Cons A y ys) zs) p)
    -> (erased (Nth A zs i y) r))
  (match erased p _
    ((SpliceHere _ _ _ _ _ _ zs1 _) (NthHere A y zs1))
    ((SpliceThere _ x xs1 ix _ _ zs1 p1) (NthThere A x zs1 ix y (splice-nth A xs1 ys zs1 ix n y p1)))))

(def-fns _ $ (erased setnth-splice : (erased Type A) (erased (List A) xs ys) (erased (Nat) i) (erased A y) (subterm erased (SetNth A xs i y ys) p)
    -> (erased (Splice A xs i (Succ (Zero)) (Cons A y (Nil A)) ys) r))
  (match erased p _
    ((SetHere _ x _ rest) (SpliceHere A x y rest (Zero) (Nil A) rest (SpliceNil A rest)))
    ((SetThere _ x rest k _ rest2 p1) (SpliceThere A x rest k (Succ (Zero)) (Cons A y (Nil A)) rest2 (setnth-splice A rest rest2 k y p1)))))

(def-fns _ $ (erased splice-cons : (erased Type A) (erased (List A) xs ys zs ds) (erased (Nat) i n) (erased A a)
    (subterm erased (Splice A xs i (Succ (Zero)) (Cons A a (Nil A)) ys) p) (erased (Splice A ys (Succ i) n ds zs) q) -> (erased (Splice A xs i (Succ n) (Cons A a ds) zs) r))
  (match erased p _
    ((SpliceHere _ x _ xs1 _ _ _ p1)
      (let-match erased p1 (SpliceNil _ _))
      (let-match erased q (SpliceThere _ _ _ _ _ _ zs1 q1))
      (SpliceHere A x a xs1 n ds zs1 q1))
    ((SpliceThere _ x xs1 ix _ _ ys1 p1)
      (let-match erased q (SpliceThere _ _ _ _ _ _ zs1 q1))
      (SpliceThere A x xs1 ix (Succ n) (Cons A a ds) zs1 (splice-cons A xs1 ys1 zs1 ds ix n a p1 q1)))))

(def-fns _ $ (erased elt-fn : (erased (Nat) w) (erased (List (U8)) us) (erased (Nat) i n m) (erased (Elt w us i n) a) (erased (Elt w us i m) b) -> (erased (Eq (Nat) n m) e))
  (let-match erased a (MkElt _ _ _ q _ ma ds sa la))
  (let-match erased b (MkElt _ _ _ q2 _ mb es sb lb))
  (let-match erased (mul-fn i w q q2 ma mb) (Refl _ _))
  (let-match erased (splice-fn _ us ds es q w sa sb) (Refl _ _))
  (le-fn ds n m la lb))

(def-fns _ $ (erased elt-bound : (erased (Nat) w) (erased (List (U8)) us) (erased (Nat) i n e c) (erased (Elt w us i n) a) (erased (Mul w eight e) me) (erased (Pow2 e c) pc)
    -> (erased (Lt n c) r))
  (let-match erased a (MkElt _ _ _ q _ _ ds s le))
  (le-bound ds n w e c le (splice-ys-length _ us ds us q w s) me pc))

(def-fns _ $ (erased put-elt : (erased (Nat) w) (erased (List (U8)) us vs) (erased (Nat) i n) (erased (Put w us i n vs) u) -> (erased (Elt w vs i n) e))
  (let-match erased u (MkPut _ _ _ _ q _ m ds s le))
  (MkElt w vs i q n m ds (splice-reread _ us ds vs q w s) le))

(def-fns _ $ (erased mul-next : (erased (Nat) i w q) (erased (Mul i w q) m) -> (erased (Nat) e) (erased (Add q w e) a) (erased (Mul (Succ i) w e) me))
  (let ((erased e) (erased me)) (mul (Succ i) w))
  (let-match erased me (MulSucc _ _ q2 _ m2 a))
  (let-match erased (mul-fn i w q q2 m m2) (Refl _ _))
  (values e a me))

(def-fns _ $ (erased put-other : (erased (Nat) w) (erased (List (U8)) us vs) (erased (Nat) j n i m) (erased (Put w us j n vs) u) (erased (Apart (Nat) Lt j i) ap)
    (erased (Elt w us i m) e) -> (erased (Elt w vs i m) r))
  (let-match erased u (MkPut _ _ _ _ q _ mq ds s _))
  (let-match erased e (MkElt _ _ _ k _ mk es t le))
  (MkElt w vs i k m mk es
    (match erased ap _
      ((ApLt _ _ _ _ l)
        (let ((erased f) (erased af) (erased mf)) (mul-next j w q mq))
        (splice-after _ us ds vs es q w f k w s t af (mul-le-mono (Succ j) i w f k (LtS _ _ l) mf mk)))
      ((ApGt _ _ _ _ l)
        (let ((erased f) (erased af) (erased mf)) (mul-next i w k mk))
        (splice-before _ us ds vs es q w k w f s t af (mul-le-mono (Succ i) j w f q (LtS _ _ l) mf mq))))
    le))

(def-fns _ $ (erased put-sz : (erased (Nat) w) (erased (List (U8)) us vs) (erased (Nat) i n len) (erased (Put w us i n vs) u) (erased (Sz w us len) z)
    -> (erased (Sz w vs len) r))
  (let-match erased u (MkPut _ _ _ _ q _ _ ds s _))
  (let-match erased z (MkSz _ _ _ bl wp m l b))
  (MkSz w vs len bl wp m (splice-length _ us ds vs q w bl s l) b))

(def-fns _ $ (erased elt-end : (erased (Nat) w) (erased (List (U8)) us) (erased (Nat) i n q len) (erased (Elt w us i n) a) (erased (Mul i w q) mq) (erased (Sz w us len) z)
    -> (erased (Nat) e) (erased (Add q w e) ae) (erased (Lt e u62-modulus) eb))
  (let-match erased a (MkElt _ _ _ q2 _ m2 ds s _))
  (let-match erased (mul-fn i w q q2 mq m2) (Refl _ _))
  (let-match erased z (MkSz _ _ _ bl _ _ l b))
  (let ((erased e) (erased ae) (erased _)) (mul-next i w q mq))
  (values e ae (lt-le-trans e (Succ bl) u62-modulus (splice-end _ us ds us q w e bl s l ae) (LtS _ _ b))))

(def-fns _ $ (erased elt-lt : (erased (Nat) w) (erased (List (U8)) us) (erased (Nat) i n len) (erased (Elt w us i n) a) (erased (Sz w us len) z) -> (erased (Lt i len) r))
  (let-match erased a (MkElt _ _ _ q _ m ds s _))
  (let-match erased z (MkSz _ _ _ bl wp ml l _))
  (let ((erased e) (erased ae) (erased _)) (mul-next i w q m))
  (let ((erased qe)) (add-pos-lt q w e ae wp))
  (let ((erased eb)) (splice-end _ us ds us q w e bl s l ae))
  (let-match erased (nat-cmp i len) (CLt _ _ _ _ c)
    (absurd (CEq _ _ _) (lt-irrefl q (lt-le-trans q e q qe (le-trans e bl q eb (mul-le-mono len i w bl q (lt-succ i) ml m)))))
    (absurd (CGt _ _ _ _ c) (lt-irrefl q (lt-le-trans q e q qe (le-trans e bl q eb (mul-le-mono len i w bl q (lt-weaken _ _ c) ml m))))))
  c)

(def-fns _ $ (erased elt-exists : (erased (Nat) w) (erased (List (U8)) us) (erased (Nat) len i) (erased (Sz w us len) z) (erased (Lt i len) il)
    -> (erased (Nat) n) (erased (Elt w us i n) e))
  (let-match erased z (MkSz _ _ _ bl _ ml l _))
  (let ((erased e) (erased me)) (mul (Succ i) w))
  (let-match erased me (MulSucc _ _ q _ mq ae))
  (let ((erased ds) (erased s)) (splice-range _ us bl l q w e ae (mul-le-mono (Succ i) len w e bl (LtS _ _ il) me ml)))
  (let ((erased n) (erased le)) (le-exists ds))
  (values n (MkElt w us i q n mq ds s le)))

(def-fns _ $ (erased fill-elt : (erased (Nat) w) (erased (List (U8)) us) (erased (Nat) len v i) (erased (Fill w us v) f) (erased (Sz w us len) z) (erased (Lt i len) il)
    -> (erased (Elt w us i v) e))
  (let-match erased f (MkFill _ _ bl _ x rp ds rd le))
  (let ((erased n) (erased e)) (elt-exists w us len i z il))
  (let-match erased e (MkElt _ _ _ q _ _ es s le2))
  (let-match erased (repeat-fn _ w x es ds (repeat-splice _ us es bl q w x rp s) rd) (Refl _ _))
  (let-match erased (le-fn es n v le2 le) (Refl _ _))
  e)

(def-fns _ $ (erased sz-u62 : (erased (Nat) w) (erased (List (U8)) us) (erased (Nat) len) (erased (Sz w us len) z) -> (erased (Lt len u62-modulus) r))
  (let-match erased z (MkSz _ _ _ bl wp m _ b))
  (lt-le-trans len (Succ bl) u62-modulus (mul-le len w bl m wp) (LtS _ _ b)))

(def-fns _ $ (erased sz-made : (erased (Nat) w len bl) (erased (U8) x) (erased (List (U8)) us) (erased (Repeat (U8) bl x us) rp) (erased (Lt (Zero) w) wp)
    (erased (Mul len w bl) m) (erased (Lt bl u62-modulus) b) -> (erased (Sz w us len) z))
  (MkSz w us len bl wp m (repeat-length _ bl x us rp) b))

(def-fns _ $ (erased zeros : (subterm erased (Nat) w) -> (erased (List (U8)) ds) (erased (Repeat (U8) w (MkU8 (Zero) u8-modulus-pos) ds) rd) (erased (LE ds (Zero)) le))
  (let-match erased w (Succ w1) ((Zero) (values (Nil _) (RepeatNil _ _) (LEEnd))))
  (let ((erased ds) (erased rd) (erased le)) (zeros w1))
  (values (Cons _ (MkU8 (Zero) u8-modulus-pos) ds) (RepeatCons _ w1 _ ds rd) (LEByte (Zero) (Zero) (Zero) (Zero) u8-modulus-pos ds le (MulZero u8-modulus) (AddZero (Zero)))))

(def-fns _ $ (erased fill-zero : (erased (Nat) w bl) (erased (List (U8)) us) (erased (Repeat (U8) bl (MkU8 (Zero) u8-modulus-pos) us) rp) -> (erased (Fill w us (Zero)) f))
  (let ((erased ds) (erased rd) (erased le)) (zeros w))
  (MkFill w us bl (Zero) _ rp ds rd le))

(def-fns _ $ (erased le-byte : (erased (Nat) v) (erased (Lt v u8-modulus) vb) -> (erased (LE (Cons (U8) (MkU8 v vb) (Nil (U8))) v) le))
  (LEByte v (Zero) (Zero) v vb (Nil _) (LEEnd) (MulZero u8-modulus) (AddZero v)))

(def-fns _ $ (erased fill-flag : (erased (Nat) bl v) (erased (Lt v u8-modulus) vb) (erased (List (U8)) us) (erased (Repeat (U8) bl (MkU8 v vb) us) rp) -> (erased (Fill flag-w us v) f))
  (MkFill flag-w us bl v _ rp (Cons _ (MkU8 v vb) (Nil _)) (RepeatCons _ _ _ _ (RepeatNil _ _)) (le-byte v vb)))

(def-fns _ $ (erased mul-two : (erased (Nat) i q) (subterm erased (Mul i cnt-w q) m) -> (erased (Add i i q) a))
  (let-match erased m (MulSucc ix _ q1 _ m1 a1) ((MulZero _) (AddZero (Zero))))
  (let-match erased (add-fn q1 cnt-w q (Succ (Succ q1)) a1 (add-succ-right q1 (Succ (Zero)) (Succ q1) (add-succ-right q1 (Zero) q1 (add-zero-right q1)))) (Refl _ _))
  (AddSucc ix (Succ ix) (Succ q1) (add-succ-right ix ix q1 (mul-two ix q1 m1))))

(def-fns _ $ (erased two-mul : (erased (Nat) i q) (erased (Add i i q) a) -> (erased (Mul i cnt-w q) m))
  (let ((erased q2) (erased m)) (mul i cnt-w))
  (let-match erased (add-fn i i q q2 a (mul-two i q2 m)) (Refl _ _))
  m)

(def-fns _ $ (erased mul-flag : (erased (Nat) i q) (erased (Mul i flag-w q) m) -> (erased (Eq (Nat) i q) e))
  (mul-fn i flag-w i q (mul-one-right i) m))

(def-fns _ $ (erased byte-of : (erased (List (U8)) us ds vs) (erased (Nat) i q v) (erased (Mul i flag-w q) m) (erased (Splice (U8) us q flag-w ds vs) s) (erased (LE ds v) le)
    -> (erased (Lt v u8-modulus) vb) (erased (Splice (U8) us i flag-w (Cons (U8) (MkU8 v vb) (Nil (U8))) vs) r))
  (let-match erased (mul-flag i q m) (Refl _ _))
  (let-match erased (splice-ys-length _ us ds vs i _ s) (LengthCons _ b ys _ l1))
  (let-match erased l1 (LengthNil _))
  (let ((erased vb) (erased eb)) (le-one b v le))
  (let-match erased eb (Refl _ _))
  (values vb s))

(def-fns _ $ (erased flag-nth : (erased (List (U8)) us) (erased (Nat) i v) (erased (Elt flag-w us i v) a) -> (erased (Lt v u8-modulus) vb) (erased (Nth (U8) us i (MkU8 v vb)) x))
  (let-match erased a (MkElt _ _ _ q _ m ds s le))
  (let ((erased vb) (erased s1)) (byte-of us ds us i q v m s le))
  (values vb (splice-nth _ us (Nil (U8)) us i (Zero) _ s1)))

(def-fns _ $ (erased flag-splice : (erased (List (U8)) us vs) (erased (Nat) i v) (erased (Put flag-w us i v vs) u)
    -> (erased (Lt v u8-modulus) vb) (erased (Splice (U8) us i flag-w (Cons (U8) (MkU8 v vb) (Nil (U8))) vs) s))
  (let-match erased u (MkPut _ _ _ _ q _ m ds s le))
  (byte-of us ds vs i q v m s le))

(def-fns _ $ (erased flag-put : (erased (List (U8)) us vs) (erased (Nat) i v) (erased (Lt v u8-modulus) vb) (erased (SetNth (U8) us i (MkU8 v vb) vs) s)
    -> (erased (Put flag-w us i v vs) u))
  (MkPut flag-w us vs i i v (mul-one-right i) (Cons _ (MkU8 v vb) (Nil _)) (setnth-splice _ us vs i _ s) (le-byte v vb)))

(def-fns _ $ (erased flag-length : (erased (List (U8)) us) (erased (Nat) len) (erased (Sz flag-w us len) z) -> (erased (Length (U8) us len) l))
  (let-match erased z (MkSz _ _ _ bl _ m l _))
  (let-match erased (mul-flag len bl m) (Refl _ _))
  l)

(def-fns _ $ (erased sz-regroup : (erased (Nat) w n bl) (erased (List (U8)) us) (erased (Sz flag-w us bl) z) (erased (Mul n w bl) m) (erased (Lt (Zero) w) wp)
    -> (erased (Sz w us n) r))
  (let-match erased z (MkSz _ _ _ bl2 _ m2 l b))
  (let-match erased (mul-flag bl bl2 m2) (Refl _ _))
  (MkSz w us n bl wp m l b))

(def-fns _ $ (erased rcd-last : (erased (List (U8)) xl) (erased (Nat) i wv e len) (erased (Elt rcd-w xl i wv) x) (erased (Mul i rcd-w e) ie) (erased (Sz rcd-w xl len) z)
    -> (erased (Lt (Succ (Succ (Succ e))) u62-modulus) r))
  (let ((erased f) (erased af) (erased fb)) (elt-end rcd-w xl i wv e len x ie z))
  (let-match erased (add-fn e rcd-w f (Succ (Succ (Succ (Succ e)))) af (add-succ-right e _ _ (add-succ-right e _ _ (add-succ-right e _ _ (add-succ-right e _ _ (add-zero-right e)))))) (Refl _ _))
  (lt-succ-left _ _ fb))

(def-fns _ $ (erased elt-q : (erased (Nat) w) (erased (List (U8)) us) (erased (Nat) i n q len) (erased (Elt w us i n) a) (erased (Mul i w q) mq) (erased (Sz w us len) z)
    -> (erased (Lt q u62-modulus) r))
  (let ((erased e) (erased ae) (erased eb)) (elt-end w us i n q len a mq z))
  (let-match erased z (MkSz _ _ _ _ wp _ _ _))
  (lt-trans q e u62-modulus (add-pos-lt q w e ae wp) eb))

(def-fns _ $ (many u16m-c : -> (many u16-modulus is r))
  (let ((many k) (erased pk)) (mul (Succ (Succ (Zero))) eight))
  (let-match erased (mul-fn _ _ _ _ pk sixteen-mul) (Refl _ _))
  (let ((many v) (erased pv) (erased _)) (pow2 k))
  (let-match erased (pow2-fn _ _ _ pv u16-modulus-pow2) (Refl _ _))
  v)

(let ((many u16m)) (u16m-c))
(comptime-match many (lt-dec (Zero) u16m) (Yes _ _ _ _ u16-pos))

(def-fns _ $ (many cnt-put : (erased (List Cnt) us) (unique (Bytes us) a) (erased (Nat) len) (erased (Sz cnt-w us len) z) (many (Nat) i) (erased (Lt i len) il)
    (many (Nat) v) (erased (Lt v u16-modulus) vb) ->
    (erased (List Cnt) us2) (unique (Bytes us2) a2 at a) (erased (Put cnt-w us i v us2) u) (erased (Sz cnt-w us2 len) z2))
  (let ((erased n) (erased e)) (elt-exists cnt-w us len i z il))
  (let-match erased e (MkElt _ _ _ q _ m ds s _))
  (let ((erased ds2) (erased us2) (unique a2) (erased s2) (erased le2)) (bytes-set16 us ds a (u62-add i i q (mul-two i q m) (elt-q cnt-w us i n q len e m z)) v s vb))
  (let ((erased u)) (MkPut cnt-w us us2 i q v m ds2 s2 le2))
  (values us2 a2 u (put-sz cnt-w us us2 i v len u z)))

(def-fns _ $ (many cnt-get : (erased (List Cnt) us) (unique (Bytes us) a) (erased (Nat) len) (erased (Sz cnt-w us len) z) (many (Nat) i) (erased (Nat) v)
    (erased (Elt cnt-w us i v) x) -> (unique a is a2 at a) (many v is k))
  (let-match erased x (MkElt _ _ _ q _ m ds s le))
  (let ((many k) (unique a2)) (bytes-get16 _ _ a (u62-add i i q (mul-two i q m) (elt-q cnt-w us i v q len x m z)) s v le))
  (values a2 k))

(def-fns _ $ (many cnt-get-many : (erased (List Cnt) us) (many (Bytes us) a) (erased (Nat) len) (erased (Sz cnt-w us len) z) (many (Nat) i) (erased (Nat) v)
    (erased (Elt cnt-w us i v) x) -> (many v is k))
  (let-match erased x (MkElt _ _ _ q _ m ds s le))
  (bytes-get16-many _ _ a (u62-add i i q (mul-two i q m) (elt-q cnt-w us i v q len x m z)) s v le))

; q is 3p.
(def-adts $ (Thrice : ((Nat) p) ((Nat) q) -> Type)
  enum
  (many TZ : -> (Thrice (Zero) (Zero)))
  (many TS : (erased (Nat) p q) (erased (Thrice p q) t) -> (Thrice (Succ p) (Succ (Succ (Succ q))))))

(def-fns _ $ (erased thrice-exists : (subterm erased (Nat) p) -> (erased (Nat) q) (erased (Thrice p q) t))
  (let-match erased p (Succ p1) ((Zero) (values (Zero) (TZ))))
  (let ((erased q1) (erased t1)) (thrice-exists p1))
  (values (Succ (Succ (Succ q1))) (TS p1 q1 t1)))

(def-fns _ $ (erased thrice-fn : (erased (Nat) p q r) (subterm erased (Thrice p q) s) (erased (Thrice p r) t) -> (erased (Eq (Nat) q r) e))
  (let-match erased s (TS p1 q1 s1) ((TZ) (let-match erased t (TZ)) (Refl _ q)))
  (let-match erased t (TS _ r1 t1))
  (let-match erased (thrice-fn p1 q1 r1 s1 t1) (Refl _ _))
  (Refl _ q))

(def-fns _ $ (erased thrice-adds : (erased (Nat) p q) (subterm erased (Thrice p q) t) ->
    (erased (Nat) d) (erased (Add p p d) a) (erased (Add d p q) b))
  (let-match erased t (TS p1 q1 t1) ((TZ) (values (Zero) (AddZero (Zero)) (AddZero (Zero)))))
  (let ((erased d1) (erased a1) (erased b1)) (thrice-adds p1 q1 t1))
  (values (Succ (Succ d1)) (AddSucc p1 p (Succ d1) (add-succ-right p1 p1 d1 a1))
    (AddSucc (Succ d1) p (Succ (Succ q1)) (AddSucc d1 p (Succ q1) (add-succ-right d1 p1 q1 b1)))))

(def-fns _ $ (erased adds-thrice : (erased (Nat) p d q) (erased (Add p p d) a) (erased (Add d p q) b) -> (erased (Thrice p q) t))
  (let ((erased q1) (erased t1)) (thrice-exists p))
  (let ((erased d1) (erased a1) (erased b1)) (thrice-adds p q1 t1))
  (let-match erased (add-fn p p d1 d a1 a) (Refl _ _))
  (let-match erased (add-fn d p q1 q b1 b) (Refl _ _))
  t1)

(def-fns _ $ (erased thrice-le : (erased (Nat) p q) (subterm erased (Thrice p q) t) -> (erased (Lt p (Succ q)) l))
  (let-match erased t (TS p1 q1 t1) ((TZ) (LtZ (Zero))))
  (LtS p1 (Succ (Succ (Succ q1))) (lt-weaken p1 (Succ (Succ q1)) (lt-weaken p1 (Succ q1) (thrice-le p1 q1 t1)))))

(def-fns _ $ (erased thrice-lt : (erased (Nat) p r q s) (subterm erased (Lt p r) l) (erased (Thrice p q) a) (erased (Thrice r s) b) ->
    (erased (Lt (Succ (Succ q)) s) c))
  (let-match erased b (TS r1 s1 b1) (absurd (TZ) l))
  (match erased l _
    ((LtZ _) (let-match erased a (TZ)) (LtS (Succ (Zero)) (Succ (Succ s1)) (LtS (Zero) (Succ s1) (LtZ s1))))
    ((LtS p1 _ l1)
      (let-match erased a (TS _ q1 a1))
      (LtS _ _ (LtS _ _ (LtS _ _ (thrice-lt p1 r1 q1 s1 l1 a1 b1)))))))

(def-fns _ $ (many thrice-c : (many (Nat) p) (erased (Nat) q) (erased (Thrice p q) t) (erased (Lt q u62-modulus) b) -> (many q is r))
  (let ((erased d) (erased a1) (erased a2)) (thrice-adds p q t))
  (let ((many d1)) (u62-add p p d a1 (lt-le-trans d (Succ q) u62-modulus (add-le-left d p q a2) (LtS q u62-modulus b))))
  (u62-add d1 p q a2 b))

; q is the prefix p followed by the colour e, as base-3 numbers with digit e - 1.
(def-adts $ (Kid : ((Nat) p) ((Col) e) ((Nat) q) -> Type)
  enum
  (many Ki1 : (erased (Nat) p q) (erased (Thrice p q) t) -> (Kid p (C1) q))
  (many Ki2 : (erased (Nat) p q) (erased (Thrice p q) t) -> (Kid p (C2) (Succ q)))
  (many Ki3 : (erased (Nat) p q) (erased (Thrice p q) t) -> (Kid p (C3) (Succ (Succ q)))))

(def-fns _ $ (erased kid-base : (erased (Nat) p q) (erased (Col) e) (erased (Kid p e q) k) ->
    (erased (Nat) q0) (erased (Thrice p q0) t) (erased (Lt q (Succ (Succ (Succ q0)))) hi) (erased (Lt q0 (Succ q)) lo))
  (match erased k _
    ((Ki1 _ _ t) (values q t (lt-weaken q (Succ (Succ q)) (lt-weaken q (Succ q) (lt-succ q))) (lt-succ q)))
    ((Ki2 _ q0 t) (values q0 t (LtS q0 (Succ (Succ q0)) (lt-weaken q0 (Succ q0) (lt-succ q0))) (lt-weaken q0 (Succ q0) (lt-succ q0))))
    ((Ki3 _ q0 t) (values q0 t (lt-succ q) (lt-weaken q0 (Succ (Succ q0)) (lt-weaken q0 (Succ q0) (lt-succ q0)))))))

(def-fns _ $ (erased kid-lt : (erased (Nat) p r a b) (erased (Col) e f) (erased (Lt p r) l) (erased (Kid p e a) ka) (erased (Kid r f b) kb) ->
    (erased (Lt a b) c))
  (let ((erased q) (erased tq) (erased hi) (erased _)) (kid-base p a e ka))
  (let ((erased s) (erased ts) (erased _) (erased lo)) (kid-base r b f kb))
  (lt-le-trans a s b (lt-le-trans a (Succ (Succ (Succ q))) s hi (LtS _ _ (thrice-lt p r q s l tq ts))) lo))

(def-fns _ $ (erased kid-apart : (erased (Nat) p r a b) (erased (Col) e f) (erased (Apart (Nat) Lt p r) ap) (erased (Kid p e a) ka)
    (erased (Kid r f b) kb) -> (erased (Apart (Nat) Lt a b) c))
  (match erased ap _
    ((ApLt _ _ _ _ l) (ApLt (Nat) Lt a b (kid-lt p r a b e f l ka kb)))
    ((ApGt _ _ _ _ l) (ApGt (Nat) Lt a b (kid-lt r p b a f e l kb ka)))))

(def-fns _ $ (many kid-c : (many (Nat) p) (many (Col) e) (erased (Nat) q) (erased (Kid p e q) k) (erased (Lt q u62-modulus) b) -> (many q is r))
  (let ((erased q0) (erased t) (erased _) (erased lo)) (kid-base p q e k))
  (let ((many r0)) (thrice-c p q0 t (lt-le-trans q0 (Succ q) u62-modulus lo (LtS q u62-modulus b))))
  (match many e _
    (absurd (C0) k)
    ((C1) (let-match erased k (Ki1 _ _ t1)) (let-match erased (thrice-fn p q0 q t t1) (Refl _ _)) r0)
    ((C2) (let-match erased k (Ki2 _ q1 t1)) (let-match erased (thrice-fn p q0 q1 t t1) (Refl _ _)) (u62-inc r0 b))
    ((C3)
      (let-match erased k (Ki3 _ q1 t1))
      (let-match erased (thrice-fn p q0 q1 t t1) (Refl _ _))
      (u62-inc (u62-inc r0 (lt-trans _ _ _ (lt-succ (Succ q0)) b)) b))))

; Reading the colours et from the prefix p gives the prefix q.
(def-adts $ (TIdx : ((Nat) p) ((List (Col)) et) ((Nat) q) -> Type)
  enum
  (many TINil : (erased (Nat) p) -> (TIdx p (Nil (Col)) p))
  (many TICons : (erased (Nat) p q r) (erased (Col) e) (erased (List (Col)) et) (erased (Kid p e q) k) (erased (TIdx q et r) t)
      -> (TIdx p (Cons (Col) e et) r)))

(def-fns _ $ (erased tidx-lt : (erased (Nat) p p2 ix iy j) (erased (List (Col)) et et2) (erased (Lt p p2) l) (subterm erased (TIdx p et ix) a)
    (erased (TIdx p2 et2 iy) b) (erased (Length (Col) et j) la) (erased (Length (Col) et2 j) lb) -> (erased (Lt ix iy) r))
  (match erased a _
    ((TINil _) (let-match erased la (LengthNil _)) (let-match erased lb (LengthNil _)) (let-match erased b (TINil _)) l)
    ((TICons _ q _ e et1 k a1)
      (let-match erased la (LengthCons _ _ _ j1 la1))
      (let-match erased lb (LengthCons _ e2 et3 _ lb1))
      (let-match erased b (TICons _ q2 _ _ _ k2 b1))
      (tidx-lt q q2 ix iy j1 et1 et3 (kid-lt p p2 q q2 e e2 l k k2) a1 b1 la1 lb1))))

; p is the prefix whose colours are those of pre reversed.
(def-adts $ (RIdx : ((List (Col)) pre) ((Nat) p) -> Type)
  enum
  (many RINil : -> (RIdx (Nil (Col)) (Zero)))
  (many RICons : (erased (List (Col)) pre) (erased (Nat) p q) (erased (Col) e) (erased (RIdx pre p) r) (erased (Kid p e q) k)
      -> (RIdx (Cons (Col) e pre) q)))

(def-fns _ $ (erased ridx-tidx : (erased (List (Col)) pre w et) (erased (Nat) p i) (subterm erased (RIdx pre p) r)
    (erased (RevApp (Col) pre w et) ra) (erased (TIdx p w i) ti) -> (erased (TIdx (Zero) et i) res))
  (match erased r _
    ((RINil) (let-match erased ra (RANil _ _)) ti)
    ((RICons pre1 p1 _ e r1 k)
      (let-match erased ra (RACons _ _ _ _ _ ra1))
      (ridx-tidx pre1 (Cons _ e w) et p1 i r1 ra1 (TICons p1 p i e w k ti)))))

(def-adts $ (Occ : ((Ctree) t) -> Type)
  enum
  (many OccN : (erased (Ctree) t1 t2 t3) -> (Occ (CNode t1 t2 t3)))
  (many OccL : (erased (Ctree) lf) -> (Occ (CLeaf lf))))

(def-adts $ (Occ3 : ((Ctree) t1) ((Ctree) t2) ((Ctree) t3) -> Type)
  enum
  (many Occ1 : (erased (Ctree) t1 t2 t3) (erased (Occ t1) o) -> (Occ3 t1 t2 t3))
  (many Occ2 : (erased (Ctree) t1 t2 t3) (erased (Occ t2) o) -> (Occ3 t1 t2 t3))
  (many Occ3c : (erased (Ctree) t1 t2 t3) (erased (Occ t3) o) -> (Occ3 t1 t2 t3)))

(def-adts $ (OccDec : ((Ctree) t) -> Type)
  enum
  (many OdE : -> (OccDec (CEmpty)))
  (many OdY : (erased (Ctree) t) (erased (Occ t) o) -> (OccDec t)))

(def-fns _ $ (many occ-c : (many (Ctree) t) -> (many (OccDec t) d))
  (match many t _ ((CEmpty) (OdE)) ((CNode a b c) (OdY t (OccN a b c))) ((CLeaf lf) (OdY t (OccL lf)))))

(def-fns _ $ (erased absurd occ3-empty : (erased (Occ3 (CEmpty) (CEmpty) (CEmpty)) o) -> (erased (False) f))
  (match erased o _ (absurd (Occ1 _ _ _ v) v) (absurd (Occ2 _ _ _ v) v) (absurd (Occ3c _ _ _ v) v)))

; t is the node of t1, t2 and t3, or empty when all three are.
(def-adts $ (Cn : ((Ctree) t1) ((Ctree) t2) ((Ctree) t3) ((Ctree) t) -> Type)
  enum
  (many CnE : -> (Cn (CEmpty) (CEmpty) (CEmpty) (CEmpty)))
  (many CnN : (erased (Ctree) t1 t2 t3) (erased (Occ3 t1 t2 t3) o) -> (Cn t1 t2 t3 (CNode t1 t2 t3))))

(def-fns _ $ (many cn-c : (many (Ctree) t1 t2 t3) -> (many (Ctree) t) (erased (Cn t1 t2 t3 t) c))
  (let-match many (occ-c t1) (OdE) ((OdY _ o) (values (CNode t1 t2 t3) (CnN t1 t2 t3 (Occ1 t1 t2 t3 o)))))
  (let-match many (occ-c t2) (OdE) ((OdY _ o) (values (CNode t1 t2 t3) (CnN t1 t2 t3 (Occ2 t1 t2 t3 o)))))
  (let-match many (occ-c t3) (OdE) ((OdY _ o) (values (CNode t1 t2 t3) (CnN t1 t2 t3 (Occ3c t1 t2 t3 o)))))
  (values (CEmpty) (CnE)))

(def-fns _ $ (erased cn-fn : (erased (Ctree) t1 t2 t3 t u) (erased (Cn t1 t2 t3 t) c) (erased (Cn t1 t2 t3 u) d) -> (erased (Eq (Ctree) t u) r))
  (match erased c _
    ((CnE) (let-match erased d (CnE) (absurd (CnN _ _ _ o) (occ3-empty o))) (Refl _ t))
    ((CnN _ _ _ o) (let-match erased d (CnN _ _ _ _) (absurd (CnE) (occ3-empty o))) (Refl _ t))))

(def-fns _ $ (erased cn-cons : (erased (Ctree) t1 t2 t3 t) (erased (Cn t1 t2 t3 t) c) -> (erased (CtCons t1 t2 t3 t) r))
  (match erased c _ ((CnE) (CCEmpty)) ((CnN _ _ _ _) (CCNode t1 t2 t3))))

(def-fns _ $ (erased cn-sel : (erased (Ctree) t1 t2 t3 t) (erased (Cn t1 t2 t3 t) c) ->
    (erased (CtSel t (C1) t1) s1) (erased (CtSel t (C2) t2) s2) (erased (CtSel t (C3) t3) s3))
  (match erased c _
    ((CnE) (values (SelE (C1)) (SelE (C2)) (SelE (C3))))
    ((CnN _ _ _ _) (values (SelN1 t1 t2 t3) (SelN2 t1 t2 t3) (SelN3 t1 t2 t3)))))

; t has height j and no node all of whose children are empty.
(def-adts $ (CtCanon : ((Nat) j) ((Ctree) t) -> Type)
  enum
  (many CanL : (erased (Ctree) t) (erased (CtH (Zero) t) k) -> (CtCanon (Zero) t))
  (many CanN : (erased (Nat) j) (erased (Ctree) t1 t2 t3 t) (erased (CtCanon j t1) c1) (erased (CtCanon j t2) c2) (erased (CtCanon j t3) c3)
      (erased (Cn t1 t2 t3 t) c) -> (CtCanon (Succ j) t)))

(def-fns _ $ (erased canon-h : (erased (Nat) j) (erased (Ctree) t) (subterm erased (CtCanon j t) c) -> (erased (CtH j t) k))
  (match erased c _
    ((CanL _ k) k)
    ((CanN j1 t1 t2 t3 _ c1 c2 c3 cn)
      (cons-h j1 t1 t2 t3 t (cn-cons t1 t2 t3 t cn) (canon-h j1 t1 c1) (canon-h j1 t2 c2) (canon-h j1 t3 c3)))))

(def-fns _ $ (erased canon-empty : (subterm erased (Nat) j) -> (erased (CtCanon j (CEmpty)) c))
  (let-match erased j (Succ j1) ((Zero) (CanL (CEmpty) (HE (Zero)))))
  (let ((erased c1)) (canon-empty j1))
  (CanN j1 (CEmpty) (CEmpty) (CEmpty) (CEmpty) c1 c1 c1 (CnE)))

(def-fns _ $ (erased cres-canon : (erased (Nat) h) (erased (Ctree) t keep gone) (erased (List RG) r) (subterm erased (CRes h t r keep gone) c)
    (erased (CtCanon (Succ h) t) ct) -> (erased (Ctree) keep2) (erased (CRes h t r keep2 gone) c2) (erased (CtCanon (Succ h) keep2) k2))
  (match erased c _
    ((CRNil _ _) (values t c ct))
    ((CRE _ _) (values t c ct))
    ((CRS h1 t1 t2 t3 a1 a2 a3 b1 b2 b3 _ _ _ r1 r2 r3 s1 s2 s3 c1 c2 c3 _ cg)
      (let-match erased ct (CanN _ _ _ _ _ q1 q2 q3 cn))
      (let-match erased cn (CnN _ _ _ _))
      (let ((erased e1) (erased d1) (erased k1)) (cres-canon h1 t1 a1 b1 r1 c1 q1))
      (let ((erased e2) (erased d2) (erased k2)) (cres-canon h1 t2 a2 b2 r2 c2 q2))
      (let ((erased e3) (erased d3) (erased k3)) (cres-canon h1 t3 a3 b3 r3 c3 q3))
      (let ((erased k) (erased kc)) (cn-c e1 e2 e3))
      (values k (CRS h1 t1 t2 t3 e1 e2 e3 b1 b2 b3 k gone r r1 r2 r3 s1 s2 s3 d1 d2 d3 (cn-cons e1 e2 e3 k kc) cg)
        (CanN (Succ h1) e1 e2 e3 k k1 k2 k3 kc)))
    ((CRZ t1 t2 t3 l1 l2 l3 g1 g2 g3 _ _ _ n1 n2 n3 p1 p2 p3 d1 d2 d3 _ f1 f2 f3 cg)
      (let-match erased d1 (MkDecrAll _ _ _ _ _ _ _ h1 _ _))
      (let-match erased d2 (MkDecrAll _ _ _ _ _ _ _ h2 _ _))
      (let-match erased d3 (MkDecrAll _ _ _ _ _ _ _ h3 _ _))
      (let ((erased k) (erased kc)) (cn-c l1 l2 l3))
      (values k (CRZ t1 t2 t3 l1 l2 l3 g1 g2 g3 k gone r n1 n2 n3 p1 p2 p3 d1 d2 d3 (cn-cons l1 l2 l3 k kc) f1 f2 f3 cg)
        (CanN (Zero) l1 l2 l3 k (CanL l1 h1) (CanL l2 h2) (CanL l3 h3) kc)))))

; The block of us for the prefix p, whose traces have j more colours, holds t: each trace's count at its index.
(def-adts $ (Tally : ((List Cnt) us) ((Nat) j) ((Nat) p) ((Ctree) t) -> Type)
  enum
  (many TaL : (erased (List Cnt) us) (erased (Nat) p n) (erased (Ctree) t) (erased (Elt cnt-w us p n) e) (erased (CtRoot t n) r) (erased (CtH (Zero) t) k) -> (Tally us (Zero) p t))
  (many TaN : (erased (List Cnt) us) (erased (Nat) j p q) (erased (Ctree) t1 t2 t3 t) (erased (Thrice p q) tq)
      (erased (Tally us j q t1) b1) (erased (Tally us j (Succ q) t2) b2) (erased (Tally us j (Succ (Succ q)) t3) b3) (erased (Cn t1 t2 t3 t) c)
      -> (Tally us (Succ j) p t)))

(def-adts $ (Fit : ((Nat) w) ((List (U8)) us) -> Type)
  enum
  (many MkFit : (erased (Nat) w) (erased (List (U8)) us) (erased (Nat) len) (erased (Sz w us len) l) -> (Fit w us)))

(def-fns _ $ (erased tally-canon : (erased (List Cnt) us) (erased (Nat) j p) (erased (Ctree) t) (subterm erased (Tally us j p t) b)
    -> (erased (CtCanon j t) c))
  (match erased b _
    ((TaL _ _ _ _ _ _ k) (CanL t k))
    ((TaN _ j1 _ q t1 t2 t3 _ _ b1 b2 b3 cn)
      (CanN j1 t1 t2 t3 t (tally-canon us j1 q t1 b1) (tally-canon us j1 (Succ q) t2 b2) (tally-canon us j1 (Succ (Succ q)) t3 b3) cn))))

(def-fns _ $ (erased leaf-fn : (erased (Ctree) t u) (erased (Nat) n) (subterm erased (CtRoot t n) r) (erased (CtH (Zero) t) k)
    (erased (CtRoot u n) s) (erased (CtH (Zero) u) m) -> (erased (Eq (Ctree) t u) e))
  (match erased r _
    ((RootE) (let-match erased m (HE _) (absurd (HL _ _) s)) (Refl _ t))
    (absurd (RootN _ _ _) k)
    ((RootL lf n1 r1)
      (let-match erased k (HL _ k1))
      (let-match erased m (HL lf2 m1) (absurd (HE _) s))
      (let-match erased s (RootL _ _ s1))
      (let-match erased (leaf-fn lf lf2 n1 r1 k1 s1 m1) (Refl _ _))
      (Refl _ t))))

(def-fns _ $ (erased tally-fn : (erased (List Cnt) us) (erased (Nat) j p) (erased (Ctree) t u) (subterm erased (Tally us j p t) b)
    (erased (Tally us j p u) c) -> (erased (Eq (Ctree) t u) e))
  (match erased b _
    ((TaL _ _ n _ x rt k)
      (let-match erased c (TaL _ _ _ _ y ru m))
      (let-match erased (elt-fn cnt-w us p _ _ x y) (Refl _ _))
      (leaf-fn t u n rt k ru m))
    ((TaN _ j1 _ q t1 t2 t3 _ tq b1 b2 b3 cn)
      (let-match erased c (TaN _ _ _ q2 u1 u2 u3 _ tq2 c1 c2 c3 cm))
      (let-match erased (thrice-fn p q q2 tq tq2) (Refl _ _))
      (let-match erased (tally-fn us j1 q t1 u1 b1 c1) (Refl _ _))
      (let-match erased (tally-fn us j1 (Succ q) t2 u2 b2 c2) (Refl _ _))
      (let-match erased (tally-fn us j1 (Succ (Succ q)) t3 u3 b3 c3) (Refl _ _))
      (cn-fn t1 t2 t3 t u cn cm))))

(def-fns _ $ (erased tally-lt : (erased (List Cnt) us) (erased (Nat) j p len) (erased (Ctree) t) (subterm erased (Tally us j p t) b)
    (erased (Sz cnt-w us len) l) -> (erased (Lt p len) r))
  (match erased b _
    ((TaL _ _ _ _ x _ _) (elt-lt cnt-w us p _ len x l))
    ((TaN _ j1 _ q t1 _ _ _ tq b1 _ _ _) (lt-le-trans p (Succ q) len (thrice-le p q tq) (LtS q len (tally-lt us j1 q len t1 b1 l))))))

(def-fns _ $ (erased tally-u62 : (erased (List Cnt) us) (erased (Nat) j p) (erased (Ctree) t) (erased (Tally us j p t) b) (erased (Fit cnt-w us) f)
    -> (erased (Lt p u62-modulus) r))
  (let-match erased f (MkFit _ _ len l))
  (lt-trans p len u62-modulus (tally-lt us j p len t b l) (sz-u62 cnt-w us len l)))

(def-fns _ $ (erased tally-down : (erased (List Cnt) us) (erased (Nat) j p a) (erased (Ctree) t) (erased (Col) e) (erased (Tally us (Succ j) p t) b)
    (erased (Kid p e a) k) -> (erased (Ctree) u) (erased (Tally us j a u) c) (erased (CtSel t e u) s))
  (let-match erased b (TaN _ _ _ q t1 t2 t3 _ tq b1 b2 b3 cn))
  (let ((erased s1) (erased s2) (erased s3)) (cn-sel t1 t2 t3 t cn))
  (match erased k _
    ((Ki1 _ _ tk) (let-match erased (thrice-fn p q a tq tk) (Refl _ _)) (values t1 b1 s1))
    ((Ki2 _ a0 tk) (let-match erased (thrice-fn p q a0 tq tk) (Refl _ _)) (values t2 b2 s2))
    ((Ki3 _ a0 tk) (let-match erased (thrice-fn p q a0 tq tk) (Refl _ _)) (values t3 b3 s3))))

(def-fns _ $ (erased tally-sub : (erased (List Cnt) us) (erased (Nat) j p i) (erased (Ctree) t) (subterm erased (List (Col)) et)
    (erased (Tally us j p t) b) (erased (TIdx p et i) ti) (erased (Length (Col) et j) le) ->
    (erased (Nat) n) (erased (Elt cnt-w us i n) x) (erased (CtSub t et n) s))
  (match erased et _
    ((Nil _)
      (let-match erased le (LengthNil _))
      (let-match erased ti (TINil _))
      (let-match erased b (TaL _ _ n _ x rt _))
      (values n x (SubNil t n rt)))
    ((Cons _ e et1)
      (let-match erased le (LengthCons _ _ _ j1 le1))
      (let-match erased ti (TICons _ a _ _ _ k ti1))
      (let ((erased u) (erased c) (erased sl)) (tally-down us j1 p a t e b k))
      (let ((erased n) (erased x) (erased s)) (tally-sub us j1 a i u et1 c ti1 le1))
      (values n x (SubCons t u e et1 n sl s)))))

(def-fns _ $ (erased tally-set : (erased (List Cnt) us vs) (erased (Nat) j p p2 i x) (erased (List (Col)) et) (erased (Ctree) t)
    (subterm erased (Tally us j p t) b) (erased (Put cnt-w us i x vs) s) (erased (TIdx p2 et i) ti) (erased (Length (Col) et j) le)
    (erased (Apart (Nat) Lt p p2) ap) -> (erased (Tally vs j p t) r))
  (match erased b _
    ((TaL _ _ n _ y rt k)
      (let-match erased le (LengthNil _))
      (let-match erased ti (TINil _))
      (TaL vs p n t
        (match erased ap _
          ((ApLt _ _ _ _ l) (put-other cnt-w us vs i x p n s (ApGt (Nat) Lt i p l) y))
          ((ApGt _ _ _ _ l) (put-other cnt-w us vs i x p n s (ApLt (Nat) Lt i p l) y)))
        rt k))
    ((TaN _ j1 _ q t1 t2 t3 _ tq b1 b2 b3 cn)
      (let-match erased le (LengthCons _ e et1 _ le1))
      (let-match erased ti (TICons _ q2 _ _ _ k ti1))
      (TaN vs j1 p q t1 t2 t3 t tq
        (tally-set us vs j1 q q2 i x et1 t1 b1 s ti1 le1 (kid-apart p p2 q q2 (C1) e ap (Ki1 p q tq) k))
        (tally-set us vs j1 (Succ q) q2 i x et1 t2 b2 s ti1 le1 (kid-apart p p2 (Succ q) q2 (C2) e ap (Ki2 p q tq) k))
        (tally-set us vs j1 (Succ (Succ q)) q2 i x et1 t3 b3 s ti1 le1 (kid-apart p p2 (Succ (Succ q)) q2 (C3) e ap (Ki3 p q tq) k))
        cn))))

; vs is us with entries set only at the indices of the block of the prefix p with j more colours.
(def-adts $ (Inside : ((List Cnt) us) ((List Cnt) vs) ((Nat) j) ((Nat) p) -> Type)
  enum
  (many InNil : (erased (List Cnt) us) (erased (Nat) j p) -> (Inside us us j p))
  (many InSet : (erased (List Cnt) us ws vs) (erased (Nat) j p i x) (erased (List (Col)) et) (erased (Inside us ws j p) w)
      (erased (Put cnt-w ws i x vs) s) (erased (TIdx p et i) ti) (erased (Length (Col) et j) le) -> (Inside us vs j p)))

(def-fns _ $ (erased inside-up : (erased (List Cnt) us vs) (erased (Nat) j p q) (erased (Col) e) (subterm erased (Inside us vs j q) w)
    (erased (Kid p e q) k) -> (erased (Inside us vs (Succ j) p) r))
  (match erased w _
    ((InNil _ _ _) (InNil us (Succ j) p))
    ((InSet _ ws _ _ _ i x et w1 s ti le)
      (InSet us ws vs (Succ j) p i x (Cons _ e et) (inside-up us ws j p q e w1 k) s (TICons p q i e et k ti) (LengthCons _ e et j le)))))

(def-fns _ $ (erased inside-cat : (erased (List Cnt) us ws vs) (erased (Nat) j p) (erased (Inside us ws j p) w1) (subterm erased (Inside ws vs j p) w2)
    -> (erased (Inside us vs j p) r))
  (match erased w2 _
    ((InNil _ _ _) w1)
    ((InSet _ xs _ _ _ i x et w3 s ti le) (InSet us xs vs j p i x et (inside-cat us ws xs j p w1 w3) s ti le))))

(def-fns _ $ (erased tally-inside : (erased (List Cnt) us vs) (erased (Nat) j p p2) (erased (Ctree) t) (erased (Tally us j p t) b)
    (subterm erased (Inside us vs j p2) w) (erased (Apart (Nat) Lt p p2) ap) -> (erased (Tally vs j p t) r))
  (match erased w _
    ((InNil _ _ _) b)
    ((InSet _ ws _ _ _ i x et w1 s ti le) (tally-set ws vs j p p2 i x et t (tally-inside us ws j p p2 t b w1 ap) s ti le ap))))

; t is the subtree of top after the reversed prefix pre.
(def-adts $ (CtAt : ((Ctree) top) ((List (Col)) pre) ((Ctree) t) -> Type)
  enum
  (many AtNil : (erased (Ctree) top) -> (CtAt top (Nil (Col)) top))
  (many AtCons : (erased (Ctree) top u t) (erased (List (Col)) pre) (erased (Col) e) (erased (CtAt top pre u) a) (erased (CtSel u e t) s)
      -> (CtAt top (Cons (Col) e pre) t)))

(def-fns _ $ (erased at-sub : (erased (Ctree) top t) (erased (List (Col)) pre w et) (erased (Nat) n) (subterm erased (CtAt top pre t) a)
    (erased (RevApp (Col) pre w et) ra) (erased (CtSub t w n) s) -> (erased (CtSub top et n) r))
  (match erased a _
    ((AtNil _) (let-match erased ra (RANil _ _)) s)
    ((AtCons _ u _ pre1 e a1 sl)
      (let-match erased ra (RACons _ _ _ _ _ ra1))
      (at-sub top u pre1 (Cons _ e w) et n a1 ra1 (SubCons u t e w n sl s)))))

; Each trace of length j after the reversed prefix pre, from the prefix p, has its count in top as its entry in us.
(def-adts $ (Pointwise : ((List Cnt) us) ((Ctree) top) ((Nat) j) ((Nat) p) ((List (Col)) pre) -> Type)
  enum
  (many PwL : (erased (List Cnt) us) (erased (Ctree) top) (erased (Nat) p n) (erased (List (Col)) pre et)
      (erased (RevApp (Col) pre (Nil (Col)) et) ra) (erased (CtSub top et n) s) (erased (Elt cnt-w us p n) x)
      -> (Pointwise us top (Zero) p pre))
  (many PwN : (erased (List Cnt) us) (erased (Ctree) top) (erased (Nat) j p q) (erased (List (Col)) pre) (erased (Thrice p q) tq)
      (erased (Pointwise us top j q (Cons (Col) (C1) pre)) a1) (erased (Pointwise us top j (Succ q) (Cons (Col) (C2) pre)) a2)
      (erased (Pointwise us top j (Succ (Succ q)) (Cons (Col) (C3) pre)) a3) -> (Pointwise us top (Succ j) p pre)))

(def-fns _ $ (erased tally-of-pointwise : (erased (List Cnt) us) (erased (Ctree) top t) (erased (Nat) j p) (erased (List (Col)) pre)
    (subterm erased (Pointwise us top j p pre) pw) (erased (CtCanon j t) c) (erased (CtAt top pre t) sa) -> (erased (Tally us j p t) b))
  (match erased pw _
    ((PwL _ _ _ n _ et ra s x)
      (let-match erased c (CanL _ k))
      (let ((erased m) (erased sm)) (sub-exists t (Nil _)))
      (let-match erased (sub-fn top et m n (at-sub top t pre (Nil _) et m sa ra sm) s) (Refl _ _))
      (let-match erased sm (SubNil _ _ rt))
      (TaL us p n t x rt k))
    ((PwN _ _ j1 _ q _ tq a1 a2 a3)
      (let-match erased c (CanN _ t1 t2 t3 _ c1 c2 c3 cn))
      (let ((erased s1) (erased s2) (erased s3)) (cn-sel t1 t2 t3 t cn))
      (TaN us j1 p q t1 t2 t3 t tq
        (tally-of-pointwise us top t1 j1 q (Cons _ (C1) pre) a1 c1 (AtCons top t t1 pre (C1) sa s1))
        (tally-of-pointwise us top t2 j1 (Succ q) (Cons _ (C2) pre) a2 c2 (AtCons top t t2 pre (C2) sa s2))
        (tally-of-pointwise us top t3 j1 (Succ (Succ q)) (Cons _ (C3) pre) a3 c3 (AtCons top t t3 pre (C3) sa s3))
        cn))))

; Trie node n, whose children are 3n + 1 to 3n + 3, holds t of height j: its entry is 0 when t is empty and 1 otherwise.
(def-adts $ (Flags : ((List (U8)) us) ((Nat) j) ((Nat) n) ((Ctree) t) -> Type)
  enum
  (many FlE : (erased (List (U8)) us) (erased (Nat) j n) (erased (Elt flag-w us n (Zero)) x) -> (Flags us j n (CEmpty)))
  (many FlL : (erased (List (U8)) us) (erased (Nat) n) (erased (Ctree) lf) (erased (Elt flag-w us n (Succ (Zero))) x) -> (Flags us (Zero) n (CLeaf lf)))
  (many FlN : (erased (List (U8)) us) (erased (Nat) j n q) (erased (Ctree) t1 t2 t3) (erased (Elt flag-w us n (Succ (Zero))) x) (erased (Thrice n q) tq)
      (erased (Flags us j (Succ q) t1) f1) (erased (Flags us j (Succ (Succ q)) t2) f2) (erased (Flags us j (Succ (Succ (Succ q))) t3) f3)
      (erased (Occ3 t1 t2 t3) o) -> (Flags us (Succ j) n (CNode t1 t2 t3))))

; What Flags us j n t says once the entry v at n is known.
(def-adts $ (FlagInv : ((List (U8)) us) ((Nat) j) ((Nat) n) ((Nat) v) ((Ctree) t) -> Type)
  enum
  (many FiE : (erased (List (U8)) us) (erased (Nat) j n) -> (FlagInv us j n (Zero) (CEmpty)))
  (many FiL : (erased (List (U8)) us) (erased (Nat) n) (erased (Ctree) lf) -> (FlagInv us (Zero) n (Succ (Zero)) (CLeaf lf)))
  (many FiN : (erased (List (U8)) us) (erased (Nat) j n q) (erased (Ctree) t1 t2 t3) (erased (Thrice n q) tq)
      (erased (Flags us j (Succ q) t1) f1) (erased (Flags us j (Succ (Succ q)) t2) f2) (erased (Flags us j (Succ (Succ (Succ q))) t3) f3)
      (erased (Occ3 t1 t2 t3) o) -> (FlagInv us (Succ j) n (Succ (Zero)) (CNode t1 t2 t3))))

(def-fns _ $ (erased flags-inv : (erased (List (U8)) us) (erased (Nat) j n v) (erased (Ctree) t)
    (erased (Flags us j n t) c) (erased (Elt flag-w us n v) x) -> (erased (FlagInv us j n v t) r))
  (match erased c _
    ((FlE _ _ _ y) (let-match erased (elt-fn flag-w us n _ _ x y) (Refl _ _)) (FiE us j n))
    ((FlL _ _ lf y) (let-match erased (elt-fn flag-w us n _ _ x y) (Refl _ _)) (FiL us n lf))
    ((FlN _ j1 _ q t1 t2 t3 y tq f1 f2 f3 o)
      (let-match erased (elt-fn flag-w us n _ _ x y) (Refl _ _))
      (FiN us j1 n q t1 t2 t3 tq f1 f2 f3 o))))

(def-fns _ $ (erased flags-mem : (erased (List (U8)) us) (erased (Nat) j n) (erased (Ctree) t) (subterm erased (Flags us j n t) c) (erased (Occ t) o)
    -> (erased (List (Col)) et) (erased (CtMem t et) m))
  (let-match erased c (FlN _ j1 _ q t1 t2 t3 _ _ f1 f2 f3 o3)
    (absurd (FlE _ _ _ _) o)
    ((FlL _ _ lf _) (values (Nil _) (leaf-mem lf))))
  (match erased o3 _
    ((Occ1 _ _ _ o1)
      (let ((erased et) (erased m)) (flags-mem us j1 (Succ q) t1 f1 o1))
      (values (Cons _ (C1) et) (mem-cons t t1 (C1) et (SelN1 t1 t2 t3) m)))
    ((Occ2 _ _ _ o1)
      (let ((erased et) (erased m)) (flags-mem us j1 (Succ (Succ q)) t2 f2 o1))
      (values (Cons _ (C2) et) (mem-cons t t2 (C2) et (SelN2 t1 t2 t3) m)))
    ((Occ3c _ _ _ o1)
      (let ((erased et) (erased m)) (flags-mem us j1 (Succ (Succ (Succ q))) t3 f3 o1))
      (values (Cons _ (C3) et) (mem-cons t t3 (C3) et (SelN3 t1 t2 t3) m)))))

(let ((many flag-um)) (u62-modulus-many))
(comptime-match many (lt-dec (Succ (Zero)) flag-um) (Yes _ _ _ _ flag-one-lt))
(let ((many flag-u8m)) u8-modulus)
(comptime-match many (lt-dec (Succ (Zero)) flag-u8m) (Yes _ _ _ _ flag-one-lt8))
(comptime-match many (lt-dec (Succ (Succ (Succ (Zero)))) flag-um) (Yes _ _ _ _ three-lt))

; Every trie node in the j levels from n has its index below len.
(def-adts $ (TrieFit : ((Nat) len) ((Nat) j) ((Nat) n) -> Type)
  enum
  (many TfL : (erased (Nat) len n) (erased (Lt n len) b) -> (TrieFit len (Zero) n))
  (many TfN : (erased (Nat) len j n q) (erased (Lt n len) b) (erased (Thrice n q) tq) (erased (TrieFit len j (Succ q)) h1)
      (erased (TrieFit len j (Succ (Succ q))) h2) (erased (TrieFit len j (Succ (Succ (Succ q)))) h3) -> (TrieFit len (Succ j) n)))

(def-fns _ $ (erased tfit-lt : (erased (Nat) len j n) (erased (TrieFit len j n) hf) -> (erased (Lt n len) r))
  (match erased hf _ ((TfL _ _ b) b) ((TfN _ _ _ _ b _ _ _ _) b)))

; m is the last trie node in the j levels from n.
(def-adts $ (Mx : ((Nat) j) ((Nat) n) ((Nat) m) -> Type)
  enum
  (many MxZ : (erased (Nat) n) -> (Mx (Zero) n n))
  (many MxS : (erased (Nat) j n q m) (erased (Thrice n q) tq) (erased (Mx j (Succ (Succ (Succ q))) m) x) -> (Mx (Succ j) n m)))

(def-fns _ $ (erased mx-exists : (subterm erased (Nat) j) (erased (Nat) n) -> (erased (Nat) m) (erased (Mx j n m) x))
  (let-match erased j (Succ j1) ((Zero) (values n (MxZ n))))
  (let ((erased q) (erased tq)) (thrice-exists n))
  (let ((erased m) (erased x)) (mx-exists j1 (Succ (Succ (Succ q)))))
  (values m (MxS j1 n q m tq x)))

(def-fns _ $ (erased mx-ge : (erased (Nat) j n m) (subterm erased (Mx j n m) x) -> (erased (Lt n (Succ m)) r))
  (let-match erased x (MxS j1 _ q _ tq x1) ((MxZ _) (lt-succ n)))
  (lt-weaken _ _ (lt-le-trans n (Succ q) m (thrice-le n q tq) (lt-succ-left _ _ (lt-succ-left _ _ (mx-ge j1 _ m x1))))))

(def-fns _ $ (erased thrice-mono : (erased (Nat) a b qa qb) (erased (Lt a (Succ b)) l) (erased (Thrice a qa) ta) (erased (Thrice b qb) tb)
    -> (erased (Lt qa (Succ qb)) r))
  (let-match erased (nat-eq a b) (Unequal _ _ _ _ ap) ((Equal _ _ _) (let-match erased (thrice-fn a qa qb ta tb) (Refl _ _)) (lt-succ qa)))
  (let-match erased ap (ApLt _ _ _ _ k) (absurd (ApGt _ _ _ _ k) (lt-irrefl b (lt-le-trans b a b k l))))
  (lt-weaken _ _ (lt-succ-left _ _ (lt-succ-left _ _ (thrice-lt a b qa qb k ta tb)))))

(def-fns _ $ (erased mx-mono : (erased (Nat) j a b ma mb) (subterm erased (Mx j a ma) x) (erased (Mx j b mb) y) (erased (Lt a (Succ b)) l)
    -> (erased (Lt ma (Succ mb)) r))
  (let-match erased x (MxS j1 _ qa _ ta x1) ((MxZ _) (let-match erased y (MxZ _)) l))
  (let-match erased y (MxS _ _ qb _ tb y1))
  (mx-mono j1 _ _ ma mb x1 y1 (LtS _ _ (LtS _ _ (LtS _ _ (thrice-mono a b qa qb l ta tb))))))

(def-fns _ $ (erased tfit-of-mx : (subterm erased (Nat) j) (erased (Nat) n m len) (erased (Mx j n m) x) (erased (Lt m len) b) -> (erased (TrieFit len j n) r))
  (let ((erased bn)) (lt-le-trans n (Succ m) len (mx-ge j n m x) (LtS _ _ b)))
  (let-match erased j (Succ j1) ((Zero) (TfL len n bn)))
  (let-match erased x (MxS _ _ q _ tq x3))
  (let ((erased q3)) (Succ (Succ (Succ q))))
  (let ((erased m1) (erased x1)) (mx-exists j1 (Succ q)))
  (let ((erased m2) (erased x2)) (mx-exists j1 (Succ (Succ q))))
  (let ((erased b1)) (lt-le-trans m1 (Succ m) len (mx-mono j1 _ _ m1 m x1 x3 (lt-weaken _ _ (lt-weaken _ _ (lt-succ (Succ q))))) (LtS _ _ b)))
  (let ((erased b2)) (lt-le-trans m2 (Succ m) len (mx-mono j1 _ _ m2 m x2 x3 (lt-weaken _ _ (lt-succ (Succ (Succ q))))) (LtS _ _ b)))
  (TfN len j1 n q bn tq (tfit-of-mx j1 (Succ q) m1 len x1 b1) (tfit-of-mx j1 (Succ (Succ q)) m2 len x2 b2) (tfit-of-mx j1 q3 m len x3 b)))

(def-fns _ $ (many mx-c : (subterm many (Nat) j) (many (Nat) n) -> (many (Nat) m) (erased (Mx j n m) x))
  (let-match many j (Succ j1) ((Zero) (values n (MxZ n))))
  (let ((many d) (erased ad)) (add n n))
  (let ((many q) (erased aq)) (add d n))
  (let ((many m) (erased x)) (tail $ mx-c j1 (Succ (Succ (Succ q)))))
  (values m (MxS j1 n q m (adds-thrice n d q ad aq) x)))

(def-fns _ $ (many base3 : (many (Nat) p) (erased (Nat) q) (erased (Thrice p q) t) (erased (Lt (Succ (Succ q)) u62-modulus) b) ->
    (many q is a) (erased (Lt (Succ q) u62-modulus) b1) (erased (Lt (Succ (Succ q)) u62-modulus) b2))
  (let ((erased b1)) (lt-trans _ _ _ (lt-succ (Succ q)) b))
  (values (thrice-c p q t (lt-trans _ _ _ (lt-succ q) b1)) b1 b))

(def-fns _ $ (many node-kids : (many (Nat) n) (erased (Nat) q) (erased (Thrice n q) t) (erased (Lt (Succ (Succ (Succ q))) u62-modulus) b) ->
    (many (Succ q) is c1) (erased (Lt (Succ (Succ q)) u62-modulus) b2) (erased (Lt (Succ (Succ (Succ q))) u62-modulus) b3))
  (let ((many a) (erased b1) (erased b2)) (base3 n q t (lt-trans _ _ _ (lt-succ (Succ (Succ q))) b)))
  (values (u62-inc a b1) b2 b))

; ms has room for a trie of j levels below the root, at index 0.
(def-adts $ (Room : ((List (U8)) ms) ((Nat) j) -> Type)
  enum
  (many MkRoom : (erased (List (U8)) ms) (erased (Nat) j len) (erased (Sz flag-w ms len) l) (erased (Lt len u62-modulus) b)
      (erased (TrieFit len j (Zero)) hf) -> (Room ms j)))

(def-fns _ $ (erased room-fit : (erased (List (U8)) ms) (erased (Nat) j) (erased (Room ms j) rm) -> (erased (Fit flag-w ms) f))
  (let-match erased rm (MkRoom _ _ len l b _))
  (MkFit flag-w ms len l))

(def-fns _ $ (many room-new : (many (Nat) j) -> (erased (List (U8)) ms) (unique (Bytes ms) m) (many (ErasedMaybe (Room ms j)) r))
  (let ((many k) (erased x)) (mx-c j (Zero)))
  (let ((many n)) (Succ k))
  (let ((erased ms) (unique m) (erased rp)) (bytes-make n (MkU8 (Zero) u8-modulus-pos)))
  (let-match many (nat-fits-u62 n) (Yes _ _ _ _ lb) ((No _ _ _ _ _) (values ms m (ENone _))))
  (values ms m (ESome _ (MkRoom ms j n (sz-made flag-w n n _ ms rp (LtZ _) (mul-one-right n) lb) lb (tfit-of-mx j (Zero) k n x (lt-succ k))))))

(let ((many bn-one)) (Succ (Zero)))
(comptime-match many (lt-dec bn-one (Succ (sixty-two-many))) (Yes _ _ _ _ bn-one-lt))

; b holds the bit stack bs: 1 for the empty stack, each push one more low bit.
(def-adts $ (Bn : ((Bstack) bs) ((Nat) b) -> Type)
  enum
  (many BnE : -> (Bn (BS0) (Succ (Zero))))
  (many Bn0 : (erased (Bstack) bs) (erased (Nat) b d) (erased (Bn bs b) r) (erased (BitCons b (Bit0) d) c) -> (Bn (BP0 bs) d))
  (many Bn1 : (erased (Bstack) bs) (erased (Nat) b d) (erased (Bn bs b) r) (erased (BitCons b (Bit1) d) c) -> (Bn (BP1 bs) d)))

; b stays below 2^62 through j more pushes.
(def-adts $ (BnB : ((Nat) j) ((Nat) b) -> Type)
  enum
  (many BbZ : (erased (Nat) b) (erased (Lt b u62-modulus) l) -> (BnB (Zero) b))
  (many BbS : (erased (Nat) j b d) (erased (Double b d) dd) (erased (BnB j (Succ d)) r) -> (BnB (Succ j) b)))

; The top of a bit stack.
(def-adts $ (BTop : ((Bstack) bs) -> Type)
  enum
  (many BTE : -> (BTop (BS0)))
  (many BT0 : (erased (Bstack) c) -> (BTop (BP0 c)))
  (many BT1 : (erased (Bstack) c) -> (BTop (BP1 c))))

(def-fns _ $ (erased bn-dadd : (erased (Nat) a b) (subterm erased (Double a b) d) -> (erased (Add a a b) r))
  (let-match erased d (DS a1 b1 d1) ((D0) (AddZero (Zero))))
  (AddSucc a1 a (Succ b1) (add-succ-right a1 a1 b1 (bn-dadd a1 b1 d1))))

(def-fns _ $ (erased double-le-mono : (erased (Nat) c b e d) (subterm erased (Lt c (Succ b)) l) (erased (Double c e) p) (erased (Double b d) q) -> (erased (Lt e (Succ d)) r))
  (match erased l _
    ((LtZ _) (let-match erased p (D0)) (LtZ d))
    ((LtS c1 _ l1)
      (let-match erased p (DS _ e1 p1))
      (let-match erased q (DS b1 d1 q1) (absurd (D0) l1))
      (LtS _ _ (LtS _ _ (double-le-mono c1 b1 e1 d1 l1 p1 q1))))))

(def-fns _ $ (erased bc-le : (erased (Nat) m n) (erased (Bit) x) (erased (BitCons m x n) c) -> (erased (Lt m (Succ n)) r))
  (match erased c _ ((BC0 _ _ dd) (double-le m n dd)) ((BC1 _ d dd) (lt-weaken _ _ (double-le m d dd)))))

(def-fns _ $ (erased bnb-lt : (erased (Nat) j b) (subterm erased (BnB j b) r) -> (erased (Lt b u62-modulus) l))
  (let-match erased r (BbS j1 _ d dd r1) ((BbZ _ l) l))
  (lt-trans b (Succ d) u62-modulus (double-le b d dd) (bnb-lt j1 (Succ d) r1)))

(def-fns _ $ (erased bnb-mono : (erased (Nat) j b c) (subterm erased (BnB j b) r) (erased (Lt c (Succ b)) l) -> (erased (BnB j c) s))
  (let-match erased r (BbS j1 _ d dd r1) ((BbZ _ lb) (BbZ c (lt-le-trans c (Succ b) u62-modulus l (LtS b u62-modulus lb)))))
  (let ((erased e) (erased de)) (double c))
  (BbS j1 c e de (bnb-mono j1 (Succ d) (Succ e) r1 (LtS _ _ (double-le-mono c b e d l de dd)))))

(def-fns _ $ (erased bnb-down : (erased (Nat) j b c) (erased (BnB (Succ j) b) r) (erased (Lt c (Succ b)) l) -> (erased (BnB j c) s))
  (let-match erased r (BbS _ _ d dd r1))
  (bnb-mono j (Succ d) c r1 (lt-weaken _ _ (le-trans c b d l (double-le b d dd)))))

(def-fns _ $ (erased bn-pos : (erased (Bstack) bs) (erased (Nat) b) (subterm erased (Bn bs b) r) -> (erased (Lt (Zero) b) l))
  (let-match erased r (Bn1 c m _ r1 bc)
    ((BnE) (LtZ (Zero)))
    ((Bn0 c m _ r1 bc) (lt-le-trans (Zero) m b (bn-pos c m r1) (bc-le m b (Bit0) bc))))
  (let-match erased bc (BC1 _ d _))
  (LtZ d))

(def-fns _ $ (erased bn-two : (erased (Bstack) c) (erased (Nat) m b) (erased (Bit) x) (erased (Bn c m) r) (erased (BitCons m x b) bc) -> (erased (Lt bn-one b) l))
  (let ((erased p)) (bn-pos c m r))
  (let-match erased p (LtZ m1))
  (match erased bc _
    ((BC0 _ _ dd) (let-match erased dd (DS _ _ _)) (LtS _ _ (LtZ _)))
    ((BC1 _ d dd) (let-match erased dd (DS _ _ _)) (LtS _ _ (LtZ _)))))

(def-fns _ $ (many bn-top : (erased (Bstack) bs) (many (Nat) b) (erased (Bn bs b) r) (erased (Lt b u62-modulus) lb) -> (many (BTop bs) t))
  (match many (u62-lt-dec bn-one b (bnb-lt _ _ (BbZ _ flag-one-lt)) lb) _
    ((No _ _ _ _ le)
      (match erased r _
        ((BnE) (BTE))
        (absurd (Bn0 c m _ r1 bc) (lt-irrefl bn-one (lt-le-trans bn-one b bn-one (bn-two c m b (Bit0) r1 bc) (le-lt-succ b bn-one le))))
        (absurd (Bn1 c m _ r1 bc) (lt-irrefl bn-one (lt-le-trans bn-one b bn-one (bn-two c m b (Bit1) r1 bc) (le-lt-succ b bn-one le))))))
    ((Yes _ _ _ _ lt1)
      (let ((many x) (erased ba)) (u62-bit-test b (Zero) lb (LtZ _)))
      (let-match erased ba (BitAtZ m _ _ bc))
      (match many x _
        ((Bit0) (let-match erased r (Bn0 c _ _ _ bc0) (absurd (BnE) (lt-irrefl bn-one lt1)) (absurd (Bn1 _ _ _ _ bc1) (let ((erased _) (erased ex)) (bitcons-fn _ _ _ _ b bc1 bc)) ex)) (BT0 c))
        ((Bit1) (let-match erased r (Bn1 c _ _ _ bc1) (absurd (BnE) (lt-irrefl bn-one lt1)) (absurd (Bn0 _ _ _ _ bc0) (let ((erased _) (erased ex)) (bitcons-fn _ _ _ _ b bc0 bc)) ex)) (BT1 c))))))

(def-fns _ $ (erased shr1-bc : (erased (Nat) q v k r b m) (erased (Bit) x) (erased (Pow2 (Succ (Zero)) v) pv) (erased (Mul q v k) mm) (erased (Add k r b) a)
    (erased (Lt r v) rl) (erased (BitCons m x b) bc) -> (erased (Eq (Nat) q m) e))
  (let-match erased (pow2-fn _ v (Succ (Succ (Zero))) pv (PS (Zero) (Succ (Zero)) (Succ (Succ (Zero))) (P0) (DS (Zero) (Zero) (D0)))) (Refl _ _))
  (let ((erased dd)) (add-diag-double q k (mul-two q k mm)))
  (let ((erased y) (erased bq))
    (match erased rl (((Bit) y0) ((BitCons q y0 b) bq0))
      ((LtZ _) (let-match erased (add-fn k (Zero) b k a (add-zero-right k)) (Refl _ _)) (values (Bit0) (BC0 q k dd)))
      ((LtS r1 _ l1)
        (let-match erased l1 (LtZ _) (absurd (LtS _ _ l2) l2))
        (let-match erased (add-fn k (Succ (Zero)) b (Succ k) a (add-succ-right k (Zero) k (add-zero-right k))) (Refl _ _))
        (values (Bit1) (BC1 q k dd)))))
  (let ((erased em) (erased _)) (bitcons-fn q y m x b bq bc))
  em)

(def-fns _ $ (many bn-push0 : (erased (Nat) j) (erased (Bstack) bs) (many (Nat) b) (erased (Bn bs b) r) (erased (BnB (Succ j) b) k) ->
    (many (Nat) d) (erased (Bn (BP0 bs) d) r0) (erased (BnB j d) k0) (erased (Bn (BP1 bs) (Succ d)) r1) (erased (BnB j (Succ d)) k1))
  (let-match erased k (BbS _ _ e dd k1))
  (let ((erased l1)) (bnb-lt j (Succ e) k1))
  (values (u62-add b b e (bn-dadd b e dd) (lt-trans _ _ _ (lt-succ e) l1))
    (Bn0 bs b e r (BC0 b e dd)) (bnb-mono j (Succ e) e k1 (lt-weaken _ _ (lt-succ e))) (Bn1 bs b (Succ e) r (BC1 b e dd)) k1))

(def-fns _ $ (many bn-pop : (erased (Nat) j) (erased (Bstack) bs c) (many (Nat) b) (erased (Bn bs b) r) (erased (Popped bs c) pp) (erased (BnB (Succ j) b) k) ->
    (many (Nat) m) (erased (Bn c m) rc) (erased (BnB j m) km))
  (let ((erased lb)) (bnb-lt (Succ j) b k))
  (let ((many q) (erased v) (erased pv) (erased k2) (erased r2) (erased mm) (erased a) (erased rl) (erased _)) (u62-shr b bn-one lb bn-one-lt))
  (let ((erased m) (erased x) (erased rc) (erased bc))
    (match erased pp (((Nat) m0) ((Bit) x0) ((Bn c m0) rc0) ((BitCons m0 x0 b) bc0))
      ((Popped0 _) (let-match erased r (Bn0 _ m1 _ r1 bc1)) (values m1 (Bit0) r1 bc1))
      ((Popped1 _) (let-match erased r (Bn1 _ m1 _ r1 bc1)) (values m1 (Bit1) r1 bc1))))
  (let-match erased (shr1-bc q v k2 r2 b m x pv mm a rl bc) (Refl _ _))
  (values q rc (bnb-down j b q k (bc-le q b x bc))))

(def-fns _ $ (many bnb-c : (subterm many (Nat) j) (many (Nat) b) -> (many (ErasedMaybe (BnB j b)) r))
  (let-match many (nat-fits-u62 b) (Yes _ _ _ _ lb) ((No _ _ _ _ _) (ENone _)))
  (let-match many j (Succ j1) ((Zero) (ESome _ (BbZ b lb))))
  (let ((many d) (erased dd)) (double b))
  (let-match many (notail $ bnb-c j1 (Succ d)) (ESome _ r) ((ENone _) (ENone _)))
  (ESome _ (BbS j1 b d dd r)))
