(def-fns _ $ (erased look-ok : (erased (Nat) n k q) (erased (List (Tr)) m) (erased (Bool) b) (erased (Tr) t)
    (erased (Rows n k m) rw) (subterm erased (Look m q b t) lk) -> (erased (TrOK n t) ok))
  (match erased lk _
    ((Look0 _ _ _) (let-match erased rw (RowsS _ _ _ _ _ o0 _ _)) o0)
    ((Look1 _ _ _) (let-match erased rw (RowsS _ _ _ _ _ _ o1 _)) o1)
    ((LookS _ _ rest q1 _ _ lk1) (let-match erased rw (RowsS _ k1 _ _ _ _ _ rw1)) (look-ok n k1 q1 rest b t rw1 lk1))))

(def-adts
  ((Run : ((List (Tr)) m) ((Cfg) c0) ((Nat) t) ((Cfg) c) -> Type)
    enum
    (many RNil : (erased (List (Tr)) m) (erased (Cfg) c0) -> (Run m c0 (Zero) c0))
    (many RSnoc : (erased (List (Tr)) m) (erased (Cfg) c0 c d) (erased (Nat) t)
       (erased (Run m c0 t c) r) (erased (Step m c d) st) -> (Run m c0 (Succ t) d))))

(def-fns _ $ (erased run-add : (erased (List (Tr)) m) (erased (Cfg) c0 c) (erased (Nat) t s u)
    (subterm erased (Run m c0 t c) r) (erased (HaltsIn m c s) h) (erased (Add t s u) a) -> (erased (HaltsIn m c0 u) h0))
  (match erased r _
    ((RNil _ _) (let-match erased a (AddZero _)) h)
    ((RSnoc _ _ c1 _ t1 r1 st)
      (let-match erased a (AddSucc _ _ u1 a1))
      (run-add m c0 c1 t1 (Succ s) u r1 (HMove m c1 c s st h) (add-succ-right t1 s u1 a1)))))

(unary 5)

(def-adts
  ((Snoc : (Type A) ((List A) xs) (A y) ((List A) ys) -> Type)
    enum
    (many SnocNil : (erased Type A) (erased A y) -> (Snoc A (Nil A) y (Cons A y (Nil A))))
    (many SnocCons : (erased Type A) (erased A x y) (erased (List A) xs ys) (erased (Snoc A xs y ys) p)
       -> (Snoc A (Cons A x xs) y (Cons A x ys)))))

(def-adts
  ((Zip : (Type A) ((List A) xs) ((Nat) i) ((List A) as) (A x) ((List A) bs) -> Type)
    enum
    (many ZHere : (erased Type A) (erased A x) (erased (List A) bs) -> (Zip A (Cons A x bs) (Zero) (Nil A) x bs))
    (many ZThere : (erased Type A) (erased (List A) xs as as2 bs) (erased (Nat) i) (erased A x y)
       (erased (Zip A xs i as x bs) z) (erased (Snoc A as y as2) sn) -> (Zip A (Cons A y xs) (Succ i) as2 x bs))))

(def-fns _ $ (erased zip-nth : (erased Type A) (erased (List A) xs as bs) (erased (Nat) i) (erased A x)
    (subterm erased (Zip A xs i as x bs) z) -> (erased (Nth A xs i x) p))
  (match erased z _
    ((ZHere _ _ _) (NthHere A x bs))
    ((ZThere _ xs1 as1 _ _ i1 _ y z1 _) (NthThere A y xs1 i1 x (zip-nth A xs1 as1 bs i1 x z1)))))

(def-fns _ $ (erased zip-set : (erased Type A) (erased (List A) xs ys as bs) (erased (Nat) i) (erased A x w)
    (subterm erased (Zip A xs i as x bs) z) (erased (SetNth A xs i w ys) st) -> (erased (Zip A ys i as w bs) z2))
  (match erased z _
    ((ZHere _ _ _) (let-match erased st (SetHere _ _ _ _)) (ZHere A w bs))
    ((ZThere _ xs1 as1 _ _ i1 _ y z1 sn)
      (let-match erased st (SetThere _ _ _ _ _ ys1 st1))
      (ZThere A ys1 as1 as bs i1 w y (zip-set A xs1 ys1 as1 bs i1 x w z1 st1) sn))))

(def-fns _ $ (erased zip-right : (erased Type A) (erased (List A) xs as bs) (erased (Nat) i) (erased A x y)
    (subterm erased (Zip A xs i as x (Cons A y bs)) z) -> (erased (Zip A xs (Succ i) (Cons A x as) y bs) z2))
  (match erased z _
    ((ZHere _ _ _) (ZThere A (Cons A y bs) (Nil A) (Cons A x (Nil A)) bs (Zero) y x (ZHere A y bs) (SnocNil A x)))
    ((ZThere _ xs1 as1 _ _ i1 _ y0 z1 sn)
      (ZThere A xs1 (Cons A x as1) (Cons A x as) bs (Succ i1) y y0 (zip-right A xs1 as1 bs i1 x y z1)
        (SnocCons A x y0 as1 as sn)))))

(def-fns _ $ (erased zip-left : (erased Type A) (erased (List A) xs as bs) (erased (Nat) i) (erased A x a)
    (subterm erased (Zip A xs (Succ i) (Cons A a as) x bs) z) -> (erased (Zip A xs i as a (Cons A x bs)) z2))
  (let-match erased z (ZThere _ xs1 as1 _ _ _ _ y z1 sn))
  (match erased as1 _
    ((Nil _)
      (let-match erased sn (SnocNil _ _))
      (let-match erased z1 (ZHere _ _ _) (absurd (ZThere _ _ _ _ _ _ _ _ _ sn2) sn2))
      (ZHere A a (Cons A x bs)))
    ((Cons _ a1 as11)
      (let-match erased sn (SnocCons _ _ _ _ as2 sn1))
      (let-match erased i (Succ i2) (absurd (Zero) z1))
      (ZThere A xs1 as11 as (Cons A x bs) i2 a y (zip-left A xs1 as11 bs i2 x a z1) sn1))))

(unary 0)

(unary 1)

(let ((erased l0)) (prove-literal-lt 0 u8-modulus))

(let ((erased l1)) (prove-literal-lt 1 u8-modulus))

(let ((many z8)) (MkU8 (Zero) l0))

(let ((many o8)) (MkU8 (Succ (Zero)) l1))

(def-adts
  ((Enc : ((Bool) b) ((U8) u) -> Type)
    enum
    (many EncF : -> (Enc (BFalse) z8))
    (many EncT : -> (Enc (BTrue) o8))))

(def-fns _ $ (many enc : (many (Bool) b) -> (many (U8) u) (erased (Enc b u) e))
  (match many b _
    ((BFalse) (values z8 (EncF)))
    ((BTrue) (values o8 (EncT)))))

(def-adts
  ((AllF : ((List (U8)) as) -> Type)
    enum
    (many AFNil : -> (AllF (Nil (U8))))
    (many AFCons : (erased (List (U8)) as) (erased (AllF as) p) -> (AllF (Cons (U8) z8 as)))))

(def-adts
  ((Ext : ((List (Bool)) l) ((List (U8)) as) -> Type)
    enum
    (many ExtNil : (erased (List (U8)) as) (erased (AllF as) z) -> (Ext (Nil (Bool)) as))
    (many ExtCons : (erased (Bool) b) (erased (U8) u) (erased (List (Bool)) l) (erased (List (U8)) as) (erased (Enc b u) e) (erased (Ext l as) p)
       -> (Ext (Cons (Bool) b l) (Cons (U8) u as)))))

(def-fns _ $ (erased ext-pop : (erased (List (Bool)) l) (erased (U8) a) (erased (List (U8)) as)
    (erased (Ext l (Cons (U8) a as)) e) ->
    (erased (Bool) h2) (erased (List (Bool)) l2) (erased (Pop l h2 l2) pp) (erased (Enc h2 a) eq)
    (erased (Ext l2 as) e2))
  (match erased e _
    ((ExtNil _ z)
      (let-match erased z (AFCons _ z1))
      (values (BFalse) (Nil (Bool)) (PopNil) (EncF) (ExtNil as z1)))
    ((ExtCons b _ l1 _ en e1) (values b l1 (PopCons b l1) en e1))))

(def-fns _ $ (erased rep-allf : (erased (Nat) n) (erased (List (U8)) xs)
    (subterm erased (Repeat (U8) n z8 xs) p) -> (erased (AllF xs) z))
  (match erased p _
    ((RepeatNil _ _) (AFNil))
    ((RepeatCons _ n1 _ xs1 p1) (AFCons xs1 (rep-allf n1 xs1 p1)))))

(def-fns _ $ (erased rep-len : (erased (Nat) n) (erased (List (U8)) xs)
    (subterm erased (Repeat (U8) n z8 xs) p) -> (erased (Length (U8) xs n) l))
  (match erased p _
    ((RepeatNil _ _) (LengthNil _))
    ((RepeatCons _ n1 _ xs1 p1) (LengthCons _ _ xs1 n1 (rep-len n1 xs1 p1)))))

(def-fns _ $ (erased add-shift : (erased (Nat) a b c) (subterm erased (Add a (Succ b) c) p) -> (erased (Add (Succ a) b c) q))
  (match erased p _
    ((AddZero _) (AddSucc (Zero) b b (AddZero b)))
    ((AddSucc a1 _ c1 p1) (AddSucc (Succ a1) b c1 (add-shift a1 b c1 p1)))))

(def-fns _ $ (erased add-unshift : (erased (Nat) a b c) (erased (Add (Succ a) b c) p) -> (erased (Add a (Succ b) c) q))
  (let-match erased p (AddSucc _ _ c1 p1))
  (add-succ-right a b c1 p1))

(def-fns _ $ (erased add-cancel : (erased (Nat) a b b2 c) (subterm erased (Add a b c) p) (erased (Add a b2 c) p2) -> (erased (Eq (Nat) b b2) e))
  (match erased p _
    ((AddZero _) (let-match erased p2 (AddZero _)) (Refl (Nat) b))
    ((AddSucc a1 _ c1 p1) (let-match erased p2 (AddSucc _ _ _ p21)) (add-cancel a1 b b2 c1 p1 p21))))

(def-fns _ $ (erased right-bound : (erased (Nat) i j n m) (erased (Add i (Succ (Succ j)) n) p) (erased (Lt n m) nm) ->
    (erased (Lt (Succ i) m) l))
  (lt-trans (Succ i) n m (add-pos-lt (Succ i) (Succ j) n (add-shift i (Succ j) n p) (LtZ j)) nm))

(def-fns _ $ (erased splice-self : (erased Type A) (erased (List A) xs) (erased (Nat) n) (subterm erased (Length A xs n) l) ->
    (erased (Splice A xs (Zero) n xs xs) p))
  (match erased l _
    ((LengthNil _) (SpliceNil A xs))
    ((LengthCons _ x rest n1 l1) (SpliceHere A x x rest n1 rest rest (splice-self A rest n1 l1)))))

(def-fns _ $ (many seek : (subterm many (Nat) k) (erased (List (U8)) xs as bs) (many (Nat) i j) (erased (Nat) n)
    (erased (Zip (U8) xs i as z8 bs) z) (erased (AllF as) fa) (erased (AllF bs) fb)
    (erased (Length (U8) as i) la) (erased (Length (U8) bs j) lb) (erased (Add i (Succ j) n) ij) ->
    (many (Nat) i2 j2) (erased (List (U8)) as2 bs2) (erased (Zip (U8) xs i2 as2 z8 bs2) z2)
    (erased (AllF as2) fa2) (erased (AllF bs2) fb2) (erased (Length (U8) as2 i2) la2) (erased (Length (U8) bs2 j2) lb2)
    (erased (Add i2 (Succ j2) n) ij2))
  (let-match many k (Succ k1) ((Zero) (values i j as bs z fa fb la lb ij)))
  (let-match many j (Succ j1) ((Zero) (values i j as bs z fa fb la lb ij)))
  (let-match erased lb (LengthCons _ b bs1 _ lb1))
  (let-match erased fb (AFCons _ fb1))
  (tail $ seek k1 xs (Cons (U8) b as) bs1 (Succ i) j1 n
    (zip-right _ xs as bs1 i z8 b z) (AFCons as fa) fb1 (LengthCons _ _ as i la) lb1 (add-shift i (Succ j1) n ij)))

(def-fns _ $ (erased setnth-len : (erased Type A) (erased (List A) xs ys) (erased (Nat) i n) (erased A w)
    (subterm erased (SetNth A xs i w ys) st) (erased (Length A xs n) l) -> (erased (Length A ys n) l2))
  (match erased st _
    ((SetHere _ x _ rest) (let-match erased l (LengthCons _ _ _ n1 l1)) (LengthCons A w rest n1 l1))
    ((SetThere _ x rest i1 _ rest2 st1)
      (let-match erased l (LengthCons _ _ _ n1 l1))
      (LengthCons A x rest2 n1 (setnth-len A rest rest2 i1 n1 w st1 l1)))))

(let ((many two)) (Succ (Succ (Zero))))

(let ((many s60) (erased m60)) (mul (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))) (Succ (Succ eight))))

(let ((many s62) (erased a62)) (add s60 two))

(let ((erased e62))
  (match erased (mul-fn _ _ s60 sixty m60 sixty-mul) (((Eq (Nat) s62 sixty-two) e))
    ((Refl _ _) (add-fn sixty two s62 sixty-two a62 sixty-two-add))))

(let-match erased e62 (Refl _ _))

(let ((many d16)) (lt-dec 16 s62))

(comptime-match many d16 (Yes _ _ l16))

(let ((many N) (erased pN) (erased posN)) (pow2 16))

(let ((erased NM)) (pow2-lt 16 sixty-two N u62-modulus l16 pN u62-modulus-pow2))

(let ((many d40)) (lt-dec 40 s62))

(comptime-match many d40 (Yes _ _ l40))

(let ((many B40) (erased pB40) (erased posB40)) (pow2 40))

(let ((erased NM40)) (pow2-lt 40 sixty-two B40 u62-modulus l40 pB40 u62-modulus-pow2))

(unary 1)

(let ((many N1) (erased aN)) (sub N 1 (LtS (Zero) N posN)))

(let-match erased aN (AddSucc _ _ _ aN0))

(let-match erased aN0 (AddZero _))

(def-adts $ (Case : -> Type)
  enum
  (many MkCase : (many (List (Tr)) m) (many (Nat) n) (many (Nat) s) -> (Case)))

(def-adts
  ((AllHalt : ((List (Case)) cs) -> Type)
    enum
    (many AHNil : -> (AllHalt (Nil (Case))))
    (many AHCons : (erased (List (Tr)) m) (erased (Nat) n s) (erased (List (Case)) rest) (erased (Rows n n m) w)
       (erased (HaltsIn m (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) h) (erased (AllHalt rest) p)
       -> (AllHalt (Cons (Case) (MkCase m n s) rest)))))

(def-adts
  ((Checked : ((List (Tr)) m) ((Nat) n) ((Nat) s) -> Type)
    enum
    (many MkChecked : (erased (List (Tr)) m) (erased (Nat) n s) (erased (Rows n n m) w)
       (erased (HaltsIn m (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) h) -> (Checked m n s))))

(def-fns _ $ (many trok : (many (Nat) n) (many (Tr) t) -> (many (Res (TrOK n t)) r))
  (let-match many t (Go w d q) ((Halt) (ROk _ (OKHalt n))))
  (let-match many (lt-dec q n) (Yes _ _ p) ((No _ _ _) (RFail _)))
  (ROk _ (OKGo n q w d p)))

(def-fns _ $ (many rows-check : (many (Nat) n) (subterm many (Nat) k) (many (List (Tr)) m) -> (many (Res (Rows n k m)) r))
  (match many k _
    ((Zero) (let-match many m (Nil _) ((Cons _ _ _) (RFail _))) (ROk _ (RowsZ n)))
    ((Succ k1)
      (let-match many m (Cons _ t0 m1) ((Nil _) (RFail _)))
      (let-match many m1 (Cons _ t1 rest) ((Nil _) (RFail _)))
      (let-match many (trok n t0) (ROk _ o0) ((RFail _) (RFail _)))
      (let-match many (trok n t1) (ROk _ o1) ((RFail _) (RFail _)))
      (let-match many (notail $ rows-check n k1 rest) (ROk _ rw) ((RFail _) (RFail _)))
      (ROk _ (RowsS n k1 t0 t1 rest o0 o1 rw)))))

(def-adts
  ((Start : ((List (U8)) xs) -> Type)
    enum
    (many MkStart : (erased (List (U8)) xs as bs) (many (Nat) i j) (erased (Zip (U8) xs i as z8 bs) z)
       (erased (AllF as) fa) (erased (AllF bs) fb) (erased (Length (U8) as i) la) (erased (Length (U8) bs j) lb)
       (erased (Add i (Succ j) N) ij) -> (Start xs))))

(def-fns _ $ (erased add-succ-inv : (erased (Nat) a b c) (erased (Add a (Succ b) (Succ c)) p) -> (erased (Add a b c) q))
  (let ((erased c1) (erased e) (erased q1)) (add-succ-right-inv a b (Succ c) p))
  (let-match erased e (Refl _ _))
  q1)

(def-fns _ $ (erased double-add : (erased (Nat) a b) (subterm erased (Double a b) d) -> (erased (Add a a b) p))
  (match erased d _
    ((D0) (AddZero (Zero)))
    ((DS a1 b1 d1) (AddSucc a1 (Succ a1) (Succ b1) (add-succ-right a1 a1 b1 (double-add a1 b1 d1))))))

(def-fns _ $ (erased splice-set : (erased Type A) (erased (List A) tx ws xs xs2) (erased (Nat) lo len i e) (erased A w)
    (subterm erased (Splice A tx lo len ws xs) sp) (erased (SetNth A xs i w xs2) st) (erased (Add lo e i) ad) (erased (Lt e len) lt) ->
    (erased (List A) ws2) (erased (Splice A tx lo len ws2 xs2) sp2))
  (match erased sp _
    (absurd (SpliceNil _ _) lt)
    ((SpliceThere _ x tx1 lo1 _ _ xs1 sp1)
      (let-match erased ad (AddSucc _ _ i1 ad1))
      (let-match erased st (SetThere _ _ _ _ _ xs21 st1))
      (let ((erased ws2) (erased sp21)) (splice-set A tx1 ws xs1 xs21 lo1 len i1 e w sp1 st1 ad1 lt))
      (values ws2 (SpliceThere A x tx1 lo1 len ws2 xs21 sp21)))
    ((SpliceHere _ x y tx1 len1 ws1 xs1 sp1)
      (let-match erased ad (AddZero _))
      (match erased st _
        ((SetHere _ _ _ _) (values (Cons A w ws1) (SpliceHere A x w tx1 len1 ws1 xs1 sp1)))
        ((SetThere _ _ _ e1 _ xs21 st1)
          (let-match erased lt (LtS _ _ lt1))
          (let ((erased ws2) (erased sp21)) (splice-set A tx1 ws1 xs1 xs21 (Zero) len1 e1 e1 w sp1 st1 (AddZero e1) lt1))
          (values (Cons A y ws2) (SpliceHere A x y tx1 len1 ws2 xs21 sp21)))))))

(def-fns _ $ (erased splice-restore : (erased Type A) (erased (List A) tx ws xs ys zs) (erased (Nat) lo len)
    (subterm erased (Splice A tx lo len ws xs) p) (erased (Splice A xs lo len ys zs) q) (erased (Splice A tx lo len ys tx) r) ->
    (erased (Eq (List A) zs tx) e))
  (match erased p _
    ((SpliceNil _ _) (let-match erased q (SpliceNil _ _)) (Refl _ zs))
    ((SpliceThere _ x tx1 lo1 _ _ xs1 p1)
      (let-match erased q (SpliceThere _ _ _ _ _ _ zs1 q1))
      (let-match erased r (SpliceThere _ _ _ _ _ _ _ r1))
      (let-match erased (splice-restore A tx1 ws xs1 ys zs1 lo1 len p1 q1 r1) (Refl _ _))
      (Refl _ zs))
    ((SpliceHere _ x y tx1 len1 ws1 xs1 p1)
      (let-match erased q (SpliceHere _ _ y2 _ _ ys1 zs1 q1))
      (let-match erased r (SpliceHere _ _ _ _ _ _ _ r1))
      (let-match erased (splice-restore A tx1 ws1 xs1 ys1 zs1 (Zero) len1 p1 q1 r1) (Refl _ _))
      (Refl _ zs))))

(def-fns _ $ (erased le-pos : (erased (Nat) a b) (erased (Lt (Succ a) (Succ b)) p) -> (erased (Nat) b1) (erased (Eq (Nat) b (Succ b1)) e))
  (let-match erased p (LtS _ _ p1))
  (let-match erased p1 (LtS _ b1 _) ((LtZ b1) (values b1 (Refl _ b))))
  (values b1 (Refl _ b)))

(def-adts $ (BTr : -> Type)
  enum
  (many BHalt : -> (BTr))
  (many BGo : (many (U8) wu) (many (Dir) d) (many (Nat) q) -> (BTr)))

(def-adts
  ((TrB : ((Tr) t) ((BTr) bt) -> Type)
    enum
    (many TBH : -> (TrB (Halt) (BHalt)))
    (many TBG : (erased (Bool) w) (erased (U8) wu) (erased (Dir) d) (erased (Nat) q) (erased (Enc w wu) e)
       -> (TrB (Go w d q) (BGo wu d q)))))

(def-fns _ $ (erased splice-same : (erased Type A) (erased (List A) tx ws ds) (erased (Nat) lo len)
    (subterm erased (Splice A tx lo len ws ds) p) -> (erased (List A) old) (erased (Splice A ds lo len old ds) q))
  (match erased p _
    ((SpliceNil _ _) (values (Nil A) (SpliceNil A ds)))
    ((SpliceThere _ x tx1 lo1 _ _ ds1 p1)
      (let ((erased o) (erased q1)) (splice-same A tx1 ws ds1 lo1 len p1))
      (values o (SpliceThere A x ds1 lo1 len o ds1 q1)))
    ((SpliceHere _ x y tx1 len1 ws1 ds1 p1)
      (let ((erased o) (erased q1)) (splice-same A tx1 ws1 ds1 (Zero) len1 p1))
      (values (Cons A y o) (SpliceHere A y y ds1 len1 o ds1 q1)))))

(def-fns _ $ (erased add-zero-eq : (erased (Nat) a b) (erased (Add a (Zero) b) p) -> (erased (Eq (Nat) b a) e))
  (add-fn a (Zero) b a p (add-zero-right a)))

(def-fns _ $ (erased slack-pos : (erased (Nat) a s b) (erased (Add a s b) p) (erased (Apart (Nat) Lt a b) ap) ->
    (erased (Nat) s1) (erased (Eq (Nat) s (Succ s1)) e))
  (match erased s _
    ((Zero) (let-match erased (add-zero-eq a b p) (Refl _ _)) (values (Zero) (match erased (apart-irrefl a ap) _)))
    ((Succ s1) (values s1 (Refl _ s)))))

(def-adts $ (BRow : -> Type)
  enum
  (many MkBRow : (many (BTr) b0) (many (BTr) b1) -> (BRow)))

(def-adts
  ((RowsB : ((List (Tr)) m) ((List (Copy (BRow))) rs) -> Type)
    enum
    (many RBNil : -> (RowsB (Nil (Tr)) (Nil (Copy (BRow)))))
    (many RBCons : (erased (Tr) t0 t1) (erased (BTr) b0 b1) (erased (List (Tr)) m) (erased (List (Copy (BRow))) rs)
       (erased (TrB t0 b0) p0) (erased (TrB t1 b1) p1) (erased (RowsB m rs) rest)
       -> (RowsB (Cons (Tr) t0 (Cons (Tr) t1 m)) (Cons (Copy (BRow)) (MkCopy (BRow) (MkBRow b0 b1)) rs)))))

(def-adts
  ((RowsR : ((List (Tr)) m) -> Type)
    enum
    (many RROk : (erased (List (Tr)) m) (many (List (Copy (BRow))) rs) (erased (RowsB m rs) p) -> (RowsR m))
    (many RRNo : (erased (List (Tr)) m) -> (RowsR m))))

(def-fns _ $ (erased lt-nth : (erased Type A) (erased (List A) xs) (erased (Nat) n q) (subterm erased (Length A xs n) l) (erased (Lt q n) lt) ->
    (erased A x) (erased (Nth A xs q x) p))
  (let-match erased l (LengthCons _ y rest n1 l1) (absurd (LengthNil _) lt))
  (match erased q _
    ((Zero) (values y (NthHere A y rest)))
    ((Succ q1)
      (let-match erased lt (LtS _ _ lt1))
      (let ((erased x) (erased p1)) (lt-nth A rest n1 q1 l1 lt1))
      (values x (NthThere A y rest q1 x p1)))))

(def-fns _ $ (erased le-lt : (erased (Nat) x y z) (erased (Lt x (Succ y)) p) (erased (Lt y z) q) -> (erased (Lt x z) r))
  (match erased (lt-succ-cases x y p) _
    ((InL _ _ e) (let-match erased e (Refl _ _)) q)
    ((InR _ _ l) (lt-trans x y z l q))))

(def-adts
  ((TrD : ((Tr) t) ((BTr) bt) -> Type)
    enum
    (many TDH : -> (TrD (Halt) (BHalt)))
    (many TDG : (erased (Bool) w) (erased (U8) wu) (erased (Dir) d) (erased (Nat) q qq) (erased (Enc w wu) e) (erased (Double q qq) dq)
       -> (TrD (Go w d q) (BGo wu d qq)))))

(def-adts
  ((MapB : ((List (Tr)) m) ((List (Copy (BTr))) fa) -> Type)
    enum
    (many MBNil : -> (MapB (Nil (Tr)) (Nil (Copy (BTr)))))
    (many MBCons : (erased (Tr) t) (erased (BTr) bt) (erased (List (Tr)) m) (erased (List (Copy (BTr))) fa)
       (erased (TrD t bt) p) (erased (MapB m fa) rest) -> (MapB (Cons (Tr) t m) (Cons (Copy (BTr)) (MkCopy (BTr) bt) fa)))))

(def-adts
  ((Idx : ((Nat) a) ((Bool) h) ((Nat) k) -> Type)
    enum
    (many IdxF : (erased (Nat) a) -> (Idx a (BFalse) a))
    (many IdxT : (erased (Nat) a) -> (Idx a (BTrue) (Succ a)))))

(def-fns _ $ (many map-b : (subterm many (List (Tr)) m) -> (many (List (Copy (BTr))) fa) (erased (MapB m fa) p))
  (let-match many m (Cons _ t rest) ((Nil _) (values (Nil (Copy (BTr))) (MBNil))))
  (let ((many fa) (erased p)) (notail $ map-b rest))
  (match many t _
    ((Halt) (values (Cons (Copy (BTr)) (MkCopy (BTr) (BHalt)) fa) (MBCons t (BHalt) rest fa (TDH) p)))
    ((Go w d q)
      (let ((many wu) (erased e)) (enc w))
      (let ((many qq) (erased dq)) (double q))
      (values (Cons (Copy (BTr)) (MkCopy (BTr) (BGo wu d qq)) fa) (MBCons t (BGo wu d qq) rest fa (TDG w wu d q qq e dq) p)))))

(def-fns _ $ (erased map-nth : (erased (List (Tr)) m) (erased (List (Copy (BTr))) fa) (erased (Nat) k) (erased (BTr) bt)
    (subterm erased (Nth (Copy (BTr)) fa k (MkCopy (BTr) bt)) p) (erased (MapB m fa) mb) ->
    (erased (Tr) t) (erased (Nth (Tr) m k t) nt) (erased (TrD t bt) td))
  (match erased p _
    ((NthHere _ _ _) (let-match erased mb (MBCons t _ rest _ td _)) (values t (NthHere (Tr) t rest) td))
    ((NthThere _ _ fa1 k1 _ p1)
      (let-match erased mb (MBCons t0 _ rest _ _ mb1))
      (let ((erased t) (erased nt) (erased td)) (map-nth rest fa1 k1 bt p1 mb1))
      (values t (NthThere (Tr) t0 rest k1 t nt) td))))

(def-fns _ $ (erased mapb-len : (erased (List (Tr)) m) (erased (List (Copy (BTr))) fa) (erased (Nat) n)
    (subterm erased (MapB m fa) mb) (erased (Length (Tr) m n) l) -> (erased (Length (Copy (BTr)) fa n) l2))
  (match erased mb _
    ((MBNil) (let-match erased l (LengthNil _)) (LengthNil _))
    ((MBCons _ _ rest fa1 _ mb1)
      (let-match erased l (LengthCons _ _ _ n1 l1))
      (LengthCons _ _ fa1 n1 (mapb-len rest fa1 n1 mb1 l1)))))

(def-fns _ $ (erased rows-len : (erased (Nat) n k b) (erased (List (Tr)) m) (subterm erased (Rows n k m) rw) (erased (Double k b) d) ->
    (erased (Length (Tr) m b) l))
  (match erased rw _
    ((RowsZ _) (let-match erased d (D0)) (LengthNil _))
    ((RowsS _ k1 t0 t1 rest _ _ rw1)
      (let-match erased d (DS _ b1 d1))
      (LengthCons _ t0 (Cons (Tr) t1 rest) (Succ b1) (LengthCons _ t1 rest b1 (rows-len n k1 b1 rest rw1 d1))))))

(def-fns _ $ (erased idx-lt : (erased (Nat) q n a b) (subterm erased (Lt q n) lt) (erased (Double q a) da) (erased (Double n b) db) ->
    (erased (Lt (Succ a) b) r))
  (match erased lt _
    ((LtZ n1)
      (let-match erased da (D0))
      (let-match erased db (DS _ b1 _))
      (LtS (Zero) (Succ b1) (LtZ b1)))
    ((LtS q1 n1 lt1)
      (let-match erased da (DS _ a1 da1))
      (let-match erased db (DS _ b1 db1))
      (LtS (Succ (Succ a1)) (Succ b1) (LtS (Succ a1) b1 (idx-lt q1 n1 a1 b1 lt1 da1 db1))))))

(def-fns _ $ (erased idx-look : (erased (Nat) n kk q a k) (erased (List (Tr)) m) (erased (Bool) h) (erased (Tr) t)
    (subterm erased (Rows n kk m) rw) (erased (Lt q kk) lq) (erased (Double q a) da) (erased (Idx a h k) ix) (erased (Nth (Tr) m k t) nt) ->
    (erased (Look m q h t) lk))
  (let-match erased rw (RowsS _ k1 t0 t1 rest _ _ rw1) (absurd (RowsZ _) lq))
  (match erased q _
    ((Zero)
      (let-match erased da (D0))
      (match erased ix _
        ((IdxF _) (let-match erased nt (NthHere _ _ _)) (Look0 t0 t1 rest))
        ((IdxT _) (let-match erased nt (NthThere _ _ _ _ _ nt1)) (let-match erased nt1 (NthHere _ _ _)) (Look1 t0 t1 rest))))
    ((Succ q1)
      (let-match erased da (DS _ a1 da1))
      (let-match erased lq (LtS _ _ lq1))
      (match erased ix _
        ((IdxF _)
          (let-match erased nt (NthThere _ _ _ _ _ nt1))
          (let-match erased nt1 (NthThere _ _ _ _ _ nt2))
          (LookS t0 t1 rest q1 h t (idx-look n k1 q1 a1 a1 rest h t rw1 lq1 da1 (IdxF a1) nt2)))
        ((IdxT _)
          (let-match erased nt (NthThere _ _ _ _ _ nt1))
          (let-match erased nt1 (NthThere _ _ _ _ _ nt2))
          (LookS t0 t1 rest q1 h t (idx-look n k1 q1 a1 (Succ a1) rest h t rw1 lq1 da1 (IdxT a1) nt2)))))))

(def-fns _ $ (many wsim : (erased (List (Tr)) m) (erased (List (Copy (BTr))) fa) (many (Array (Copy (BTr)) fa) fx) (erased (MapB m fa) mb) (many (Nat) F) (subterm many (Nat) fuel)
    (erased (Cfg) c0) (erased (Nat) t) (erased (Nat) q) (many (Nat) qq)
    (erased (List (Bool)) l r) (erased (Bool) h) (erased (U8) x) (erased (Enc h x) ex)
    (erased (List (U8)) xs) (unique (Bytes xs) a) (many (Nat) i) (erased (Nat) j) (erased (List (U8)) as bs)
    (erased (Nat) sl sr) (many (Nat) lo hi) (erased (List (U8)) tx ws) (erased (Nat) len)
    (erased (Lt lo u62-modulus) blo) (erased (Lt hi u62-modulus) bhi)
    (erased (Splice (U8) tx lo len ws xs) sp) (erased (Add lo sl i) ai) (erased (Add sl (Succ sr) len) aw) (erased (Add i sr hi) ah)
    (erased (Lt sr (Succ j)) lsr)
    (erased (Run m c0 t (MkCfg q l h r)) run) (erased (Zip (U8) xs i as x bs) z)
    (erased (Ext l as) xl) (erased (Ext r bs) xr) (erased (Length (U8) as i) la) (erased (Length (U8) bs j) lb)
    (erased (Nat) N) (erased (Add i (Succ j) N) ij) (erased (Lt N u62-modulus) nm) (erased (Add t fuel F) tf) (erased (Lt F u62-modulus) bF)
    (erased (Nat) n) (erased (Rows n n m) wf) (erased (Lt q n) lq) (erased (Double q qq) dq) (erased (Nat) b2) (erased (Double n b2) db) (erased (Length (Copy (BTr)) fa b2) lfa) (erased (Lt b2 u62-modulus) b2m) (erased (Length (U8) xs N) lx) ->
    (many (SimR m c0) res) (erased (List (U8)) ys) (unique (Bytes ys) out) (erased (List (U8)) ws2)
    (erased (Splice (U8) tx lo len ws2 ys) sp2) (erased (Length (U8) ys N) ly))
  (let ((erased bf)) (le-lt fuel F u62-modulus (add-le-left fuel t F (add-comm t fuel F tf)) bF))
  (let-match many (u62-eq (Zero) fuel u62-modulus-pos bf) (Unequal _ _ _ _ apf) ((Equal _ _ _) (values (SRun m c0) xs a ws sp lx)))
  (let ((erased f0) (erased ef)) (slack-pos (Zero) fuel fuel (AddZero fuel) apf))
  (let-match erased ef (Refl _ _))
  (let ((many f)) (u62-dec f0 fuel bf))
  (let ((many u) (unique a1)) (bytes-get _ a i x (zip-nth _ xs as bs i _ z)))
  (let-match many u (MkU8 nb _))
  (let ((erased k) (erased ad) (erased lkb) (erased ix))
    (match erased ex (((Nat) k) ((Add qq nb k) ad) ((Lt k b2) lkb) ((Idx qq h k) ix))
      ((EncF) (values qq (add-zero-right qq) (lt-trans qq (Succ qq) b2 (lt-succ qq) (idx-lt q n qq b2 lq dq db)) (IdxF qq)))
      ((EncT) (values (Succ qq) (add-succ-right qq (Zero) qq (add-zero-right qq)) (idx-lt q n qq b2 lq dq db) (IdxT qq)))))
  (let ((many kk)) (u62-add qq nb k ad (lt-trans k b2 u62-modulus lkb b2m)))
  (let ((erased cx) (erased np)) (lt-nth _ fa b2 k lfa lkb))
  (let ((many cell)) (array-get-many _ _ fx kk cx np))
  (let-match many cell (MkCopy _ bt))
  (let ((erased tr) (erased nt) (erased tbt)) (map-nth m fa k bt np mb))
  (let ((erased lk)) (idx-look n n q qq k m h tr wf lq dq ix nt))
  (let-match many bt (BGo wu d qq2)
    ((BHalt)
      (let-match erased tbt (TDH))
      (let ((many c) (erased ac)) (sub F fuel (add-le-left _ _ _ (add-comm t fuel F tf))))
      (let-match erased (add-cancel fuel t c F (add-comm t fuel F tf) ac) (Refl _ _))
      (values (SHalt m c0 (Succ c) (run-add m c0 (MkCfg q l h r) t (Succ (Zero)) (Succ t) run (HStop m q l r h lk)
        (add-succ-right t (Zero) t (add-zero-right t)))) xs a1 ws sp lx)))
  (let-match erased tbt (TDG w _ _ q2 _ ew dq2))
  (let-match erased (look-ok n n q m h _ wf lk) (OKGo _ _ _ _ lq2))
  (let ((erased ys) (unique a2) (erased st)) (bytes-set _ a1 i wu x (zip-nth _ xs as bs i _ z)))
  (let ((erased z2)) (zip-set _ xs ys as bs i x wu z st))
  (let ((erased lx2)) (setnth-len _ xs ys i N wu st lx))
  (let ((erased ws3) (erased sp3)) (splice-set _ tx ws xs ys lo len i sl wu sp st ai (add-pos-lt sl (Succ sr) len aw (LtZ sr))))
  (let ((erased tf2)) (add-shift t f F tf))
  (let ((erased bi)) (lt-trans i N u62-modulus (add-pos-lt i (Succ j) N ij (LtZ j)) nm))
  (match many d _
    ((DL)
      (let-match many (u62-eq lo i blo bi) (Unequal _ _ _ _ apl) ((Equal _ _ _) (values (SRun m c0) ys a2 ws3 sp3 lx2)))
      (let ((erased sl1) (erased es)) (slack-pos lo sl i ai apl))
      (let-match erased es (Refl _ _))
      (let ((erased ai1)) (add-shift lo sl1 i ai))
      (let-match erased ai1 (AddSucc _ _ i1 ai2))
      (let-match erased la (LengthCons _ a0 as1 _ la1))
      (let ((erased h2) (erased l2) (erased pp) (erased e2) (erased xl2)) (ext-pop l a0 as1 xl))
      (tail $ wsim m fa fx mb F f c0 (Succ t) q2 qq2 l2 (Cons (Bool) w r) h2 a0 e2 ys a2 (u62-dec i1 i bi) (Succ j) as1 (Cons (U8) wu bs)
        sl1 (Succ sr) lo hi tx ws3 len blo bhi sp3 (add-succ-inv lo sl1 i1 ai) (add-unshift sl1 (Succ sr) len aw) (add-unshift i1 sr hi ah)
        (LtS sr (Succ j) lsr)
        (RSnoc m c0 (MkCfg q l h r) _ t run (StepL m q q2 l r l2 h w h2 lk pp))
        (zip-left _ ys as1 bs i1 wu a0 z2)
        xl2 (ExtCons w wu r bs ew xr) la1 (LengthCons _ _ bs j lb) N (add-unshift i1 (Succ j) N ij) nm tf2 bF n wf lq2 dq2 b2 db lfa b2m lx2))
    ((DR)
      (let-match many (u62-eq i hi bi bhi) (Unequal _ _ _ _ aph) ((Equal _ _ _) (values (SRun m c0) ys a2 ws3 sp3 lx2)))
      (let ((erased sr1) (erased es)) (slack-pos i sr hi ah aph))
      (let-match erased es (Refl _ _))
      (let ((erased j1) (erased ej)) (le-pos sr1 j lsr))
      (let-match erased ej (Refl _ _))
      (let-match erased lb (LengthCons _ b0 bs1 _ lb1))
      (let ((erased h2) (erased r2) (erased pp) (erased e2) (erased xr2)) (ext-pop r b0 bs1 xr))
      (let-match erased lsr (LtS _ _ lsr1))
      (tail $ wsim m fa fx mb F f c0 (Succ t) q2 qq2 (Cons (Bool) w l) r2 h2 b0 e2 ys a2 (u62-inc i (right-bound i j1 N u62-modulus ij nm)) j1
        (Cons (U8) wu as) bs1
        (Succ sl) sr1 lo hi tx ws3 len blo bhi sp3 (add-succ-right lo sl i ai) (add-shift sl (Succ sr1) len aw) (add-shift i sr1 hi ah) lsr1
        (RSnoc m c0 (MkCfg q l h r) _ t run (StepR m q q2 l r r2 h w h2 lk pp))
        (zip-right _ ys as bs1 i wu b0 z2)
        (ExtCons w wu l as ew xl) xr2 (LengthCons _ _ as i la) lb1 N (add-shift i (Succ j1) N ij) nm tf2 bF n wf lq2 dq2 b2 db lfa b2m lx2))))

(def-adts
  ((Win : ((List (U8)) tx) ((Nat) i) ((Nat) j) -> Type)
    enum
    (many MkWin : (erased (List (U8)) tx) (erased (Nat) i j) (many (Nat) lo len sl sr) (erased (List (U8)) ws)
       (erased (Splice (U8) tx lo len ws tx) sp) (erased (Add lo sl i) ai) (erased (Add sl (Succ sr) len) aw)
       (erased (Lt sl (Succ i)) lsl) (erased (Lt sr (Succ j)) lsr) -> (Win tx i j))))

(def-fns _ $ (many window : (many (Nat) s) (erased (List (U8)) tx) (erased (Length (U8) tx N) ltx) (many (Nat) i j)
    (erased (Add i (Succ j) N) ij) -> (many (Win tx i j) w))
  (let ((many full)) (MkWin tx i j (Zero) N i j tx (splice-self _ tx N ltx) (AddZero i) ij (lt-succ i) (lt-succ j)))
  (let-match many (lt-dec s i) (Yes _ _ pi) ((No _ _ _) full))
  (let-match many (lt-dec s j) (Yes _ _ pj) ((No _ _ _) full))
  (let ((many lo) (erased al)) (sub i s (lt-weaken s i pi)))
  (let ((many d) (erased dd)) (double s))
  (let ((many e) (erased ae)) (add lo (Succ d)))
  (let-match many (lt-dec e (Succ N)) (Yes _ _ pe) ((No _ _ _) full))
  (let ((erased ws) (erased sp)) (splice-range _ tx N ltx lo (Succ d) e ae pe))
  (MkWin tx i j lo (Succ d) s s ws sp (add-comm s lo i al) (add-succ-right s s d (double-add s d dd)) (lt-weaken s i pi) (lt-weaken s j pj)))

(def-fns _ $ (many check-case : (many (List (Tr)) m) (many (Nat) n s) (erased (List (U8)) tx) (many (Bytes tx) tmpl)
    (erased (Length (U8) tx N) ltx) (many (Start tx) st) (unique (Bytes tx) a) ->
    (many (Res (Checked m n s)) r) (unique (Bytes tx) a2))
  (let-match many st (MkStart _ as bs i j z fa fb la lb ij))
  (let-match many (rows-check n n m) (ROk _ wf) ((RFail _) (values (RFail _) a)))
  (let-match many (lt-dec (Zero) n) (Yes _ _ lq0) ((No _ _ _) (values (RFail _) a)))
  (let ((many ft) (erased mb)) (map-b m))
  (let ((unique fxu)) (list-to-array _ ft))
  (let ((many fx)) (share fxu))
  (let ((many b2) (erased db)) (double n))
  (let-match many (lt-dec b2 B40) (Yes _ _ pb2) ((No _ _ _) (values (RFail _) a)))
  (let-match many (window s tx ltx i j ij) (MkWin _ _ _ lo len sl sr ws0 sp0 ai aw lsl lsr))
  (let ((many hi) (erased ah)) (add i sr))
  (let-match many (lt-dec s B40) (Yes _ _ ps) ((No _ _ _) (values (RFail _) a)))
  (let ((erased bs40)) (lt-trans s B40 u62-modulus ps NM40))
  (let-match many (lt-dec lo N) (Yes _ _ plo) ((No _ _ _) (values (RFail _) a)))
  (let-match many (lt-dec hi N) (Yes _ _ phi) ((No _ _ _) (values (RFail _) a)))
  (let ((many res) (erased ys) (unique a1) (erased ws2) (erased sp2) (erased ly))
    (wsim m ft fx mb s s (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) (Zero) (Zero) (Zero) (Nil (Bool)) (Nil (Bool)) (BFalse) z8 (EncF)
      tx a i j as bs sl sr lo hi tx ws0 len (lt-trans lo N u62-modulus plo NM) (lt-trans hi N u62-modulus phi NM) sp0 ai aw ah lsr
      (RNil m (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool)))) z (ExtNil as fa) (ExtNil bs fb) la lb
      N ij NM (AddZero s) bs40 n wf lq0 (D0) b2 db (mapb-len m ft b2 mb (rows-len n n b2 m wf db)) (lt-trans b2 B40 u62-modulus pb2 NM40) ltx))
  (let ((erased old) (erased spo)) (splice-same _ tx ws2 ys lo len sp2))
  (let ((erased zs) (unique a4) (erased sp)) (bytes-blit _ tmpl lo _ a1 lo len ws0 sp0 old spo))
  (let-match erased (splice-restore _ tx ws2 ys ws0 zs lo len sp2 sp sp0) (Refl _ _))
  (let-match many res (SHalt _ _ s2 hh) ((SRun _ _) (values (RFail _) a4)))
  (let-match many (nat-eq s2 s) (Equal _ _ _) ((Unequal _ _ _ _ _) (values (RFail _) a4)))
  (values (ROk _ (MkChecked m n s wf hh)) a4))

(def-fns _ $ (many check-all : (subterm many (List (Case)) cs) (erased (List (U8)) tx) (many (Bytes tx) tmpl)
    (erased (Length (U8) tx N) ltx) (many (Start tx) st) (unique (Bytes tx) a) -> (many (Res (AllHalt cs)) r))
  (let-match many cs (Cons _ c rest) ((Nil _) (ROk _ (AHNil))))
  (let-match many c (MkCase m n s))
  (let ((many rc) (unique a2)) (check-case m n s tx tmpl ltx st a))
  (let-match many rc (ROk _ ck) ((RFail _) (RFail _)))
  (let-match erased ck (MkChecked _ _ _ wf hh))
  (let-match many (notail $ check-all rest tx tmpl ltx st a2) (ROk _ ah) ((RFail _) (RFail _)))
  (ROk _ (AHCons m n s rest wf hh ah)))

(def-fns _ $ (erased ah-get : (erased (List (Case)) cs) (erased (List (Tr)) m) (erased (Nat) n s)
    (erased (AllHalt cs) ah) (subterm erased (Mem (Case) (MkCase m n s) cs) mm) ->
    (erased (HaltsIn m (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) h))
  (match erased mm _
    ((MemHere _ _ _) (let-match erased ah (AHCons _ _ _ _ _ h _)) h)
    ((MemThere _ _ _ rest mm1) (let-match erased ah (AHCons _ _ _ _ _ _ ah1)) (ah-get rest m n s ah1 mm1))))

(def-fns _ $ (erased rep-same : (erased (Nat) n) (erased (List (U8)) xs ys) (subterm erased (Repeat (U8) n z8 xs) p) (erased (Repeat (U8) n z8 ys) p2) ->
    (erased (Eq (List (U8)) xs ys) e))
  (match erased p _
    ((RepeatNil _ _) (let-match erased p2 (RepeatNil _ _)) (Refl _ xs))
    ((RepeatCons _ n1 _ xs1 p1)
      (let-match erased p2 (RepeatCons _ _ _ ys1 p21))
      (let-match erased (rep-same n1 xs1 ys1 p1 p21) (Refl _ _))
      (Refl _ xs))))

(def-adts
  ((Got : (Type A) ((TyCtor ((Char) c) (A a) -> Type) R) ((Char) c) -> Type)
    enum
    (many GotOk : (erased Type A) (erased (TyCtor ((Char) c) (A a) -> Type) R) (erased (Char) c) (many A a) (erased (R c a) p) -> (Got A R c))
    (many GotNo : (erased Type A) (erased (TyCtor ((Char) c) (A a) -> Type) R) (erased (Char) c) -> (Got A R c))))

(def-adts
  ((CharBit : ((Char) c) ((Bool) b) -> Type)
    enum
    (many CB0 : -> (CharBit #\0 (BFalse)))
    (many CB1 : -> (CharBit #\1 (BTrue)))))

(def-adts
  ((CharDir : ((Char) c) ((Dir) d) -> Type)
    enum
    (many CDL : -> (CharDir #\L (DL)))
    (many CDR : -> (CharDir #\R (DR)))))

(def-adts
  ((CharSt : ((Char) c) ((Nat) q) -> Type)
    enum
    (many CSA : -> (CharSt #\A (Zero)))
    (many CSB : -> (CharSt #\B (Succ (Zero))))
    (many CSC : -> (CharSt #\C (Succ (Succ (Zero)))))
    (many CSD : -> (CharSt #\D (Succ (Succ (Succ (Zero))))))
    (many CSE : -> (CharSt #\E (Succ (Succ (Succ (Succ (Zero)))))))))

(def-adts
  ((CharDig : ((Char) c) ((Nat) d) -> Type)
    enum
    (many CD0 : -> (CharDig #\0 0)) (many CD1 : -> (CharDig #\1 1)) (many CD2 : -> (CharDig #\2 2))
    (many CD3 : -> (CharDig #\3 3)) (many CD4 : -> (CharDig #\4 4)) (many CD5 : -> (CharDig #\5 5))
    (many CD6 : -> (CharDig #\6 6)) (many CD7 : -> (CharDig #\7 7)) (many CD8 : -> (CharDig #\8 8))
    (many CD9 : -> (CharDig #\9 9))))

(def-fns _ $ (many get-bit : (many (Char) c) -> (many (Got (Bool) CharBit c) r))
  (match many (char-eq c #\0) _ ((Equal _ _ _) (GotOk _ _ c (BFalse) (CB0))) (else
  (match many (char-eq c #\1) _ ((Equal _ _ _) (GotOk _ _ c (BTrue) (CB1))) (else (GotNo _ _ c))))))

(def-fns _ $ (many get-dir : (many (Char) c) -> (many (Got (Dir) CharDir c) r))
  (match many (char-eq c #\L) _ ((Equal _ _ _) (GotOk _ _ c (DL) (CDL))) (else
  (match many (char-eq c #\R) _ ((Equal _ _ _) (GotOk _ _ c (DR) (CDR))) (else (GotNo _ _ c))))))

(def-fns _ $ (many get-st : (many (Char) c) -> (many (Got (Nat) CharSt c) r))
  (match many (char-eq c #\A) _ ((Equal _ _ _) (GotOk _ _ c (Zero) (CSA))) (else
  (match many (char-eq c #\B) _ ((Equal _ _ _) (GotOk _ _ c (Succ (Zero)) (CSB))) (else
  (match many (char-eq c #\C) _ ((Equal _ _ _) (GotOk _ _ c (Succ (Succ (Zero))) (CSC))) (else
  (match many (char-eq c #\D) _ ((Equal _ _ _) (GotOk _ _ c (Succ (Succ (Succ (Zero)))) (CSD))) (else
  (match many (char-eq c #\E) _ ((Equal _ _ _) (GotOk _ _ c (Succ (Succ (Succ (Succ (Zero))))) (CSE))) (else (GotNo _ _ c))))))))))))

(def-fns _ $ (many get-dig : (many (Char) c) -> (many (Got (Nat) CharDig c) r))
  (match many (char-eq c #\0) _ ((Equal _ _ _) (GotOk _ _ c 0 (CD0))) (else
  (match many (char-eq c #\1) _ ((Equal _ _ _) (GotOk _ _ c 1 (CD1))) (else
  (match many (char-eq c #\2) _ ((Equal _ _ _) (GotOk _ _ c 2 (CD2))) (else
  (match many (char-eq c #\3) _ ((Equal _ _ _) (GotOk _ _ c 3 (CD3))) (else
  (match many (char-eq c #\4) _ ((Equal _ _ _) (GotOk _ _ c 4 (CD4))) (else
  (match many (char-eq c #\5) _ ((Equal _ _ _) (GotOk _ _ c 5 (CD5))) (else
  (match many (char-eq c #\6) _ ((Equal _ _ _) (GotOk _ _ c 6 (CD6))) (else
  (match many (char-eq c #\7) _ ((Equal _ _ _) (GotOk _ _ c 7 (CD7))) (else
  (match many (char-eq c #\8) _ ((Equal _ _ _) (GotOk _ _ c 8 (CD8))) (else
  (match many (char-eq c #\9) _ ((Equal _ _ _) (GotOk _ _ c 9 (CD9))) (else (GotNo _ _ c))))))))))))))))))))))

(def-adts
  ((PTr : ((String) s) ((Tr) t) ((String) s2) -> Type)
    enum
    (many PTH : (erased (String) s) -> (PTr (SCons #\- (SCons #\- (SCons #\- s))) (Halt) s))
    (many PTZ : (erased (Char) c1 c2) (erased (String) s) -> (PTr (SCons c1 (SCons c2 (SCons #\Z s))) (Halt) s))
    (many PTG : (erased (Char) c1 c2 c3) (erased (String) s) (erased (Bool) w) (erased (Dir) d) (erased (Nat) q)
       (erased (CharBit c1 w) pw) (erased (CharDir c2 d) pd) (erased (CharSt c3 q) pq)
       -> (PTr (SCons c1 (SCons c2 (SCons c3 s))) (Go w d q) s))))

(def-adts
  ((PRows : ((String) s) ((List (Tr)) m) ((Nat) k) ((String) s2) -> Type)
    enum
    (many PR1 : (erased (String) s s1 s2) (erased (Tr) t0 t1) (erased (PTr s t0 s1) p0) (erased (PTr s1 t1 (SCons #\space s2)) p1)
       -> (PRows s (Cons (Tr) t0 (Cons (Tr) t1 (Nil (Tr)))) (Succ (Zero)) s2))
    (many PRS : (erased (String) s s1 s2 s3) (erased (Tr) t0 t1) (erased (List (Tr)) m) (erased (Nat) k)
       (erased (PTr s t0 s1) p0) (erased (PTr s1 t1 (SCons #\_ s2)) p1) (erased (PRows s2 m k s3) pr)
       -> (PRows s (Cons (Tr) t0 (Cons (Tr) t1 m)) (Succ k) s3))))

(def-adts
  ((PNum : ((String) s) ((Nat) acc) ((Nat) v) ((String) s2) -> Type)
    enum
    (many PN0 : (erased (String) s) (erased (Nat) acc) -> (PNum (SCons #\newline s) acc acc s))
    (many PND : (erased (Char) c) (erased (String) s s2) (erased (Nat) acc d x a2 v)
       (erased (CharDig c d) pd) (erased (Mul acc 10 x) pm) (erased (Add x d a2) pa) (erased (PNum s a2 v s2) pn)
       -> (PNum (SCons c s) acc v s2))))

(def-adts
  ((PCases : ((String) s) ((List (Case)) cs) -> Type)
    enum
    (many PCNil : -> (PCases (SNil) (Nil (Case))))
    (many PCCons : (erased (String) s s1 s2) (erased (List (Tr)) m) (erased (Nat) n v) (erased (List (Case)) cs)
       (erased (PRows s m n s1) pr) (erased (PNum s1 (Zero) v s2) pn) (erased (PCases s2 cs) pc)
       -> (PCases s (Cons (Case) (MkCase m n v) cs)))))

(def-adts
  ((Parsed : (Type A) ((TyCtor ((String) s) (A a) ((String) s2) -> Type) R) ((String) s) -> Type)
    enum
    (many POk : (erased Type A) (erased (TyCtor ((String) s) (A a) ((String) s2) -> Type) R) (erased (String) s)
       (many A a) (many (String) s2) (erased (R s a s2) p) -> (Parsed A R s))
    (many PNo : (erased Type A) (erased (TyCtor ((String) s) (A a) ((String) s2) -> Type) R) (erased (String) s) -> (Parsed A R s))))

(def-fns _ $ (many p-tr : (many (String) s) -> (many (Parsed (Tr) PTr s) r))
  (let-match many s (SCons c1 s1) ((SNil) (PNo _ _ s)))
  (let-match many s1 (SCons c2 s2) ((SNil) (PNo _ _ s)))
  (let-match many s2 (SCons c3 s3) ((SNil) (PNo _ _ s)))
  (match many (char-eq c3 #\Z) _
    ((Equal _ _ _) (POk _ _ s (Halt) s3 (PTZ c1 c2 s3)))
    (else
      (match many (char-eq c1 #\-) _
        ((Equal _ _ _)
          (let-match many (char-eq c2 #\-) (Equal _ _ _) (else (PNo _ _ s)))
          (let-match many (char-eq c3 #\-) (Equal _ _ _) (else (PNo _ _ s)))
          (POk _ _ s (Halt) s3 (PTH s3)))
        (else
          (let-match many (get-bit c1) (GotOk _ _ _ w pw) ((GotNo _ _ _) (PNo _ _ s)))
          (let-match many (get-dir c2) (GotOk _ _ _ d pd) ((GotNo _ _ _) (PNo _ _ s)))
          (let-match many (get-st c3) (GotOk _ _ _ q pq) ((GotNo _ _ _) (PNo _ _ s)))
          (POk _ _ s (Go w d q) s3 (PTG c1 c2 c3 s3 w d q pw pd pq)))))))

(def-adts
  ((RowsR : ((String) s) -> Type)
    enum
    (many RowsOk : (erased (String) s) (many (List (Tr)) m) (many (Nat) k) (many (String) s2) (erased (PRows s m k s2) p) -> (RowsR s))
    (many RowsNo : (erased (String) s) -> (RowsR s))))

(def-fns _ $ (many p-rows : (subterm many (Nat) fuel) (many (String) s) -> (many (RowsR s) r))
  (let-match many fuel (Succ f) ((Zero) (RowsNo s)))
  (let-match many (p-tr s) (POk _ _ _ t0 s1 p0) ((PNo _ _ _) (RowsNo s)))
  (let-match many (p-tr s1) (POk _ _ _ t1 s2 p1) ((PNo _ _ _) (RowsNo s)))
  (let-match many s2 (SCons c s3) ((SNil) (RowsNo s)))
  (match many (char-eq c #\space) _
    ((Equal _ _ _) (RowsOk s (Cons (Tr) t0 (Cons (Tr) t1 (Nil (Tr)))) (Succ (Zero)) s3 (PR1 s s1 s3 t0 t1 p0 p1)))
    (else
      (let-match many (char-eq c #\_) (Equal _ _ _) (else (RowsNo s)))
      (let-match many (notail $ p-rows f s3) (RowsOk _ m k s4 pr) ((RowsNo _) (RowsNo s)))
      (RowsOk s (Cons (Tr) t0 (Cons (Tr) t1 m)) (Succ k) s4 (PRS s s1 s3 s4 t0 t1 m k p0 p1 pr)))))

(def-adts
  ((NumR : ((String) s) ((Nat) acc) -> Type)
    enum
    (many NumOk : (erased (String) s) (erased (Nat) acc) (many (Nat) v) (many (String) s2) (erased (PNum s acc v s2) p) -> (NumR s acc))
    (many NumNo : (erased (String) s) (erased (Nat) acc) -> (NumR s acc))))

(def-fns _ $ (many p-num : (subterm many (Nat) fuel) (many (String) s) (many (Nat) acc) -> (many (NumR s acc) r))
  (let-match many fuel (Succ f) ((Zero) (NumNo s acc)))
  (let-match many s (SCons c s1) ((SNil) (NumNo s acc)))
  (match many (char-eq c #\newline) _
    ((Equal _ _ _) (NumOk s acc acc s1 (PN0 s1 acc)))
    (else
      (let-match many (get-dig c) (GotOk _ _ _ d pd) ((GotNo _ _ _) (NumNo s acc)))
      (let ((many x) (erased pm)) (mul acc 10))
      (let ((many a2) (erased pa)) (add x d))
      (let-match many (notail $ p-num f s1 a2) (NumOk _ _ v s2 pn) ((NumNo _ _) (NumNo s acc)))
      (NumOk s acc v s2 (PND c s1 s2 acc d x a2 v pd pm pa pn)))))

(def-adts
  ((CasesR : ((String) s) -> Type)
    enum
    (many CasesOk : (erased (String) s) (many (List (Case)) cs) (erased (PCases s cs) p) -> (CasesR s))
    (many CasesNo : (erased (String) s) -> (CasesR s))))

(def-fns _ $ (many p-cases : (subterm many (Nat) fuel) (many (String) s) -> (many (CasesR s) r))
  (let-match many fuel (Succ f) ((Zero) (CasesNo s)))
  (match many s _
    ((SNil) (CasesOk s (Nil (Case)) (PCNil)))
    (else
      (let-match many (p-rows 64 s) (RowsOk _ m n s1 pr) ((RowsNo _) (CasesNo s)))
      (let-match many (p-num 64 s1 (Zero)) (NumOk _ _ v s2 pn) ((NumNo _ _) (CasesNo s)))
      (let-match many (notail $ p-cases f s2) (CasesOk _ cs pc) ((CasesNo _) (CasesNo s)))
      (CasesOk s (Cons (Case) (MkCase m n v) cs) (PCCons s s1 s2 m n v cs pr pn pc)))))

(def-fns _ $ (many eq-dir : (many (Dir) x) (many (Dir) y) -> (many (Maybe (Eq (Dir) x y)) r))
  (match many x _
    ((DL) (match many y _ ((DL) (Some _ (Refl (Dir) x))) ((DR) (None _))))
    ((DR) (match many y _ ((DR) (Some _ (Refl (Dir) x))) ((DL) (None _))))))

(def-fns _ $ (many eq-tr : (many (Tr) x) (many (Tr) y) -> (many (Maybe (Eq (Tr) x y)) r))
  (match many x _
    ((Halt) (match many y _ ((Halt) (Some _ (Refl (Tr) x))) (else (None _))))
    ((Go w d q)
      (let-match many y (Go w2 d2 q2) ((Halt) (None _)))
      (let-match many (eq-bit w w2) (Some _ e1) ((None _) (None _)))
      (let-match many (eq-dir d d2) (Some _ e2) ((None _) (None _)))
      (let-match many (eq-nat q q2) (Some _ e3) ((None _) (None _)))
      (let-match many e1 (Refl _ _))
      (let-match many e2 (Refl _ _))
      (let-match many e3 (Refl _ _))
      (Some _ (Refl (Tr) x)))))

(def-fns _ $ (many eq-trs : (subterm many (List (Tr)) x) (many (List (Tr)) y) -> (many (Maybe (Eq (List (Tr)) x y)) r))
  (match many x _
    ((Nil _) (match many y _ ((Nil _) (Some _ (Refl (List (Tr)) x))) (else (None _))))
    ((Cons _ a xs)
      (let-match many y (Cons _ b ys) ((Nil _) (None _)))
      (let-match many (eq-tr a b) (Some _ e1) ((None _) (None _)))
      (let-match many (notail $ eq-trs xs ys) (Some _ e2) ((None _) (None _)))
      (let-match many e1 (Refl _ _))
      (let-match many e2 (Refl _ _))
      (Some _ (Refl (List (Tr)) x)))))

(def-fns _ $ (many eq-case : (many (Case) x) (many (Case) y) -> (many (Maybe (Eq (Case) x y)) r))
  (let-match many x (MkCase m1 n1 s1))
  (let-match many y (MkCase m2 n2 s2))
  (let-match many (eq-trs m1 m2) (Some _ e1) ((None _) (None _)))
  (let-match many (eq-nat n1 n2) (Some _ e2) ((None _) (None _)))
  (let-match many (eq-nat s1 s2) (Some _ e3) ((None _) (None _)))
  (let-match many e1 (Refl _ _))
  (let-match many e2 (Refl _ _))
  (let-match many e3 (Refl _ _))
  (Some _ (Refl (Case) x)))

(def-fns _ $ (many find-case : (many (Case) a) (subterm many (List (Case)) S) -> (many (Res (Mem (Case) a S)) r))
  (let-match many S (Cons _ b rest) ((Nil _) (RFail _)))
  (match many (eq-case a b) _
    ((Some _ e) (let-match many e (Refl _ _)) (ROk _ (MemHere (Case) a rest)))
    ((None _)
      (let-match many (notail $ find-case a rest) (ROk _ mm) ((RFail _) (RFail _)))
      (ROk _ (MemThere (Case) a b rest mm)))))

(def-adts
  ((AllMem : ((List (Case)) qs) ((List (Case)) cs) -> Type)
    enum
    (many AMNil : (erased (List (Case)) cs) -> (AllMem (Nil (Case)) cs))
    (many AMCons : (erased (Case) q) (erased (List (Case)) qs cs) (erased (Mem (Case) q cs) mm) (erased (AllMem qs cs) rest)
       -> (AllMem (Cons (Case) q qs) cs))))

(def-fns _ $ (many find-all : (subterm many (List (Case)) qs) (many (List (Case)) cs) -> (many (Res (AllMem qs cs)) r))
  (let-match many qs (Cons _ q rest) ((Nil _) (ROk _ (AMNil cs))))
  (let-match many (find-case q cs) (ROk _ mm) ((RFail _) (RFail _)))
  (let-match many (notail $ find-all rest cs) (ROk _ am) ((RFail _) (RFail _)))
  (ROk _ (AMCons q rest cs mm am)))

(def-adts
  ((Valid : ((String) str) ((List (Case)) qs) -> Type)
    enum
    (many MkValid : (erased (String) str) (erased (List (Case)) qs cs) (erased (PCases str cs) pc) (erased (AllHalt cs) ah)
       (erased (AllMem qs cs) am) -> (Valid str qs))))

(def-fns _ $ (many validate : (many (Nat) fuel) (many (String) str) (many (List (Case)) qs) -> (many (Res (Valid str qs)) r))
  (let-match many (p-cases fuel str) (CasesOk _ cs pc) ((CasesNo _) (RFail _)))
  (let ((erased tx) (unique tmpl) (erased rp)) (bytes-make N z8))
  (let ((erased tx2) (unique a) (erased rp2)) (bytes-make N z8))
  (let-match erased (rep-same N tx tx2 rp rp2) (Refl _ _))
  (let-match erased rp (RepeatCons _ _ _ b0 rp0))
  (let ((many i) (many j) (erased as) (erased bs) (erased z) (erased fa) (erased fb) (erased la) (erased lb) (erased ij))
    (seek 32768 tx (Nil (U8)) b0 (Zero) N1 N (ZHere _ _ b0) (AFNil) (rep-allf _ b0 rp0) (LengthNil _) (rep-len _ b0 rp0) (AddZero _)))
  (let ((many st)) (MkStart tx as bs i j z fa fb la lb ij))
  (let ((many tm)) (share tmpl))
  (let-match many (check-all cs tx tm (LengthCons _ _ _ _ (rep-len _ b0 rp0)) st a) (ROk _ ah) ((RFail _) (RFail _)))
  (let-match many (find-all qs cs) (ROk _ am) ((RFail _) (RFail _)))
  (ROk _ (MkValid str qs cs pc ah am)))
