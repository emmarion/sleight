; The source prelude (DESIGN.md section 41), elaborated ahead of every program. Its extern-marked
; definitions are the models the FFI's implementations in ffi.ml stand in for.

(def-adts $ Nat : -> Type
  enum extern
  (many Zero : -> (Nat))
  (many Succ : (many (Nat) pred) -> (Nat)))

(def-adts $ False : -> Type
  enum)

(def-adts
  (Eq : (Type A) (A x) (A y) -> Type
    enum
    (many Refl : (erased Type A) (erased A x) -> (Eq A x x))))

(def-fns _ $ erased eq-trans : (erased Type A) (erased A x) (erased A y) (erased A z)
    (erased (Eq A x y) e) (erased (Eq A y z) f) -> (erased (Eq A x z) g)
  (match erased e _ ((Refl a b) (match erased f _ ((Refl c d) (Refl A x))))))

(def-fns _ $ erased eq-cong-succ : (erased (Nat) x) (erased (Nat) y) (erased (Eq (Nat) x y) e) ->
    (erased (Eq (Nat) (Succ x) (Succ y)) f)
  (match erased e _ ((Refl a b) (Refl (Nat) (Succ x)))))

(def-adts
  (Add : ((Nat) a) ((Nat) b) ((Nat) c) -> Type
    enum
    (many AddZero : (erased (Nat) b) -> (Add (Zero) b b))
    (many AddSucc : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Add a b c) q) -> (Add (Succ a) b (Succ c)))))

(def-adts
  (Lt : ((Nat) a) ((Nat) b) -> Type
    enum
    (many LtZ : (erased (Nat) b) -> (Lt (Zero) (Succ b)))
    (many LtS : (erased (Nat) a) (erased (Nat) b) (erased (Lt a b) p) -> (Lt (Succ a) (Succ b)))))

(def-adts
  (Double : ((Nat) a) ((Nat) b) -> Type
    enum
    (many D0 : -> (Double (Zero) (Zero)))
    (many DS : (erased (Nat) a) (erased (Nat) b) (erased (Double a b) d) -> (Double (Succ a) (Succ (Succ b))))))

(def-adts
  (Pow2 : ((Nat) k) ((Nat) v) -> Type
    enum
    (many P0 : -> (Pow2 (Zero) (Succ (Zero))))
    (many PS : (erased (Nat) k) (erased (Nat) v) (erased (Nat) w) (erased (Pow2 k v) p) (erased (Double v w) d) ->
       (Pow2 (Succ k) w))))

(def-adts
  (Mod : ((Nat) s) ((Nat) c) ((Nat) r) -> Type
    enum
    (many ModLt : (erased (Nat) s) (erased (Nat) c) (erased (Lt s c) p) -> (Mod s c s))
    (many ModSub : (erased (Nat) s1) (erased (Nat) c) (erased (Nat) s) (erased (Nat) r) (erased (Add c s1 s) a) (erased (Mod s1 c r) m) ->
       (Mod s c r))))

(def-adts
  (Dec : ((Nat) a) ((Nat) b) -> Type
    enum
    (many Yes : (erased (Nat) a) (erased (Nat) b) (erased (Lt a b) p) -> (Dec a b))
    (many No : (erased (Nat) a) (erased (Nat) b) (erased (Lt b (Succ a)) q) -> (Dec a b))))

; Parametric in the carrier and its strict order, every field erased, so a value is only its tag and two
; instances differ by a coercion (section 38).
(def-adts
  (Cmp : (Type T) ((TyCtor (T x) (T y) -> Type) R) (T a) (T b) -> Type
    enum
    (many CLt : (erased Type T) (erased (TyCtor (T x) (T y) -> Type) R) (erased T a) (erased T b)
                (erased (R a b) p) -> (Cmp T R a b))
    (many CEq : (erased Type T) (erased (TyCtor (T x) (T y) -> Type) R) (erased T a) -> (Cmp T R a a))
    (many CGt : (erased Type T) (erased (TyCtor (T x) (T y) -> Type) R) (erased T a) (erased T b)
                (erased (R b a) q) -> (Cmp T R a b))))

(def-fns _ $ erased add-zero-right : (subterm erased (Nat) a) -> (erased (Add a (Zero) a) p)
  (match erased a _
    ((Zero) (AddZero (Zero)))
    ((Succ a1) (AddSucc a1 (Zero) a1 (add-zero-right a1)))))

(def-fns _ $ erased add-succ-right : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (subterm erased (Add a b c) p) ->
    (erased (Add a (Succ b) (Succ c)) q)
  (match erased p _
    ((AddZero b0) (AddZero (Succ b)))
    ((AddSucc a1 b1 c0 q0) (AddSucc a1 (Succ b) (Succ c0) (add-succ-right a1 b c0 q0)))))

(def-fns _ $ erased add-succ-right-inv : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (subterm erased (Add a (Succ b) c) p) ->
    (erased (Nat) c1) (erased (Eq (Nat) c (Succ c1)) e) (erased (Add a b c1) q)
  (match erased p _
    ((AddZero b0) (values b (Refl (Nat) c) (AddZero b)))
    ((AddSucc a1 b1 c0 q0)
      (let (erased c1) (erased e1) (erased q1) (add-succ-right-inv a1 b c0 q0))
      (match erased e1 _
        ((Refl t r) (values (Succ c1) (Refl (Nat) c) (AddSucc a1 b c1 q1)))))))

(def-fns _ $ erased add-diag-double : (subterm erased (Nat) a) (erased (Nat) b) (erased (Add a a b) p) -> (erased (Double a b) d)
  (match erased p _
    ((AddZero b0) (D0))
    ((AddSucc a1 b1 c0 q0)
      (let (erased c1) (erased e1) (erased q1) (add-succ-right-inv a1 a1 c0 q0))
      (match erased e1 _
        ((Refl t r) (DS a1 c1 (add-diag-double a1 c1 q1)))))))

(def-fns _ $ erased double-pos : (erased (Nat) v) (erased (Nat) w) (erased (Lt (Zero) v) q) (erased (Double v w) d) ->
    (erased (Lt (Zero) w) r)
  (match erased q _
    ((LtZ b)
      (match erased d _
        (absurd D0)
        ((DS a b2 d1) (LtZ (Succ b2)))))
    (absurd LtS)))

(def-fns _ $ erased lt-asym : (erased (Nat) r) (erased (Nat) c) (subterm erased (Lt r c) p) (erased (Lt c (Succ r)) g) -> (erased (False) f)
  (match erased p _
    ((LtZ b)
      (match erased g _
        (absurd LtZ)
        ((LtS x y g1) (match erased g1 _ (absurd LtZ) (absurd LtS)))))
    ((LtS a b p1)
      (match erased g _
        (absurd LtZ)
        ((LtS x y g1) (lt-asym a b p1 g1))))))

(def-fns _ $ erased mod-succ-lt : (erased (Nat) s) (erased (Nat) c) (erased (Nat) r) (subterm erased (Mod s c r) q) (erased (Lt (Succ r) c) lt) ->
    (erased (Mod (Succ s) c (Succ r)) q1)
  (match erased q _
    ((ModLt x y p0) (ModLt (Succ s) c lt))
    ((ModSub s1 c0 s0 r0 a m) (ModSub (Succ s1) c (Succ s) (Succ r) (add-succ-right c s1 s a) (mod-succ-lt s1 c r m lt)))))

(def-fns _ $ erased mod-succ-wrap : (erased (Nat) s) (erased (Nat) r) (subterm erased (Mod s (Succ r) r) q) -> (erased (Mod (Succ s) (Succ r) (Zero)) q1)
  (match erased q _
    ((ModLt x y p0) (ModSub (Zero) (Succ r) (Succ s) (Zero) (add-zero-right (Succ r)) (ModLt (Zero) (Succ r) (LtZ r))))
    ((ModSub s1 c0 s0 r0 a m) (ModSub (Succ s1) (Succ r) (Succ s) (Zero) (add-succ-right (Succ r) s1 s a) (mod-succ-wrap s1 r m)))))

(def-adts
  (Half : ((Nat) n) -> Type
    enum extern
    (many HZ : -> (Half (Zero)))
    (many H1 : (many (Nat) m) (erased (Nat) d) (erased (Double m d) dd) -> (Half (Succ d)))
    (many H2 : (many (Nat) m) (erased (Nat) d) (erased (Double m d) dd) -> (Half (Succ (Succ d))))))

(def-fns _ $ many extern nat-halve : (subterm many (Nat) n) -> (many (Half n) h)
  (match many n _
    ((Zero) (HZ))
    ((Succ k)
      (match many (nat-halve k) _
        ((HZ) (H1 (Zero) (Zero) (D0)))
        ((H1 m d dd) (H2 m d dd))
        ((H2 m d dd) (H1 (Succ m) (Succ (Succ d)) (DS m d dd)))))))

(def-fns _ $ many extern add : (subterm many (Nat) a) (many (Nat) b) -> (many (Nat) c) (erased (Add a b c) p)
  (match many a _
    ((Zero) (values b (AddZero b)))
    ((Succ k)
      (let (many c) (erased q) (add k b))
      (values (Succ c) (AddSucc k b c q)))))

(def-fns _ $ erased lt-succ : (subterm erased (Nat) a) -> (erased (Lt a (Succ a)) p)
  (match erased a _
    ((Zero) (LtZ (Zero)))
    ((Succ a1) (LtS a1 (Succ a1) (lt-succ a1)))))

(def-fns _ $ erased lt-weaken : (erased (Nat) x) (erased (Nat) y) (subterm erased (Lt x y) p) -> (erased (Lt x (Succ y)) q)
  (match erased p _
    ((LtZ b) (LtZ (Succ b)))
    ((LtS a b p1) (LtS a (Succ b) (lt-weaken a b p1)))))

(def-fns _ $ many extern nat-cmp : (subterm many (Nat) a) (many (Nat) b) -> (many (Cmp (Nat) Lt a b) c)
  (match many a _
    ((Zero)
      (match many b _
        ((Zero) (CEq (Nat) Lt a))
        ((Succ b1) (CLt (Nat) Lt a b (LtZ b1)))))
    ((Succ a1)
      (match many b _
        ((Zero) (CGt (Nat) Lt a b (LtZ a1)))
        ((Succ b1)
          (match many (nat-cmp a1 b1) _
            ((CLt t r x y p) (CLt (Nat) Lt a b (LtS a1 b1 p)))
            ((CEq t r x) (CEq (Nat) Lt a))
            ((CGt t r x y q) (CGt (Nat) Lt a b (LtS b1 a1 q)))))))))

(def-adts
  (Mul : ((Nat) a) ((Nat) b) ((Nat) c) -> Type
    enum
    (many MulZero : (erased (Nat) b) -> (Mul (Zero) b (Zero)))
    (many MulSucc : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Nat) d) (erased (Mul a b c) m) (erased (Add c b d) p) ->
       (Mul (Succ a) b d))))

(def-fns _ $ erased add-comm : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (subterm erased (Add a b c) p) -> (erased (Add b a c) q)
  (match erased p _
    ((AddZero b0) (add-zero-right b))
    ((AddSucc a1 b1 c1 p1) (add-succ-right b a1 c1 (add-comm a1 b c1 p1)))))

(def-fns _ $ many extern mul : (subterm many (Nat) a) (many (Nat) b) -> (many (Nat) c) (erased (Mul a b c) p)
  (match many a _
    ((Zero) (values (Zero) (MulZero b)))
    ((Succ a1)
      (let (many c1) (erased m) (mul a1 b))
      (let (many c) (erased q) (add b c1))
      (values c (MulSucc a1 b c1 c m (add-comm b c1 c q))))))

(def-fns _ $ many extern sub : (many (Nat) a) (subterm many (Nat) b) (erased (Lt b (Succ a)) le) -> (many (Nat) c) (erased (Add b c a) p)
  (match many b _
    ((Zero) (values a (AddZero a)))
    ((Succ b1)
      (match many a _
        ((Zero) (match erased le _ (absurd LtZ) ((LtS x y l1) (match erased l1 _ (absurd LtZ) (absurd LtS)))))
        ((Succ a1)
          (let (erased le1) (match erased le (((Lt b1 (Succ a1)) l)) (absurd LtZ) ((LtS x y l1) l1)))
          (let (many c) (erased q) (sub a1 b1 le1))
          (values c (AddSucc b1 c a1 q)))))))

(def-fns _ $ many succ-div : (many (Nat) q) (many (Nat) r) (many (Nat) c) (erased (Nat) m) (erased (Nat) s)
    (erased (Mul q c m) mm) (erased (Add m r s) a) (erased (Lt r c) p) ->
    (many (Nat) q1) (many (Nat) r1) (erased (Nat) m1) (erased (Mul q1 c m1) mm1) (erased (Add m1 r1 (Succ s)) a1) (erased (Lt r1 c) p1)
  (match many (nat-cmp (Succ r) c) _
    ((CLt t rr x y lt) (values q (Succ r) m mm (add-succ-right m r s a) lt))
    ((CEq t rr x) (values (Succ q) (Zero) (Succ s) (MulSucc q c m (Succ s) mm (add-succ-right m r s a)) (add-zero-right (Succ s)) (LtZ r)))
    (absurd (CGt t rr x y gt) (lt-asym r c p gt))))

(def-fns _ $ many extern divmod : (subterm many (Nat) s) (many (Nat) c) (erased (Lt (Zero) c) pos) ->
    (many (Nat) q) (many (Nat) r) (erased (Nat) m) (erased (Mul q c m) mm) (erased (Add m r s) a) (erased (Lt r c) p)
  (match many s _
    ((Zero) (values (Zero) (Zero) (Zero) (MulZero c) (AddZero (Zero)) pos))
    ((Succ s1)
      (let (many q1) (many r1) (erased m1) (erased mm1) (erased a1) (erased p1) (divmod s1 c pos))
      (succ-div q1 r1 c m1 s1 mm1 a1 p1))))

(def-fns _ $ many extern div : (many (Nat) s) (many (Nat) c) (erased (Lt (Zero) c) pos) ->
    (many (Nat) q) (erased (Nat) m) (erased (Nat) r) (erased (Mul q c m) mm) (erased (Add m r s) a) (erased (Lt r c) p)
  (let (many q) (many r) (erased m) (erased mm) (erased a) (erased p) (divmod s c pos))
  (values q m r mm a p))

(def-fns _ $ erased lt-trans : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (subterm erased (Lt a b) p) (erased (Lt b c) q) -> (erased (Lt a c) r)
  (match erased p _
    ((LtZ b1) (match erased q _ ((LtS x y q1) (LtZ y))))
    ((LtS a1 b1 p1) (match erased q _ ((LtS x y q1) (LtS a1 y (lt-trans a1 b1 y p1 q1)))))))

(def-fns _ $ erased lt-le-trans : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (subterm erased (Lt a b) p) (erased (Lt b (Succ c)) q) -> (erased (Lt a c) r)
  (match erased p _
    ((LtZ b1)
      (match erased q _
        ((LtS x y q1) (match erased q1 _ ((LtZ z) (LtZ z)) ((LtS x2 y2 q2) (LtZ y2))))))
    ((LtS a1 b1 p1)
      (match erased q _
        ((LtS x y q1)
          (match erased q1 _
            (absurd (LtZ z) (match erased p1 (((False) f)) (absurd LtZ) (absurd LtS)))
            ((LtS b2 c1 q2) (LtS a1 c1 (lt-le-trans a1 b1 c1 p1 (LtS b2 c1 q2))))))))))

(def-fns _ $ erased lt-subterm : (erased (Nat) a) (subterm erased (Nat) b) (erased (Lt a b) p) -> (erased (Subterm (Nat) a (Nat) b) s)
  (match erased b _
    ((Zero) (match erased p _ (absurd LtZ) (absurd LtS)))
    ((Succ b1)
      (match erased (nat-cmp a b1) _
        ((CLt t r x y q) (subterm-trans (lt-subterm a b1 q) (prove-subterm b1 b)))
        ((CEq t r x) (prove-subterm a b))
        (absurd (CGt t r x y g) (lt-asym b1 a g p))))))

(def-fns _ $ erased add-le-left : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (subterm erased (Add a b c) p) -> (erased (Lt a (Succ c)) q)
  (match erased p _
    ((AddZero b0) (LtZ b))
    ((AddSucc a1 b1 c1 p1) (LtS a1 (Succ c1) (add-le-left a1 b c1 p1)))))

(def-fns _ $ erased add-lt-left : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (subterm erased (Add a b c) p) (erased (Lt (Succ (Zero)) b) two) -> (erased (Lt (Succ a) c) q)
  (match erased p _
    ((AddZero b0) two)
    ((AddSucc a1 b1 c1 p1) (LtS (Succ a1) c1 (add-lt-left a1 b c1 p1 two)))))

(def-fns _ $ erased mul-lt : (erased (Nat) q) (erased (Nat) c) (erased (Nat) m) (subterm erased (Mul (Succ q) c m) mm) (erased (Lt (Succ (Zero)) c) two) -> (erased (Lt (Succ q) m) l)
  (match erased mm _
    ((MulSucc q0 c0 m0 d0 mm0 p0)
      (match erased q _
        ((Zero) (match erased mm0 _ ((MulZero b0) (match erased p0 _ ((AddZero b1) two)))))
        ((Succ q1) (lt-trans (Succ q) (Succ m0) m (LtS q m0 (mul-lt q1 c m0 mm0 two)) (add-lt-left m0 c m p0 two)))))))

(def-fns _ $ erased divmod-lt : (erased (Nat) s) (erased (Nat) c) (erased (Nat) q) (erased (Nat) r) (erased (Nat) m)
    (erased (Mul q c m) mm) (erased (Add m r (Succ s)) a) (erased (Lt (Succ (Zero)) c) two) -> (erased (Lt q (Succ s)) l)
  (match erased q _
    ((Zero) (LtZ s))
    ((Succ q1) (lt-le-trans q m (Succ s) (mul-lt q1 c m mm two) (add-le-left m r (Succ s) a)))))

(def-lvl nat-lvl)

(def-fns nat-lvl $ many nat-add : (many (Nat) a) (many (Nat) b) -> (many (Nat) c)
  (let (many c) (erased p) (delegate (add a b)))
  c)

(def-fns nat-lvl $ many nat-mul : (many (Nat) a) (many (Nat) b) -> (many (Nat) c)
  (let (many c) (erased p) (delegate (mul a b)))
  c)

(def-fns nat-lvl $ many double : (many (Nat) a) -> (many (Nat) b) (erased (Double a b) d)
  (let (many b) (erased p) (add a a))
  (values b (add-diag-double a b p)))

(def-fns nat-lvl $ many lt-dec : (many (Nat) a) (many (Nat) b) -> (many (Dec a b) d)
  (match many (nat-cmp a b) _
    ((CLt t r x y p) (Yes a b p))
    ((CEq t r x) (No a b (lt-succ a)))
    ((CGt t r x y q) (No a b (lt-weaken b a q)))))

(def-fns _ $ many succ-mod : (many (Nat) r) (many (Nat) c) (erased (Nat) s) (erased (Lt r c) p) (erased (Mod s c r) q) ->
    (many (Nat) r1) (erased (Lt r1 c) p1) (erased (Mod (Succ s) c r1) q1)
  (match many (nat-cmp (Succ r) c) _
    ((CLt t rr x y lt) (values (Succ r) lt (mod-succ-lt s c r q lt)))
    ((CEq t rr x) (values (Zero) (LtZ r) (mod-succ-wrap s r q)))
    (absurd (CGt t rr x y gt) (lt-asym r c p gt))))

(def-fns _ $ many extern nat-mod : (subterm many (Nat) s) (many (Nat) c) (erased (Lt (Zero) c) pos) ->
    (many (Nat) r) (erased (Lt r c) p) (erased (Mod s c r) q)
  (match many s _
    ((Zero) (values (Zero) pos (ModLt (Zero) c pos)))
    ((Succ s1)
      (let (many r1) (erased p1) (erased q1) (nat-mod s1 c pos))
      (succ-mod r1 c s1 p1 q1))))

(def-fns _ $ many pow2 : (subterm many (Nat) k) -> (many (Nat) v) (erased (Pow2 k v) p) (erased (Lt (Zero) v) q)
  (match many k _
    ((Zero) (values (Succ (Zero)) (P0) (LtZ (Zero))))
    ((Succ k1)
      (let (many v) (erased p) (erased q) (pow2 k1))
      (let (many w) (erased d) (double v))
      (values w (PS k1 v w p d) (double-pos v w q d)))))

(let (many eight) (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))))))
(let (many u8-modulus) (erased u8-modulus-pow2) (erased u8-modulus-pos) (pow2 eight))

(def-adts $ U8 : -> Type
  enum newtype
  (many MkU8 : (many (Nat) n) (erased (Lt n u8-modulus) p) -> (U8)))

(def-adts
  (U8Add : ((U8) a) ((U8) b) ((U8) c) -> Type
    enum
    (many MkU8Add : (erased (Nat) n) (erased (Nat) m) (erased (Nat) r)
                    (erased (Lt n u8-modulus) pn) (erased (Lt m u8-modulus) pm) (erased (Lt r u8-modulus) pr)
                    (erased (Nat) s) (erased (Add n m s) a) (erased (Mod s u8-modulus r) q) ->
       (U8Add (MkU8 n pn) (MkU8 m pm) (MkU8 r pr)))))

(def-fns _ $ many add-u8 : (many (U8) a) (many (U8) b) -> (many (U8) c) (erased (U8Add a b c) w)
  (let-match many a (MkU8 n pn))
  (let-match many b (MkU8 m pm))
  (let (many s) (erased ps) (add n m))
  (let (many r) (erased pr) (erased q) (nat-mod s u8-modulus u8-modulus-pos))
  (values (MkU8 r pr) (MkU8Add n m r pn pm pr s ps q)))

(def-lvl u8-lvl)

(def-fns u8-lvl $ many u8-add : (many (U8) a) (many (U8) b) -> (many (U8) c)
  (let (many c) (erased w) (delegate (add-u8 a b)))
  c)

(def-adts $ Bin : -> Type
  enum
  (many BZ : -> (Bin))
  (many B1 : (many (Bin) rest) -> (Bin))
  (many B2 : (many (Bin) rest) -> (Bin)))

(def-adts
  (Numeral : ((Bin) b) ((Nat) n) -> Type
    enum
    (many NZ : -> (Numeral (BZ) (Zero)))
    (many N1 : (erased (Bin) b) (erased (Nat) m) (erased (Nat) d) (erased (Numeral b m) v) (erased (Double m d) dd) ->
       (Numeral (B1 b) (Succ d)))
    (many N2 : (erased (Bin) b) (erased (Nat) m) (erased (Nat) d) (erased (Numeral b m) v) (erased (Double m d) dd) ->
       (Numeral (B2 b) (Succ (Succ d))))))

(def-fns _ $ many bin-to-nat : (subterm many (Bin) b) -> (many (Nat) n) (erased (Numeral b n) v)
  (match many b _
    ((BZ) (values (Zero) (NZ)))
    ((B1 b1)
      (let (many m) (erased v1) (bin-to-nat b1))
      (let (many d) (erased dd) (double m))
      (values (Succ d) (N1 b1 m d v1 dd)))
    ((B2 b1)
      (let (many m) (erased v1) (bin-to-nat b1))
      (let (many d) (erased dd) (double m))
      (values (Succ (Succ d)) (N2 b1 m d v1 dd)))))

; Reasoning about a numeral through its spelling rather than its opaque Nat: the relations below are
; functional and injective, and the spelling's successor is structural (DESIGN.md section 16's let-match
; carries their conclusions outward).

(def-fns _ $ erased lt-unique :
    (erased (Nat) a) (erased (Nat) b) (subterm erased (Lt a b) p) (erased (Lt a b) q) ->
    (erased (Eq (Lt a b) p q) e)
  (match erased p _
    ((LtZ b1) (match erased q _ ((LtZ b2) (Refl (Lt a b) p)) (absurd LtS)))
    ((LtS a1 b1 p1)
      (match erased q _
        (absurd LtZ)
        ((LtS a2 b2 q1)
          (let (erased sp) (prove-subterm p1 p))
          (let (erased ih) (lt-unique a1 b1 (subterm sp) p1 q1))
          (match erased ih _ ((Refl t r) (Refl (Lt a b) p))))))))

(def-fns _ $ erased double-fn :
    (erased (Nat) m) (erased (Nat) d1) (erased (Nat) d2)
    (subterm erased (Double m d1) p) (erased (Double m d2) q) -> (erased (Eq (Nat) d1 d2) e)
  (match erased p _
    ((D0) (match erased q _ ((D0) (Refl (Nat) d1)) (absurd DS)))
    ((DS a1 b1 pp)
      (match erased q _
        (absurd D0)
        ((DS a2 b2 qq)
          (let (erased sp) (prove-subterm pp p))
          (let (erased ih) (double-fn a1 b1 b2 (subterm sp) pp qq))
          (match erased ih _ ((Refl t r) (Refl (Nat) d1))))))))

(def-fns _ $ erased double-inj :
    (erased (Nat) m1) (erased (Nat) m2) (erased (Nat) d)
    (subterm erased (Double m1 d) p) (erased (Double m2 d) q) -> (erased (Eq (Nat) m1 m2) e)
  (match erased p _
    ((D0) (match erased q _ ((D0) (Refl (Nat) m1)) (absurd DS)))
    ((DS a1 b1 pp)
      (match erased q _
        (absurd D0)
        ((DS a2 b2 qq)
          (let (erased sp) (prove-subterm pp p))
          (let (erased ih) (double-inj a1 a2 b1 (subterm sp) pp qq))
          (match erased ih _ ((Refl t r) (Refl (Nat) m1))))))))

(def-fns _ $ erased double-parity :
    (erased (Nat) a) (erased (Nat) b) (erased (Nat) e)
    (subterm erased (Double a (Succ e)) p) (erased (Double b e) q) -> (erased (False) f)
  (match erased p _
    (absurd D0)
    ((DS a1 b1 pp)
      (match erased q _
        (absurd D0)
        ((DS a2 b2 qq)
          (let (erased sp) (prove-subterm pp p))
          (double-parity a1 a2 b2 (subterm sp) pp qq))))))

(def-fns _ $ erased numeral-zero :
    (erased (Nat) n) (erased (Numeral (BZ) n) v) -> (erased (Eq (Nat) n (Zero)) e)
  (match erased v _
    ((NZ) (Refl (Nat) n))
    (absurd N1)
    (absurd N2)))

(def-fns _ $ erased numeral-fn :
    (erased (Bin) b) (erased (Nat) m1) (erased (Nat) m2)
    (subterm erased (Numeral b m1) v1) (erased (Numeral b m2) v2) -> (erased (Eq (Nat) m1 m2) e)
  (match erased v1 _
    ((NZ) (match erased v2 _ ((NZ) (Refl (Nat) m1)) (absurd N1) (absurd N2)))
    ((N1 c1 x1 d1 w1 dd1)
      (match erased v2 _
        (absurd NZ)
        ((N1 c2 x2 d2 w2 dd2)
          (let (erased sp) (prove-subterm w1 v1))
          (let (erased ih) (numeral-fn c1 x1 x2 (subterm sp) w1 w2))
          (match erased ih _
            ((Refl t r)
              (let (erased ed) (double-fn x1 d1 d2 dd1 dd2))
              (match erased ed _ ((Refl t2 r2) (Refl (Nat) m1))))))
        (absurd N2)))
    ((N2 c1 x1 d1 w1 dd1)
      (match erased v2 _
        (absurd NZ)
        (absurd N1)
        ((N2 c2 x2 d2 w2 dd2)
          (let (erased sp) (prove-subterm w1 v1))
          (let (erased ih) (numeral-fn c1 x1 x2 (subterm sp) w1 w2))
          (match erased ih _
            ((Refl t r)
              (let (erased ed) (double-fn x1 d1 d2 dd1 dd2))
              (match erased ed _ ((Refl t2 r2) (Refl (Nat) m1))))))))))

(def-fns _ $ erased numeral-inj :
    (erased (Bin) b1) (erased (Bin) b2) (erased (Nat) n)
    (subterm erased (Numeral b1 n) v1) (erased (Numeral b2 n) v2) -> (erased (Eq (Bin) b1 b2) e)
  (match erased v1 _
    ((NZ) (match erased v2 _ ((NZ) (Refl (Bin) b1)) (absurd N1) (absurd N2)))
    ((N1 c1 m1 d1 w1 dd1)
      (match erased v2 _
        (absurd NZ)
        ((N1 c2 m2 d2 w2 dd2)
          (let (erased em) (double-inj m1 m2 d1 dd1 dd2))
          (match erased em _
            ((Refl t r)
              (let (erased sp) (prove-subterm w1 v1))
              (let (erased ih) (numeral-inj c1 c2 m1 (subterm sp) w1 w2))
              (match erased ih _ ((Refl t2 r2) (Refl (Bin) b1))))))
        (absurd (N2 c2 m2 d2 w2 dd2) (double-parity m1 m2 d2 dd1 dd2))))
    ((N2 c1 m1 d1 w1 dd1)
      (match erased v2 _
        (absurd NZ)
        (absurd (N1 c2 m2 d2 w2 dd2) (double-parity m2 m1 d1 dd2 dd1))
        ((N2 c2 m2 d2 w2 dd2)
          (let (erased em) (double-inj m1 m2 d1 dd1 dd2))
          (match erased em _
            ((Refl t r)
              (let (erased sp) (prove-subterm w1 v1))
              (let (erased ih) (numeral-inj c1 c2 m1 (subterm sp) w1 w2))
              (match erased ih _ ((Refl t2 r2) (Refl (Bin) b1))))))))))

(def-adts
  (BinSucc : ((Bin) b) ((Bin) c) -> Type
    enum
    (many BSZ : -> (BinSucc (BZ) (B1 (BZ))))
    (many BS1 : (erased (Bin) b) -> (BinSucc (B1 b) (B2 b)))
    (many BS2 : (erased (Bin) b) (erased (Bin) c) (erased (BinSucc b c) s) -> (BinSucc (B2 b) (B1 c)))))

(def-fns _ $ erased numeral-succ :
    (erased (Bin) b) (erased (Bin) c) (erased (Nat) m) (erased (Nat) n)
    (subterm erased (BinSucc b c) s)
    (erased (Numeral b m) v) (erased (Numeral c n) w) -> (erased (Eq (Nat) n (Succ m)) e)
  (match erased s _
    ((BSZ)
      (match erased v _
        ((NZ)
          (match erased w _
            (absurd NZ)
            ((N1 c1 x1 d1 w1 dd1)
              (match erased w1 _
                ((NZ) (match erased dd1 _ ((D0) (Refl (Nat) n)) (absurd DS)))
                (absurd N1)
                (absurd N2)))
            (absurd N2)))
        (absurd N1)
        (absurd N2)))
    ((BS1 b0)
      (match erased v _
        (absurd NZ)
        ((N1 c1 x1 d1 w1 dd1)
          (match erased w _
            (absurd NZ)
            (absurd N1)
            ((N2 c2 x2 d2 w2 dd2)
              (let (erased ex) (numeral-fn c1 x1 x2 w1 w2))
              (match erased ex _
                ((Refl t r)
                  (let (erased ed) (double-fn x1 d1 d2 dd1 dd2))
                  (match erased ed _ ((Refl t2 r2) (Refl (Nat) n))))))))
        (absurd N2)))
    ((BS2 b0 c0 s0)
      (match erased v _
        (absurd NZ)
        (absurd N1)
        ((N2 c1 x1 d1 w1 dd1)
          (match erased w _
            (absurd NZ)
            ((N1 c2 x2 d2 w2 dd2)
              (let (erased sp) (prove-subterm s0 s))
              (let (erased ih) (numeral-succ b0 c0 x1 x2 (subterm sp) s0 w1 w2))
              (match erased ih _
                ((Refl t r)
                  (match erased dd2 _
                    (absurd D0)
                    ((DS a2 bb ddx)
                      (let (erased ed) (double-fn x1 d1 bb dd1 ddx))
                      (match erased ed _ ((Refl t2 r2) (Refl (Nat) n))))))))
            (absurd N2)))))))

(def-adts $ Char : -> Type
  enum newtype
  (many MkChar : (many (U8) u) -> (Char)))

(def-adts
  (CharLt : ((Char) a) ((Char) b) -> Type
    enum
    (many MkCharLt : (erased (Nat) m) (erased (Nat) n)
                     (erased (Lt m u8-modulus) pm) (erased (Lt n u8-modulus) pn)
                     (erased (Lt m n) p) -> (CharLt (MkChar (MkU8 m pm)) (MkChar (MkU8 n pn))))))

(def-lvl char-lvl)

; A Char is its code at runtime, so this is nat-cmp: the arguments coerce down through both newtypes and
; the result back up, the Coercible for it built by an erased match that leaves no code behind.
(def-fns char-lvl $ many char-cmp : (many (Char) a) (many (Char) b) ->
    (many (Cmp (Char) CharLt a b) c)
  (let-match erased a (MkChar ua))
  (let-match erased ua (MkU8 ma pa))
  (let-match erased b (MkChar ub))
  (let-match erased ub (MkU8 nb pb))
  (let (many ka) (coerce a (coercible-trans (coercible-sym (coercible-wrap (Shared) MkChar ua))
                                            (coercible-sym (coercible-wrap (Shared) MkU8 ma pa)))))
  (let (many kb) (coerce b (coercible-trans (coercible-sym (coercible-wrap (Shared) MkChar ub))
                                            (coercible-sym (coercible-wrap (Shared) MkU8 nb pb)))))
  (let (many r) (delegate (nat-cmp ka kb)))
  (let (erased c2) (erased cr)
    (match erased r (((Cmp (Char) CharLt a b) c2)
                     ((Coercible (Shared) (Cmp (Nat) Lt ka kb) r (Shared) (Cmp (Char) CharLt a b) c2) cc))
      ((CLt t rr x y p)
        (values (CLt (Char) CharLt a b (MkCharLt ma nb pa pb p))
                (coercible-ctor (Shared) CLt (Nat) (Char) Lt CharLt ka a kb b p (MkCharLt ma nb pa pb p))))
      ((CEq t rr x)
        (match erased (lt-unique ma u8-modulus pa pb) _
          ((Refl u2 v2)
            (values (CEq (Char) CharLt a)
                    (coercible-ctor (Shared) CEq (Nat) (Char) Lt CharLt ka a)))))
      ((CGt t rr x y q)
        (values (CGt (Char) CharLt a b (MkCharLt nb ma pb pa q))
                (coercible-ctor (Shared) CGt (Nat) (Char) Lt CharLt ka a kb b q (MkCharLt nb ma pb pa q))))))
  (coerce r cr))

(def-adts $ String : -> Type
  enum extern
  (many SNil : -> (String))
  (many SCons : (many (Char) c) (many (String) rest) -> (String)))

(def-adts
  (Append : ((String) a) ((String) b) ((String) c) -> Type
    enum
    (many AppNil : (erased (String) b) -> (Append (SNil) b b))
    (many AppCons : (erased (Char) ch) (erased (String) a) (erased (String) b) (erased (String) c) (erased (Append a b c) q) ->
       (Append (SCons ch a) b (SCons ch c)))))

(def-fns _ $ many extern append : (subterm many (String) a) (many (String) b) -> (many (String) c) (erased (Append a b c) p)
  (match many a _
    ((SNil) (values b (AppNil b)))
    ((SCons ch rest)
      (let (many c) (erased q) (append rest b))
      (values (SCons ch c) (AppCons ch rest b c q)))))

(def-lvl str-lvl)

(def-fns str-lvl $ many extern trim : (many (String) s) -> (many s is t)
  s)

(def-fns str-lvl $ many str-append : (many (String) a) (many (String) b) -> (many (String) c)
  (let (many c) (erased p) (delegate (append a b)))
  c)

(def-adts
  (StrLt : ((String) a) ((String) b) -> Type
    enum
    (many SLtNil : (erased (Char) d) (erased (String) t) -> (StrLt (SNil) (SCons d t)))
    (many SLtHead : (erased (Char) c) (erased (Char) d) (erased (String) s) (erased (String) t) (erased (CharLt c d) p) -> (StrLt (SCons c s) (SCons d t)))
    (many SLtTail : (erased (Char) c) (erased (String) s) (erased (String) t) (erased (StrLt s t) p) -> (StrLt (SCons c s) (SCons c t)))))

(def-fns _ $ many extern str-cmp : (subterm many (String) a) (many (String) b) -> (many (Cmp (String) StrLt a b) r)
  (match many a _
    ((SNil) (match many b _ ((SNil) (CEq _ _ a)) ((SCons d t) (CLt _ _ a b $ SLtNil d t))))
    ((SCons c s)
      (match many b _
        ((SNil) (CGt _ _ a b $ SLtNil c s))
        ((SCons d t)
          (match many (char-cmp c d) _
            ((CLt ct cr cx cy p) (CLt _ _ a b $ SLtHead c d s t p))
            ((CEq ct cr cx)
              (match many (str-cmp s t) _
                ((CLt st sr sx sy q) (CLt _ _ a b $ SLtTail c s t q))
                ((CEq st sr sx) (CEq _ _ a))
                ((CGt st sr sx sy q) (CGt _ _ a b $ SLtTail c t s q))))
            ((CGt ct cr cx cy p) (CGt _ _ a b $ SLtHead d c t s p))))))))

(def-adts
  (StrLength : ((String) s) ((Nat) n) -> Type
    enum
    (many SLenNil : -> (StrLength (SNil) (Zero)))
    (many SLenCons : (erased (Char) c) (erased (String) s) (erased (Nat) n) (erased (StrLength s n) p) -> (StrLength (SCons c s) (Succ n)))))

(def-fns _ $ many extern str-length : (subterm many (String) s) -> (many (Nat) n) (erased (StrLength s n) p)
  (match many s _
    ((SNil) (values (Zero) (SLenNil)))
    ((SCons c rest)
      (let (many n) (erased p) (str-length rest))
      (values (Succ n) (SLenCons c rest n p)))))

(def-fns _ $ many extern str-split : (many (String) s) (subterm many (Nat) k) (erased (Nat) len) (erased (StrLength s len) l) (erased (Lt k (Succ len)) le) ->
    (many (String) a) (many (String) b) (erased (Append a b s) p) (erased (StrLength a k) la)
  (match many k _
    ((Zero) (values (SNil) s (AppNil s) (SLenNil)))
    ((Succ k1)
      (match many s _
        ((SNil) (match erased l _ ((SLenNil) (match erased le _ (absurd LtZ) ((LtS x y q) (match erased q _ (absurd LtZ) (absurd LtS)))))))
        ((SCons c rest)
          (match erased l _
            ((SLenCons c0 s0 len1 l1)
              (match erased le _
                ((LtS x y q)
                  (let (many a1) (many b) (erased p) (erased la1) (str-split rest k1 len1 l1 q))
                  (values (SCons c a1) b (AppCons c a1 b rest p) (SLenCons c a1 k1 la1)))))))))))

(def-adts $ Rope : -> Type
  enum
  (many REmpty : -> (Rope))
  (many RStr : (many (String) s) -> (Rope))
  (many RCat : (many (Rope) a) (many (Rope) b) -> (Rope))
  (many RChar : (many (Char) c) -> (Rope)))

(def-adts
  (Flat : ((Rope) r) ((String) s) -> Type
    enum
    (many FlatEmpty : -> (Flat (REmpty) (SNil)))
    (many FlatStr : (erased (String) s) -> (Flat (RStr s) s))
    (many FlatCat : (erased (Rope) a) (erased (Rope) b) (erased (String) s1) (erased (String) s2) (erased (String) s)
                    (erased (Flat a s1) p) (erased (Flat b s2) q) (erased (Append s1 s2 s) ap) -> (Flat (RCat a b) s))
    (many FlatChar : (erased (Char) c) -> (Flat (RChar c) (SCons c (SNil))))))

(def-fns _ $ many extern flatten : (subterm many (Rope) r) -> (many (String) s) (erased (Flat r s) p)
  (match many r _
    ((REmpty) (values (SNil) (FlatEmpty)))
    ((RStr s) (values s (FlatStr s)))
    ((RCat a b)
      (let (many s1) (erased p) (flatten a))
      (let (many s2) (erased q) (flatten b))
      (let (many s) (erased ap) (append s1 s2))
      (values s (FlatCat a b s1 s2 s p q ap)))
    ((RChar c) (values (SCons c (SNil)) (FlatChar c)))))

(let (many ten) (Succ (Succ eight)))
(let (many ten-dec) (lt-dec (Zero) ten))
(comptime-match many ten-dec (Yes tda tdb ten-positive))
(let (many ten-dec2) (lt-dec (Succ (Zero)) ten))
(comptime-match many ten-dec2 (Yes tea teb ten-above-one))
(let (many forty-eight) (nat-add (nat-mul (Succ (Succ (Succ (Succ (Zero))))) ten) eight))

(def-fns _ $ many digit-char : (many (Nat) d) -> (many (Char) c)
  (let (many code) (nat-add forty-eight d))
  (match many (lt-dec code u8-modulus) _
    ((Yes a b p) (MkChar $ MkU8 code p))
    ((No a b q) (MkChar $ MkU8 (Zero) u8-modulus-pos))))

(def-fns _ $ many nat-digits : (subterm many (Nat) n) (many (Rope) acc) -> (many (Rope) r)
  (match many n _
    ((Zero) acc)
    ((Succ n1)
      (let (many q) (many d) (erased m) (erased mm) (erased a) (erased p) (divmod n ten ten-positive))
      (let (erased lt) (divmod-lt n1 ten q d m mm a ten-above-one))
      (nat-digits (subterm (lt-subterm q n lt)) q $ RCat (RChar $ digit-char d) acc))))

(def-fns _ $ many extern nat-str : (subterm many (Nat) n) -> (many (String) s)
  (match many n _
    ((Zero) (SCons (digit-char (Zero)) (SNil)))
    ((Succ n1)
      (let (many s) (erased p) (flatten $ nat-digits n $ REmpty))
      s)))

(def-adts $ Unit : -> Type
  enum
  (many MkUnit : -> (Unit)))

(def-adts
  (Maybe : (Type A) -> Type
    enum
    (many None : (erased Type A) -> (Maybe A))
    (many Some : (erased Type A) (many A a) -> (Maybe A))))

(def-adts
  (Result : (Type A) -> Type
    enum
    (many Ok : (erased Type A) (many A a) -> (Result A))
    (many Fail : (erased Type A) (many (String) message) -> (Result A))))

(def-adts
  (List : (Type A) -> Type
    enum
    (many Nil : (erased Type A) -> (List A))
    (many Cons : (erased Type A) (many A head) (many (List A) tail) -> (List A))))

(def-adts
  (Pair : (Type A) (Type B) -> Type
    enum
    (many MkPair : (erased Type A) (erased Type B) (many A first) (many B second) -> (Pair A B))))

(def-adts $ EntryKind : -> Type
  enum
  (many IsFile : -> (EntryKind))
  (many IsDir : -> (EntryKind))
  (many IsOther : -> (EntryKind))
  (many Missing : -> (EntryKind)))

(def-adts $ Change : -> Type
  enum
  (many Changed : -> (Change))
  (many Unchanged : -> (Change)))

(def-lvl thunk-lvl)

(def-fns thunk-lvl $ many thunk : (erased Type A) (erased (Level) L) (many A a) -> (many (Fn L -> (many A r)) k)
  (def-fns L $ many held : -> (many A r) a)
  held)

; A program's requests to the driver (ASSUMPTIONS.md): every entry but Exit carries a continuation the
; driver applies to the request's answer, so a step never recurses and the driver loops.
(def-adts
  (IO : ((Level) L) -> Type
    enum
    (many Exit : (erased (Level) L) (many (U8) code) -> (IO L))
    (many Step : (erased (Level) L) (many (Fn L -> (many (IO L) next)) k) -> (IO L))
    (many WriteOut : (erased (Level) L) (many (String) text) (many (Fn L -> (many (IO L) next)) k) -> (IO L))
    (many WriteErr : (erased (Level) L) (many (String) text) (many (Fn L -> (many (IO L) next)) k) -> (IO L))
    (many ReadLine : (erased (Level) L) (many (Fn L (many (Maybe (String)) line) -> (many (IO L) next)) k) -> (IO L))
    (many ReadFile : (erased (Level) L) (many (String) path) (many (Fn L (many (Result (String)) contents) -> (many (IO L) next)) k) -> (IO L))
    (many WriteFile : (erased (Level) L) (many (String) path) (many (String) text) (many (Fn L (many (Result (Unit)) outcome) -> (many (IO L) next)) k) -> (IO L))
    (many GetArgs : (erased (Level) L) (many (Fn L (many (List (String)) args) -> (many (IO L) next)) k) -> (IO L))
    (many GetEnv : (erased (Level) L) (many (String) name) (many (Fn L (many (Maybe (String)) value) -> (many (IO L) next)) k) -> (IO L))
    (many GetEnvs : (erased (Level) L) (many (Fn L (many (List (Pair (String) (String))) vars) -> (many (IO L) next)) k) -> (IO L))
    (many AppendFile : (erased (Level) L) (many (String) path) (many (String) text) (many (Fn L (many (Result (Unit)) outcome) -> (many (IO L) next)) k) -> (IO L))
    (many ReadRemaining : (erased (Level) L) (many (Fn L (many (String) rest) -> (many (IO L) next)) k) -> (IO L))
    (many ListDir : (erased (Level) L) (many (String) path) (many (Fn L (many (Result (List (String))) entries) -> (many (IO L) next)) k) -> (IO L))
    (many GetCwd : (erased (Level) L) (many (Fn L (many (String) path) -> (many (IO L) next)) k) -> (IO L))
    (many Stat : (erased (Level) L) (many (String) path) (many (Fn L (many (Result (EntryKind)) kind) -> (many (IO L) next)) k) -> (IO L))
    (many MkDir : (erased (Level) L) (many (String) path) (many (Fn L (many (Result (Change)) outcome) -> (many (IO L) next)) k) -> (IO L))
    (many DeleteFile : (erased (Level) L) (many (String) path) (many (Fn L (many (Result (Change)) outcome) -> (many (IO L) next)) k) -> (IO L))
    (many DeleteDir : (erased (Level) L) (many (String) path) (many (Fn L (many (Result (Change)) outcome) -> (many (IO L) next)) k) -> (IO L))))

(def-adts $ Array : (Type A) ((Nat) n) -> Type
  enum extern
  (many ANil : (erased Type A) -> (Array A (Zero)))
  (many ACons : (erased Type A) (erased (Nat) n)
                (unique A head) (unique (Array A n) tail) ->
     (Array A (Succ n))))

(def-adts $ MaybeUninit : (Type A) -> Type
  union newtype
  (many Uninit : (erased Type A) -> (MaybeUninit A))
  (many Init : (erased Type A) (unique A value) -> (MaybeUninit A)))

(def-adts
  (AllUninit : (Type A) ((Nat) n) ((Array (MaybeUninit A) n) a) -> Type
    enum
    (many AUNil : (erased Type A) -> (AllUninit A (Zero) (ANil (MaybeUninit A))))
    (many AUCons : (erased Type A) (erased (Nat) n) (erased (Array (MaybeUninit A) n) tl)
                   (erased (AllUninit A n tl) p) ->
       (AllUninit A (Succ n) (ACons (MaybeUninit A) n (Uninit A) tl))))
  (AllInit : (Type A) ((Nat) n) ((Array (MaybeUninit A) n) a) -> Type
    enum
    (many AINil : (erased Type A) -> (AllInit A (Zero) (ANil (MaybeUninit A))))
    (many AICons : (erased Type A) (erased (Nat) n) (erased A x)
                   (erased (Array (MaybeUninit A) n) tl) (erased (AllInit A n tl) p) ->
       (AllInit A (Succ n) (ACons (MaybeUninit A) n (Init A x) tl))))
  (ANth : (Type A) ((Nat) n) ((Array A n) a) ((Nat) i) (A x) -> Type
    enum
    (many NthZ : (erased Type A) (erased (Nat) n) (erased A x) (erased (Array A n) tl) ->
       (ANth A (Succ n) (ACons A n x tl) (Zero) x))
    (many NthS : (erased Type A) (erased (Nat) n) (erased A h) (erased (Array A n) tl)
                 (erased (Nat) i) (erased A x) (erased (ANth A n tl i x) p) ->
       (ANth A (Succ n) (ACons A n h tl) (Succ i) x)))
  (ASet : (Type A) ((Nat) n) ((Array A n) a) ((Nat) i) (A y) ((Array A n) r) -> Type
    enum
    (many SetZ : (erased Type A) (erased (Nat) n) (erased A h) (erased A y) (erased (Array A n) tl) ->
       (ASet A (Succ n) (ACons A n h tl) (Zero) y (ACons A n y tl)))
    (many SetS : (erased Type A) (erased (Nat) n) (erased A h) (erased (Array A n) tl)
                 (erased (Nat) i) (erased A y) (erased (Array A n) tl2)
                 (erased (ASet A n tl i y tl2) p) ->
       (ASet A (Succ n) (ACons A n h tl) (Succ i) y (ACons A n h tl2)))))

(def-fns _ $ many extern array-new : (erased Type A) (subterm many (Nat) n) ->
    (unique (Array (MaybeUninit A) n) a) (erased (AllUninit A n a) p)
  (match many n _
    ((Zero) (values (ANil _) (AUNil _)))
    ((Succ n1)
      (let (unique tl) (erased q) (array-new A n1))
      (values (ACons _ _ (Uninit _) tl) (AUCons _ _ _ q)))))

(def-fns _ $ many extern array-swap : (erased Type A) (erased (Nat) n)
    (unique (Array A n) a) (subterm many (Nat) i) (unique A x)
    (erased A m) (erased (ANth A n a i m) nth) ->
    (unique m is old) (unique (Array A n) r at a)
    (erased (ASet A n a i x r) p)
  (match unique a _
    (absurd (ANil _ _) (match erased nth (((False) f))))
    ((ACons _ _ hd tl u)
      (match many i _
        ((Zero)
          (match erased nth _
            ((NthZ _ _ _ _)
              (values hd (u _ _ x (at) tl) (SetZ _ _ _ _ _)))
            (absurd NthS)))
        ((Succ i1)
          (match erased nth _
            (absurd NthZ)
            ((NthS _ _ _ _ _ _ q)
              (let (unique old) (unique tl3) (erased p1) (tail (array-swap _ _ tl i1 x _ q)))
              (values old (at (u _ _ hd tl3)) (SetS _ _ _ _ _ _ _ p1)))))))))

(def-fns _ $ many extern array-pluck : (erased Type A) (erased (Nat) n)
    (unique (Array (MaybeUninit A) n) a) (many (Nat) i)
    (erased (MaybeUninit A) m) (erased (ANth (MaybeUninit A) n a i m) nth) ->
    (unique m is v) (unique (Array (MaybeUninit A) n) r at a)
    (erased (ASet (MaybeUninit A) n a i (Uninit A) r) p)
  (tail (array-swap _ _ a i (Uninit _) _ nth)))

(def-fns _ $ many extern array-place : (erased Type A) (erased (Nat) n)
    (unique (Array A n) a) (many (Nat) i) (unique A x)
    (erased A m) (erased (ANth A n a i m) nth) ->
    (unique (Array A n) r at a) (erased (ASet A n a i x r) p)
  (let (unique old) (unique r) (erased p) (array-swap _ _ a i x _ nth))
  (values r p))

(def-fns _ $ erased init-witness : (erased Type A) (erased (Nat) n)
    (erased (Array (MaybeUninit A) n) a) (subterm erased (AllInit A n a) all) ->
    (erased (Array A n) b)
    (erased (Coercible (Unique) (Array (MaybeUninit A) n) a (Unique) (Array A n) b) c)
  (match erased all _
    ((AINil _)
      (values (ANil _) (coercible-ctor _ ANil (MaybeUninit A) A)))
    ((AICons _ n1 x tl q)
      (let (erased b1) (erased c1) (init-witness _ _ tl q))
      (values (ACons _ _ x b1)
              (coercible-ctor _ ACons (MaybeUninit A) A n1 n1
                 (coercible-sym (coercible-wrap _ Init _ x))
                 c1)))))
