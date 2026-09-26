; The source prelude (DESIGN.md section 41), elaborated ahead of every program. Its extern-marked
; definitions are the models the FFI's implementations in ffi.ml stand in for.
;
; The reference does not read this file at run time: lib/dune embeds it into the OCaml build as
; Prelude_source, so an edit here needs a rebuild. slc does not embed it: it is slc's first file on the
; command line (self/bootstrap.sh). Both compilers also name some of its definitions in their own source --
; the literal types, the IO driver's types, the lemmas unary and distinct expand to, and the externs
; lib/ffi.ml and lib/ffi_templates.txt implement -- so renaming one here means renaming it there too.

(def-adts $ (Nat : -> Type)
  enum extern
  (many Zero : -> (Nat))
  (many Succ : (many (Nat) pred) -> (Nat)))

(def-adts $ (False : -> Type)
  enum)

(def-adts
  ((Eq : (Type A) (A x) (A y) -> Type)
    enum
    (many Refl : (erased Type A) (erased A x) -> (Eq A x x))))

(def-fns _ $ (erased eq-trans : (erased Type A) (erased A x) (erased A y) (erased A z)
    (erased (Eq A x y) e) (erased (Eq A y z) f) -> (erased (Eq A x z) g))
  (match erased e _ ((Refl a b) (match erased f _ ((Refl c d) (Refl A x))))))

(def-fns _ $ (erased eq-cong-succ : (erased (Nat) x) (erased (Nat) y) (erased (Eq (Nat) x y) e) ->
    (erased (Eq (Nat) (Succ x) (Succ y)) f))
  (match erased e _ ((Refl a b) (Refl (Nat) (Succ x)))))

(def-adts
  ((Add : ((Nat) a) ((Nat) b) ((Nat) c) -> Type)
    enum
    (many AddZero : (erased (Nat) b) -> (Add (Zero) b b))
    (many AddSucc : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Add a b c) q) -> (Add (Succ a) b (Succ c)))))

(def-adts
  ((Lt : ((Nat) a) ((Nat) b) -> Type)
    enum
    (many LtZ : (erased (Nat) b) -> (Lt (Zero) (Succ b)))
    (many LtS : (erased (Nat) a) (erased (Nat) b) (erased (Lt a b) p) -> (Lt (Succ a) (Succ b)))))

(def-adts
  ((Double : ((Nat) a) ((Nat) b) -> Type)
    enum
    (many D0 : -> (Double (Zero) (Zero)))
    (many DS : (erased (Nat) a) (erased (Nat) b) (erased (Double a b) d) -> (Double (Succ a) (Succ (Succ b))))))

(def-adts
  ((Pow2 : ((Nat) k) ((Nat) v) -> Type)
    enum
    (many P0 : -> (Pow2 (Zero) (Succ (Zero))))
    (many PS : (erased (Nat) k) (erased (Nat) v) (erased (Nat) w) (erased (Pow2 k v) p) (erased (Double v w) d)
       -> (Pow2 (Succ k) w))))

(def-adts
  ((Mod : ((Nat) s) ((Nat) c) ((Nat) r) -> Type)
    enum
    (many ModLt : (erased (Nat) s) (erased (Nat) c) (erased (Lt s c) p) -> (Mod s c s))
    (many ModSub : (erased (Nat) s1) (erased (Nat) c) (erased (Nat) s) (erased (Nat) r) (erased (Add c s1 s) a) (erased (Mod s1 c r) m)
       -> (Mod s c r))))

(def-adts
  ((Dec : ((Nat) a) ((Nat) b) -> Type)
    enum
    (many Yes : (erased (Nat) a) (erased (Nat) b) (erased (Lt a b) p) -> (Dec a b))
    (many No : (erased (Nat) a) (erased (Nat) b) (erased (Lt b (Succ a)) q) -> (Dec a b))))

; Parametric in the carrier and its strict order, every field erased, so a value is only its tag and two
; instances differ by a coercion (section 38).
(def-adts
  ((Cmp : (Type T) ((TyCtor (T x) (T y) -> Type) R) (T a) (T b) -> Type)
    enum
    (many CLt : (erased Type T) (erased (TyCtor (T x) (T y) -> Type) R) (erased T a) (erased T b)
                (erased (R a b) p) -> (Cmp T R a b))
    (many CEq : (erased Type T) (erased (TyCtor (T x) (T y) -> Type) R) (erased T a) -> (Cmp T R a a))
    (many CGt : (erased Type T) (erased (TyCtor (T x) (T y) -> Type) R) (erased T a) (erased T b)
                (erased (R b a) q) -> (Cmp T R a b))))

(def-fns _ $ (erased add-zero-right : (subterm erased (Nat) a) -> (erased (Add a (Zero) a) p))
  (match erased a _
    ((Zero) (AddZero (Zero)))
    ((Succ a1) (AddSucc a1 (Zero) a1 (add-zero-right a1)))))

(def-fns _ $ (erased add-succ-right : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (subterm erased (Add a b c) p) ->
    (erased (Add a (Succ b) (Succ c)) q))
  (match erased p _
    ((AddZero b0) (AddZero (Succ b)))
    ((AddSucc a1 b1 c0 q0) (AddSucc a1 (Succ b) (Succ c0) (add-succ-right a1 b c0 q0)))))

(def-fns _ $ (erased add-succ-right-inv : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (subterm erased (Add a (Succ b) c) p) ->
    (erased (Nat) c1) (erased (Eq (Nat) c (Succ c1)) e) (erased (Add a b c1) q))
  (let-match erased p (AddSucc a1 b1 c0 q0) ((AddZero b0) (values b (Refl (Nat) c) (AddZero b))))
  (let ((erased c1) (erased e1) (erased q1)) (add-succ-right-inv a1 b c0 q0))
  (match erased e1 _
    ((Refl t r) (values (Succ c1) (Refl (Nat) c) (AddSucc a1 b c1 q1)))))

(def-fns _ $ (erased add-diag-double : (subterm erased (Nat) a) (erased (Nat) b) (erased (Add a a b) p) -> (erased (Double a b) d))
  (let-match erased p (AddSucc a1 b1 c0 q0) ((AddZero b0) (D0)))
  (let ((erased c1) (erased e1) (erased q1)) (add-succ-right-inv a1 a1 c0 q0))
  (match erased e1 _
    ((Refl t r) (DS a1 c1 (add-diag-double a1 c1 q1)))))

(def-fns _ $ (erased double-pos : (erased (Nat) v) (erased (Nat) w) (erased (Lt (Zero) v) q) (erased (Double v w) d) ->
    (erased (Lt (Zero) w) r))
  (let-match erased q (LtZ b) (absurd LtS))
  (match erased d _
    (absurd D0)
    ((DS a b2 d1) (LtZ (Succ b2)))))

(def-fns _ $ (erased absurd lt-asym : (erased (Nat) r) (erased (Nat) c) (subterm erased (Lt r c) p) (erased (Lt c (Succ r)) g) -> (erased (False) f))
  (match erased p _
    (absurd (LtZ b) (let-match erased g (LtS x y g1)) g1)
    (absurd (LtS a b p1) (let-match erased g (LtS x y g1)) (lt-asym a b p1 g1))))

(def-fns _ $ (erased mod-succ-lt : (erased (Nat) s) (erased (Nat) c) (erased (Nat) r) (subterm erased (Mod s c r) q) (erased (Lt (Succ r) c) lt) ->
    (erased (Mod (Succ s) c (Succ r)) q1))
  (match erased q _
    ((ModLt x y p0) (ModLt (Succ s) c lt))
    ((ModSub s1 c0 s0 r0 a m) (ModSub (Succ s1) c (Succ s) (Succ r) (add-succ-right c s1 s a) (mod-succ-lt s1 c r m lt)))))

(def-fns _ $ (erased mod-succ-wrap : (erased (Nat) s) (erased (Nat) r) (subterm erased (Mod s (Succ r) r) q) -> (erased (Mod (Succ s) (Succ r) (Zero)) q1))
  (match erased q _
    ((ModLt x y p0) (ModSub (Zero) (Succ r) (Succ s) (Zero) (add-zero-right (Succ r)) (ModLt (Zero) (Succ r) (LtZ r))))
    ((ModSub s1 c0 s0 r0 a m) (ModSub (Succ s1) (Succ r) (Succ s) (Zero) (add-succ-right (Succ r) s1 s a) (mod-succ-wrap s1 r m)))))

(def-adts
  ((Half : ((Nat) n) -> Type)
    enum extern
    (many HZ : -> (Half (Zero)))
    (many H1 : (many (Nat) m) (erased (Nat) d) (erased (Double m d) dd) -> (Half (Succ d)))
    (many H2 : (many (Nat) m) (erased (Nat) d) (erased (Double m d) dd) -> (Half (Succ (Succ d))))))

(def-fns _ $ (many extern nat-halve : (subterm many (Nat) n) -> (many (Half n) h))
  (let-match many n (Succ k) ((Zero) (HZ)))
  (match many (notail $ nat-halve k) _
    ((HZ) (H1 (Zero) (Zero) (D0)))
    ((H1 m d dd) (H2 m d dd))
    ((H2 m d dd) (H1 (Succ m) (Succ (Succ d)) (DS m d dd)))))

(def-fns _ $ (many extern add : (subterm many (Nat) a) (many (Nat) b) -> (many (Nat) c) (erased (Add a b c) p))
  (let-match many a (Succ k) ((Zero) (values b (AddZero b))))
  (let ((many c) (erased q)) (notail $ add k b))
  (values (Succ c) (AddSucc k b c q)))

(def-fns _ $ (erased lt-succ : (subterm erased (Nat) a) -> (erased (Lt a (Succ a)) p))
  (match erased a _
    ((Zero) (LtZ (Zero)))
    ((Succ a1) (LtS a1 (Succ a1) (lt-succ a1)))))

(def-fns _ $ (erased lt-weaken : (erased (Nat) x) (erased (Nat) y) (subterm erased (Lt x y) p) -> (erased (Lt x (Succ y)) q))
  (match erased p _
    ((LtZ b) (LtZ (Succ b)))
    ((LtS a b p1) (LtS a (Succ b) (lt-weaken a b p1)))))

(def-fns _ $ (many extern nat-cmp : (subterm many (Nat) a) (many (Nat) b) -> (many (Cmp (Nat) Lt a b) c))
  (match many a _
    ((Zero)
      (match many b _
        ((Zero) (CEq (Nat) Lt a))
        ((Succ b1) (CLt (Nat) Lt a b (LtZ b1)))))
    ((Succ a1)
      (let-match many b (Succ b1) ((Zero) (CGt (Nat) Lt a b (LtZ a1))))
      (match many (notail $ nat-cmp a1 b1) _
        ((CLt t r x y p) (CLt (Nat) Lt a b (LtS a1 b1 p)))
        ((CEq t r x) (CEq (Nat) Lt a))
        ((CGt t r x y q) (CGt (Nat) Lt a b (LtS b1 a1 q)))))))

(def-adts
  ((Mul : ((Nat) a) ((Nat) b) ((Nat) c) -> Type)
    enum
    (many MulZero : (erased (Nat) b) -> (Mul (Zero) b (Zero)))
    (many MulSucc : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Nat) d) (erased (Mul a b c) m) (erased (Add c b d) p)
       -> (Mul (Succ a) b d))))

(def-fns _ $ (erased add-comm : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (subterm erased (Add a b c) p) -> (erased (Add b a c) q))
  (match erased p _
    ((AddZero b0) (add-zero-right b))
    ((AddSucc a1 b1 c1 p1) (add-succ-right b a1 c1 (add-comm a1 b c1 p1)))))

(def-fns _ $ (many extern mul : (subterm many (Nat) a) (many (Nat) b) -> (many (Nat) c) (erased (Mul a b c) p))
  (let-match many a (Succ a1) ((Zero) (values (Zero) (MulZero b))))
  (let ((many c1) (erased m)) (notail $ mul a1 b))
  (let ((many c) (erased q)) (add b c1))
  (values c (MulSucc a1 b c1 c m (add-comm b c1 c q))))

(def-fns _ $ (many extern sub : (many (Nat) a) (subterm many (Nat) b) (erased (Lt b (Succ a)) le) -> (many (Nat) c) (erased (Add b c a) p))
  (let-match many b (Succ b1) ((Zero) (values a (AddZero a))))
  (let-match many a (Succ a1) (absurd (Zero) (let-match erased le (LtS x y l1)) l1))
  (let ((erased le1)) (match erased le (((Lt b1 (Succ a1)) l)) (absurd LtZ) ((LtS x y l1) l1)))
  (let ((many c) (erased q)) (tail $ sub a1 b1 le1))
  (values c (AddSucc b1 c a1 q)))

(def-fns _ $ (many succ-div : (many (Nat) q) (many (Nat) r) (many (Nat) c) (erased (Nat) m) (erased (Nat) s)
    (erased (Mul q c m) mm) (erased (Add m r s) a) (erased (Lt r c) p) ->
    (many (Nat) q1) (many (Nat) r1) (erased (Nat) m1) (erased (Mul q1 c m1) mm1) (erased (Add m1 r1 (Succ s)) a1) (erased (Lt r1 c) p1))
  (match many (nat-cmp (Succ r) c) _
    ((CLt t rr x y lt) (values q (Succ r) m mm (add-succ-right m r s a) lt))
    ((CEq t rr x) (values (Succ q) (Zero) (Succ s) (MulSucc q c m (Succ s) mm (add-succ-right m r s a)) (add-zero-right (Succ s)) (LtZ r)))
    (absurd (CGt t rr x y gt) (lt-asym r c p gt))))

(def-fns _ $ (many extern divmod : (subterm many (Nat) s) (many (Nat) c) (erased (Lt (Zero) c) pos) ->
    (many (Nat) q) (many (Nat) r) (erased (Nat) m) (erased (Mul q c m) mm) (erased (Add m r s) a) (erased (Lt r c) p))
  (let-match many s (Succ s1) ((Zero) (values (Zero) (Zero) (Zero) (MulZero c) (AddZero (Zero)) pos)))
  (let ((many q1) (many r1) (erased m1) (erased mm1) (erased a1) (erased p1)) (notail $ divmod s1 c pos))
  (succ-div q1 r1 c m1 s1 mm1 a1 p1))

(def-fns _ $ (many extern div : (many (Nat) s) (many (Nat) c) (erased (Lt (Zero) c) pos) ->
    (many (Nat) q) (erased (Nat) m) (erased (Nat) r) (erased (Mul q c m) mm) (erased (Add m r s) a) (erased (Lt r c) p))
  (let ((many q) (many r) (erased m) (erased mm) (erased a) (erased p)) (divmod s c pos))
  (values q m r mm a p))

(def-fns _ $ (erased lt-trans : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (subterm erased (Lt a b) p) (erased (Lt b c) q) -> (erased (Lt a c) r))
  (match erased p _
    ((LtZ b1) (match erased q _ ((LtS x y q1) (LtZ y))))
    ((LtS a1 b1 p1) (match erased q _ ((LtS x y q1) (LtS a1 y (lt-trans a1 b1 y p1 q1)))))))

(def-fns _ $ (erased lt-le-trans : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (subterm erased (Lt a b) p) (erased (Lt b (Succ c)) q) -> (erased (Lt a c) r))
  (match erased p _
    ((LtZ b1)
      (match erased q _
        ((LtS x y q1) (match erased q1 _ ((LtZ z) (LtZ z)) ((LtS x2 y2 q2) (LtZ y2))))))
    ((LtS a1 b1 p1)
      (match erased q _
        ((LtS x y q1)
          (match erased q1 _
            (absurd (LtZ z) p1)
            ((LtS b2 c1 q2) (LtS a1 c1 (lt-le-trans a1 b1 c1 p1 (LtS b2 c1 q2))))))))))

(def-fns _ $ (erased lt-subterm : (erased (Nat) a) (subterm erased (Nat) b) (erased (Lt a b) p) -> (erased (Subterm (Nat) a (Nat) b) s))
  (let-match erased b (Succ b1) (absurd (Zero) p))
  (match erased (nat-cmp a b1) _
    ((CLt t r x y q) (subterm-trans (lt-subterm a b1 q) (prove-subterm b1 b)))
    ((CEq t r x) (prove-subterm a b))
    (absurd (CGt t r x y g) (lt-asym b1 a g p))))

(def-fns _ $ (erased add-le-left : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (subterm erased (Add a b c) p) -> (erased (Lt a (Succ c)) q))
  (match erased p _
    ((AddZero b0) (LtZ b))
    ((AddSucc a1 b1 c1 p1) (LtS a1 (Succ c1) (add-le-left a1 b c1 p1)))))

(def-fns _ $ (erased add-lt-left : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (subterm erased (Add a b c) p) (erased (Lt (Succ (Zero)) b) two) -> (erased (Lt (Succ a) c) q))
  (match erased p _
    ((AddZero b0) two)
    ((AddSucc a1 b1 c1 p1) (LtS (Succ a1) c1 (add-lt-left a1 b c1 p1 two)))))

(def-fns _ $ (erased mul-lt : (erased (Nat) q) (erased (Nat) c) (erased (Nat) m) (subterm erased (Mul (Succ q) c m) mm) (erased (Lt (Succ (Zero)) c) two) -> (erased (Lt (Succ q) m) l))
  (match erased mm _
    ((MulSucc q0 c0 m0 d0 mm0 p0)
      (match erased q _
        ((Zero) (match erased mm0 _ ((MulZero b0) (match erased p0 _ ((AddZero b1) two)))))
        ((Succ q1) (lt-trans (Succ q) (Succ m0) m (LtS q m0 (mul-lt q1 c m0 mm0 two)) (add-lt-left m0 c m p0 two)))))))

(def-fns _ $ (erased divmod-lt : (erased (Nat) s) (erased (Nat) c) (erased (Nat) q) (erased (Nat) r) (erased (Nat) m)
    (erased (Mul q c m) mm) (erased (Add m r (Succ s)) a) (erased (Lt (Succ (Zero)) c) two) -> (erased (Lt q (Succ s)) l))
  (match erased q _
    ((Zero) (LtZ s))
    ((Succ q1) (lt-le-trans q m (Succ s) (mul-lt q1 c m mm two) (add-le-left m r (Succ s) a)))))

(def-lvl nat-lvl)

(def-fns nat-lvl $ (many nat-add : (many (Nat) a) (many (Nat) b) -> (many (Nat) c))
  (let ((many c) (erased p)) (delegate (add a b)))
  c)

(def-fns nat-lvl $ (many nat-mul : (many (Nat) a) (many (Nat) b) -> (many (Nat) c))
  (let ((many c) (erased p)) (delegate (mul a b)))
  c)

(def-fns nat-lvl $ (many double : (many (Nat) a) -> (many (Nat) b) (erased (Double a b) d))
  (let ((many b) (erased p)) (add a a))
  (values b (add-diag-double a b p)))

(def-fns nat-lvl $ (many extern lt-dec : (many (Nat) a) (many (Nat) b) -> (many (Dec a b) d))
  (match many (nat-cmp a b) _
    ((CLt t r x y p) (Yes a b p))
    ((CEq t r x) (No a b (lt-succ a)))
    ((CGt t r x y q) (No a b (lt-weaken b a q)))))

(def-fns _ $ (many succ-mod : (many (Nat) r) (many (Nat) c) (erased (Nat) s) (erased (Lt r c) p) (erased (Mod s c r) q) ->
    (many (Nat) r1) (erased (Lt r1 c) p1) (erased (Mod (Succ s) c r1) q1))
  (match many (nat-cmp (Succ r) c) _
    ((CLt t rr x y lt) (values (Succ r) lt (mod-succ-lt s c r q lt)))
    ((CEq t rr x) (values (Zero) (LtZ r) (mod-succ-wrap s r q)))
    (absurd (CGt t rr x y gt) (lt-asym r c p gt))))

(def-fns _ $ (many extern nat-mod : (subterm many (Nat) s) (many (Nat) c) (erased (Lt (Zero) c) pos) ->
    (many (Nat) r) (erased (Lt r c) p) (erased (Mod s c r) q))
  (let-match many s (Succ s1) ((Zero) (values (Zero) pos (ModLt (Zero) c pos))))
  (let ((many r1) (erased p1) (erased q1)) (notail $ nat-mod s1 c pos))
  (succ-mod r1 c s1 p1 q1))

(def-fns _ $ (many pow2 : (subterm many (Nat) k) -> (many (Nat) v) (erased (Pow2 k v) p) (erased (Lt (Zero) v) q))
  (let-match many k (Succ k1) ((Zero) (values (Succ (Zero)) (P0) (LtZ (Zero)))))
  (let ((many v) (erased p) (erased q)) (notail $ pow2 k1))
  (let ((many w) (erased d)) (double v))
  (values w (PS k1 v w p d) (double-pos v w q d)))

(let ((many eight)) (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))))))
(let ((many u8-modulus) (erased u8-modulus-pow2) (erased u8-modulus-pos)) (pow2 eight))

(def-adts $ (U8 : -> Type)
  enum newtype
  (many MkU8 : (many (Nat) n) (erased (Lt n u8-modulus) p) -> (U8)))

(let ((erased sixty) (erased sixty-mul)) (mul (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))) (Succ (Succ eight))))
(let ((erased sixty-two) (erased sixty-two-add)) (add sixty (Succ (Succ (Zero)))))
(let ((erased u62-modulus) (erased u62-modulus-pow2) (erased u62-modulus-pos)) (pow2 sixty-two))

(def-adts $ (U62 : -> Type)
  enum newtype
  (many MkU62 : (many (Nat) n) (erased (Lt n u62-modulus) p) -> (U62)))

(def-fns _ $ (erased pow2-pos : (erased (Nat) k) (erased (Nat) v) (subterm erased (Pow2 k v) p) -> (erased (Lt (Zero) v) q))
  (match erased p _
    ((P0) (LtZ (Zero)))
    ((PS k1 v1 w p1 d) (double-pos v1 w (pow2-pos k1 v1 p1) d))))

(def-fns _ $ (erased double-mono : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Nat) d)
    (subterm erased (Lt a b) l) (erased (Double a c) p) (erased (Double b d) q) -> (erased (Lt c d) r))
  (match erased l _
    ((LtZ b1)
      (let-match erased p (D0))
      (let-match erased q (DS _ d1 q1))
      (LtZ (Succ d1)))
    ((LtS a1 b1 l1)
      (let-match erased p (DS _ c1 p1))
      (let-match erased q (DS _ d1 q1))
      (LtS (Succ c1) (Succ d1) (LtS c1 d1 (double-mono a1 b1 c1 d1 l1 p1 q1))))))

(def-fns _ $ (erased pow2-lt : (erased (Nat) k) (erased (Nat) k2) (erased (Nat) v) (erased (Nat) w)
    (subterm erased (Lt k k2) l) (erased (Pow2 k v) p) (erased (Pow2 k2 w) q) -> (erased (Lt v w) r))
  (match erased l _
    ((LtZ b1)
      (let-match erased p (P0))
      (let-match erased q (PS _ w1 _ q1 d))
      (let-match erased (pow2-pos _ _ q1) (LtZ x))
      (let-match erased d (DS _ y _))
      (LtS (Zero) (Succ y) (LtZ y)))
    ((LtS k1 k3 l1)
      (let-match erased p (PS _ v1 _ p1 dp))
      (let-match erased q (PS _ w1 _ q1 dq))
      (double-mono v1 w1 v w (pow2-lt k1 k3 v1 w1 l1 p1 q1) dp dq))))

(def-fns _ $ (erased eight-lt-sixty-two : -> (erased (Lt eight sixty-two) l))
  (let-match erased sixty-mul (MulSucc _ _ m0 _ _ s60))
  (let ((erased ten-le)) (add-le-left _ _ _ (add-comm _ _ _ s60)))
  (let ((erased eight-ten)) (lt-trans eight (Succ eight) (Succ (Succ eight)) (lt-succ eight) (lt-succ (Succ eight))))
  (lt-le-trans eight sixty sixty-two (lt-le-trans _ _ _ eight-ten ten-le) (add-le-left _ _ _ sixty-two-add)))

(let ((erased u8-below-u62)) (pow2-lt _ _ _ _ (eight-lt-sixty-two) u8-modulus-pow2 u62-modulus-pow2))

(def-fns _ $ (erased add-fn : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c1) (erased (Nat) c2)
    (subterm erased (Add a b c1) p) (erased (Add a b c2) q) -> (erased (Eq (Nat) c1 c2) e))
  (let-match erased p (AddSucc a1 b1 d1 p1) ((AddZero b0) (match erased q _ ((AddZero b1) (Refl (Nat) c1)) (absurd AddSucc))))
  (let-match erased q (AddSucc a2 b2 d2 q1) (absurd AddZero))
  (let ((erased sp)) (prove-subterm p1 p))
  (match erased (add-fn a1 b d1 d2 (subterm sp) p1 q1) _ ((Refl t r) (Refl (Nat) c1))))

(def-fns _ $ (erased mul-fn : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c1) (erased (Nat) c2)
    (subterm erased (Mul a b c1) p) (erased (Mul a b c2) q) -> (erased (Eq (Nat) c1 c2) e))
  (let-match erased p (MulSucc a1 b1 x1 d1 m1 p1)
    ((MulZero b0) (match erased q _ ((MulZero b1) (Refl (Nat) c1)) (absurd MulSucc))))
  (let-match erased q (MulSucc a2 b2 x2 d2 m2 q1) (absurd MulZero))
  (let ((erased sp)) (prove-subterm m1 p))
  (match erased (mul-fn a1 b x1 x2 (subterm sp) m1 m2) _
    ((Refl t r) (add-fn x1 b c1 c2 p1 q1))))

(def-fns _ $ (erased add-pos-lt : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (subterm erased (Add a b c) p) (erased (Lt (Zero) b) pos) -> (erased (Lt a c) q))
  (match erased p _
    ((AddZero b0) pos)
    ((AddSucc a1 b1 c1 p1) (LtS a1 c1 (add-pos-lt a1 b c1 p1 pos)))))

(def-fns _ $ (erased mul-le : (erased (Nat) q) (erased (Nat) c) (erased (Nat) k) (subterm erased (Mul q c k) mm) (erased (Lt (Zero) c) pos) -> (erased (Lt q (Succ k)) l))
  (match erased mm _
    ((MulZero b0) (LtZ k))
    ((MulSucc q1 c1 k1 k2 mm1 p1)
      (LtS q1 k (lt-le-trans q1 (Succ k1) k (mul-le q1 c k1 mm1 pos) (LtS k1 k (add-pos-lt k1 c k p1 pos)))))))

(def-fns _ $ (many extern u62-add : (many (Nat) n) (many (Nat) m)
    (erased (Nat) s) (erased (Add n m s) sum) (erased (Lt s u62-modulus) ps) ->
    (many s is r))
  (let ((many s1) (erased sum1)) (add n m))
  (match erased (add-fn n m s1 s sum1 sum) _ ((Refl t x) s1)))

(def-fns _ $ (many extern u62-sub : (many (Nat) n) (many (Nat) m)
    (erased (Lt n u62-modulus) pn) (erased (Lt m (Succ n)) le) ->
    (many (Nat) d) (erased (Add m d n) diff) (erased (Lt d u62-modulus) pd))
  (let ((many d) (erased diff)) (sub n m le))
  (values d diff (lt-le-trans d (Succ n) u62-modulus (add-le-left d m n (add-comm m d n diff)) (LtS n u62-modulus pn))))

(def-fns _ $ (many extern u62-mul : (many (Nat) n) (many (Nat) m)
    (erased (Lt n u62-modulus) pn) (erased (Lt m u62-modulus) pm)
    (erased (Nat) r) (erased (Mul n m r) prod) (erased (Lt r u62-modulus) pr) ->
    (many r is c))
  (let ((many r1) (erased prod1)) (mul n m))
  (match erased (mul-fn n m r1 r prod1 prod) _ ((Refl t x) r1)))

(def-fns _ $ (many extern u62-divmod : (many (Nat) n) (many (Nat) m)
    (erased (Lt n u62-modulus) pn) (erased (Lt m u62-modulus) pm) (erased (Lt (Zero) m) pos) ->
    (many (Nat) q) (many (Nat) r) (erased (Nat) k) (erased (Mul q m k) mm) (erased (Add k r n) ad) (erased (Lt r m) rlt)
    (erased (Lt q u62-modulus) pq) (erased (Lt r u62-modulus) pr))
  (let ((many q) (many r) (erased k) (erased mm) (erased ad) (erased rlt)) (divmod n m pos))
  (let ((erased qle)) (lt-le-trans q (Succ k) (Succ n) (mul-le q m k mm pos) (LtS k (Succ n) (add-le-left k r n ad))))
  (values q r k mm ad rlt (lt-le-trans q (Succ n) u62-modulus qle (LtS n u62-modulus pn)) (lt-trans r m u62-modulus rlt pm)))

(def-fns _ $ (many extern u62-div : (many (Nat) n) (many (Nat) m)
    (erased (Lt n u62-modulus) pn) (erased (Lt m u62-modulus) pm) (erased (Lt (Zero) m) pos) ->
    (many (Nat) q) (erased (Nat) k) (erased (Nat) r) (erased (Mul q m k) mm) (erased (Add k r n) ad) (erased (Lt r m) rlt)
    (erased (Lt q u62-modulus) pq))
  (let ((many q) (erased k) (erased r) (erased mm) (erased ad) (erased rlt)) (div n m pos))
  (let ((erased qle)) (lt-le-trans q (Succ k) (Succ n) (mul-le q m k mm pos) (LtS k (Succ n) (add-le-left k r n ad))))
  (values q k r mm ad rlt (lt-le-trans q (Succ n) u62-modulus qle (LtS n u62-modulus pn))))

(def-fns _ $ (many extern u62-mod : (many (Nat) n) (many (Nat) m)
    (erased (Lt n u62-modulus) pn) (erased (Lt m u62-modulus) pm) (erased (Lt (Zero) m) pos) ->
    (many (Nat) r) (erased (Lt r m) rlt) (erased (Mod n m r) md) (erased (Lt r u62-modulus) pr))
  (let ((many r) (erased rlt) (erased md)) (nat-mod n m pos))
  (values r rlt md (lt-trans r m u62-modulus rlt pm)))

(def-fns _ $ (many extern u62-cmp : (many (Nat) n) (many (Nat) m)
    (erased (Lt n u62-modulus) pn) (erased (Lt m u62-modulus) pm) ->
    (many (Cmp (Nat) Lt n m) c))
  (tail (nat-cmp n m)))

(def-fns _ $ (many extern u62-lt-dec : (many (Nat) n) (many (Nat) m)
    (erased (Lt n u62-modulus) pn) (erased (Lt m u62-modulus) pm) ->
    (many (Dec n m) d))
  (tail (lt-dec n m)))

(def-adts $ (Bin : -> Type)
  enum
  (many BZ : -> (Bin))
  (many B1 : (many (Bin) rest) -> (Bin))
  (many B2 : (many (Bin) rest) -> (Bin)))

(def-adts
  ((Numeral : ((Bin) b) ((Nat) n) -> Type)
    enum
    (many NZ : -> (Numeral (BZ) (Zero)))
    (many N1 : (erased (Bin) b) (erased (Nat) m) (erased (Nat) d) (erased (Numeral b m) v) (erased (Double m d) dd)
       -> (Numeral (B1 b) (Succ d)))
    (many N2 : (erased (Bin) b) (erased (Nat) m) (erased (Nat) d) (erased (Numeral b m) v) (erased (Double m d) dd)
       -> (Numeral (B2 b) (Succ (Succ d))))))

(def-fns _ $ (many bin-to-nat : (subterm many (Bin) b) -> (many (Nat) n) (erased (Numeral b n) v))
  (match many b _
    ((BZ) (values (Zero) (NZ)))
    ((B1 b1)
      (let ((many m) (erased v1)) (notail $ bin-to-nat b1))
      (let ((many d) (erased dd)) (double m))
      (values (Succ d) (N1 b1 m d v1 dd)))
    ((B2 b1)
      (let ((many m) (erased v1)) (notail $ bin-to-nat b1))
      (let ((many d) (erased dd)) (double m))
      (values (Succ (Succ d)) (N2 b1 m d v1 dd)))))

; Reasoning about a numeral through its spelling rather than its opaque Nat: the relations below are
; functional and injective, and the spelling's successor is structural (DESIGN.md section 16's let-match
; carries their conclusions outward).

(def-fns _ $ (erased lt-unique :
    (erased (Nat) a) (erased (Nat) b) (subterm erased (Lt a b) p) (erased (Lt a b) q) ->
    (erased (Eq (Lt a b) p q) e))
  (let-match erased p (LtS a1 b1 p1) ((LtZ b1) (match erased q _ ((LtZ b2) (Refl (Lt a b) p)) (absurd LtS))))
  (let-match erased q (LtS a2 b2 q1) (absurd LtZ))
  (let ((erased sp)) (prove-subterm p1 p))
  (let ((erased ih)) (lt-unique a1 b1 (subterm sp) p1 q1))
  (match erased ih _ ((Refl t r) (Refl (Lt a b) p))))

(def-fns _ $ (erased double-fn :
    (erased (Nat) m) (erased (Nat) d1) (erased (Nat) d2)
    (subterm erased (Double m d1) p) (erased (Double m d2) q) -> (erased (Eq (Nat) d1 d2) e))
  (let-match erased p (DS a1 b1 pp) ((D0) (match erased q _ ((D0) (Refl (Nat) d1)) (absurd DS))))
  (let-match erased q (DS a2 b2 qq) (absurd D0))
  (let ((erased sp)) (prove-subterm pp p))
  (let ((erased ih)) (double-fn a1 b1 b2 (subterm sp) pp qq))
  (match erased ih _ ((Refl t r) (Refl (Nat) d1))))

(def-fns _ $ (erased pow2-fn : (erased (Nat) k) (erased (Nat) v) (erased (Nat) w)
    (subterm erased (Pow2 k v) p) (erased (Pow2 k w) q) -> (erased (Eq (Nat) v w) e))
  (let-match erased p (PS k1 v1 v2 p1 d1) ((P0) (match erased q _ ((P0) (Refl (Nat) (Succ (Zero)))) (absurd PS))))
  (match erased q _
    (absurd P0)
    ((PS k2 w1 w2 q1 d2)
      (match erased (pow2-fn k1 v1 w1 p1 q1) _ ((Refl t x) (double-fn v1 v2 w2 d1 d2))))))

(def-fns _ $ (erased double-inj :
    (erased (Nat) m1) (erased (Nat) m2) (erased (Nat) d)
    (subterm erased (Double m1 d) p) (erased (Double m2 d) q) -> (erased (Eq (Nat) m1 m2) e))
  (let-match erased p (DS a1 b1 pp) ((D0) (match erased q _ ((D0) (Refl (Nat) m1)) (absurd DS))))
  (let-match erased q (DS a2 b2 qq) (absurd D0))
  (let ((erased sp)) (prove-subterm pp p))
  (let ((erased ih)) (double-inj a1 a2 b1 (subterm sp) pp qq))
  (match erased ih _ ((Refl t r) (Refl (Nat) m1))))

(def-fns _ $ (erased absurd double-parity :
    (erased (Nat) a) (erased (Nat) b) (erased (Nat) e)
    (subterm erased (Double a (Succ e)) p) (erased (Double b e) q) -> (erased (False) f))
  (let-match erased p (DS a1 b1 pp))
  (let-match erased q (DS a2 b2 qq))
  (let ((erased sp)) (prove-subterm pp p))
  (double-parity a1 a2 b2 (subterm sp) pp qq))

(def-fns _ $ (erased numeral-zero :
    (erased (Nat) n) (erased (Numeral (BZ) n) v) -> (erased (Eq (Nat) n (Zero)) e))
  (match erased v _
    ((NZ) (Refl (Nat) n))
    (absurd N1)
    (absurd N2)))

(def-fns _ $ (erased numeral-fn :
    (erased (Bin) b) (erased (Nat) m1) (erased (Nat) m2)
    (subterm erased (Numeral b m1) v1) (erased (Numeral b m2) v2) -> (erased (Eq (Nat) m1 m2) e))
  (match erased v1 _
    ((NZ) (match erased v2 _ ((NZ) (Refl (Nat) m1)) (absurd N1) (absurd N2)))
    ((N1 c1 x1 d1 w1 dd1)
      (let-match erased v2 (N1 c2 x2 d2 w2 dd2) (absurd NZ) (absurd N2))
      (let ((erased sp)) (prove-subterm w1 v1))
      (let ((erased ih)) (numeral-fn c1 x1 x2 (subterm sp) w1 w2))
      (match erased ih _
        ((Refl t r)
          (let ((erased ed)) (double-fn x1 d1 d2 dd1 dd2))
          (match erased ed _ ((Refl t2 r2) (Refl (Nat) m1))))))
    ((N2 c1 x1 d1 w1 dd1)
      (let-match erased v2 (N2 c2 x2 d2 w2 dd2) (absurd NZ) (absurd N1))
      (let ((erased sp)) (prove-subterm w1 v1))
      (let ((erased ih)) (numeral-fn c1 x1 x2 (subterm sp) w1 w2))
      (match erased ih _
        ((Refl t r)
          (let ((erased ed)) (double-fn x1 d1 d2 dd1 dd2))
          (match erased ed _ ((Refl t2 r2) (Refl (Nat) m1))))))))

(def-fns _ $ (erased numeral-inj :
    (erased (Bin) b1) (erased (Bin) b2) (erased (Nat) n)
    (subterm erased (Numeral b1 n) v1) (erased (Numeral b2 n) v2) -> (erased (Eq (Bin) b1 b2) e))
  (match erased v1 _
    ((NZ) (match erased v2 _ ((NZ) (Refl (Bin) b1)) (absurd N1) (absurd N2)))
    ((N1 c1 m1 d1 w1 dd1)
      (let-match erased v2 (N1 c2 m2 d2 w2 dd2) (absurd NZ) (absurd (N2 c2 m2 d2 w2 dd2) (double-parity m1 m2 d2 dd1 dd2)))
      (let ((erased em)) (double-inj m1 m2 d1 dd1 dd2))
      (match erased em _
        ((Refl t r)
          (let ((erased sp)) (prove-subterm w1 v1))
          (let ((erased ih)) (numeral-inj c1 c2 m1 (subterm sp) w1 w2))
          (match erased ih _ ((Refl t2 r2) (Refl (Bin) b1))))))
    ((N2 c1 m1 d1 w1 dd1)
      (let-match erased v2 (N2 c2 m2 d2 w2 dd2) (absurd NZ) (absurd (N1 c2 m2 d2 w2 dd2) (double-parity m2 m1 d1 dd2 dd1)))
      (let ((erased em)) (double-inj m1 m2 d1 dd1 dd2))
      (match erased em _
        ((Refl t r)
          (let ((erased sp)) (prove-subterm w1 v1))
          (let ((erased ih)) (numeral-inj c1 c2 m1 (subterm sp) w1 w2))
          (match erased ih _ ((Refl t2 r2) (Refl (Bin) b1))))))))

(def-adts
  ((BinSucc : ((Bin) b) ((Bin) c) -> Type)
    enum
    (many BSZ : -> (BinSucc (BZ) (B1 (BZ))))
    (many BS1 : (erased (Bin) b) -> (BinSucc (B1 b) (B2 b)))
    (many BS2 : (erased (Bin) b) (erased (Bin) c) (erased (BinSucc b c) s) -> (BinSucc (B2 b) (B1 c)))))

(def-fns _ $ (erased numeral-succ :
    (erased (Bin) b) (erased (Bin) c) (erased (Nat) m) (erased (Nat) n)
    (subterm erased (BinSucc b c) s)
    (erased (Numeral b m) v) (erased (Numeral c n) w) -> (erased (Eq (Nat) n (Succ m)) e))
  (match erased s _
    ((BSZ)
      (let-match erased v (NZ) (absurd N1) (absurd N2))
      (let-match erased w (N1 c1 x1 d1 w1 dd1) (absurd NZ) (absurd N2))
      (match erased w1 _
        ((NZ) (match erased dd1 _ ((D0) (Refl (Nat) n)) (absurd DS)))
        (absurd N1)
        (absurd N2)))
    ((BS1 b0)
      (let-match erased v (N1 c1 x1 d1 w1 dd1) (absurd NZ) (absurd N2))
      (let-match erased w (N2 c2 x2 d2 w2 dd2) (absurd NZ) (absurd N1))
      (let ((erased ex)) (numeral-fn c1 x1 x2 w1 w2))
      (match erased ex _
        ((Refl t r)
          (let ((erased ed)) (double-fn x1 d1 d2 dd1 dd2))
          (match erased ed _ ((Refl t2 r2) (Refl (Nat) n))))))
    ((BS2 b0 c0 s0)
      (let-match erased v (N2 c1 x1 d1 w1 dd1) (absurd NZ) (absurd N1))
      (let-match erased w (N1 c2 x2 d2 w2 dd2) (absurd NZ) (absurd N2))
      (let ((erased sp)) (prove-subterm s0 s))
      (let ((erased ih)) (numeral-succ b0 c0 x1 x2 (subterm sp) s0 w1 w2))
      (match erased ih _
        ((Refl t r)
          (let-match erased dd2 (DS a2 bb ddx) (absurd D0))
          (let ((erased ed)) (double-fn x1 d1 bb dd1 ddx))
          (match erased ed _ ((Refl t2 r2) (Refl (Nat) n))))))))

(def-adts $ (Char : -> Type)
  enum newtype
  (many MkChar : (many (U8) u) -> (Char)))

(def-adts
  ((CharLt : ((Char) a) ((Char) b) -> Type)
    enum
    (many MkCharLt : (erased (Nat) m) (erased (Nat) n)
                     (erased (Lt m u8-modulus) pm) (erased (Lt n u8-modulus) pn)
                     (erased (Lt m n) p) -> (CharLt (MkChar (MkU8 m pm)) (MkChar (MkU8 n pn))))))

(def-lvl char-lvl)

; A Char is its code at runtime, so this is u62-cmp: the arguments coerce down through both newtypes and
; the result back up, the Coercible for it built by an erased match that leaves no code behind.
(def-fns char-lvl $ (many char-cmp : (many (Char) a) (many (Char) b) ->
    (many (Cmp (Char) CharLt a b) c))
  (let-match erased a (MkChar ua))
  (let-match erased ua (MkU8 ma pa))
  (let-match erased b (MkChar ub))
  (let-match erased ub (MkU8 nb pb))
  (let ((many ka)) (coerce a (coercible-trans (coercible-sym (coercible-wrap (Shared) MkChar ua))
                                            (coercible-sym (coercible-wrap (Shared) MkU8 ma pa)))))
  (let ((many kb)) (coerce b (coercible-trans (coercible-sym (coercible-wrap (Shared) MkChar ub))
                                            (coercible-sym (coercible-wrap (Shared) MkU8 nb pb)))))
  (let ((many r)) (delegate (u62-cmp ka kb (lt-trans _ _ _ pa u8-below-u62) (lt-trans _ _ _ pb u8-below-u62))))
  (let ((erased c2) (erased cr))
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

(def-adts $ (String : -> Type)
  enum extern
  (many SNil : -> (String))
  (many SCons : (many (Char) c) (many (String) rest) -> (String)))

;! warn SCons copies the whole string, O(n); build a `Rope` and `flatten` it once

(def-adts
  ((Append : ((String) a) ((String) b) ((String) c) -> Type)
    enum
    (many AppNil : (erased (String) b) -> (Append (SNil) b b))
    (many AppCons : (erased (Char) ch) (erased (String) a) (erased (String) b) (erased (String) c) (erased (Append a b c) q)
       -> (Append (SCons ch a) b (SCons ch c)))))

(def-fns _ $ (many extern append : (subterm many (String) a) (many (String) b) -> (many (String) c) (erased (Append a b c) p))
  (let-match many a (SCons ch rest) ((SNil) (values b (AppNil b))))
  (let ((many c) (erased q)) (notail $ append rest b))
  (values (SCons ch c) (AppCons ch rest b c q)))

(def-lvl str-lvl)

(def-fns str-lvl $ (many extern trim : (many (String) s) -> (many s is t))
  s)

(def-fns str-lvl $ (many str-append : (many (String) a) (many (String) b) -> (many (String) c))
  (let ((many c) (erased p)) (delegate (append a b)))
  c)

(def-adts
  ((StrLt : ((String) a) ((String) b) -> Type)
    enum
    (many SLtNil : (erased (Char) d) (erased (String) t) -> (StrLt (SNil) (SCons d t)))
    (many SLtHead : (erased (Char) c) (erased (Char) d) (erased (String) s) (erased (String) t) (erased (CharLt c d) p) -> (StrLt (SCons c s) (SCons d t)))
    (many SLtTail : (erased (Char) c) (erased (String) s) (erased (String) t) (erased (StrLt s t) p) -> (StrLt (SCons c s) (SCons c t)))))

(def-fns _ $ (many extern str-cmp : (subterm many (String) a) (many (String) b) -> (many (Cmp (String) StrLt a b) r))
  (let-match many a (SCons c s) ((SNil) (match many b _ ((SNil) (CEq _ _ a)) ((SCons d t) (CLt _ _ a b $ SLtNil d t)))))
  (let-match many b (SCons d t) ((SNil) (CGt _ _ a b $ SLtNil c s)))
  (let-match many (char-cmp c d) (CEq ct cr cx)
    ((CLt ct cr cx cy p) (CLt _ _ a b $ SLtHead c d s t p))
    ((CGt ct cr cx cy p) (CGt _ _ a b $ SLtHead d c t s p)))
  (match many (notail $ str-cmp s t) _
    ((CLt st sr sx sy q) (CLt _ _ a b $ SLtTail c s t q))
    ((CEq st sr sx) (CEq _ _ a))
    ((CGt st sr sx sy q) (CGt _ _ a b $ SLtTail c t s q))))

(def-adts
  ((StrLength : ((String) s) ((Nat) n) -> Type)
    enum
    (many SLenNil : -> (StrLength (SNil) (Zero)))
    (many SLenCons : (erased (Char) c) (erased (String) s) (erased (Nat) n) (erased (StrLength s n) p) -> (StrLength (SCons c s) (Succ n)))))

(def-fns _ $ (many extern str-length : (subterm many (String) s) -> (many (Nat) n) (erased (StrLength s n) p))
  (let-match many s (SCons c rest) ((SNil) (values (Zero) (SLenNil))))
  (let ((many n) (erased p)) (notail $ str-length rest))
  (values (Succ n) (SLenCons c rest n p)))

(def-fns _ $ (many extern str-split : (many (String) s) (subterm many (Nat) k) (erased (Nat) len) (erased (StrLength s len) l) (erased (Lt k (Succ len)) le) ->
    (many (String) a) (many (String) b) (erased (Append a b s) p) (erased (StrLength a k) la))
  (let-match many k (Succ k1) ((Zero) (values (SNil) s (AppNil s) (SLenNil))))
  (let-match many s (SCons c rest) (absurd (SNil) (let-match erased l (SLenNil)) (let-match erased le (LtS x y q)) q))
  (match erased l _
    ((SLenCons c0 s0 len1 l1)
      (match erased le _
        ((LtS x y q)
          (let ((many a1) (many b) (erased p) (erased la1)) (notail $ str-split rest k1 len1 l1 q))
          (values (SCons c a1) b (AppCons c a1 b rest p) (SLenCons c a1 k1 la1)))))))

(def-adts $ (Rope : -> Type)
  enum
  (many REmpty : -> (Rope))
  (many RStr : (many (String) s) -> (Rope))
  (many RCat : (many (Rope) a) (many (Rope) b) -> (Rope))
  (many RChar : (many (Char) c) -> (Rope)))

(def-adts
  ((Flat : ((Rope) r) ((String) s) -> Type)
    enum
    (many FlatEmpty : -> (Flat (REmpty) (SNil)))
    (many FlatStr : (erased (String) s) -> (Flat (RStr s) s))
    (many FlatCat : (erased (Rope) a) (erased (Rope) b) (erased (String) s1) (erased (String) s2) (erased (String) s)
                    (erased (Flat a s1) p) (erased (Flat b s2) q) (erased (Append s1 s2 s) ap) -> (Flat (RCat a b) s))
    (many FlatChar : (erased (Char) c) -> (Flat (RChar c) (SCons c (SNil))))))

(def-fns _ $ (many extern flatten : (subterm many (Rope) r) -> (many (String) s) (erased (Flat r s) p))
  (let-match many r (RCat a b)
    ((REmpty) (values (SNil) (FlatEmpty)))
    ((RStr s) (values s (FlatStr s)))
    ((RChar c) (values (SCons c (SNil)) (FlatChar c))))
  (let ((many s1) (erased p)) (notail $ flatten a))
  (let ((many s2) (erased q)) (notail $ flatten b))
  (let ((many s) (erased ap)) (append s1 s2))
  (values s (FlatCat a b s1 s2 s p q ap)))

(let ((many ten)) (Succ (Succ eight)))
(let ((many ten-dec)) (lt-dec (Zero) ten))
(comptime-match many ten-dec (Yes tda tdb ten-positive))
(let ((many ten-dec2)) (lt-dec (Succ (Zero)) ten))
(comptime-match many ten-dec2 (Yes tea teb ten-above-one))
(let ((many forty-eight)) (nat-add (nat-mul (Succ (Succ (Succ (Succ (Zero))))) ten) eight))

(def-fns _ $ (many digit-char : (many (Nat) d) -> (many (Char) c))
  (let ((many code)) (nat-add forty-eight d))
  (match many (lt-dec code u8-modulus) _
    ((Yes a b p) (MkChar $ MkU8 code p))
    ((No a b q) (MkChar $ MkU8 (Zero) u8-modulus-pos))))

(def-fns _ $ (many nat-digits : (subterm many (Nat) n) (many (Rope) acc) -> (many (Rope) r))
  (let-match many n (Succ n1) ((Zero) acc))
  (let ((many q) (many d) (erased m) (erased mm) (erased a) (erased p)) (divmod n ten ten-positive))
  (let ((erased lt)) (divmod-lt n1 ten q d m mm a ten-above-one))
  (tail $ nat-digits (subterm (lt-subterm q n lt)) q $ RCat (RChar $ digit-char d) acc))

(def-fns _ $ (many extern nat-str : (subterm many (Nat) n) -> (many (String) s))
  (let-match many n (Succ n1) ((Zero) (SCons (digit-char (Zero)) (SNil))))
  (let ((many s) (erased p)) (flatten $ nat-digits n $ REmpty))
  s)

(def-adts $ (Unit : -> Type)
  enum
  (many MkUnit : -> (Unit)))

(def-adts $ (Bool : -> Type)
  enum
  (many BTrue : -> (Bool))
  (many BFalse : -> (Bool)))

(def-adts
  ((Maybe : (Type A) -> Type)
    enum
    (many None : (erased Type A) -> (Maybe A))
    (many Some : (erased Type A) (many A a) -> (Maybe A))))

(def-adts
  ((Result : (Type A) -> Type)
    enum
    (many Ok : (erased Type A) (many A a) -> (Result A))
    (many Fail : (erased Type A) (many (String) message) -> (Result A))))

(def-adts
  ((List : (Type A) -> Type)
    enum
    (many Nil : (erased Type A) -> (List A))
    (many Cons : (erased Type A) (many A head) (many (List A) rest) -> (List A))))

(def-adts
  ((Pair : (Type A) (Type B) -> Type)
    enum
    (many MkPair : (erased Type A) (erased Type B) (many A first) (many B second) -> (Pair A B))))

(def-adts $ (EntryKind : -> Type)
  enum
  (many IsFile : -> (EntryKind))
  (many IsDir : -> (EntryKind))
  (many IsOther : -> (EntryKind))
  (many Missing : -> (EntryKind)))

(def-adts $ (Change : -> Type)
  enum
  (many Changed : -> (Change))
  (many Unchanged : -> (Change)))

(def-lvl thunk-lvl)

(def-fns thunk-lvl $ (many thunk : (erased Type A) (erased (Level) L) (many A a) -> (many (Fn L -> (many A r)) k))
  (def-fns L $ (many held : -> (many A r)) a)
  held)

(def-fns thunk-lvl $ (many unique-thunk : (erased Type A) (erased (Level) L) (unique A a) -> (unique (UniqueFn L -> (unique A r)) k))
  (def-unique L $ (unique held : -> (unique A r)) a)
  held)

; A program's requests to the driver (ASSUMPTIONS.md): every entry but Exit carries a continuation the
; driver applies to the request's answer, so a step never recurses and the driver loops. A continuation is a
; UniqueFn and a request unique, so a continuation may own what it closes over and is applied once.
(def-adts
  ((IO : ((Level) L) -> Type)
    enum
    (many Exit : (erased (Level) L) (many (U8) code) -> (IO L))
    (many Step : (erased (Level) L) (unique (UniqueFn L -> (unique (IO L) next)) k) -> (IO L))
    (many WriteOut : (erased (Level) L) (many (String) text) (unique (UniqueFn L -> (unique (IO L) next)) k) -> (IO L))
    (many WriteErr : (erased (Level) L) (many (String) text) (unique (UniqueFn L -> (unique (IO L) next)) k) -> (IO L))
    (many ReadLine : (erased (Level) L) (unique (UniqueFn L (many (Maybe (String)) line) -> (unique (IO L) next)) k) -> (IO L))
    (many ReadFile : (erased (Level) L) (many (String) path) (unique (UniqueFn L (many (Result (String)) contents) -> (unique (IO L) next)) k) -> (IO L))
    (many WriteFile : (erased (Level) L) (many (String) path) (many (String) text) (unique (UniqueFn L (many (Result (Unit)) outcome) -> (unique (IO L) next)) k) -> (IO L))
    (many GetArgs : (erased (Level) L) (unique (UniqueFn L (many (List (String)) args) -> (unique (IO L) next)) k) -> (IO L))
    (many GetEnv : (erased (Level) L) (many (String) name) (unique (UniqueFn L (many (Maybe (String)) value) -> (unique (IO L) next)) k) -> (IO L))
    (many GetEnvs : (erased (Level) L) (unique (UniqueFn L (many (List (Pair (String) (String))) vars) -> (unique (IO L) next)) k) -> (IO L))
    (many AppendFile : (erased (Level) L) (many (String) path) (many (String) text) (unique (UniqueFn L (many (Result (Unit)) outcome) -> (unique (IO L) next)) k) -> (IO L))
    (many ReadRemaining : (erased (Level) L) (unique (UniqueFn L (many (String) rest) -> (unique (IO L) next)) k) -> (IO L))
    (many ListDir : (erased (Level) L) (many (String) path) (unique (UniqueFn L (many (Result (List (String))) entries) -> (unique (IO L) next)) k) -> (IO L))
    (many GetCwd : (erased (Level) L) (unique (UniqueFn L (many (String) path) -> (unique (IO L) next)) k) -> (IO L))
    (many Stat : (erased (Level) L) (many (String) path) (unique (UniqueFn L (many (Result (EntryKind)) kind) -> (unique (IO L) next)) k) -> (IO L))
    (many MkDir : (erased (Level) L) (many (String) path) (unique (UniqueFn L (many (Result (Change)) outcome) -> (unique (IO L) next)) k) -> (IO L))
    (many DeleteFile : (erased (Level) L) (many (String) path) (unique (UniqueFn L (many (Result (Change)) outcome) -> (unique (IO L) next)) k) -> (IO L))
    (many DeleteDir : (erased (Level) L) (many (String) path) (unique (UniqueFn L (many (Result (Change)) outcome) -> (unique (IO L) next)) k) -> (IO L))))

(def-adts $ (Array : (Type A) ((Nat) n) -> Type)
  enum extern
  (many ANil : (erased Type A) -> (Array A (Zero)))
  (many ACons : (erased Type A) (erased (Nat) n)
                (unique A head) (unique (Array A n) rest)
                -> (Array A (Succ n))))

;! warn ACons copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
;! warn Array copies the array's tail, O(n); read with `array-get` and `array-length`

(def-adts $ (MaybeUninit : (Type A) -> Type)
  union newtype
  (many Uninit : (erased Type A) -> (MaybeUninit A))
  (many Init : (erased Type A) (unique A value) -> (MaybeUninit A)))

(def-adts $ (Copy : (Type A) -> Type)
  enum newtype
  (many MkCopy : (erased Type A) (many A v) -> (Copy A)))

; A closed list: every enum whose constructors carry no non-erased field is immediate too in extracted
; code, which a form reading its Matchable could in principle prove in general.
(def-adts
  ((Immediate : (Type A) -> Type)
    enum
    (many ImmU62 : -> (Immediate (U62)))
    (many ImmU8 : -> (Immediate (U8)))
    (many ImmChar : -> (Immediate (Char)))
    (many ImmBool : -> (Immediate (Bool)))
    (many ImmCopy : (erased Type A) (erased (Immediate A) p) -> (Immediate (Copy A)))))

(def-adts
  ((ArrayIsList : (Type A) ((List A) xs) ((Nat) n) ((Array (Copy A) n) a) -> Type)
    enum
    (many AILNil : (erased Type A) -> (ArrayIsList A (Nil A) (Zero) (ANil (Copy A))))
    (many AILCons : (erased Type A) (erased A x) (erased (List A) xs) (erased (Nat) n)
                    (erased (Array (Copy A) n) a) (erased (ArrayIsList A xs n a) p)
                    -> (ArrayIsList A (Cons A x xs) (Succ n) (ACons (Copy A) n (MkCopy A x) a)))))

(def-adts
  ((ArrayRepeat : (Type A) ((Nat) n) (A x) ((Array (Copy A) n) a) -> Type)
    enum
    (many ARepNil : (erased Type A) (erased A x) -> (ArrayRepeat A (Zero) x (ANil (Copy A))))
    (many ARepCons : (erased Type A) (erased (Nat) n) (erased A x)
                   (erased (Array (Copy A) n) a) (erased (ArrayRepeat A n x a) p)
                   -> (ArrayRepeat A (Succ n) x (ACons (Copy A) n (MkCopy A x) a)))))

(def-adts
  ((AllUninit : (Type A) ((Nat) n) ((Array (MaybeUninit A) n) a) -> Type)
    enum
    (many AUNil : (erased Type A) -> (AllUninit A (Zero) (ANil (MaybeUninit A))))
    (many AUCons : (erased Type A) (erased (Nat) n) (erased (Array (MaybeUninit A) n) tl)
                   (erased (AllUninit A n tl) p)
                   -> (AllUninit A (Succ n) (ACons (MaybeUninit A) n (Uninit A) tl))))
  ((AllInit : (Type A) ((Nat) n) ((Array (MaybeUninit A) n) a) -> Type)
    enum
    (many AINil : (erased Type A) -> (AllInit A (Zero) (ANil (MaybeUninit A))))
    (many AICons : (erased Type A) (erased (Nat) n) (erased A x)
                   (erased (Array (MaybeUninit A) n) tl) (erased (AllInit A n tl) p)
                   -> (AllInit A (Succ n) (ACons (MaybeUninit A) n (Init A x) tl))))
  ((ANth : (Type A) ((Nat) n) ((Array A n) a) ((Nat) i) (A x) -> Type)
    enum
    (many NthZ : (erased Type A) (erased (Nat) n) (erased A x) (erased (Array A n) tl)
       -> (ANth A (Succ n) (ACons A n x tl) (Zero) x))
    (many NthS : (erased Type A) (erased (Nat) n) (erased A h) (erased (Array A n) tl)
                 (erased (Nat) i) (erased A x) (erased (ANth A n tl i x) p)
                 -> (ANth A (Succ n) (ACons A n h tl) (Succ i) x)))
  ((ASet : (Type A) ((Nat) n) ((Array A n) a) ((Nat) i) (A y) ((Array A n) r) -> Type)
    enum
    (many SetZ : (erased Type A) (erased (Nat) n) (erased A h) (erased A y) (erased (Array A n) tl)
       -> (ASet A (Succ n) (ACons A n h tl) (Zero) y (ACons A n y tl)))
    (many SetS : (erased Type A) (erased (Nat) n) (erased A h) (erased (Array A n) tl)
                 (erased (Nat) i) (erased A y) (erased (Array A n) tl2)
                 (erased (ASet A n tl i y tl2) p)
                 -> (ASet A (Succ n) (ACons A n h tl) (Succ i) y (ACons A n h tl2)))))

(def-fns _ $ (many extern array-new : (erased Type A) (subterm many (Nat) n) ->
    (unique (Array (MaybeUninit A) n) a) (erased (AllUninit A n a) p))
  (let-match many n (Succ n1) ((Zero) (values (ANil _) (AUNil _))))
  (let ((unique tl) (erased q)) (notail $ array-new A n1))
  (values (ACons _ _ (Uninit _) tl) (AUCons _ _ _ q)))

(def-fns _ $ (many extern array-swap : (erased Type A) (erased (Nat) n)
    (unique (Array A n) a) (subterm many (Nat) i) (unique A x)
    (erased A m) (erased (ANth A n a i m) nth) ->
    (unique m is old) (unique (Array A n) r at a)
    (erased (ASet A n a i x r) p))
  (let-match unique a (ACons _ _ hd tl u) (absurd (ANil _ _) nth))
  (match many i _
    ((Zero)
      (match erased nth _
        ((NthZ _ _ _ _)
          (values hd (u _ _ x (at) tl) (SetZ _ _ _ _ _)))
        (absurd NthS)))
    ((Succ i1)
      (let-match erased nth (NthS _ _ _ _ _ _ q) (absurd NthZ))
      (let ((unique old) (unique tl3) (erased p1)) (tail (array-swap _ _ tl i1 x _ q)))
      (values old (at (u _ _ hd tl3)) (SetS _ _ _ _ _ _ _ p1)))))

(def-fns _ $ (many extern array-pluck : (erased Type A) (erased (Nat) n)
    (unique (Array (MaybeUninit A) n) a) (many (Nat) i)
    (erased (MaybeUninit A) m) (erased (ANth (MaybeUninit A) n a i m) nth) ->
    (unique m is v) (unique (Array (MaybeUninit A) n) r at a)
    (erased (ASet (MaybeUninit A) n a i (Uninit A) r) p))
  (tail (array-swap _ _ a i (Uninit _) _ nth)))

(def-fns _ $ (many extern array-place : (erased Type A) (erased (Nat) n)
    (unique (Array A n) a) (many (Nat) i) (unique A x)
    (erased A m) (erased (ANth A n a i m) nth) ->
    (unique (Array A n) r at a) (erased (ASet A n a i x r) p))
  (let ((unique old) (unique r) (erased p)) (array-swap _ _ a i x _ nth))
  (values r p))

(def-fns _ $ (many extern array-get : (erased Type A) (erased (Nat) n)
    (unique (Array (Copy A) n) a) (subterm many (Nat) i)
    (erased A x) (erased (ANth (Copy A) n a i (MkCopy A x)) nth) ->
    (many x is v) (unique a is r at a))
  (let-match unique a (ACons _ _ hd tl u) (absurd (ANil _ _) nth))
  (match many i _
    ((Zero)
      (let-match erased nth (NthZ _ _ _ _) (absurd NthS))
      (let-match unique hd (MkCopy _ v))
      (values v (at (u _ _ (MkCopy _ v) tl))))
    ((Succ i1)
      (let-match erased nth (NthS _ _ _ _ _ _ q) (absurd NthZ))
      (let ((many v) (unique tl3)) (tail (array-get _ _ tl i1 _ q)))
      (values v (at (u _ _ hd tl3))))))

; TODO: add read-only functions over many arrays.

; The Immediate proof lets extraction skip OCaml's write barrier, measured ~4x faster.
(def-fns _ $ (many extern array-swap-imm : (erased Type A) (erased (Nat) n)
    (unique (Array A n) a) (many (Nat) i) (unique A x)
    (erased A m) (erased (ANth A n a i m) nth) (erased (Immediate A) imm) ->
    (unique m is old) (unique (Array A n) r at a)
    (erased (ASet A n a i x r) p))
  (tail (array-swap _ _ a i x _ nth)))

(def-fns _ $ (many extern array-place-imm : (erased Type A) (erased (Nat) n)
    (unique (Array A n) a) (many (Nat) i) (unique A x)
    (erased A m) (erased (ANth A n a i m) nth) (erased (Immediate A) imm) ->
    (unique (Array A n) r at a) (erased (ASet A n a i x r) p))
  (tail (array-place _ _ a i x _ nth)))

(def-fns _ $ (many extern array-length : (erased Type A) (erased (Nat) n)
    (subterm unique (Array A n) a) -> (many n is len) (unique a is r at a))
  (let-match unique a (ACons _ n1 hd tl u) ((ANil _ u) (values (Zero) (at (u _)))))
  (let ((many l1) (unique tl2)) (notail $ array-length _ _ tl))
  (values (Succ l1) (at (u _ _ hd tl2))))

(def-fns _ $ (many extern list-to-array : (erased Type A) (subterm many (List A) xs) ->
    (erased (Nat) n) (unique (Array (Copy A) n) a) (erased (ArrayIsList A xs n a) p))
  (let-match many xs (Cons _ hd tl) ((Nil _) (values (Zero) (ANil _) (AILNil _))))
  (let ((erased n1) (unique a1) (erased p1)) (notail $ list-to-array _ tl))
  (values (Succ n1) (ACons _ _ (MkCopy _ hd) a1) (AILCons _ _ _ _ _ p1)))

(def-fns _ $ (many extern array-make : (erased Type A) (subterm many (Nat) n) (many A x) ->
    (unique (Array (Copy A) n) a) (erased (ArrayRepeat A n x a) p))
  (let-match many n (Succ n1) ((Zero) (values (ANil _) (ARepNil _ _))))
  (let ((unique a1) (erased p1)) (notail $ array-make A n1 x))
  (values (ACons _ _ (MkCopy _ x) a1) (ARepCons _ _ _ _ p1)))

(def-fns _ $ (erased init-witness : (erased Type A) (erased (Nat) n)
    (erased (Array (MaybeUninit A) n) a) (subterm erased (AllInit A n a) all) ->
    (erased (Array A n) b)
    (erased (Coercible (Unique) (Array (MaybeUninit A) n) a (Unique) (Array A n) b) c))
  (match erased all _
    ((AINil _)
      (values (ANil _) (coercible-ctor _ ANil (MaybeUninit A) A)))
    ((AICons _ n1 x tl q)
      (let ((erased b1) (erased c1)) (init-witness _ _ tl q))
      (values (ACons _ _ x b1)
              (coercible-ctor _ ACons (MaybeUninit A) A n1 n1
                 (coercible-sym (coercible-wrap _ Init _ x))
                 c1)))))
