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
  (Dec : ((Nat) a) ((Nat) b) -> Type
    enum
    (many Yes : (erased (Nat) a) (erased (Nat) b) (erased (Lt a b) p) -> (Dec a b))
    (many No : (erased (Nat) a) (erased (Nat) b) (erased (Lt b (Succ a)) q) -> (Dec a b))))

(def-lvl nat-lvl)

(def-fns nat-lvl $ many extern nat-add : (subterm many (Nat) a) (many (Nat) b) -> (many (Nat) c)
  (match many a _
    ((Zero) b)
    ((Succ k) (Succ (nat-add (subterm _) k b)))))

(def-fns nat-lvl $ many double : (subterm many (Nat) a) -> (many (Nat) b) (erased (Double a b) d)
  (match many a _
    ((Zero) (values (Zero) (D0)))
    ((Succ a1)
      (let (many b1) (erased d1) (double (subterm _) a1))
      (values (Succ (Succ b1)) (DS a1 b1 d1)))))

(def-fns nat-lvl $ erased double-pos : (erased (Nat) v) (erased (Nat) w) (erased (Lt (Zero) v) q) (erased (Double v w) d) ->
    (erased (Lt (Zero) w) r)
  (match erased q _
    ((LtZ b)
      (match erased d _
        (absurd D0)
        ((DS a b2 d1) (LtZ (Succ b2)))))
    (absurd LtS)))

(def-fns nat-lvl $ erased lt-pos : (erased (Nat) r) (erased (Nat) c) (erased (Lt r c) p) -> (erased (Lt (Zero) c) q)
  (match erased p _
    ((LtZ b) (LtZ b))
    ((LtS a b p1) (LtZ b))))

(def-fns nat-lvl $ many lt-dec : (subterm many (Nat) a) (many (Nat) b) -> (many (Dec a b) d)
  (match many a _
    ((Zero)
      (match many b _
        ((Zero) (No a b (LtZ (Zero))))
        ((Succ b1) (Yes a b (LtZ b1)))))
    ((Succ a1)
      (match many b _
        ((Zero) (No a b (LtZ (Succ a1))))
        ((Succ b1)
          (match many (lt-dec (subterm _) a1 b1) _
            ((Yes x y p) (Yes a b (LtS a1 b1 p)))
            ((No x y q) (No a b (LtS b1 (Succ a1) q)))))))))

(def-lvl pow-lvl)
(let (erased nat-pow) (prove-predates nat-lvl pow-lvl))

(def-fns pow-lvl $ many pow2 : (subterm many (Nat) k) -> (many (Nat) v) (erased (Pow2 k v) p) (erased (Lt (Zero) v) q)
  (match many k _
    ((Zero) (values (Succ (Zero)) (P0) (LtZ (Zero))))
    ((Succ k1)
      (let (many v) (erased p) (erased q) (pow2 (subterm _) k1))
      (let (many w) (erased d) (double (predates nat-pow) v))
      (values w (PS k1 v w p d) (double-pos (predates nat-pow) v w q d)))))

(def-fns pow-lvl $ many succ-mod : (many (Nat) r) (many (Nat) c) (erased (Lt r c) p) -> (many (Nat) s) (erased (Lt s c) q)
  (match many (lt-dec (predates nat-pow) (Succ r) c) _
    ((Yes x y p1) (values (Succ r) p1))
    ((No x y q1) (values (Zero) (lt-pos (predates nat-pow) r c p)))))

(def-lvl mod-lvl)
(let (erased pow-mod) (prove-predates pow-lvl mod-lvl))

(def-fns mod-lvl $ many mod-add : (many (Nat) r) (many (Nat) c) (erased (Lt r c) p) (subterm many (Nat) m) ->
    (many (Nat) s) (erased (Lt s c) q)
  (match many m _
    ((Zero) (values r p))
    ((Succ m1)
      (let (many r1) (erased p1) (succ-mod (predates pow-mod) r c p))
      (mod-add r1 c p1 (subterm _) m1))))

(let (many eight) (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))))))
(let (many u8-modulus) (erased u8-modulus-pow2) (erased u8-modulus-pos) (pow2 eight))

(def-adts $ U8 : -> Type
  enum extern
  (many MkU8 : (many (Nat) n) (erased (Lt n u8-modulus) p) -> (U8)))

(def-lvl u8-lvl)
(let (erased mod-u8) (prove-predates mod-lvl u8-lvl))

(def-fns u8-lvl $ many extern u8-add : (many (U8) a) (many (U8) b) -> (many (U8) c)
  (match many a _
    ((MkU8 n p)
      (match many b _
        ((MkU8 m q)
          (let (many r) (erased pr) (mod-add (predates mod-u8) n u8-modulus p m))
          (MkU8 r pr))))))

(def-fns u8-lvl $ many extern nat-to-u8 : (many (Nat) n) -> (many (U8) u)
  (let (many r) (erased pr) (mod-add (predates mod-u8) (Zero) u8-modulus u8-modulus-pos n))
  (MkU8 r pr))

(def-fns u8-lvl $ many extern u8-to-nat : (many (U8) u) -> (many (Nat) n)
  (match many u _
    ((MkU8 n p) n)))

(def-adts $ Bin : -> Type
  enum extern
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

(def-lvl bin-lvl)
(let (erased nat-bin) (prove-predates nat-lvl bin-lvl))

(def-fns bin-lvl $ many extern bin-to-nat : (subterm many (Bin) b) -> (many (Nat) n) (erased (Numeral b n) v)
  (match many b _
    ((BZ) (values (Zero) (NZ)))
    ((B1 b1)
      (let (many m) (erased v1) (bin-to-nat (subterm _) b1))
      (let (many d) (erased dd) (double (predates nat-bin) m))
      (values (Succ d) (N1 b1 m d v1 dd)))
    ((B2 b1)
      (let (many m) (erased v1) (bin-to-nat (subterm _) b1))
      (let (many d) (erased dd) (double (predates nat-bin) m))
      (values (Succ (Succ d)) (N2 b1 m d v1 dd)))))

; Reasoning about a numeral through its spelling rather than its opaque Nat: the relations below are
; functional and injective, and the spelling's successor is structural (DESIGN.md section 16's let-match
; carries their conclusions outward).

(def-lvl dbl-lvl)

(def-fns dbl-lvl $ erased double-fn :
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

(def-fns dbl-lvl $ erased double-inj :
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

(def-fns dbl-lvl $ erased double-parity :
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

(def-lvl num-lvl)
(let (erased dbl-num) (prove-predates dbl-lvl num-lvl))

(def-fns num-lvl $ erased numeral-zero :
    (erased (Nat) n) (erased (Numeral (BZ) n) v) -> (erased (Eq (Nat) n (Zero)) e)
  (match erased v _
    ((NZ) (Refl (Nat) n))
    (absurd N1)
    (absurd N2)))

(def-fns num-lvl $ erased numeral-fn :
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
              (let (erased ed) (double-fn (predates dbl-num) x1 d1 d2 dd1 dd2))
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
              (let (erased ed) (double-fn (predates dbl-num) x1 d1 d2 dd1 dd2))
              (match erased ed _ ((Refl t2 r2) (Refl (Nat) m1))))))))))

(def-fns num-lvl $ erased numeral-inj :
    (erased (Bin) b1) (erased (Bin) b2) (erased (Nat) n)
    (subterm erased (Numeral b1 n) v1) (erased (Numeral b2 n) v2) -> (erased (Eq (Bin) b1 b2) e)
  (match erased v1 _
    ((NZ) (match erased v2 _ ((NZ) (Refl (Bin) b1)) (absurd N1) (absurd N2)))
    ((N1 c1 m1 d1 w1 dd1)
      (match erased v2 _
        (absurd NZ)
        ((N1 c2 m2 d2 w2 dd2)
          (let (erased em) (double-inj (predates dbl-num) m1 m2 d1 dd1 dd2))
          (match erased em _
            ((Refl t r)
              (let (erased sp) (prove-subterm w1 v1))
              (let (erased ih) (numeral-inj c1 c2 m1 (subterm sp) w1 w2))
              (match erased ih _ ((Refl t2 r2) (Refl (Bin) b1))))))
        (absurd (N2 c2 m2 d2 w2 dd2) (double-parity (predates dbl-num) m1 m2 d2 dd1 dd2))))
    ((N2 c1 m1 d1 w1 dd1)
      (match erased v2 _
        (absurd NZ)
        (absurd (N1 c2 m2 d2 w2 dd2) (double-parity (predates dbl-num) m2 m1 d1 dd2 dd1))
        ((N2 c2 m2 d2 w2 dd2)
          (let (erased em) (double-inj (predates dbl-num) m1 m2 d1 dd1 dd2))
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

(def-lvl succ-lvl)
(let (erased dbl-succ) (prove-predates dbl-lvl succ-lvl))
(let (erased num-succ) (prove-predates num-lvl succ-lvl))

(def-fns succ-lvl $ erased numeral-succ :
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
              (let (erased ex) (numeral-fn (predates num-succ) c1 x1 x2 w1 w2))
              (match erased ex _
                ((Refl t r)
                  (let (erased ed) (double-fn (predates dbl-succ) x1 d1 d2 dd1 dd2))
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
                      (let (erased ed) (double-fn (predates dbl-succ) x1 d1 bb dd1 ddx))
                      (match erased ed _ ((Refl t2 r2) (Refl (Nat) n))))))))
            (absurd N2)))))))

(def-adts $ Char : -> Type
  enum newtype
  (many MkChar : (many (U8) u) -> (Char)))

(def-adts $ String : -> Type
  enum extern
  (many SNil : -> (String))
  (many SCons : (many (Char) c) (many (String) rest) -> (String)))

(def-lvl str-lvl)

(def-fns str-lvl $ many extern trim : (many (String) s) -> (many (String) t)
  s)

(def-fns str-lvl $ many str-append : (subterm many (String) a) (many (String) b) -> (many (String) c)
  (match many a _
    ((SNil) b)
    ((SCons ch rest) (SCons ch (str-append (subterm _) rest b)))))

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

; A program's requests to the driver (ASSUMPTIONS.md): each carries what comes next, as a value or as a
; continuation the driver applies to the request's answer, so a step never recurses and the driver loops.
(def-adts
  (IO : ((Level) L) -> Type
    enum
    (many Exit : (erased (Level) L) (many (U8) code) -> (IO L))
    (many WriteOut : (erased (Level) L) (many (String) text) (many (IO L) next) -> (IO L))
    (many WriteErr : (erased (Level) L) (many (String) text) (many (IO L) next) -> (IO L))
    (many ReadLine : (erased (Level) L) (many (Fn L (many (Maybe (String)) line) -> (many (IO L) next)) k) -> (IO L))
    (many ReadFile : (erased (Level) L) (many (String) path) (many (Fn L (many (Result (String)) contents) -> (many (IO L) next)) k) -> (IO L))
    (many WriteFile : (erased (Level) L) (many (String) path) (many (String) text) (many (Fn L (many (Result (Unit)) outcome) -> (many (IO L) next)) k) -> (IO L))
    (many GetArgs : (erased (Level) L) (many (Fn L (many (List (String)) args) -> (many (IO L) next)) k) -> (IO L))))
