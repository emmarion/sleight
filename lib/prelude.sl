; The source prelude (DESIGN.md section 41), elaborated ahead of every program. Its extern-marked
; definitions are the models the FFI's implementations in ffi.ml stand in for.

(def-adts $ Nat : -> Type
  enum extern
  (many Zero : -> (Nat))
  (many Succ : (many (Nat) pred) -> (Nat)))

(def-adts $ False : -> Type
  enum)

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
