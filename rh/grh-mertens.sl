(def-adts $ (NoDivFrom : ((Nat) p) ((Nat) d) -> Type)
  enum
  (many NoDivEnd : (erased (Nat) p) -> (NoDivFrom p p))
  (many NoDivStep : (erased (Nat) p d r) (erased (Mod p d (Succ r)) m) (erased (NoDivFrom p (Succ d)) h)
     -> (NoDivFrom p d)))

(def-adts $ (Prime : ((Nat) p) -> Type)
  enum
  (many MkPrime : (erased (Nat) p) (erased (Lt (Succ (Zero)) p) l) (erased (NoDivFrom p (Succ (Succ (Zero)))) h)
     -> (Prime p)))

(def-adts $ (PrimeProd : ((Nat) lo) ((Nat) n) ((Nat) k) -> Type)
  enum
  (many PPOne : (erased (Nat) lo) -> (PrimeProd lo (Succ (Zero)) (Zero)))
  (many PPCons : (erased (Nat) lo p m n k) (erased (Prime p) hp) (erased (Lt lo p) l) (erased (PrimeProd p m k) h)
     (erased (Mul p m n) pm) -> (PrimeProd lo n (Succ k))))

(def-adts $ (Sign : -> Type)
  enum
  (many SPlus : -> (Sign))
  (many SMinus : -> (Sign))
  (many SZero : -> (Sign)))

(def-adts $ (ParitySign : ((Nat) k) ((Sign) s) -> Type)
  enum
  (many PSZ : -> (ParitySign (Zero) (SPlus)))
  (many PSPlus : (erased (Nat) k) (erased (ParitySign k (SMinus)) h) -> (ParitySign (Succ k) (SPlus)))
  (many PSMinus : (erased (Nat) k) (erased (ParitySign k (SPlus)) h) -> (ParitySign (Succ k) (SMinus))))

(def-adts $ (Moebius : ((Nat) n) ((Sign) s) -> Type)
  enum
  (many MuFree : (erased (Nat) n k) (erased (Sign) s) (erased (PrimeProd (Zero) n k) h) (erased (ParitySign k s) ps)
     -> (Moebius n s))
  (many MuSquare : (erased (Nat) n p pp c) (erased (Lt (Succ (Zero)) p) l) (erased (Mul p p pp) sq)
     (erased (Mul pp c n) m) -> (Moebius n (SZero))))

; MertensAP q a x pos neg: among 1..x with n mod q = a, pos have mu(n) = 1 and neg have mu(n) = -1.
(def-adts $ (MertensAP : ((Nat) q) ((Nat) a) ((Nat) x) ((Nat) pos) ((Nat) neg) -> Type)
  enum
  (many MZ : (erased (Nat) q a) -> (MertensAP q a (Zero) (Zero) (Zero)))
  (many MOff : (erased (Nat) q a x r pos neg) (erased (MertensAP q a x pos neg) h) (erased (Mod (Succ x) q r) m)
     (erased (Apart (Nat) Lt r a) d) -> (MertensAP q a (Succ x) pos neg))
  (many MNil : (erased (Nat) q a x pos neg) (erased (MertensAP q a x pos neg) h) (erased (Mod (Succ x) q a) m)
     (erased (Moebius (Succ x) (SZero)) mu) -> (MertensAP q a (Succ x) pos neg))
  (many MPlus : (erased (Nat) q a x pos neg) (erased (MertensAP q a x pos neg) h) (erased (Mod (Succ x) q a) m)
     (erased (Moebius (Succ x) (SPlus)) mu) -> (MertensAP q a (Succ x) (Succ pos) neg))
  (many MMinus : (erased (Nat) q a x pos neg) (erased (MertensAP q a x pos neg) h) (erased (Mod (Succ x) q a) m)
     (erased (Moebius (Succ x) (SMinus)) mu) -> (MertensAP q a (Succ x) pos (Succ neg))))

(def-adts $ (MertensBelow : ((Nat) q) ((Nat) a) ((Nat) m) ((Nat) c) ((Nat) x) -> Type)
  enum
  (many MkMertensBelow : (erased (Nat) q a m c x pos neg d m2 l xp r) (erased (MertensAP q a x pos neg) h)
     (erased (AbsDiff pos neg d) dd) (erased (Add m m m2) mm) (erased (Pow d m2 l) pl)
     (erased (Pow x (Succ (Succ m)) xp) px) (erased (Mul c xp r) cr) (erased (Lt l (Succ r)) le)
     -> (MertensBelow q a m c x)))

; L, M: levels of the outer function and of the bound it returns.
(def-adts $ (MertensAPBound : ((Nat) q) ((Nat) a) -> Type)
  enum
  (many MkMertensAPBound : (erased (Nat) q a) (erased (Level) L)
     (erased (Fn L (erased (Nat) m) -> (erased (Nat) c) (erased (Level) M)
                 (erased (Fn M (erased (Nat) x) -> (erased (MertensBelow q a (Succ m) c x) b)) bound)) f)
     -> (MertensAPBound q a)))

(def-adts $ (GRH : -> Type)
  enum
  (many MkGRH : (erased (Level) L)
     (erased (Fn L (erased (Nat) q a) (erased (Lt a (Succ q)) r) (erased (Gcd a (Succ q) (Succ (Zero))) g)
                -> (erased (MertensAPBound (Succ q) a) h)) f) -> (GRH)))

(def-adts $ (RHMertens : -> Type)
  enum
  (many MkRHMertens : (erased (MertensAPBound (Succ (Zero)) (Zero)) h) -> (RHMertens)))

(goal erased (GRH))
