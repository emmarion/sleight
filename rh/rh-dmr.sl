(def-adts $ (LcmUpTo : ((Nat) n) ((Nat) m) -> Type)
  enum
  (many LcmZ : -> (LcmUpTo (Zero) (Succ (Zero))))
  (many LcmS : (erased (Nat) n m g t m2) (erased (LcmUpTo n m) h) (erased (Gcd m (Succ n) g) gh)
     (erased (Mul m (Succ n) t) mt) (erased (Mul g m2 t) gt) -> (LcmUpTo (Succ n) m2)))

(def-adts $ (Delta : ((Nat) x) ((Nat) d) -> Type)
  enum
  (many DeltaZ : -> (Delta (Zero) (Succ (Zero))))
  (many DeltaS : (erased (Nat) x d m d2) (erased (Delta x d) h) (erased (LcmUpTo x m) l) (erased (Mul d m d2) p)
     -> (Delta (Succ x) d2)))

(def-adts $ (Harmonic : ((Nat) n) ((Nat) a) ((Nat) b) -> Type)
  enum
  (many HarmZ : -> (Harmonic (Zero) (Zero) (Succ (Zero))))
  (many HarmS : (erased (Nat) n a b t a2 b2) (erased (Harmonic n a b) h) (erased (Mul a (Succ n) t) ma)
     (erased (Add t b a2) ad) (erased (Mul b (Succ n) b2) mb) -> (Harmonic (Succ n) a2 b2)))

(def-adts $ (DmrBelow : ((Nat) n) -> Type)
  enum
  (many MkDmrBelow : (erased (Nat) n d a b a2 n2 n2b e e2 n3 b2 t r) (erased (Delta n d) hd) (erased (Harmonic d a b) hh)
     (erased (Add a a a2) da) (erased (Mul n n n2) sq) (erased (Mul n2 b n2b) sqb) (erased (AbsDiff a2 n2b e) de)
     (erased (Mul e e e2) se) (erased (Mul n2 n n3) cu) (erased (Mul b b b2) sb) (erased (Mul 144 n3 t) k) (erased (Mul t b2 r) kr)
     (erased (Lt e2 r) lt) -> (DmrBelow n)))

(def-adts $ (RH : -> Type)
  enum
  (many MkRH : (erased (Level) L)
     (erased (Fn L (erased (Nat) n) -> (erased (DmrBelow (Succ n)) p)) f) -> (RH)))

(goal erased (RH))
