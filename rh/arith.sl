(def-adts $ (Pow : ((Nat) b) ((Nat) e) ((Nat) r) -> Type)
  enum
  (many PowZ : (erased (Nat) b) -> (Pow b (Zero) (Succ (Zero))))
  (many PowS : (erased (Nat) b e r s) (erased (Pow b e r) p) (erased (Mul b r s) m) -> (Pow b (Succ e) s)))

(def-adts $ (AbsDiff : ((Nat) x) ((Nat) y) ((Nat) d) -> Type)
  enum
  (many AbsLe : (erased (Nat) x y d) (erased (Add x d y) a) -> (AbsDiff x y d))
  (many AbsGe : (erased (Nat) x y d) (erased (Add y d x) a) -> (AbsDiff x y d)))

(def-adts $ (Gcd : ((Nat) a) ((Nat) b) ((Nat) g) -> Type)
  enum
  (many GcdZ : (erased (Nat) a) -> (Gcd a (Zero) a))
  (many GcdS : (erased (Nat) a b r g) (erased (Mod a (Succ b) r) m) (erased (Gcd (Succ b) r g) h)
     -> (Gcd a (Succ b) g)))
