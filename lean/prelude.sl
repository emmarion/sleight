; The prelude of the Lean prototype, elaborated ahead of every program unless --no-prelude is given.

(def-adts $ (Nat : -> Type)
  enum
  (many Zero : -> (Nat))
  (many Succ : (many (Nat) pred) -> (Nat)))

(def-adts $ (False : -> Type)
  enum)

(def-adts
  ((Eq : (Type A) (A x) (A y) -> Type)
    enum
    (many Refl : (erased Type A) (erased A x) -> (Eq A x x))))

(def-adts
  ((List : (Type A) -> Type)
    enum
    (many Nil : (erased Type A) -> (List A))
    (many Cons : (erased Type A) (many A head) (many (List A) rest) -> (List A))))

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
