; a call nested in an argument for an erased parameter or field is itself erased
(def-adts
  ((Add : ((Nat) a) ((Nat) b) ((Nat) c) -> Type)
    enum
    (many AddZ : (many (Nat) b) -> (Add (Zero) b b))
    (many AddS : (many (Nat) a) (many (Nat) b) (many (Nat) c) (erased (Add a b c) p) -> (Add (Succ a) b (Succ c)))))
(def-lvl L)
(def-fns L $ (erased addZR : (subterm many (Nat) n) -> (erased (Add n (Zero) n) p))
  (match erased n (((Add n (Zero) n) p))
    ((Zero) (AddZ (Zero)))
    ((Succ k)
      (let ((erased q)) (prove-subterm k n))
      (AddS k (Zero) k (addZR (subterm q) k)))))
(def-lvl M)
(def-fns M $ (many keep : (many (Nat) n) (erased (Add n (Zero) n) p) -> (many (Nat) r))
  n)
(def-adts
  ((Pair : -> Type)
    enum
    (many MkPair : (many (Nat) n) (erased (Add n (Zero) n) p) -> (Pair))))
(let ((many two)) (Succ (Succ (Zero))))
(let ((many k)) (keep two (addZR two)))
(MkPair k (addZR k))
