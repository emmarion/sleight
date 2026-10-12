; multiplicities (DESIGN.md sections 13 and 14): an erased proof built by an erased function
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
(let ((many two)) (Succ (Succ (Zero))))
(let ((erased pr)) (addZR two))
(keep two pr)
