; Refused (round-6 review of 06): Nth's signature is dependent, so it does not fit a three-input wrapper.
(def-adts $ (Out3 : (Type T1) (T1 a1) (Type T2) (T2 a2) (Type T3) (T3 a3) (Type W)
    ((TyCtor (T1 b1) (T2 b2) (T3 b3) (W w) -> Type) R) -> Type)
  enum
  (many Found3 : (erased Type T1) (erased T1 a1) (erased Type T2) (erased T2 a2) (erased Type T3) (erased T3 a3) (erased Type W)
     (erased (TyCtor (T1 b1) (T2 b2) (T3 b3) (W w) -> Type) R) (many W x) (erased (R a1 a2 a3 x) p)
     -> (Out3 T1 a1 T2 a2 T3 a3 W R)))
(def-fns _ $ (many g : (many (Nat) b) -> (many (Out3 Type (Nat) (List (Nat)) (Cons (Nat) b (Nil (Nat))) (Nat) (Zero) (Nat) Nth) r))
  (Found3 _ _ _ _ _ _ _ _ b (NthHere _ b (Nil _))))
