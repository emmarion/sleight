(def-adts $ (GRHImpliesRH : -> Type)
  enum
  (many MkGRHImpliesRH : (erased (Level) K) (erased (Fn K (erased (GRH) g) -> (erased (RHMertens) r)) imp)
     -> (GRHImpliesRH)))

(goal erased (GRHImpliesRH))

(def-fns _ $ (erased grh-rh : (erased (GRH) g) -> (erased (RHMertens) r))
  (let-match erased g (MkGRH L C pick bound))
  (def-adts $ (C1 : ((Nat) m) ((Nat) c) -> Type)
    enum
    (many MkC1 : (erased (Nat) m c) (erased (C (Zero) (Zero) m c) h) -> (C1 m c)))
  (let ((erased lt)) (LtZ (Zero)))
  (let ((erased gcd)) (GcdS (Zero) (Zero) (Zero) (Succ (Zero)) (ModLt (Zero) (Succ (Zero)) lt) (GcdZ (Succ (Zero)))))
  (def-fns _
    ((erased pick1 : (erased (Nat) m) -> (erased (Nat) c) (erased (C1 m c) h))
      (let ((erased c) (erased h)) (pick (Zero) (Zero) m lt gcd))
      (values c (MkC1 m c h)))
    ((erased bound1 : (erased (Nat) m c x) (erased (C1 m c) h1)
        -> (erased (MertensBelow (Succ (Zero)) (Zero) (Succ m) c x) b))
      (let-match erased h1 (MkC1 _ _ h))
      (bound (Zero) (Zero) m c x lt gcd h)))
  (MkRHMertens (level-of pick1) C1 pick1 bound1))

(qed (MkGRHImpliesRH (level-of grh-rh) grh-rh))
