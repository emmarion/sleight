(def-adts $ (GRHImpliesRH : -> Type)
  enum
  (many MkGRHImpliesRH : (erased (Level) K)
     (erased (Fn K (erased (GRH) g) -> (erased (Level) M) (erased (Fn M -> (erased (RHMertens) r)) rh)) imp)
     -> (GRHImpliesRH)))

(goal erased (GRHImpliesRH))

(def-fns _ $ (erased grh-rh : (erased (GRH) g) -> (erased (Level) M) (erased (Fn M -> (erased (RHMertens) r)) rh))
  (let-match erased g (MkGRH L f))
  (def-lvl M)
  (def-fns M $ (erased go : -> (erased (RHMertens) r))
    (MkRHMertens (f (Zero) (Zero) (LtZ (Zero))
      (GcdS (Zero) (Zero) (Zero) (Succ (Zero)) (ModLt (Zero) (Succ (Zero)) (LtZ (Zero))) (GcdZ (Succ (Zero)))))))
  (values M go))

(qed (MkGRHImpliesRH (level-of grh-rh) grh-rh))
