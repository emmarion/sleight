(def-fns _ $ (erased lower : (erased (Level) K)
    (erased (Fn K (erased (Level) M) (erased (Level) N) (erased (Predates (Level) M N) mn)
         (erased Type P) (erased (IsProp M P) h) ->
         (erased (Or P (Fn N (erased P p) -> (erased (False) f))) d)) lem)
    (erased (Level) M) (erased (Level) N) (erased (Predates (Level) M N) mn)
    (erased Type P) (erased (IsProp M P) h)
    (erased (Level) H) (erased (Fn H (erased P p) -> (erased (False) f)) n) ->
    (erased (Level) Z) (erased (Fn Z -> (erased (Fn N (erased P p) -> (erased (False) f)) m)) t))
  (def-fns _ $ (erased go : -> (erased (Fn N (erased P p) -> (erased (False) f)) m))
    (match erased (lem M N mn P h) _
      (absurd (Inl _ _ p) (n p))
      ((Inr _ _ m) m)))
  (values (level-of go) go))
