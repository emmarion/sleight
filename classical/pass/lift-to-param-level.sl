(def-fns _ $ (erased lift : (erased Type P) (erased (Level) M) (erased (Level) N) (erased (Predates (Level) M N) mn)
    (erased (Fn M (erased P p) -> (erased (False) f)) r) ->
    (erased (Fn N (erased P p) -> (erased (False) f)) n))
  (def-fns N $ (erased n : (erased P p) -> (erased (False) f))
    (r (predates mn) p))
  n)
