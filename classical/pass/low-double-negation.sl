(def-fns _ $ (many no-low-dneg : (erased Type A) (erased (Level) W) (erased (Level) N)
    (erased (Predates (Level) W N) wn)
    (erased (Fn W (erased (Fn N (erased A a) -> (erased (False) f)) n) -> (erased (False) f)) k) ->
    (erased (Level) Z) (many (Fn Z -> (many (False) f)) absurdity))
  (def-fns N $ (erased n : (erased A a) -> (erased (False) f))
    (k (predates wn) n))
  (def-fns _ $ (many absurd absurdity : -> (many (False) f))
    (k n))
  (values (level-of absurdity) absurdity))
