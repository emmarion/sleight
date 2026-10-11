; error: argument 5, `b`, of `gensym-unique`: type mismatch
(def-fns _ $ (erased bad : (erased (Nat) n) (erased (String) s) (erased (Gensym n s) g)
    (erased (Nat) m) (erased (String) t) (erased (Gensym m t) h) ->
    (erased (JMEq (Gensym n s) g (Gensym m t) h) e))
  (gensym-unique _ _ _ g h))
