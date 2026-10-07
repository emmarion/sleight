; error: argument 1, `f`, of `use`: type mismatch: expected `(Fn L (erased Type A) -> (erased A is r))`, got `(Fn L (erased Type A) -> (erased A r))`
(def-lvl L)
(def-fns _ $ (erased use : (erased (Fn L (erased Type A) -> (erased A is r)) f) -> (erased Type t))
  (f (False)))
(def-fns _ $ (erased pass : (erased (Fn L (erased Type A) -> (erased A r)) g) -> (erased Type t))
  (use g))
