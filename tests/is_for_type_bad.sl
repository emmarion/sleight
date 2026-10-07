; error: argument 1, `f`, of `use`: type mismatch: expected `(Fn L (erased Type A) -> (erased A r))`, got `(Fn L (erased Type A) -> (erased A is r))`
(def-lvl L)
(def-fns L $ (erased reflect : (erased Type A) -> (erased A is r)) A)
(def-fns _ $ (erased use : (erased (Fn L (erased Type A) -> (erased A r)) f) -> (erased (False) impossible))
  (f (False)))
(let ((erased (False) contradiction)) (use reflect))
(def-fns _ $ (many absurd explode : -> (many (Nat) n)) contradiction)
explode
