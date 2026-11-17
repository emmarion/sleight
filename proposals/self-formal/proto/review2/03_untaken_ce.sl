(def-fns _ $ (many t : -> (many (Bool) b)) (BTrue))
(match many (t) (((Nat) r))
  ((BTrue) 0)
  ((BFalse) (compile-error "untaken")))
