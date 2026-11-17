(def-fns _ $ (many call-bad : (many (Val) v) (many (Tm) b) (many (List $ Val) env) (many (List $ Frame) rest) ->
    (many (Out) o) (erased (Step (Rt v $ Cons (Frame) (KCall $ VClo b env) rest) o) p))
  (values (Go $ Ev b env rest) (SCall v b env rest)))
