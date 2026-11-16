(def-adts $ (EvalTotal : -> Type)
  enum
  (many MkEvalTotal : (erased (Level) L)
     (many (Fn L (many (Env) env) (many (Core) c) (erased (List (Val)) vs) (subterm erased (Eval env c vs) d) -> (many vs is r)) f)
     -> (EvalTotal)))

(goal many (EvalTotal))
