(def-adts $ (FuelUnobservable : -> Type)
  enum
  (many MkFuelUnobservable : (erased (Level) L)
     (erased (Fn L (erased (Env) env) (erased (Core) c) (erased (List (Val)) vs) (erased (Eval env c vs) d) -> (erased (FuelBound env c vs) b)) thm)
     -> (FuelUnobservable)))

(goal erased (FuelUnobservable))
