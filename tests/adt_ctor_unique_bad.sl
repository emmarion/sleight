; error: a constructor declaration cannot be `unique`
(def-adts $ (U : -> Type)
  enum
  (unique MkU : -> (U)))
(Zero)
