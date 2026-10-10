; prelude: none
; expect: (Succ $ Succ $ Succ $ Zero)
(def-adts $ (Nat : -> Type) enum extern (many Zero : -> (Nat)) (many Succ : (many (Nat) pred) -> (Nat)))
(def-fns _ $ (many extern add : (subterm many (Nat) a) (many (Nat) b) -> (many (Nat) c))
  (match many a _ ((Zero) b) ((Succ p) (Succ $ notail $ add p b))))
(add (Succ $ Zero) (Succ $ Succ $ Zero))
