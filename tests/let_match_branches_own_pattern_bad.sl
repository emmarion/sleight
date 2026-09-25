; error: constructor `Full` has 2 branches
(def-adts $ (Opt : -> Type) enum
  (many Full : (many (Nat) v) -> (Opt))
  (many Empty : -> (Opt)))
(def-lvl X)
(def-fns X $ (many f : (many (Opt) o) -> (many (Nat) n))
  (let-match many o (Full v) ((Full w) w) ((Empty) 0))
  v)
0
