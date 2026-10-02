; error: constructor `A3` has no branch and is not refuted, so this `let-match` needs a branch for it
(def-adts $ (Opt : -> Type) enum
  (many Full : (many (Nat) v) -> (Opt))
  (many Empty : -> (Opt)))
(def-lvl X)
(def-adts $ (Three : -> Type) enum (many A1 : -> (Three)) (many A2 : -> (Three)) (many A3 : -> (Three)))
(def-fns X $ (many f : (many (Three) t) -> (many (Nat) n))
  (let-match many t (A1) ((A2) 1))
  0)
0
