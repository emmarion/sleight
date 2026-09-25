; error: must be a statement of a function, match branch or cell-match body
(def-adts $ (Opt : -> Type) enum
  (many Full : (many (Nat) v) -> (Opt))
  (many Empty : -> (Opt)))
(def-lvl X)
(def-fns X $ (many absurd f : (many (Opt) o) (erased (False) g) -> (many (Nat) n))
  (let-match many o (Full v) ((Empty) g))
  g)
0
