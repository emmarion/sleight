; error: a match without a runtime discriminant can have only one real branch
(def-adts $ (Opt : -> Type) enum
  (many Full : (many (Nat) v) -> (Opt))
  (many Empty : -> (Opt)))
(def-lvl X)
(def-fns X $ (many f : (erased (Opt) o) -> (many (Nat) n))
  (let-match erased o (Full v) ((Empty) 0))
  1)
0
