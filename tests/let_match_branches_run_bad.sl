; error: must be a statement of a function, match branch or cell-match body
(def-adts $ (Opt : -> Type) enum
  (many Full : (many (Nat) v) -> (Opt))
  (many Empty : -> (Opt)))
(def-lvl X)
(let ((many o)) (Full 1))
(let-match many o (Full v) ((Empty) 0))
v
