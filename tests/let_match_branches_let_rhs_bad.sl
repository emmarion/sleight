; error: must be a statement of a function, match branch or cell-match body
(def-adts $ (Opt : -> Type) enum
  (many Full : (many (Nat) v) -> (Opt))
  (many Empty : -> (Opt)))
(def-lvl X)
(def-fns X $ (many f : (many (Opt) o) -> (many (Nat) n))
  (let ((many w)) (let-match many o (Full v) (else (Zero))) v)
  w)
