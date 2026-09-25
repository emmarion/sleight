; error: branch `Full` is not refuted
(def-adts $ (Opt : -> Type) enum
  (many Full : (many (Nat) v) -> (Opt))
  (many Empty : -> (Opt)))
(let ((many o)) (Full 1))
(let-match many o (Full v) (absurd Full))
v
