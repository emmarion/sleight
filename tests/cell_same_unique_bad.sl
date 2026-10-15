; error: `c`, declared `unique`, used at many without `share`
(def-fns _ $ (many f : -> (many (Nat) r))
  (let ((unique c)) (cell-alloc Cons))
  (let ((many s)) (cell-same c c))
  0)
