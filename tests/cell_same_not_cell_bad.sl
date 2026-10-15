; error: `cell-same` takes cells, and `xs` : `(List (Nat))` is not one
(def-fns _ $ (many f : (many (List (Nat)) xs) -> (many (Nat) r))
  (let ((many s)) (cell-same xs xs))
  0)
