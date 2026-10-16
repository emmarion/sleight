; error: `fn-same` takes functions, and `a` : `T` is not one
(def-fns _ $ (many f : (erased Type T) (many T a) (many T b at a) -> (many (Nat) r))
  (let ((many s)) (fn-same a b))
  0)
