; error: `y` is `Dyn`, and a handle names a `Const`
(def-fns _ $ (many g : (many (Nat) y) -> (many (Nat) r))
  (let ((many h)) (constant-of many y))
  y)
