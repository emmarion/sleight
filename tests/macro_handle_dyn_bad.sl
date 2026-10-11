; error: `y` is `Hypothetical`, and a handle names a `Settled` entry
(def-fns _ $ (many g : (many (Nat) y) -> (many (Nat) r))
  (let ((many h)) (settled-of many y))
  y)
