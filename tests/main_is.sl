; error: a final function must be `(Fn L (many (String) x) -> (many (String) y))` or `(Fn L -> (many T y))`
(def-fns _ $ (many identity : (many (String) x) -> (many x is y)) x)
identity
