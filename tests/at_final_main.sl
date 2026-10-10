; error: a final function must be `(Fn L (many (String) x) -> (many (String) y))` or `(Fn L -> (many T y))`
(def-fns _ $ (many main : (many (String) s) -> (many (String) r at s)) s)
main
