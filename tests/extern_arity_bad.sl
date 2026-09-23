; error: the extern implementation of `trim` takes 1 arguments, its model 2
(def-fns _ $ (many extern trim : (many (String) s) (many (String) t) -> (many (String) r)) s)
(trim "a" "b")
