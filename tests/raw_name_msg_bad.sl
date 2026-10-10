; error: type mismatch: expected `(Nat)`, got `(Fn (level-of #"f g") (many (#"T t") #"x y") -> (many (#"T t") #"_"))`
(def-adts $ (#"T t" : -> Type) enum (many #"A b" : -> (#"T t")))
(def-fns _ $ (many #"f g" : (many (#"T t") #"x y") -> (many (#"T t") #"_")) #"x y")
(let ((many (Nat) n)) #"f g")
