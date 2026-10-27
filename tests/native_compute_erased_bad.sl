; error: `native-compute` produces its results at `many`
(def-adts $ (B : -> Type) enum (many T : -> (B)) (many F : -> (B)))
(def-fns _ $ (many fine : -> (many (B) r)) (T))
(let ((erased a) (many b)) (native-compute fine fine))
