; error: only the prelude may mark a definition `extern`
(def-adts $ (Foo : -> Type) enum extern (many MkFoo : -> (Foo)))
