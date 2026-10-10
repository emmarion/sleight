; prelude: none
; error: no extern implementation
(def-adts $ (Foo : -> Type)
  enum extern
  (many MkFoo : -> (Foo)))
