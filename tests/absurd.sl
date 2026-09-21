; expect: _
; DESIGN.md section 39: an absurd function.

(def-adts $ False : -> Type
  enum)

(def-lvl X)

(def-fns X $ many absurd explode : (erased Type A) (many (False) f) ->
    (many A a)
  f)

explode
