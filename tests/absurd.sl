; expect: _
; DESIGN.md section 39: an absurd function.

(def-adts $ (Void : -> Type)
  enum)

(def-lvl absurd-lvl)

(def-fns absurd-lvl $ (many absurd explode : (erased Type A) (many (Void) f) ->
    (many A a))
  f)

explode
