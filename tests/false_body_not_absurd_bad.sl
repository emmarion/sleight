; error: type mismatch
; A body that is a value of an empty type is still checked against the declared
; return telescope unless the function is marked absurd (DESIGN.md section 25):
; without the marker (Void) is not A. shadow_false_capture.sl is this program
; with the marker, where the point is what happens after it.

(def-adts $ (Void : -> Type) enum)
(def-lvl X)
(def-fns X $ (many explode : (erased Type A) (many (Void) f) -> (many A a)) f)
explode
