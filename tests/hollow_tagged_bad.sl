; error: return does not satisfy `at` `vacant-slot`
(def-adts $ (Two : -> Type) enum
  (many One : -> (Two))
  (many Other : -> (Two)))

(def-fns _ $ (many one : -> (many (Two) r at vacant-slot))
  (Other))
