; error: return does not satisfy `at` `vacant-slot`
(def-adts $ (Mark : -> Type) union
  (many MA : -> (Mark))
  (many MB : (many (Nat) n) -> (Mark)))

(def-fns _ $ (many ma : -> (many (Mark) r at vacant-slot))
  (MA))
