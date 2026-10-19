; error: return does not satisfy `at` `vacant-slot`
(def-adts $ (Tok : -> Type) enum
  (many MkTok : -> (Tok)))

(def-fns _ $ (many mk : (many (ValCtor -> (Tok)) c) -> (many (Tok) r at vacant-slot))
  (c))
