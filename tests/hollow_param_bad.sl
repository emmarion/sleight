; error: return does not satisfy `at` `vacant-slot`
(def-adts $ (Tok : -> Type) enum
  (many MkTok : (erased (Nat) n) -> (Tok)))

(def-fns _ $ (many same : (many (Tok) t) -> (many (Tok) r at vacant-slot))
  t)
