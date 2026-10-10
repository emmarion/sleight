; expect: (MkP "a\xc3\xa9\x01\x7f~ \n\t\"\\" #\xc3)
(def-adts $ (P : -> Type)
  enum
  (many MkP : (many (String) s) (many (Char) c) -> (P)))
(MkP "a\xc3\xA9\x01\x7f~ \n\t\"\\" #\xc3)
