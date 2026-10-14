; expect: (Blue)
(def-adts $ (Color : -> Type)
  enum
  (many Red : -> (Color))
  (many Green : -> (Color))
  (many Blue : -> (Color)))

(def-fns _ $ (many next : (many (Color) c) -> (many (Color) d))
  (match many c _
    ((Red) (Green))
    ((Green) (Blue))
    ((Blue) (Red))))

(next $ next (Red))
