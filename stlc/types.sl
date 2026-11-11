(def-adts $ (Ty : -> Type)
  enum
  (many Base : -> (Ty))
  (many Arr : (many (Ty) dom) (many (Ty) cod) -> (Ty)))
