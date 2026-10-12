; two real branches on a union need a discriminant it does not have
(def-adts
  ((Shape : -> Type)
    union
    (many Dot : -> (Shape))
    (many Seg : (many (Nat) len) -> (Shape))))
(def-fns _ $ (many len : (many (Shape) s) -> (many (Nat) n))
  (match many s _
    ((Dot) 0)
    ((Seg l) l)))
(len (Seg 4))
