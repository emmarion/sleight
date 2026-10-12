; a union has no runtime discriminant, so a non-erased match on one has one real branch (DESIGN.md section 21)
(def-adts
  ((Shape : ((Nat) k) -> Type)
    union
    (many Dot : -> (Shape (Zero)))
    (many Seg : (many (Nat) len) -> (Shape (Succ (Zero))))))
(def-fns _ $ (many len : (many (Shape (Succ (Zero))) s) -> (many (Nat) n))
  (match many s _
    (absurd Dot)
    ((Seg l) l)))
(len (Seg 4))
