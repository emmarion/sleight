(def-adts
  ((Two : ((Nat) a) -> Type)
    enum
    (many MkTwo : (many (Nat) a) (many (Succ (Succ a)) is s) -> (Two a))))
(MkTwo (Zero) (Succ (Zero)))
