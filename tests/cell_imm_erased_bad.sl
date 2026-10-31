; error: `imm` cannot mark an erased argument
(def-adts $ (Tag : (Type A) -> Type)
  enum
  (many MkTag : (erased Type A) (many (U62) x) -> (Tag A)))

(def-fns _ $ (many f : (unique (Tag (Nat)) t) -> (unique (Tag (Nat)) r at t))
  (let-match unique t (MkTag _ x u))
  (u (imm (ImmVacant) ImmVacant) _ x))
