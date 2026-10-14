(def-adts $ (Counter : -> Type)
  enum
  (many MkCounter : (many (Nat) n) -> (Counter)))

(def-fns _ $ (many twice : (unique (Counter) c) -> (unique (Counter) d) (unique (Counter) e))
  (values c c))
; error: unique value `c` has conflicting non-erased uses
