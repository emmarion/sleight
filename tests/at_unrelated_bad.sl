; error: return does not satisfy `at`
(def-adts $ (Box : -> Type) enum (many B : (many (Nat) n) -> (Box)))
(def-fns _ $ (many bad : (unique (Box) x) -> (unique (Box) r at x))
  (B (Zero)))
