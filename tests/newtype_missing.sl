; error: has no opened newtype Matchable

(def-adts $ Meters : -> Type
  enum
  (many MkMeters : (many (Nat) n) -> (Meters)))

(let (many one) (Succ (Zero)))
(coerce one (coercible-wrap (Shared) MkMeters one))
