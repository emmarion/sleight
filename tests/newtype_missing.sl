; error: has no Newtype in scope
; coercible-wrap needs the type's Newtype in ambient scope (section 38); an unmarked type has none.

(def-adts $ Meters : -> Type
  enum
  (many MkMeters : (many (Nat) n) -> (Meters)))

(let (many one) (Succ (Zero)))
(coerce one (coercible-wrap MkMeters one))
