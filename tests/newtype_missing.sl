; error: has no Newtype open
; coercible-wrap needs the constructor's Newtype opened (DESIGN.md sections 19 and 38);
; an unmarked type mints none.

(def-adts $ Meters : -> Type
  enum
  (many MkMeters : (many (Nat) n) -> (Meters)))

(let (many one) (Succ (Zero)))
(coerce one (coercible-wrap MkMeters one))
