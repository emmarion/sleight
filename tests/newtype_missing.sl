; error: has no Newtype open
; coercible-wrap needs the constructor's Newtype opened (section 38, proposals/matchable-newtype-opening.md);
; an unmarked type mints none.

(def-adts $ Meters : -> Type
  enum
  (many MkMeters : (many (Nat) n) -> (Meters)))

(let (many one) (Succ (Zero)))
(coerce one (coercible-wrap MkMeters one))
