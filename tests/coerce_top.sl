; needs: list
; expect: (Succ (Zero))
; coerce in run position, with a proof by reflexivity and by wrapping.

(def-adts $ Meters : -> Type
  enum
  (many MkMeters : (many (Nat) n) -> (Meters)))

(let (many one) (Succ (Zero)))
(let (many m) (coerce one (coercible-wrap MkMeters one)))
(let (many (MkMeters one) is m2) m)
(let (many n) (coerce m2 (coercible-trans (coercible-sym (coercible-wrap MkMeters one)) (coercible-refl one))))
n
