; needs: list
; expect: (Succ (Zero))
; comptime-match on a Const of a transparent type projects the value itself as the field.

(def-adts $ Meters : -> Type
  enum
  (many MkMeters : (many (Nat) n) -> (Meters)))

(let (many m) (MkMeters (Succ (Zero))))
(comptime-match m (MkMeters n))
n
