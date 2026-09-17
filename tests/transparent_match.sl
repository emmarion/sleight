; needs: list
; expect: 1
; Matching on a transparent enum binds the field to the value itself.

(def-adts $ Meters : -> Type
  enum
  (many MkMeters : (many (Nat) n) -> (Meters)))

(def-lvl X)
(def-fns X $ many unwrap : (many (Meters) m) -> (many (Nat) n)
  (match many m (((Nat) r))
    ((MkMeters n) n)))

(unwrap (MkMeters (Succ (Zero))))
