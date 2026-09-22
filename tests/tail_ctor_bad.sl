; needs: list
; error: marks a function call
; tail and delegate mark a call (section 9); a constructor application is not one.

(def-lvl X)

(def-fns X $ (many bump : (many (Nat) n) -> (many (Nat) m))
  (tail (Succ n)))
