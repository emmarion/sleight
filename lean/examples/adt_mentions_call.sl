; a def-adts signature may mention a call's result, typed by the callee's returns
(def-fns L $ (many f : (many (Nat) n) -> (many (Nat) m))
  n)
(let ((many h)) (f (Zero)))
(def-adts
  ((Bad : -> Type)
    enum
    (many MkBad : (many (Nat) b) (many (Succ h) is c) -> (Bad))))
(Zero)
