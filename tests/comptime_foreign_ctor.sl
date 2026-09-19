; error: A is not a constructor of Nat
; comptime-match may only assert a constructor of the scrutinee's own type, even one whose index and arity happen to match.

(def-adts $ T : -> Type
  enum
  (many A : -> (T))
  (many B : -> (T)))
(let (many z) (Zero))
(comptime-match many z (A))
