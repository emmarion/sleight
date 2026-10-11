; needs: list
; expect: 2
; A def-adts inside a body: a constructor's return mentions a parameter, and the constructors are Hypothetical,
; built and matched at runtime.

(def-lvl X)
(def-fns X $ (many twice : (many (Nat) n) -> (many (Nat) m))
  (def-adts $ (Holds : ((Nat) k) -> Type)
    enum
    (many Here : (many (Nat) a) -> (Holds n)))
  (let ((many h)) (Here n))
  (match many h (((Nat) r))
    ((Here a) (Succ a))))

(twice (Succ (Zero)))
