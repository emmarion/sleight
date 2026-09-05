; needs: absurd
; error: type mismatch
; The else in tests/phantom_false_bad.sl's boo still owes an erased False, and the scrutinee is not one.

(def-adts $ Ghost : -> Type
  enum
  (erased G : -> (Ghost)))

(def-lvl X)

(def-fns X $ many boo : (many (Ghost) g) -> (many (False) x)
  (match many g (((False) x))
    (else g)))

(boo (G))
