; needs: list
; error: returns an application of a type constructor
; A ValCtor's return is a type-constructor application (section 12), so a bare type variable is refused.

(def-lvl X)

(def-fns X $ many use : (erased Type A) (many (ValCtor (many (Nat) n) -> A) C) (many (Nat) n) -> (many A a)
  (C n))
