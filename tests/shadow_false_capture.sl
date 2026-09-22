; needs: list
; error: type mismatch
; Shadowing Void after explode is defined cannot feed the new, inhabited Void to it:
; explode captured the original empty Void by entry identity (section 9).

(def-adts $ (Void : -> Type) enum)
(def-lvl X)
(def-fns X $ (many explode : (erased Type A) (many (Void) f) -> (many A a)) f)

(def-adts $ (Void : -> Type) enum (many Yes : -> (Void)))
(def-lvl Y)
(let ((erased p)) (prove-predates explode Y))
(def-fns Y $ (many boom : -> (many (Nat) n))
  (explode (predates p) (Nat) (Yes)))
(boom)
