; needs: list
; error: type mismatch
; Shadowing False after explode is defined cannot feed the new, inhabited False to it:
; explode captured the original empty False by entry identity (section 9).

(def-adts $ False : -> Type enum)
(def-lvl X)
(def-fns X $ many explode : (erased Type A) (many (False) f) -> (many A a) f)

(def-adts $ False : -> Type enum (many Yes : -> (False)))
(def-lvl Y)
(let (erased p) (prove-predates explode Y))
(def-fns Y $ many boom : -> (many (Nat) n)
  (explode (predates p) (Nat) (Yes)))
(boom)
