; error: a type constructor declares one return
; The signature bracket makes the return telescope's extent written rather than guessed, so a form after the
; one Type a type constructor returns is a mistake rather than the start of the body.

(def-adts ((T : -> Type junk) enum (many A : -> (T))))
(A)
