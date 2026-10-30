; needs: ../std/list ../std/macro ../std/buffer
; error: `instances` takes a list of substitutions, then the forms they instantiate
(instances x (def-fns _ $ (many f : -> (many (Nat) n)) 0))
