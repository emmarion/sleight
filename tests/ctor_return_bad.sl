; needs: list
; error: must return an application of

(def-adts
  (Wrong : -> Type
    enum
    (many Oops : -> (Nat))))
