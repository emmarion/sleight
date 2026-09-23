; needs: list
; error: erased constructor `Ghost` in a non-erased position

(def-adts
  ((Opt : -> Type)
    enum
    (many OSome : (many (Nat) n) -> (Opt))
    (erased Ghost : (erased (Nat) n) -> (Opt))))

(Ghost (Zero))
