(def-adts
  ((Opt : -> Type)
    enum
    (many None : -> (Opt))
    (erased Hidden : (erased (Nat) n) -> (Opt))))
(let ((many o)) (Hidden (Zero)))
o
