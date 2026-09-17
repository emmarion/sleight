; needs: list absurd
; expect: 1
; A transparent union: the other constructor has only erased fields and is refuted by proof.

(def-adts
  (Wrapped : -> Type
    union
    (many W : (many (Nat) n) -> (Wrapped))
    (many E : (erased (False) f) -> (Wrapped))))

(def-lvl X)
(def-fns X $ many unwrap : (many (Wrapped) w) -> (many (Nat) n)
  (match many w (((Nat) r))
    ((W n) n)
    (absurd (E f) f)))

(unwrap (W (Succ (Zero))))
