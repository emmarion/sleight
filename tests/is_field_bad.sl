; needs: list
; error: value mismatch

(def-adts
  ((Duo : ((Nat) a) ((Nat) b) -> Type)
    enum
    (many Two : (erased (Nat) a) (erased (Nat) b)
       (many (Cons (Nat) a $ Cons (Nat) b $ Nil (Nat)) is lst) -> (Duo a b))))

(Two (Zero) (Succ (Zero)) (Nil (Nat)))
