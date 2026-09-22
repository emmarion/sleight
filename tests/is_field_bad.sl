; needs: list
; error: value mismatch

(def-adts
  ((Pair : ((Nat) a) ((Nat) b) -> Type)
    enum
    (many Two : (erased (Nat) a) (erased (Nat) b)
       (many (Cons (Nat) a $ Cons (Nat) b $ Nil (Nat)) is lst) -> (Pair a b))))

(Two (Zero) (Succ (Zero)) (Nil (Nat)))
