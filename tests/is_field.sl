; needs: list
; expect: (Two _ _ $ Cons _ 0 $ Cons _ 1 $ Nil _)
; Pair is transparent (section 38), so a Two is represented as its list.
; Section 30's constructor with an is field.

(def-adts
  ((Pair : ((Nat) a) ((Nat) b) -> Type)
    enum
    (many Two : (erased (Nat) a) (erased (Nat) b)
       (many (Cons (Nat) a $ Cons (Nat) b $ Nil (Nat)) is lst) -> (Pair a b))))

(Two (Zero) (Succ (Zero)) (Cons (Nat) (Zero) $ Cons (Nat) (Succ (Zero)) $ Nil (Nat)))
