; expect: (Cons _ 5 $ Cons _ 7 $ Nil _)

(def-adts
  ((Either : ((Bool) k) -> Type)
    union newtype
    (many Left : (many (Nat) x) -> (Either (BTrue)))
    (many Right : (many (Nat) y) -> (Either (BFalse)))))

(def-fns _ $ (many at unwrap : (erased (Bool) k) (many (Either k) e) -> (many (Nat) n at e))
  (match many e (at (((Nat) n at e)))
    ((Left x) x)
    ((Right y) y)))

(Cons _ (unwrap _ (Left 5)) $ Cons _ (unwrap _ (Right 7)) $ Nil _)
