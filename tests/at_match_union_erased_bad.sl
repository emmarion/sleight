; error: only one real branch

(def-adts
  ((Either : ((Bool) k) -> Type)
    union newtype
    (many Left : (many (Nat) x) -> (Either (BTrue)))
    (many Right : (many (Nat) y) -> (Either (BFalse)))))

(def-fns _ $ (many same : (erased (Bool) k) (many (Either k) e) -> (many (Either k) r at e))
  (match erased e (at (((Either k) r at e)))
    ((Left x) e)
    ((Right y) e)))
