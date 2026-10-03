; error: only one real branch
; Several wrapping constructors do not give a union newtype a runtime discriminant: a match still has one
; real branch.

(def-adts
  ((Either : ((Bool) k) -> Type)
    union newtype
    (many Left : (many (Nat) x) -> (Either (BTrue)))
    (many Right : (many (Nat) y) -> (Either (BFalse)))))

(def-fns _ $ (many pick : (erased (Bool) k) (many (Either k) e) -> (many (Nat) n))
  (match many e _
    ((Left x) x)
    ((Right y) y)))
