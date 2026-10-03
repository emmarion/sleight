; expect: 1
; Each wrapping constructor of a union newtype is at its field (UNIQUE.md U9), the second as the first.

(def-adts
  ((Either : ((Bool) k) -> Type)
    union newtype
    (many Left : (unique (Nat) x) -> (Either (BTrue)))
    (many Right : (unique (Nat) y) -> (Either (BFalse)))))

(def-fns _ $ (many wrap-right : (unique (Nat) y) -> (unique (Either (BFalse)) r at y)) (Right y))
(def-fns _ $ (many unwrap-right : (unique (Either (BFalse)) e) -> (unique (Nat) r at e))
  (let-match unique e (Right y)) y)
(let ((unique r)) (unwrap-right (wrap-right (Succ (Zero)))))
(share r)
