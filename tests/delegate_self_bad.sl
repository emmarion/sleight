; error: the function a `delegate` call names must be introduced before the function whose body it is
; A delegate may not name the function whose body it is, even where its decrease is in order.

(def-adts $ (Inf : -> Type)
  enum
  (many MkInf : (erased (Inf) i) -> (Inf)))

(def-lvl L)
(def-fns L $ (many f : (many (Nat) n) (subterm erased (Inf) k) -> (many (Nat) m))
  (let-match erased k (MkInf i))
  (let ((erased p)) (prove-subterm i k))
  (delegate (f n (subterm p) i)))
