; error: unbound name `f`
; A delegate may not name the function whose body it is, even where its decrease is in order: its header does
; not see it (sections 41, 53).

(def-adts $ (Inf : -> Type)
  enum
  (many MkInf : (erased (Inf) i) -> (Inf)))

(def-lvl L)
(def-fns L $ (many f at f : (many (Nat) n) (subterm erased (Inf) k) -> (many (Nat) m))
  (let-match erased k (MkInf i))
  (let ((erased p)) (prove-subterm i k))
  (delegate (f n (subterm p) i)))
