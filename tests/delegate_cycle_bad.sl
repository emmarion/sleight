; error: unbound name `g`
; Two functions of one block delegating to each other: the first's header names a later function of its block,
; which a header does not see (sections 41, 53).

(def-adts $ (Inf : -> Type)
  enum
  (many MkInf : (erased (Inf) i) -> (Inf)))

(def-lvl L)
(def-fns L
  ((many f at g : (many (Nat) n) (subterm erased (Inf) k) -> (many (Nat) m))
    (let-match erased k (MkInf i))
    (let ((erased p)) (prove-subterm i k))
    (delegate (g n (subterm p) i)))
  ((many g at f : (many (Nat) n) (subterm erased (Inf) k) -> (many (Nat) m))
    (let-match erased k (MkInf i))
    (let ((erased p)) (prove-subterm i k))
    (delegate (f n (subterm p) i))))
