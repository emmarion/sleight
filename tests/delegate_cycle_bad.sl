; error: the function a `delegate` call names must be introduced before the function whose body it is
; Two functions of one block delegating to each other: the first names a later function of its block.

(def-adts $ (Inf : -> Type)
  enum
  (many MkInf : (erased (Inf) i) -> (Inf)))

(def-lvl L)
(def-fns L
  ((many f : (many (Nat) n) (subterm erased (Inf) k) -> (many (Nat) m))
    (let-match erased k (MkInf i))
    (let ((erased p)) (prove-subterm i k))
    (delegate (g n (subterm p) i)))
  ((many g : (many (Nat) n) (subterm erased (Inf) k) -> (many (Nat) m))
    (let-match erased k (MkInf i))
    (let ((erased p)) (prove-subterm i k))
    (delegate (f n (subterm p) i))))
