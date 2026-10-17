; expect: 2
; A def-adts inside a body whose erased field's type mentions the enclosing function's parameter n, closed over.

(def-lvl X)
(def-fns X $ (many same : (many (Nat) n) -> (many (Nat) m))
  (def-adts $ (Same : -> Type)
    enum
    (many MkSame : (many (Nat) k) (erased (Eq (Nat) n k) e) -> (Same)))
  (let ((many s)) (MkSame n (Refl (Nat) n)))
  (match many s (((Nat) r))
    ((MkSame k _) (Succ k))))
(same (Succ (Zero)))
