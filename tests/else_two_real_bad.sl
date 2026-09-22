; error: only one real branch
; An else counts as a real branch, so beside a present branch under an erased scrutinee it is one too many.

(def-lvl X)

(def-fns X $ (many f : (erased (Nat) n) -> (many (Nat) m))
  (match erased n (((Nat) r))
    ((Zero) (Zero))
    (else (Succ (Zero)))))

(f (Zero))
