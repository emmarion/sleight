; expect: 1
; An else alone under an erased scrutinee is the match's one real branch, so no dispatch is needed.

(def-lvl X)

(def-fns X $ (many f : (erased (Nat) n) -> (many (Nat) m))
  (match erased n (((Nat) r))
    (else (Succ (Zero)))))

(f (Zero))
