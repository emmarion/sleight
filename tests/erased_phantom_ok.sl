; needs: list
; expect: (Zero)
; With an erased scrutinee a phantom branch is an ordinary branch: here it is the only one that is not refuted.

(def-adts
  (Opt : ((Nat) n) -> Type
    enum
    (many Some : -> (Opt (Zero)))
    (erased Ghost : -> (Opt (Succ (Zero))))))

(def-lvl X)
(def-fns X $ many f : (erased (Opt (Succ (Zero))) o) -> (many (Nat) n)
  (match erased o (((Nat) r))
    (absurd Some)
    ((Ghost) (Zero))))

(f (Ghost))
