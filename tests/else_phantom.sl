; needs: absurd
; expect: 1
; An else covering only phantom constructors under a many scrutinee can never run: it counts as no real branch and
; its body is erased throughout, so returning an erased variable is accepted.

(def-adts
  ((Wrapped : -> Type)
    union
    (many W : (many (Nat) n) -> (Wrapped))
    (erased E : (erased (False) f) -> (Wrapped))))

(def-lvl X)

(def-fns X $ (many unwrap : (many (Wrapped) w) (erased (Nat) hidden) -> (many (Nat) n))
  (match many w (((Nat) r))
    ((W n) n)
    (else hidden)))

(unwrap (W (Succ (Zero))) (Zero))
