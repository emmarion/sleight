; needs: absurd
; error: only one real branch
; Under an erased scrutinee a phantom constructor's branch is ordinary, so an else standing for it is a real branch
; beside the listed one.

(def-adts
  (Wrapped : -> Type
    union
    (many W : (many (Nat) n) -> (Wrapped))
    (erased E : (erased (False) f) -> (Wrapped))))

(def-lvl X)

(def-fns X $ many f : (erased (Wrapped) w) -> (many (Nat) n)
  (match erased w (((Nat) r))
    ((W n) (Zero))
    (else (Succ (Zero)))))

(f (W (Zero)))
