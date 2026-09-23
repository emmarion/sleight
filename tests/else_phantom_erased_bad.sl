; needs: absurd
; error: constructor `E` has 0 branches
; Under an erased scrutinee a phantom constructor's branch is an ordinary one, so it must be listed or covered.

(def-adts
  ((Wrapped : -> Type)
    union
    (many W : (many (Nat) n) -> (Wrapped))
    (erased E : (erased (False) f) -> (Wrapped))))

(def-lvl X)

(def-fns X $ (many f : (erased (Wrapped) w) -> (many (Nat) n))
  (match erased w (((Nat) r))
    ((W n) (Zero))))

(f (W (Zero)))
