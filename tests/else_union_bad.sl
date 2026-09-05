; needs: absurd
; error: only one real branch
; A union has no runtime discriminant, so an else beside a present branch is refused as in tests/union_two_real.sl.

(def-adts
  (Wrapped : -> Type
    union
    (many W : (many (Nat) n) -> (Wrapped))
    (many E : (erased (False) f) -> (Wrapped))))

(def-lvl X)

(def-fns X $ many unwrap : (many (Wrapped) w) -> (many (Nat) n)
  (match many w (((Nat) r))
    ((W n) n)
    (else (Zero))))

(unwrap (W (Succ (Zero))))
