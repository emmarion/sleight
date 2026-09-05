; needs: absurd
; error: erased
; An else standing for a phantom constructor and a non-phantom one is a real branch, so its body is not exempt from
; the match's erasures: returning an erased variable is refused.

(def-adts $ Three : -> Type
  enum
  (many A : -> (Three))
  (many B : -> (Three))
  (erased P : (erased (False) f) -> (Three)))

(def-lvl X)

(def-fns X $ many pick : (many (Three) t) (erased (Nat) hidden) -> (many (Nat) n)
  (match many t (((Nat) r))
    ((A) (Zero))
    (else hidden)))

(pick (B) (Zero))
