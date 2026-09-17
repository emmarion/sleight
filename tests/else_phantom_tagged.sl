; needs: absurd
; expect: 1
; An else standing only for a phantom constructor beside two listed non-phantom ones: the enum stays tagged on the
; two, the else adds no real branch and is checked erased.

(def-adts $ Three : -> Type
  enum
  (many A : -> (Three))
  (many B : -> (Three))
  (erased P : (erased (False) f) -> (Three)))

(def-lvl X)

(def-fns X $ many pick : (many (Three) t) (erased (Nat) hidden) -> (many (Nat) n)
  (match many t (((Nat) r))
    ((A) (Zero))
    ((B) (Succ (Zero)))
    (else hidden)))

(pick (B) (Zero))
