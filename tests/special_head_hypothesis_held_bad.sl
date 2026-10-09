; error: is not a statement
; The same holds when the hidden value is a special form: only run-position facts can show it to be one.
(def-fns _ $ (many make : -> (erased Type T) (many T v))
  (values (Special) let))

(let ((erased T) (many v)) (make))

(def-fns _ $ (many hyp : (erased (Eq Type T (Special)) p) -> (many (Nat) r))
  (match erased p (((Nat) r))
    ((Refl t x)
      (v ((many y)) (Zero))
      y)))

(Zero)
