; error: is not a statement
; A forwarding binder's annotation, checked under a branch's hypothesis, does not change the minted type it forwards.
(def-fns _ $ (many make : -> (erased Type T) (many T v))
  (values (Special) let))

(let ((erased T) (many v)) (make))

(def-fns _ $ (many hyp : (erased (Eq Type T (Special)) p) -> (many (Nat) r))
  (let-match erased p (Refl t x))
  (let ((many (Special) w)) v)
  (w ((many y)) (Zero))
  y)

(Zero)
