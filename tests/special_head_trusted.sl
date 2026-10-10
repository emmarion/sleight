; expect: 2
; A run-position let-match makes a hidden special form's type known, and a forwarded Const keeps dispatching in a body.
(def-fns _ $ (many make : -> (erased Type T) (many T v) (erased (Eq Type T (Special)) p))
  (values (Special) let (Refl Type (Special))))

(let ((erased T) (many v) (erased p)) (make))
(let-match erased p (Refl t x))
(v ((many a)) (Succ (Zero)))

(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) r))
  (let ((many w)) v)
  (w ((many b)) (Succ n))
  b)

(f a)
