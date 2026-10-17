; expect: 2
; An erased parameter written `at` an erased or a non-erased variable (section 36): the argument for it must
; sit where the target's does, here the same variable or an erased binder forwarding it.
(def-fns _ $ (many f : (erased (Nat) x) (erased (Nat) _y at x) -> (many (Nat) r)) 0)
(def-fns _ $ (many h : (many (Nat) x) (erased (Nat) _y at x) -> (many (Nat) r)) x)
(def-fns _ $ (many g : (erased (Nat) a) (many (Nat) b) -> (many (Nat) r))
  (let ((erased c)) a)
  (let ((many _)) (f a c))
  (h b b))
(g 1 2)
