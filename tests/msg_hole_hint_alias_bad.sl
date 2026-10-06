(def-fns _ $ (many f : (many (Nat) a) (many (Nat) b) (erased (Lt a b) p) -> (many (Nat) r)) a)
(def-fns _ $ (many g : (many (Nat) a) (many (Nat) b) (erased (Lt a b) lt) -> (many (Nat) r))
  (let ((erased also)) lt)
  (f a b _))
(Zero)
; error: hint: `_?1` has type `(Lt a b)`, as does:
; error: tests/msg_hole_hint_alias_bad.sl:3:9: hint: `also`, bound here
