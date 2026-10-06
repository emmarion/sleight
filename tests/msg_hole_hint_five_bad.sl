(def-fns _ $ (many f : (many (Nat) a) (many (Nat) b) (erased (Lt a b) p) -> (many (Nat) r)) a)
(def-fns _ $ (many g : (many (Nat) a) (many (Nat) b) (erased (Lt a b) p1) (erased (Lt a b) p2) (erased (Lt a b) p3)
    (erased (Lt a b) p4) (erased (Lt a b) p5) -> (many (Nat) r))
  (f a b _))
(Zero)
; error: hint: `_?1` has type `(Lt a b)`, as do:
; error: hint: `p5`, bound here
; error: hint: `p1`, bound here
