; expect: 0
; warn-unused: no
(def-fns _ $ (many g : (many (Copy (Nat)) x) (erased (Placed (slot-of x) (Copy (Nat)) x) pw) -> (many (Nat) r))
  0)

(def-fns _ $ (many h : (many (Nat) n) -> (many (Nat) r))
  (let ((many c)) (MkCopy _ n))
  (let ((erased q)) (place-at-many _ c))
  (g (MkCopy _ n) q))

(h 5)
