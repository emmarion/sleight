; error: return does not satisfy `at` `(slot-of x)`
; An erased function's `at` promise is checked (section 14): unchecked, the proof it returns would equate
; the slots of `a` and `b`, and `id2` would read `a`'s word for `b`.
(def-fns _ $ (erased lie : (many (Nat) x) (many (Nat) y) ->
    (erased (Nat) r at x) (erased (Eq (Slot) (slot-of r) (slot-of y)) p))
  (values y (Refl _ (slot-of y))))
(def-fns _ $ (many id2 : (many (Nat) x) (many (Nat) y at x) -> (many (Nat) r)) y)
(def-fns _ $ (many go : (many (Nat) a) (many (Nat) b) -> (many (Nat) r))
  (let ((erased r) (erased p)) (lie a b))
  (let-match erased p (Refl _ _))
  (id2 a b))
(go 1 2)
