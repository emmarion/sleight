; error: return does not satisfy `at`
(def-fns _ $ (many bad : (unique (Nat) x) (unique (Nat) y)
    (erased (Eq (Nat) x y) same) -> (unique (Nat) r at x))
  (let-match erased same (Refl _ _)) y)
