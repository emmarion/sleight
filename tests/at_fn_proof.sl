; expect: 7
; `at-fn-of` fetches the proof `def-fns` minted and `open-at-fn` opens it where a first-class function is
; called, so the call through the parameter is skipped (AT_REDESIGN A10); without the open it runs the
; dummy body, which performs nothing, and the caller reads the result off its argument either way.
(def-fns _ $ (many at same : (many (Nat) x) -> (many (Nat) r at x)) x)
(def-fns _ $ (many apply : (many (Fn (level-of same) (many (Nat) x) -> (many (Nat) r at x)) f)
    (erased (AtFn (Fn (level-of same) (many (Nat) x) -> (many (Nat) r at x)) f) p) (many (Nat) n) -> (many (Nat) r at n))
  (open-at-fn p)
  (at (f n)))
(def-fns _ $ (many apply-plain : (many (Fn (level-of same) (many (Nat) x) -> (many (Nat) r at x)) f)
    (many (Nat) n) -> (many (Nat) r at n))
  (f n))
(let ((many a)) (apply same (at-fn-of same) 7))
(apply-plain same a)
