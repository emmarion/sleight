; expect: 3
; A function marked `extern` and `at` has no implementation (section 39): the marks are a promise, the
; model body is checked, and passing it where a plain function is expected runs a dummy that cannot crash.
(def-fns _ $ (many extern at keep : (many (Nat) x) -> (many (Nat) r at x)) x)
(def-fns _ $ (many apply-plain : (many (Fn (level-of keep) (many (Nat) x) -> (many (Nat) r at x)) f)
    (many (Nat) n) -> (many (Nat) r at n))
  (f n))
(apply-plain keep 3)
