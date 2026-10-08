; prelude: none
; expect: (Succ $ Succ $ Succ $ Zero)
; A function marked `extern` and `at` has no implementation (section 39): the marks are a promise, the
; model body is checked, and passing it where a plain function is expected runs a dummy that cannot crash.
(def-adts $ (Nat : -> Type) enum (many Zero : -> (Nat)) (many Succ : (many (Nat) pred) -> (Nat)))
(def-fns _ $ (many extern at keep : (many (Nat) x) -> (many (Nat) r at x)) x)
(def-fns _ $ (many apply-plain : (many (Fn (level-of keep) (many (Nat) x) -> (many (Nat) r at x)) f)
    (many (Nat) n) -> (many (Nat) r at n))
  (f n))
(apply-plain keep (Succ $ Succ $ Succ $ Zero))
