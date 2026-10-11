; error: the message of `compile-error` must be a `Settled`, non-erased `String`; `s` is `Hypothetical`
(def-fns _ $ (many f : (many (String) s) -> (many (Nat) m))
  (compile-error s))
