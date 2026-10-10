; error: the message of `compile-error` must be a `Const`, non-erased `String`; `s` is `Dyn`
(def-fns _ $ (many f : (many (String) s) -> (many (Nat) m))
  (compile-error s))
