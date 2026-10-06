(def-fns _ $ (many k : (many (Nat) p) -> (many (Nat) y))
  (match many p _ ((k a) p) (else p)))
; error: tests/msg_pattern_not_ctor_bad.sl:2:20: error: `k` is not a constructor of `Nat`
; error: lib/prelude.sl:<**>: note: type constructor `Nat` is declared here
