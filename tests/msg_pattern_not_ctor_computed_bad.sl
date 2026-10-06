(def-fns _ $ (many id : (many (Nat) v) -> (many (Nat) w)) v)
(def-fns _ $ (many k : (many (Nat) p) -> (many (Nat) y))
  (match many (id p) _ ((k a) p) (else p)))
; error: tests/msg_pattern_not_ctor_computed_bad.sl:3:25: error: `k` is not a constructor of `Nat`
; error: lib/prelude.sl:<**>: note: type constructor `Nat` is declared here
