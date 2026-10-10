(def-adts $ (P : ((Nat) n) -> Type)
  enum
  (many MkP : (erased (Nat) n) (erased (Lt (Zero) n) p) -> (P n)))
(MkP u8-modulus _)
; error: cannot infer `__?1` in `(MkP u8-modulus __?1)`
; error: tests/msg_hole_hint_prelude_bad.sl:4:17: hint: `__?1` has type `(Lt (Zero) u8-modulus)`, as does:
; error: hint: `u8-modulus-pos`, bound here
