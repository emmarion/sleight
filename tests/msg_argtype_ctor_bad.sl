(def-adts $ (P : -> Type)
  enum
  (many MkP : (many (Nat) a) (many (Nat) b) -> (P)))
(MkP (Zero) (Nil (Nat)))
; error: tests/msg_argtype_ctor_bad.sl:4:13: error: argument 2, `b`, of `MkP`: type mismatch: expected `(Nat)`, got `(List (Nat))`
; error: tests/msg_argtype_ctor_bad.sl:3:3: note: value constructor `MkP` is declared here
