(def-adts $ (P3 : -> Type)
  enum
  (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P3)))
(MkP (Zero) (Zero))
; error: tests/arity_ctor_bad.sl:4:1: error: `MkP` expects 3 arguments, got 2
; error: tests/arity_ctor_bad.sl:3:3: note: `MkP` takes `(many (Nat) a) (erased (Nat) b) (many (Nat) c)`
