; error: tests/compile_error.sl:6:54: error: in a type
; `compile-error` stops elaboration wherever it stands, here a signature's type.

(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) m))
  n)
(def-fns _ $ (many g : (many (Nat) n) -> (many (Pair (compile-error "in a type") (Nat)) m))
  n)
