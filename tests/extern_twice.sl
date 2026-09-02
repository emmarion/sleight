; error: already bound
; An FFI implementation backs one declaration per program (ASSUMPTIONS 42).

(def-lvl X)
(def-fns X $ many extern nat-add : (many (Nat) a) (many (Nat) b) -> (many (Nat) c) a)
