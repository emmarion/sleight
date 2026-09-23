; error: tests/display_alias_bad.sl:7:13: error: type mismatch: expected `(Add x x s)`, got `(Add (Zero) s s)`
; A let binder is an alias of the call result it binds, which canonicalization keeps as the older, anonymous
; atom; a message names it by the binder still in scope, and points at the result that fails, not the header.

(def-fns _ $ (many f : (many (Nat) x) -> (many (Nat) y) (erased (Add x x y) p))
  (let ((many s) (erased q)) (add x x))
  (values s (AddZero s)))
(Zero)
