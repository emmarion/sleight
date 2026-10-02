(let ((erased Type)) (Nat))
(def-fns _ $ (many f : (many List xs) -> (many (Nat) m))
  (Zero))
; error: type mismatch: expected `(Univ)`, got `(TyCtor ((Univ) A) -> (Univ))`
; warns: tests/universe_shadowed_bad.sl:1:7: warning: declaration of `Type` shadows a built-in
