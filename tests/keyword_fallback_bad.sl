(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))
(let ((many ->)) (Zero))
(let ((many (Nat) z)) inc)
(Zero)
; warns: tests/keyword_fallback_bad.sl:3:7: warning: declaration of `->` shadows a built-in
; error: error: type mismatch: expected `(Nat)`, got `(Fn _1 (many (Nat) n) _-> (many (Nat) m))`
; error: tests/keyword_fallback_bad.sl:1:10: note: `_1` is anonymous, minted here
; error: note: `_->` is the built-in `->`, which no name in scope denotes here
